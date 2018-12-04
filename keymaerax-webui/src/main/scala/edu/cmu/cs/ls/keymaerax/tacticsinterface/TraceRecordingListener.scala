package edu.cmu.cs.ls.keymaerax.tacticsinterface

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.hydra.{ProofPOJO, ExecutionStepPOJO, DBAbstraction, ExecutionStepStatus}
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus

/**
  * Created by bbohrer on 11/20/15.
  */

/**
  * @param ruleName A display name merely for UI purposes
  */
class TraceRecordingListener(db: DBAbstraction,
                             proofId: Int,
                             initialSibling: Option[Int],
                             globalProvable: ProvableSig,
                             branch: Int,
                             ruleName: String) extends IOListener {

  class TraceNode(isFirstNode: Boolean) {
    var id: Option[Int] = None
    var parent: TraceNode = null
    var sibling: Option[Int] = None
    var local: ProvableSig = null
    var executable: BelleExpr = null
    var status: ExecutionStepStatus = null
    var reverseChildren: List[TraceNode] = Nil

    def children = reverseChildren.reverse

    /* This is generated by the DB, so it will not be present when we first create an object for the step. However,
       we need to set it once it has been generated so other steps can get the appropriate ID.
     */
    var stepId: Option[Int] = None
    val branchLabel: String = null
    val branchOrder: Int = branch
    val userExe = isFirstNode

    var localProvableId: Option[Int] = None
    var executableId: Option[Int] = None

    def getLocalProvableId: Option[Int] = {
      if (local != null && localProvableId.isEmpty)
        localProvableId = Some(db.createProvable(local))
      localProvableId
    }

    def getExecutableId: Int = {
      if (executable != null && executableId.isEmpty)
        executableId = Some(db.addBelleExpr(executable))
      executableId.get
    }

    def asPOJO: ExecutionStepPOJO = {
      //val parentStep = if (parent == null) None else parent.stepId
      ExecutionStepPOJO(stepId, proofId, sibling, branchOrder,
        status, getExecutableId, None, None,
        getLocalProvableId, userExe, ruleName,
        if (local != null) local.subgoals.size else -1,
        if (local != null) local.subgoals.size else -1)
    }
  }

  var youngestSibling: Option[Int] = initialSibling
  var node: TraceNode = null
  var isDead: Boolean = false
  var nodesWritten: List[TraceNode] = Nil

  /* Debug info: Records how deep inside the tree of begin-end pairs we are */
  var depth: Int = 0

  def begin(v: BelleValue, expr: BelleExpr): Unit = {
    synchronized {
      depth = depth + 1
      if (isDead) return
      val parent = node
      node = new TraceNode(isFirstNode = parent == null)
      node.parent = parent
      node.sibling = youngestSibling
      node.executable = expr
      node.status = ExecutionStepStatus.Running

      if (parent != null) {
        parent.status = ExecutionStepStatus.DependsOnChildren
        parent.reverseChildren = node :: parent.reverseChildren
      }
      if (parent == null) {
        node.stepId = Some(db.addExecutionStep(node.asPOJO))
        nodesWritten = node :: nodesWritten
      }
    }
  }

  def end(v: BelleValue, expr: BelleExpr, result: Either[BelleValue, BelleThrowable]): Unit = {
    synchronized {
      depth = depth - 1
      if (isDead) return
      val current = node
      node = node.parent
      youngestSibling = current.id
      current.status =
        result match {
          case Left(_) => ExecutionStepStatus.Finished
          case Right(_) => ExecutionStepStatus.Error
        }
      if (node != null) return
      //      db.updateExecutionStep(current.stepId.get, current.asPOJO)
      //      if (node == null) {
      //        result match {
      //          // Only reconstruct provables for the top-level because the meaning of "branch" can change inside a
      // tactic
      //          case Left(BelleProvable(p, _)) =>
      //            current.output = globalProvable(p, branch)
      //            current.local = p
      //          case _ =>
      //        }
      //        if (current.output != null) {
      //          db.updateExecutionStep(current.stepId.get, current.asPOJO)
      //          if (current.output.isProved) {
      //            val p = db.getProofInfo(proofId)
      //            val provedProof = new ProofPOJO(p.proofId, p.modelId, p.name, p.description, p.date, p.stepCount,
      //              closed = true, p.provableId, p.temporary)
      //            db.updateProofInfo(provedProof)
      //          }
      //        }
      //      }
      if (node == null) {
        result match {
          // Only reconstruct provables for the top-level because the meaning of "branch" can change inside a tactic
          case Left(BelleProvable(p, _)) =>
            // no longer want to construct global provables (want to allow halfway done substitutions)
            current.local = p
            db.updateExecutionStep(current.stepId.get, current.asPOJO)
            if (db.getPlainOpenSteps(proofId).isEmpty) {
              //@note proof might be done
              val p = db.getProofInfo(proofId)
              val provedProof = new ProofPOJO(p.proofId, p.modelId, p.name, p.description, p.date, p.stepCount,
                closed = true, p.provableId, p.temporary, p.tactic)
              db.updateProofInfo(provedProof)
            }
          case _ =>
            db.updateExecutionStep(current.stepId.get, current.asPOJO)
        }
      }
    }
  }

  /** Called by HyDRA before killing the interpreter's thread. Updates the database to reflect that the computation
    * was interrupted. There are two race conditions to worry about here:
    * (1) kill() can race with a call to begin/end that was in progress when kill() started. This is resolved with
    * a mutex (synchronized{} blocks)
    * (2) An in-progress computation can race with a kill signal (sent externally after kill() is called). This is
    * resolved by setting a flag during kill() which turns future operations into a no-op. */
  def kill(): Unit = {
    synchronized {
      isDead = true
      nodesWritten.foreach(node =>
        node.stepId.foreach { id =>
          node.status = ExecutionStepStatus.Aborted
          db.updateExecutionStep(id, node.asPOJO)
        })
    }
  }
}

case class StepPointer(step: Int, branch: Int) {}

class StepByStepRecordingListener(db: DBAbstraction,
                                  proofId: Int,
                                  previousStep: Option[StepPointer],
                                  ruleName: String,
                                 ) extends IOListener {
  /** Set when we've finished the entire proof tree */
  var isDone: Boolean = false
  /** Set when the listener is killed */
  var isDead: Boolean = false

  /** Our depth within an atomic leaf node */
  var depth: Int = 0
  /** The node that is currently being executed */
  var node: Option[StepNode] = None

  /** A list of all of the nodes that have been created. Used for aborting nodes if `kill`ed */
  var allNodes: List[StepNode] = Nil

  class StepNode(previous: List[StepPointer], val parent: Option[StepNode], val executable: BelleExpr) {
    var id: Option[Int] = None
    var status: ExecutionStepStatus = ExecutionStepStatus.Running

    lazy val executableId: Int = db.addBelleExpr(executable)

    val previousId: Option[Int] = previous.headOption.map(_.step)
    val branchOrder: Int = previous.headOption.map(_.branch).getOrElse(0)

    /** Only execution steps with a unique parent can be inserted into the database */
    val canInsert: Boolean = previous.drop(1).isEmpty

    private var _local: ProvableSig = _
    private var _localProvableId: Option[Int] = None

    def local_=(local: ProvableSig): Unit = {
      assert(_local == null)
      _local = local
    }

    def local: ProvableSig = _local

    def localProvableId: Option[Int] = {
      if (_local != null && _localProvableId.isEmpty)
        _localProvableId = Some(db.createProvable(_local))
      _localProvableId
    }

    def next: List[StepPointer] =
      id match {
        case Some(step) if local != null =>
          local.subgoals.indices.map(StepPointer(step, _)).toList
        case _ =>
          Nil
      }

    def localNumSubgoals: Int = if (local != null) local.subgoals.size else -1

    def localNumOpenSubgoals: Int = if (local != null) local.subgoals.size else -1

    /** Add this node to the database */
    def add(): Unit = {
      assert(id.isEmpty && canInsert)
      id = Some(db.addExecutionStep(asPOJO))
    }

    /** Update this node in the database */
    def update(): Unit = {
      assert(canInsert)
      id.foreach(db.updateExecutionStep(_, asPOJO))
    }

    /** Remove this node from the database */
    def remove(): Unit = {
      assert(canInsert)
      id.foreach(db.deleteExecutionStep(proofId, _))
      id = None
    }

    /** Starts a new child of this node running `executable` on `input`
      *
      * @return Some(child) unless this node is an atom that cannot have children
      */
    def startChild(input: BelleValue, executable: BelleExpr): Option[StepNode] =
      None

    /** Notifies that the currently running `child` of this node finished */
    def finishChild(child: StepNode): Unit =
      throw new AssertionError("Cannot finish a child on atomic node")

    protected def asPOJO: ExecutionStepPOJO =
      ExecutionStepPOJO(id, proofId, previousId, branchOrder, status, executableId, None, None, localProvableId,
        userExecuted = parent == null, ruleName, localNumSubgoals, localNumOpenSubgoals)
  }

  class SeqStepNode(previous: List[StepPointer], parent: Option[StepNode], executable: BelleExpr)
    extends StepNode(previous, parent, executable) {

    var previousPointer: List[StepPointer] = previous

    override def startChild(input: BelleValue, executable: BelleExpr): Option[StepNode] = {
      Some(makeNode(input, executable, Some(this), previousPointer))
    }

    override def finishChild(child: StepNode): Unit = {
      previousPointer = child.next
      id = child.id
    }

    override def next: List[StepPointer] = previousPointer

    override def add(): Unit = ()

    override def update(): Unit = ()

    override def remove(): Unit = ()
  }

  class BranchStepNode(previous: List[StepPointer], parent: Option[StepNode], executable: BelleExpr)
    extends StepNode(previous, parent, executable) {

    var stepsLeft: List[StepPointer] = previous
    var allStepsRev: List[StepPointer] = Nil

    override def startChild(input: BelleValue, executable: BelleExpr): Option[StepNode] = {
      stepsLeft match {
        case Nil =>
          throw new AssertionError("Unexpectedly had no steps left. Listener got out of sync with the interpreter")
        case hd :: _ =>
          Some(makeNode(input, executable, Some(this), hd :: Nil))
      }
    }

    override def finishChild(child: StepNode): Unit = {
      allStepsRev = child.next.reverse ++ allStepsRev
      stepsLeft = stepsLeft.tail
    }

    override def next: List[StepPointer] = allStepsRev.reverse

    override def add(): Unit = ()

    override def update(): Unit = ()

    override def remove(): Unit = ()
  }

  //@todo Add nodes for EitherTactic and DependentTactics

  private def makeNode(input: BelleValue, executable: BelleExpr,
                       parent: Option[StepNode], previous: List[StepPointer]
                      ): StepNode = {
    executable match {
      case SeqTactic(_, _) | RepeatTactic(_, _) | SaturateTactic(_) =>
        new SeqStepNode(previous, parent, executable)
      case BranchTactic(_) | OnAll(_) =>
        new BranchStepNode(previous, parent, executable)
      case _ => new StepNode(previous, parent, executable)
    }
  }

  override def begin(input: BelleValue, expr: BelleExpr): Unit = this.synchronized {
    assert(!isDone)
    if (isDead) return

    if (depth > 0) {
      depth += 1
      return
    }

    node match {
      case None =>
        val next = makeNode(input, expr, node, previousStep.toList)
        allNodes = next :: allNodes
        next.add()
        node = Some(next)

      case Some(n) =>
        n.startChild(input, expr) match {
          case None =>
            depth += 1
          case Some(next) =>
            n.status = ExecutionStepStatus.DependsOnChildren
            n.update()

            allNodes = next :: allNodes
            next.add()
            node = Some(next)
        }
    }
  }

  override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, BelleThrowable]
                  ): Unit = this.synchronized {
    assert(!isDone)
    if (isDead) return

    if (depth > 0) {
      depth -= 1
      return
    }

    val curr = node.get
    output match {
      case Left(BelleProvable(p, _)) =>
        curr.local = p
        curr.status = ExecutionStepStatus.Finished
      case Left(_) =>
        curr.status = ExecutionStepStatus.Finished
      case Right(_) =>
        curr.status = ExecutionStepStatus.Error
    }
    curr.update()

    curr.parent match {
      case None =>
        if (db.getPlainOpenSteps(proofId).isEmpty)
          db.updateProofSetClosed(proofId)
        isDone = true

      case Some(parent) =>
        parent.finishChild(curr)
        node = Some(parent)
    }
  }

  override def kill(): Unit = this.synchronized {
    isDead = true
    allNodes.foreach(node => {
      node.status match {
        case ExecutionStepStatus.DependsOnChildren | ExecutionStepStatus.Running =>
          node.status = ExecutionStepStatus.Aborted
          node.update()
      }
    })
  }
}
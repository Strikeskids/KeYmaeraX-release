package edu.cmu.cs.ls.keymaerax.tacticsinterface

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, BelleThrowable, ExhaustiveSequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.hydra._

class StepByStepRecordingListenerTest extends TacticTestBase {
  def makeInterpreter(db: TempDBTools, proofId: Int, startStep: Option[StepPointer]) =
    new ExhaustiveSequentialInterpreter(
      new StepByStepRecordingListener(db.db, proofId, startStep, "") :: Nil)

  def nodePointer(node: ProofTreeNode): Option[StepPointer] =
    node.id match {
      case DbStepPathNodeId(id, _) => id.map(StepPointer(_, node.goalIdx))
      case _ => throw new AssertionError("Bad ID")
    }

  def executeTactic(db: TempDBTools, node: ProofTreeNode, tactic: BelleExpr): Unit =
    makeInterpreter(db, node.proofId.toInt, nodePointer(node))(
      tactic, BelleProvable(node.localProvable.sub(node.goalIdx)))

  def nodeAt(tree: ProofTree, accessPattern: List[Int]): ProofTreeNode =
    accessPattern.foldLeft(tree.root)((node, idx) => node.children(idx))

  def executeAt(db: TempDBTools, proofId: Int, access: List[Int], tactic: String): Unit =
    executeTactic(db, nodeAt(DbProofTree(db.db, proofId.toString), access), BelleParser(tactic))

  def startProof(db: TempDBTools, model: String): Int = {
    val modelId = db.db.createModel(db.user.userName, "M" + model.hashCode.toString, db.makeModel(model), "")
    db.db.createProofForModel(modelId.get, "MP" + model.hashCode.toString, "", "", None)
  }

  def nodeAtProof(db: TempDBTools, proofId: Int, access: List[Int]): ProofTreeNode =
    nodeAt(DbProofTree(db.db, proofId.toString), access)

  def asTree(tree: ProofTreeNode): Tree[BelleExpr] =
    tree.children match {
      case Nil =>
        Leaf
      case ch :: _ =>
        Node(BelleParser(ch.maker.get), tree.children.map(asTree): _*)
    }

  def belleTree(tree: Tree[String]): Tree[BelleExpr] =
    tree match {
      case Leaf => Leaf
      case Node(x, ch@_*) =>
        Node(BelleParser(x), ch.map(belleTree): _*)
    }

  "Single tactics" should "be stored individually" in withDatabase { db =>
    val proofId = startProof(db, "true")
    executeAt(db, proofId, Nil, "closeTrue")
    asTree(nodeAtProof(db, proofId, Nil)) shouldBe belleTree(Node("closeTrue", Leaf))
  }

  "Nested tactics" should "be combined" in withDatabase { db =>
    val proofId = startProof(db, "true & true & true")
    executeAt(db, proofId, Nil, "andR(1); <( closeTrue, nil); andR(1); <( closeTrue, nil )")
    asTree(nodeAtProof(db, proofId, Nil)) shouldBe
      belleTree(Node("andR(1)", Node("closeTrue", Leaf), Node("nil", Node("andR(1)", Node("closeTrue", Leaf), Node
      ("nil", Leaf)))))
  }

  "Failing tactics" should "not prevent other successes while saving progress" in withDatabase { db =>
    val p1 = startProof(db, "true & true & true")
    a[BelleThrowable] should be thrownBy
      executeAt(db, p1, Nil, "andR(1); <( orR(1), andR(1) )")
    asTree(nodeAtProof(db, p1, Nil)) shouldBe
      belleTree(Node("andR(1)", Node("pending(orR(1))", Leaf), Node("andR(1)", Leaf, Leaf)))
    DbProofTree(db.db, p1.toString).isClosed shouldBe false

    val p2 = startProof(db, "(true | true) & (true | true)")
    a[BelleThrowable] should be thrownBy
      executeAt(db, p2, Nil, "andR(1); doall(orR(1)); doall(andR(1))")
    asTree(nodeAtProof(db, p2, Nil)) shouldBe
      belleTree(Node("andR(1)", Node("orR(1)", Node("pending(andR(1))", Leaf)), Node("orR(1)", Node("pending(andR(1))" +
        "", Leaf))))
    DbProofTree(db.db, p2.toString).isClosed shouldBe false

    val p3 = startProof(db, " (true | true) & (true | true)")
    a[BelleThrowable] should be thrownBy
      executeAt(db, p3, Nil, "andR(1); doall(andR(1)); doall(orR(1))")
    asTree(nodeAtProof(db, p3, Nil)) shouldBe
      belleTree(Node("andR(1)", Node("pending(andR(1))", Leaf),
        Node("pending(andR(1))", Node("pending({`Outside branch`}, doall(orR(1)))", Leaf))))
  }

  sealed abstract class Tree[+A] {}

  case class Node[+A](x: A, ch: Tree[A]*) extends Tree[A] {}

  case object Leaf extends Tree[Nothing] {}

}

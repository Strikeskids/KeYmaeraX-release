package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BRANCH_COMBINATOR, BelleParser, PENDING, SEQ_COMBINATOR}
import edu.cmu.cs.ls.keymaerax.btactics.{Generator, Idioms}
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.{Location, SuffixRegion}

object ExtractTacticFromTrace {
  // Additional wrappers
  def apply(tree: ProofTree): BelleExpr = {
    apply(tree.info.modelId)(tree.root)
  }

  def getTacticString(tree: ProofTree): String =
    getTacticString("")(tree.root)

  def getTacticLocators(tree: ProofTree): List[TacticLocator] =
    getTacticLocators("")(tree.root)

  def getTacticInfo(tree: ProofTree): (String, List[TacticLocator]) =
    getTacticInfo("")(tree.root)

  /**
    * @note this could be tailrec.
    * @return A structured Bellerophon tactic that constructs the proof tree.
    */
  def apply(modelId: Option[Int])(node: ProofTreeNode): BelleExpr = {
    assert(!node.children.contains(node), "A node should not be its own child.") //but apparently this happens.
    val gen = None
    /* new ConfigurableGenerator(
         modelId match {
           case Some(mid) => db.getInvariants(mid)
           case None => Map()
         })*/
    val subgoals = node.children.map(apply(modelId)(_))
    val thisTactic = tacticAt(gen, node)

    if (subgoals.isEmpty || (subgoals.length == 1 && subgoals.head == Idioms.nil)) thisTactic
    else if (subgoals.length == 1) thisTactic & subgoals.head
    else thisTactic & BranchTactic(subgoals)
  }

  private def tacticAt(gen: Option[Generator.Generator[Formula]], node: ProofTreeNode): BelleExpr = BelleParser
    .parseWithInvGen(node.action.getOrElse("nil"), gen)

  def getTacticString(indent: String)(node: ProofTreeNode): String = {
    extractTacticsNonempty(indent)(node).map(_.tacticPart).mkString("")
  }

  def getTacticLocators(indent: String)(node: ProofTreeNode): List[TacticLocator] =
    fillLocations(extractTactics(indent)(node))

  def getTacticInfo(indent: String)(node: ProofTreeNode): (String, List[TacticLocator]) = {
    val extracted = extractTacticsNonempty(indent)(node)
    (extracted.map(_.tacticPart).mkString(""), fillLocations(extracted))
  }

  private def extractTacticsNonempty(indent: String)(node: ProofTreeNode): List[TacticStringifier] = {
    extractTactics(indent)(node) match {
      case Nil => TacticNodeString(node.id, "nil") :: Nil
      case nonempty => nonempty
    }
  }

  private def extractTactics(indent: String)(node: ProofTreeNode): List[TacticStringifier] =
    seqCombine(
      node.action match {
        case None | Some("assert") =>
          Nil
        case Some(m) =>
          val indented = m.replace("\n", "\n" + indent)
          val wrapped =
            if (!m.startsWith(PENDING.img) && m.contains(SEQ_COMBINATOR.img))
              "(" + indented + ")"
            else
              indented
          TacticNodeString(node.id, wrapped) :: Nil
      },
      branchCombine(indent)(node.children)
    )

  private def branchCombine(indent: String)(children: List[ProofTreeNode])
  : List[TacticStringifier] = children match {
    case Nil => Nil
    case ch :: Nil =>
      extractTactics(indent)(ch)
    case _ =>
      TacticPadString(BRANCH_COMBINATOR.img + "(\n  " + indent) ::
        children.map(extractTacticsNonempty(indent + "  "))
          .foldRight[List[TacticStringifier]](Nil) {
          case (a, Nil) => a :+ TacticPadString("\n" + indent + ")")
          case (a, b) => a ++ (TacticPadString(",\n  " + indent) :: b)
        }
  }

  private def seqCombine(a: List[TacticStringifier], b: List[TacticStringifier]): List[TacticStringifier] = (a, b)
  match {
    case (Nil, _) => b
    case (_, Nil) => a
    case _ => a ++ (TacticPadString(SEQ_COMBINATOR.img + " ") :: b)
  }

  private def fillLocations(extracted: List[TacticStringifier]): List[TacticLocator] =
    extracted.foldLeft(0: Int, Nil: List[TacticLocator]) {
      case ((start, rest), TacticNodeString(node, tactic)) =>
        val end = start + tactic.length
        (end, TacticLocator(node, tactic, start, end) :: rest)
      case ((reg, rest), s) =>
        (reg + s.tacticPart.length, rest)
    }._2.reverse

  /** Find the root of the difference between the tactic of `node` and `tactic` */
  def differenceRoot(tactic: BelleExpr, node: ProofTreeNode): Option[(BelleExpr, ProofTreeNode)] = {
    differenceRootHelper(tactic, node)
  }

  /**
    * Find the root of the difference between the two tactics.
    *
    * @param compare The tactic we are comparing with
    * @return
    */
  private def differenceRootHelper(compare: BelleExpr, node: ProofTreeNode): Option[(BelleExpr, ProofTreeNode)] = {
    val mine = tacticAt(None, node)
    compare match {
      case `mine` if node.children.size <= 1 && node.children.headOption.flatMap(_.action).isEmpty =>
        //@note Our (potential) child is a leaf and we match the comparison
        None
      case SeqTactic(cmpLeft, cmpRest) if mine == cmpLeft =>
        cmpRest match {
          case BranchTactic(cmpBs) if cmpBs.size == node.children.size =>
            // Branching deduction where we need to recurse
            (cmpBs zip node.children).map((differenceRootHelper _).tupled).flatMap(_.toList) match {
              case Nil => None
              case child :: Nil => Some(child)
              case _ => Some(compare, node) //@note multiple differing children mean we need to run from the current node
            }
          case _ if node.children.size == 1 =>
            // Normal sequential deduction
            differenceRootHelper(cmpRest, node.children.head)
          case _ =>
            // Incompatible deductions, so the error must be at this node
            Some(compare, node)
        }
      case _ =>
        Some(compare, node)
    }
  }
}

private sealed abstract class TacticStringifier {
  def tacticPart: String
}

private case class TacticPadString(data: String) extends TacticStringifier {
  override def tacticPart: String = data
}

private case class TacticNodeString(node: ProofTreeNodeId, tactic: String) extends TacticStringifier {
  override def tacticPart: String = tactic
}

case class TacticLocator(node: ProofTreeNodeId, tactic: String, start: Int, end: Int)

object TacticExtractionErrors {

  class TacticExtractionError(message: String, cause: Option[Throwable]) extends Exception(message + {
    cause match {
      case Some(e) => ". Caused by: " + e.getMessage;
      case None => ""
    }
  })

  object TacticExtractionError {
    def apply(message: String, cause: Exception) = new TacticExtractionError(message, Some(cause))

    def apply(message: String, cause: Throwable) = new TacticExtractionError(message, Some(cause))

    def apply(message: String) = new TacticExtractionError(message, None)
  }

}


package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BRANCH_COMBINATOR, BelleParser, SEQ_COMBINATOR}
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
      case Nil => TacticPadString("nil") :: Nil
      case nonempty => nonempty
    }
  }

  private def extractTactics(indent: String)(node: ProofTreeNode): List[TacticStringifier] =
    seqCombine(
      node.action match {
        case None | Some("assert") =>
          TacticNodeString(node.id, "nil") :: Nil
        case Some(m) =>
          TacticNodeString(node.id, m.replace("\n", "\n" + indent)) :: Nil
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
    extracted.foldLeft((SuffixRegion(1, 1): Location, Nil: List[TacticLocator])) {
      case ((reg, rest), TacticNodeString(node, tactic)) =>
        val (cur, after) = reg.advanceBy(tactic)
        (after, TacticLocator(node, tactic, cur) :: rest)
      case ((reg, rest), s) =>
        val (_, after) = reg.advanceBy(s.tacticPart)
        (after, rest)
    }._2.reverse
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

case class TacticLocator(node: ProofTreeNodeId, tactic: String, loc: Location)

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


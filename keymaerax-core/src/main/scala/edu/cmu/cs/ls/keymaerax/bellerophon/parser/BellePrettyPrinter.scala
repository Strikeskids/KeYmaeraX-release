package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import BelleOpSpec.op
import edu.cmu.cs.ls.keymaerax.btactics.TacticInfo

/**
  * A pretty-printer for the Bellerophon tactics language.
  *
  * @author Nathan Fulton
  * @note Prefer this implementation over [[BelleExpr.prettyString]].
  */
object BellePrettyPrinter extends (BelleExpr => String) {
  override def apply(e: BelleExpr): String = pp(e, 0)

  private def pp(e : BelleExpr, indent: Int): String = {
    try {
      //Prefer the code name if one exists for this tactic.
//      println("Looking for a code name for " + e)
      val info = TacticInfo.apply(e.prettyString)
      if(info.belleExpr.asInstanceOf[BelleExpr] != e) throw new Exception("")
      else info.codeName
    }
    catch {
      case exn:Throwable =>
        e match {
          case SeqTactic(l,r,_)     => wrapLeft(e, l, indent) + op(e).terminal.img + wrapRight(e, r, indent)
          case EitherTactic(l,r,_) => wrapLeft(e, l, indent) + op(e).terminal.img + wrapRight(e, r, indent)
          case BranchTactic(ts, _) => op(e).terminal.img + "(" + newline(indent) + ts.map(pp(_, indent+1)).mkString(newline(indent) + ",") + newline(indent) + ")"
          case b : BuiltInTactic => b.name
          case e: PartialTactic => op(e).terminal.img + "(" + pp(e.child, indent) + ")"
          case _ => e.prettyString
        }
    }
  }

  private val TAB = "  "
  private def newline(indent: Int) = Range(0, indent).foldLeft("")((s,n) => s + TAB)

  private def wrapLeft(parent: BelleExpr, current: BelleExpr, indent: Int) : String =
    if(op(parent) < op(current) || (op(parent) == op(current) && !op(current).leftAssoc))
      wrap(current, indent)
    else
      pp(current, indent)

  private def wrapRight(parent: BelleExpr, current: BelleExpr, indent: Int) : String =
    if(op(parent) < op(current) || (op(parent) == op(current) && op(current).leftAssoc))
      wrap(current, indent)
    else
      pp(current, indent)

  private def wrap(e : BelleExpr, indent: Int) = "(" + pp(e, indent) + ")"
}


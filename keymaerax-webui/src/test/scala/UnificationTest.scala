/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Unification
import scala.collection.immutable._
import org.scalatest.{Matchers, FlatSpec}


/**
 * Created by aplatzer on 7/28/15.
 * @author aplatzer
 */
class UnificationTest extends FlatSpec with Matchers {

  private def should(e1: Expression, e2: Expression, us: Option[USubst]): Unit = {
    if (us.isDefined) {
      println("Expression: " + e1)
      println("Expression: " + e2)
      val s = Unification(e1, e2)
      println("Unified:  " + s)
      println("Expected: " + us.get)
      s shouldBe us
    } else {
      println("Expression: " + e1)
      println("Expression: " + e2)
      println("Expected: " + "<ununifiable>")
      Unification(e1, e2) shouldBe us
    }
  }

  private def shouldUnify(e1: Expression, e2: Expression, us: USubst): Unit = should(e1,e2,Some(us))

  "Unification terms" should "unify f() with x^2+y" in {
    shouldUnify("f()".asTerm, "x^2+y".asTerm, USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil))
  }

  it should "unify f(x) with x^2+y" in {
    shouldUnify("f(x)".asTerm, "x^2+y".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f() with 3+(x^2+y)" in {
    shouldUnify("3+f()".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f(x) with 3+(x^2+y)" in {
    shouldUnify("3+f(x)".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }


  "Unification formulas" should "unify p() with x^2+y>=0" in {
    shouldUnify("p()".asFormula, "x^2+y>=0".asFormula, USubst(
      SubstitutionPair("p()".asFormula, "x^2+y>=0".asFormula) :: Nil))
  }


  "Unification programs" should "unify [a;]x>=0 with [x:=x+5;]x>=0" in {
    shouldUnify("[a;]x>=0".asFormula, "[x:=x+5;]x>=0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil))
  }

  it should "unify [a;x:=7;]x>=0 with [x:=x+5;x:=7;]x>=0" in {
    shouldUnify("[a;x:=7;]x>=0".asFormula, "[x:=x+5;x:=7;]x>=0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil))
  }
}

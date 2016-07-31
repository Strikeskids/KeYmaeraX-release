/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase, TactixLibrary}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

/**
 * Test when substituting systems instead of single differential equations.
 * @author Andre Platzer
 */
@AdvocatusTest
class SystemSubstituterTest extends TacticTestBase {
  import TactixLibrary._

  "Substituting into systems" should "not allow primes in ODEs for DE" in {
    // [{x_'=f(??),c&H(??)}]p(??) <-> [{c,x_'=f(??)&H(??)}][x_':=f(??);]p(??)
    val pr = Provable.axioms("DE differential effect (system)")
    pr shouldBe 'proved
    a [CoreException] shouldBe thrownBy {pr(USubst(SubstitutionPair(FuncOf(Function("f",None,Real,Real),DotTerm), "y'+1".asTerm) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),DotTerm), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("y",None,Real)), Number(2))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), "x'=3".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG differential ghost" in {
    // [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=(t()*y_)+s()&H(??)}]p(??)
    val pr = Provable.axioms("DG differential ghost")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(SubstitutionPair(FuncOf(Function("t",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(FuncOf(Function("s",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),DotTerm), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG differential ghost constant" in {
    // [{c&H(??)}]p(??) <-> \exists y_ [{c,y_'=g()&H(??)}]p(??)
    val pr = Provable.axioms("DG differential ghost constant")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(SubstitutionPair(FuncOf(Function("g",None,Unit,Real),Nothing), Number(0)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),DotTerm), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), "y_=0".asFormula) ::
      Nil))}
  }

  it should "not allow ghosts in postconditions of DG++ System" in {
    // ([{x_'=f(??),c&H(??)}]p(??))  ->  (\forall y_ [{y_'=g(??),x_'=f(??),c&H(??)}]p(??))
    val pr = Provable.axioms("DG++ System")
    pr shouldBe 'proved
    a [SubstitutionClashException] shouldBe thrownBy {pr(USubst(SubstitutionPair(FuncOf(Function("f",None,Real,Real),DotTerm), Number(0)) ::
      SubstitutionPair(FuncOf(Function("g",None,Real,Real),DotTerm), Number(0)) ::
      SubstitutionPair(PredOf(Function("H",None,Real,Bool),DotTerm), True) ::
      SubstitutionPair(DifferentialProgramConst("c"), AtomicODE(DifferentialSymbol(Variable("t",None,Real)), Number(1))) ::
      SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), "y_=0".asFormula) ::
      Nil))}
  }

}
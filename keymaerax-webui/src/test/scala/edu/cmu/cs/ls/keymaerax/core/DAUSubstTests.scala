/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, SystemTestBase}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, USubstTest, UsualTest}
import testHelper.CustomAssertions.{withSafeClue, _}
import testHelper.KeYmaeraXTestTags
import testHelper.KeYmaeraXTestTags.{AdvocatusTest, CoverageTest}

import scala.collection.immutable
import scala.collection.immutable.{IndexedSeq, List, Seq}
import scala.language.postfixOps

/** 15624
 */
@SummaryTest
@UsualTest
@USubstTest
class DAUSubstTests extends SystemTestBase {
  /** Test whether `operation(data)` is either a no-op returning `data` or throws an exception of type `E`. */
  def throwOrNoOp[In,Out,E:Manifest](operation: In => Out, data: In) = {
    var done = false
    try {
      // noop
      done = (operation(data) == data)
    }
    catch {
      case ignore : Throwable => done = false
    }
    if (!done) a [E] should be thrownBy {
      operation(data)
    }
  }

  val x = Variable("x", None, Real)
  val z = Variable("z", None, Real)
  val p0 = PredOf(Function("p", None, Unit, Bool), Nothing)
  val p1 = Function("p", None, Real, Bool)


  "Uniform substitution" should "substitute non-clashing variables" in {
    val prem = "p() -> [a;]p()".asFormula

    println(KeYmaeraXPrettyPrinter.stringify(prem))

    val s = USubst(("p()".asFormula ~> "z=1".asFormula)::("a".asProgram ~> "\\dexists {y} {x' = y}".asProgram)::Nil)

    println(KeYmaeraXPrettyPrinter.stringify(s(prem)))
  }

  it should "substitute quantified variables into post-conditions" in {
    val prem = "p() -> [a;]p()".asFormula

    println(KeYmaeraXPrettyPrinter.stringify(prem))

    val s = USubst(("p()".asFormula ~> "y=1".asFormula)::("a".asProgram ~> "\\dexists {y} {x' = y}".asProgram)::Nil)

    println(KeYmaeraXPrettyPrinter.stringify(s(prem)))
  }

  it should "clash when substituting ." in {
    val prem = "p() -> [a;]p()".asFormula
    val s = USubst(("p()".asFormula ~> "x=1".asFormula)::("a".asProgram ~> "\\dexists {y} {x' = y}".asProgram)::Nil)

    a [SubstitutionClashException] should be thrownBy(s(prem))
  }

  it should "test" in {
    val p = "[a;]p() -> [a;]q()".asFormula
    val s = USubst(("p()".asFormula ~> "x=1".asFormula)::("q()".asFormula ~> "y > 0".asFormula)::
      ("a".asProgram ~> "\\dexists {y} {x' = y}".asProgram)::Nil)

    a [SubstitutionClashException] should be thrownBy(s(p))
  }

}
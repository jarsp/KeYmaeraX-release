/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.{closeTrue, cut, cutLR}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._

import scala.collection.immutable.Nil


@AdvocatusTest
class DAProvableTest extends TacticTestBase {

  it should "prove vacuous" in {

    val fml = "y=1 -> [\\dexists {z} {x'=z}] y=1".asFormula
    val pr = proveBy(fml, implyR(1) & abstractionb(1) & closeId)

  }

  it should "DAW test" in {

    val fml = "\\forall x [\\dexists {x} {y'=x & y>=0}]y>=0".asFormula
    val pr = proveBy(fml, useAt("DAW base", PosInExpr(Nil))(1))

  }

  it should "DAI test" in {

    val fml = "([\\dexists {x} {y'=x}](x+y>=z) <-> \\forall x [?true;]y>=z) <- (\\forall x [{y'=x}]((y>=z)'))".asFormula
    //val pr = proveBy(fml, useAt("DAI differential invariance", PosInExpr(Nil))(1))
    val pr = proveBy(fml, allInstantiateInverse(("q".asTerm, Variable("x")))(1, Nil))
    //val pr = proveBy(fml, replaceFree(Variable("x"), Variable("q"))(1, 1::0::0::0::Nil)) //useAt("DAI differential invariance", PosInExpr(Nil))(1))
    println(pr)

  }

}


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
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.{closeTrue, cut, cutLR, boundRenaming}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._
import edu.cmu.cs.ls.keymaerax.pt._

import scala.collection.immutable.Nil


@AdvocatusTest
class DAProvableTest extends TacticTestBase {

  it should "prove vacuous" in {

    val fml = "y=1 -> [\\dexists {z} {x'=z}] y=1".asFormula
    val pr = proveBy(fml, implyR(1) & abstractionb(1) & closeId)

  }

  it should "prove by DAW axiom" in {

    val fml = "\\forall x [\\dexists {x} {y'=x & y>=0}]y>=0".asFormula
    val pr = proveBy(fml, useAt("DAW base", PosInExpr(Nil))(1))

  }

  it should "prove by DAI axiom" in {

    val fml = "([\\dexists {x} {y'=x}](y>=z) <-> \\forall x [?true;]y>=z) <- (\\forall x [{y'=x}]((y>=z)'))".asFormula
    val pr = proveBy(fml, useAt("DAI differential invariance", PosInExpr(Nil))(1))

  }

  it should "substitute only quantified variables in DASystem" in {

    val x = Variable("x")
    val y = Variable("y")
    val z = Variable("z")
    val q = Variable("q")

    val fml = "([\\dexists {x} {y'=x}](y>=z) <-> \\forall x [?true;]y>=z) <- (\\forall x [{y'=x}]((y>=z)'))".asFormula
    val pr = proveBy(fml, boundRenaming(x, q)(1, 1::0::Nil))

    pr.isInstanceOf[ElidingProvable] should be (true)

    val Sequent(ante, succ) = pr.conclusion

    ante.length should be (0)
    succ.length should be (1)

    succ.head should be (Imply(
        Forall(x::Nil, Box(ODESystem(AtomicODE(DifferentialSymbol(y), x), True),
          DifferentialFormula(GreaterEqual(y, z)))),
        Equiv(Box(DASystem(DExists(x::Nil, ODESystem(AtomicODE(DifferentialSymbol(y), x), True))), GreaterEqual(y, z)),
          Forall(x::Nil, Box(Test(True), GreaterEqual(y, z))))))

    pr.subgoals.length should be (1)

    val goal1 = pr.subgoals.head
    goal1.ante.length should be (0)
    goal1.succ.length should be (1)

    goal1.succ.head should be (Imply(
      Forall(x::Nil, Box(ODESystem(AtomicODE(DifferentialSymbol(y), x), True),
        DifferentialFormula(GreaterEqual(y, z)))),
      Equiv(Box(DASystem(DExists(q::Nil, ODESystem(AtomicODE(DifferentialSymbol(y), q), True))), GreaterEqual(y, z)),
        Forall(x::Nil, Box(Test(True), GreaterEqual(y, z))))))

  }

}


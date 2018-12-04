/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{AdvocatusTest, USubstTest}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.{boundRenaming, closeTrue, cut, cutLR}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._

import scala.collection.immutable.Nil


@AdvocatusTest
@USubstTest
class DAProvableTest extends TacticTestBase {

  it should "prove vacuous" in {

    val fml = "y=1 -> [\\dexists {z} {x'=z}] y=1".asFormula
    val pr = proveBy(fml, implyR(1) & abstractionb(1) & closeId)

  }

  it should "prove by DAI axiom" in {

    // val fml = "([\\dexists {x} {y'=x}](y>=z) <-> \\forall x [?true;]y>=z) <- (\\forall x [{y'=x}]((y>=z)'))".asFormula
    val fml = "([\\dexists {x} {y'=x}](y>=z) <-> \\forall x [?true;]y>=z) <- ([\\dexists {x} {y'=x}]((y>=z)'))".asFormula
    val pr = proveBy(fml, useAt("DAI differential invariance", PosInExpr(Nil))(1))

  }

  it should "refuse DAI axiom when quantified variables appear in postcondition" in {

    val fml = "([\\dexists {x} {y'=x}](y>=x) <-> \\forall x [?true;](y>=x)) <- [\\dexists {x} {y'=x}]((y>=x)')".asFormula
    a [Exception] should be thrownBy(proveBy(fml, useAt("DAI differential invariance", PosInExpr(Nil))(1)))

  }

  it should "match DAS" in {

    val fml = "[\\dexists {x} {y'=x&x>=2*y}](y>=z) <-> \\forall x [\\dexists {x} {y'=x&x>=2*y}][{y'=x&x>=2*y}](y>=z)".asFormula
    val pr = proveBy(fml, useAt("DAS differential stutter", PosInExpr(Nil))(1))

  }

  it should "refuse DAS when quantified variables appear in postcondition" in {

    val fml = "[\\dexists {x} {y'=x&x>=2*y}](y>=x) <-> \\forall x [\\dexists {x} {y'=x&x>=2*y}][{y'=x&x>=2*y}](y>=x)".asFormula
    a [Exception] should be thrownBy(proveBy(fml, useAt("DAS differential stutter", PosInExpr(Nil))(1)))

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

  it should "apply tactic" in {

    val fml = "[{y'=x & y>=2}]y>=0".asFormula
    val pr = proveBy(fml, diffWeaken(1))

    //println(pr)
  }


  it should "apply DAWeaken tactic" in {

    val fml = "x=5 ==> [\\dexists {x} {y'=x & y>=2}]y>=0".asSequent
    val pr = proveBy(fml, DAWeaken(1))

    //println(pr)

    val y = Variable("y")
    pr.isInstanceOf[ElidingProvable] should be (true)

    val Sequent(ante, succ) = pr.conclusion

    val goal1 = pr.subgoals.head
    goal1.ante.length should be (2)
    goal1.succ.length should be (1)

    //goal1.ante.head should be (GreaterEqual(y, Number(2)))
    goal1.succ.head should be (GreaterEqual(y, Number(0)))

  }


  it should "apply DAWeaken in context?" in {
    val fml = "false & [\\dexists {x} {y'=x & y>=2}]y>=0".asFormula
    val pr = proveBy(fml, andR(1) & Idioms.<(
      skip,
      DAWeaken(1)
    ))

    //println(pr)
  }

  it should "apply DAWeaken in context2?" in {
    val fml = "==> y >= 2, [\\dexists {x} {y'=x & y>=2}]y>=0".asSequent
    val pr = proveBy(fml, DAWeaken(2))

    println(pr)
  }


  it should "DAI" in {
    val fml = "([\\dexists{x}{c&q(||)}]p(|x|)) <- ((\\forall x (q(||) -> p(|x|))) & [\\dexists{x}{c&q(||)}]((p(|x|))'))".asFormula
    val pr = proveBy(fml, useAt(DAIinvariant, PosInExpr(Nil))(1, PosInExpr(Nil)))

    println(pr)
  }

  it should "DAI tactic" in {
    val fml = "(v^2 <= 2*(b-u)*(m-z) & b>u & u>=0 & l>=0) -> [\\dexists{c}{z' = v, v' = a - l + c & c >= 0 & v >= 0}](z <= m)".asFormula
    val pr = proveBy(fml,
      implyR(1) & DAInvariant(1)
    )

    println(pr)
  }


}


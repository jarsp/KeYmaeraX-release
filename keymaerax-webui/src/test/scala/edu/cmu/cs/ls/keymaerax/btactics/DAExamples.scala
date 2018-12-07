/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms._
import edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics._
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.boundRenaming
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.tags.{AdvocatusTest, USubstTest}

import scala.collection.immutable.Nil


@AdvocatusTest
@USubstTest
class DAExamples extends TacticTestBase {

  it should "prove braking invariant with DAI" in withMathematica { _ =>
    val fml = "v^2 <= 2*(b-u)*(m-z) & b > u & u >= 0 & l >= 0 ==> [\\dexists{d}{z'=v, v'=-b+d & -l<=d & d<=u & v>=0}](z <= m)".asSequent
    val pr = proveBy(fml,
      andL(-1) & DACut("v^2 <= 2*(b-u)*(m-z) & b > u & u >= 0 & l >= 0".asFormula)(1) <(
        DAWeaken(1) & QE & done,
        Dconstify(DAInvariant(1) <(
          QE & done,
          Dassignb(1)*2 & QE & done
        ))(1)
      )
    )

    println("Train braking test")
    println(pr)
    println("\n\n")

    pr shouldBe 'proved
  }

  it should "prove disturbed circular motion does not escape" in withMathematica { _ =>
    val fml = "x^2 + y^2 = 1 -> [\\dexists{e} {x'=-y+e, y'=x & x*e <= 0}] x^2 + y^2 <= 1".asFormula
    val pr = proveBy(fml,
      implyR(1) & Dconstify(DAInvariant(1) <(
        QE & done,
        Dassignb(1)*2 & QE & done
      ))(1)
    )

    println("disturbed circular motion")
    println(pr)

    pr shouldBe 'proved
  }

}


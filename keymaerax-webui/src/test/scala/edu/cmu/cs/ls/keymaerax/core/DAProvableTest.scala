/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

import scala.collection.immutable.Nil


@AdvocatusTest
class DAProvableTest extends TacticTestBase {

  it should "prove vacuous" in withMathematica { _ =>

    val fml = "y=1 -> [\\dexists {z} {x'=z}] y=1".asFormula
    val pr = proveBy(fml, implyR(1) & abstractionb(1) & closeId)

  }

}


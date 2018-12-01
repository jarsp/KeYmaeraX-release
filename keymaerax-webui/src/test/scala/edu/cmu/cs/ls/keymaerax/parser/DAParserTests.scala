package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool

import org.scalatest._

import scala.collection.immutable._

class DAParserTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  var parser: Parser = _
  var pp: PrettyPrinter = _

  override def beforeEach(): Unit = {
    KeYmaeraXTool.init(Map.empty)
    parser = KeYmaeraXParser
    pp = KeYmaeraXPrettyPrinter
  }

  override def afterEach(): Unit = {
    pp = null
    parser = null
    KeYmaeraXTool.shutdown()
  }

  "The parser" should "parse DASystem with one quantified variable" in {
    val input = "\\dexists {y} {x' = y & y >= 5}"

    val x = Variable("x")
    val y = Variable("y")

    val parsed = parser(input)

    parsed shouldBe DASystem(DExists(Seq(y), ODESystem(AtomicODE(DifferentialSymbol(x), y), GreaterEqual(y, Number(5)))))
  }

  it should "parse DASystem with more than one quantified variable" in {
    val input = "\\dexists {y, z, c} {x' = y + z & 3 <= y & y <= 4 & x - c <= z & z <= x + c}"

    val x = Variable("x")
    val y = Variable("y")
    val z = Variable("z")
    val c = Variable("c")

    val parsed = parser(input)

    parsed shouldBe DASystem(DExists(Seq(y, z, c), ODESystem(AtomicODE(DifferentialSymbol(x), Plus(y, z)),
      And(LessEqual(Number(3), y), And(LessEqual(y, Number(4)),
        And(LessEqual(Minus(x, c), z), LessEqual(z, Plus(x, c))))))))
  }

  it should "parse DASystem with more than one differential equation (diff product)" in {
    val input = "\\dexists {c,d,u,l} {x' = c, y' = x + d & c <= x + u & d >= y - l}"

    val x = Variable("x")
    val y = Variable("y")
    val c = Variable("c")
    val d = Variable("d")
    val u = Variable("u")
    val l = Variable("l")

    val parsed = parser(input)

    parsed shouldBe DASystem(DExists(Seq(c, d, u, l), ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), c),
      AtomicODE(DifferentialSymbol(y), Plus(x, d))), And(LessEqual(c, Plus(x, u)), GreaterEqual(d, Minus(y, l))))))
  }

  it should "parse DASystem with no quantified variables?" in {
    val input = "\\dexists {} {x' = c}"

    val parsed = parser(input)

    parsed shouldBe DASystem(DExists(Seq(), ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Variable("c")))))
  }

  it should "parse DASystem in box" in {
    val input = "[\\dexists {y} {x' = y + x & y <= 0.2 * x}]x >= 5"

    val x = Variable("x")
    val y = Variable("y")

    val parsed = parser(input)

    parsed shouldBe Box(DASystem(DExists(Seq(y), ODESystem(AtomicODE(DifferentialSymbol(x), Plus(y, x)),
      LessEqual(y, Times(Number(0.2), x))))), GreaterEqual(x, Number(5)))
  }

  it should "parse loopy DAsystem" in {
    val input = "[{c:=c+1; \\dexists {y} {x'=y & y<=0.2*x}}*]x = 0"

    val x = Variable("x")
    val y = Variable("y")
    val c = Variable("c")

    val parsed = parser(input)

    parsed shouldBe Box(Loop(Compose(Assign(c, Plus(c, Number(1))),
      DASystem(DExists(Seq(y), ODESystem(AtomicODE(DifferentialSymbol(x), y), LessEqual(y, Times(Number(0.2), x))))))),
      Equal(x, Number(0)))
  }

  it should "refuse differential in quantified variables" in {
    assertThrows[ParseException] {
      parser("\\dexists {y'} {x'=y & true}")
    }
    /* TODO: also add message thrown by parser */
  }

  it should "refuse differential in list of quantified variables" in {
    assertThrows[ParseException] {
      parser("\\dexists {c,y'} {x'=y & y>=c}")
    }
    /* TODO: also add message thrown by parser */
  }

  /*
  it should "refuse differential in constraints" in {
    assertThrows[ParseException] {
      parser("\\dexists {y} {x'=y & y>=x-1 & x'>=5}")
    }
  }
  */

  /*
  it should "refuse differential of quantified variables in ode" in {
    assertThrows[Exception] {
      parser("\\dexists {y} {x'=y, y'=1 & y<=5}")
    }
  }
  */

  it should "refuse bad syntax" in {
    assertThrows[ParseException] {
      parser("\\dexists y {x' = y & y >= 5}")
    }
  }
}

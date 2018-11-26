/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic lexer for concrete KeYmaera X notation.
  *
  * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import org.apache.logging.log4j.scala.Logging

import scala.annotation.tailrec
import scala.collection.immutable._
import scala.util.matching.Regex

/**
 * LexerModes corresponds to file types.
 */
sealed abstract class LexerMode
object ExpressionMode extends LexerMode
object AxiomFileMode extends LexerMode
object ProblemFileMode extends LexerMode
object LemmaFileMode extends LexerMode

/**
 * Terminal symbols of the differential dynamic logic grammar.
  *
  * @author Andre Platzer
 */
sealed abstract class Terminal(val img: String) {
  override def toString: String = getClass.getSimpleName// + "\"" + img + "\""
  /**
   * @return The regex that identifies this token.
   */
  def regexp : scala.util.matching.Regex = img.r

  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private abstract class OPERATOR(val opcode: String) extends Terminal(opcode) {
  //final def opcode: String = img
  override def toString: String = getClass.getSimpleName //+ "\"" + img + "\""
}
private case class IDENT(name: String, index: Option[Int] = None) extends Terminal(name + (index match {case Some(x) => "_"+x.toString case None => ""})) {
  override def toString: String = "ID(\"" + (index match {
    case None => name
    case Some(idx) => name + "," + idx
  }) + "\")"
  override def regexp: Regex = IDENT.regexp
}
private object IDENT {
  //@note Pattern is more permissive than NamedSymbol's since Lexer's IDENT will include the index, so xy_95 is acceptable.
  def regexp: Regex = """([a-zA-Z][a-zA-Z0-9]*\_?\_?[0-9]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private case class NUMBER(value: String) extends Terminal(value) {
  override def toString: String = "NUM(" + value + ")"
  override def regexp: Regex = NUMBER.regexp
}
private object NUMBER {
  //A bit weird, but this gives the entire number in a single group.
  //def regexp = """(-?[0-9]+\.?[0-9]*)""".r
  //@NOTE Minus sign artificially excluded from the number to make sure x-5 lexes as IDENT("x"),MINUS,NUMBER("5") not as IDENT("x"),NUMBER("-5")
  def regexp: Regex = """([0-9]+\.?[0-9]*)""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

/**
 * End Of Stream
 */
object EOF extends Terminal("<EOF>") {
  override def regexp: Regex = "$^".r //none.
}

private object LPAREN  extends Terminal("(") {
  override def regexp: Regex = """\(""".r
}
private object RPAREN  extends Terminal(")") {
  override def regexp: Regex = """\)""".r
}
private object LBANANA  extends Terminal("(|") {
  override def regexp: Regex = """\(\|""".r
}
private object RBANANA  extends Terminal("|)") {
  override def regexp: Regex = """\|\)""".r
}
private object LBRACE  extends Terminal("{") {
  override def regexp: Regex = """\{""".r
}
private object RBRACE  extends Terminal("}") {
  override def regexp: Regex = """\}""".r
}
private object LBARB   extends Terminal("{|") {
  override def regexp: Regex = """\{\|""".r
}
private object RBARB   extends Terminal("|}") {
  override def regexp: Regex = """\|\}""".r
}
private object LBOX    extends Terminal("[") {
  override def regexp: Regex = """\[""".r
}
private object RBOX    extends Terminal("]") {
  override def regexp: Regex = """\]""".r
}
private object LDIA    extends OPERATOR("<") {
  override def regexp: Regex = """\<""".r
}//@todo really operator or better not?
private object RDIA    extends OPERATOR(">") {
  override def regexp: Regex = """\>""".r
}

private object PRG_DEF  extends OPERATOR("::=")

private object COMMA   extends OPERATOR(",")
private object COLON   extends OPERATOR(":")

private object PRIME   extends OPERATOR("'")
private object POWER   extends OPERATOR("^") {
  override def regexp: Regex = """\^""".r
}
private object STAR    extends OPERATOR("*") {
  override def regexp: Regex = """\*""".r
}
private object SLASH   extends OPERATOR("/")
private object PLUS    extends OPERATOR("+") {
  override def regexp: Regex = """\+""".r
}
private object MINUS   extends OPERATOR("-")

private object NOT     extends OPERATOR("!") {
  override def regexp: Regex = """\!""".r
}
private object AMP     extends OPERATOR("&")
private object OR      extends OPERATOR("|") {
  override def regexp: Regex = """\|""".r
}
private object EQUIV   extends OPERATOR("<->")
private object EQUIV_UNICODE extends OPERATOR("↔")
private object IMPLY   extends OPERATOR("->")
private object IMPLY_UNICODE extends OPERATOR("→")

//@todo maybe could change to <-- to disambiguate poor lexer's x<-7 REVIMPLY from LDIA MINUS
private object REVIMPLY extends OPERATOR("<-")
private object REVIMPLY_UNICODE extends OPERATOR("←")

private object FORALL  extends OPERATOR("\\forall") {
  override def regexp: Regex = """\\forall""".r
}
private object EXISTS  extends OPERATOR("\\exists") {
  override def regexp: Regex = """\\exists""".r
}

/** 15624: For DAL */
private object DEXISTS extends OPERATOR("\\dexists") {
  override def regexp: Regex = """\\dexists""".r
}

private object EQ      extends OPERATOR("=")
private object NOTEQ   extends OPERATOR("!=") {
  override def regexp: Regex = """\!=""".r
}
private object GREATEREQ extends OPERATOR(">=")
private object LESSEQ  extends OPERATOR("<=")

//Unicode versions of operators:
private object LESSEQ_UNICODE extends OPERATOR("≤")
private object GREATEREQ_UNICODE extends OPERATOR("≥")
private object AND_UNICODE extends OPERATOR("∧")
private object OR_UNICODE extends OPERATOR("∨")
private object UNEQUAL_UNICODE extends OPERATOR("≠")
private object FORALL_UNICODE extends OPERATOR("∀")
private object EXISTS_UNICODE extends OPERATOR("∃")

private object TRUE    extends OPERATOR("true")
private object FALSE   extends OPERATOR("false")

//@todo should probably also allow := *
private object ASSIGNANY extends OPERATOR(":=*") {
  override def regexp: Regex = """:=\*""".r
}
private object ASSIGN  extends OPERATOR(":=")
private object TEST    extends OPERATOR("?") {
  override def regexp: Regex = """\?""".r
}
private object IF extends OPERATOR("if")
private object ELSE extends OPERATOR("else")
private object SEMI    extends OPERATOR(";")
private object CHOICE  extends OPERATOR("++") {
  override def regexp: Regex = """\+\+""".r
}
//@todo simplify lexer by using silly ^@ notation rather than ^d for now. @ for adversary isn't too bad to remember but doesn't look as good as ^d.
private object DUAL    extends OPERATOR("^@") {
  override def regexp: Regex = """\^\@""".r
}

/*@TODO
private object DCHOICE  extends OPERATOR("--") {
  override def regexp = """--""".r
}
*/

// pseudos: could probably demote so that some are not OPERATOR
private object NOTHING extends Terminal("")

private case class DOT(index: Option[Int] = None) extends Terminal("•" + (index match {case Some(x) => "_"+x case None => ""})) {
  override def toString: String = "DOT(\"" + (index match {
    case None => ""
    case Some(idx) => idx
  }) + "\")"
  override def regexp: Regex = DOT.regexp
}
private object DOT {
  def regexp: Regex = """((?:•(?:\_[0-9]+)?)|(?:\.\_[0-9]+))""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

private object PLACE   extends OPERATOR("⎵") //("_")
private object ANYTHING extends OPERATOR("??") {
  override def regexp: Regex = """\?\?""".r
}
private object PSEUDO  extends Terminal("<pseudo>")


// @annotations

private object INVARIANT extends Terminal("@invariant") {
  override def regexp: Regex = """\@invariant""".r
}

// axiom and problem file

private object AXIOM_BEGIN extends Terminal("Axiom") {
  override def regexp: Regex = """Axiom""".r
}
private object END_BLOCK extends Terminal("End")
private case class DOUBLE_QUOTES_STRING(var s: String) extends Terminal("<string>") {
  override def regexp: Regex = DOUBLE_QUOTES_STRING_PAT.regexp
}
private object DOUBLE_QUOTES_STRING_PAT {
  def regexp: Regex = """\"(.*)\"""".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}
private object PERIOD extends Terminal(".") {
  override def regexp: Regex = "\\.".r
}
private object FUNCTIONS_BLOCK extends Terminal("Functions") {
  //not totally necessary -- you'll still get the right behavior because . matches \. But also allows stuff like Functions: which maybe isn't terrible.
//  override def regexp = """Functions\.""".r
}
private object DEFINITIONS_BLOCK extends Terminal("Definitions")
private object PROGRAM_VARIABLES_BLOCK extends Terminal("ProgramVariables")
private object VARIABLES_BLOCK extends Terminal("Variables") //used in axioms file...
private object PROBLEM_BLOCK extends Terminal("Problem")
private object TACTIC_BLOCK extends Terminal("Tactic")
//@todo the following R, B, T, P etc should be lexed as identifiers. Adapt code to make them disappear.
//@todo the following should all be removed or at most used as val REAL = Terminal("R")
private object REAL extends Terminal("$$$R")
private object BOOL extends Terminal("$$$B")
//Is there any reason we parse a bunch of stuff just to throw it away? Are these suppose to be in our sort heirarchy...?
private object TERM extends Terminal("$$$T")
private object PROGRAM extends Terminal("$$$P")
private object CP extends Terminal("$$$CP")
private object MFORMULA extends Terminal("$$F")

///////////
// Section: Terminal signals for extended lemma files.
///////////
private object SEQUENT_BEGIN extends Terminal("Sequent")  {
  override def regexp: Regex = """Sequent""".r
}
private object TURNSTILE extends Terminal("==>") {
  override def regexp: Regex = """==>""".r
}
private object FORMULA_BEGIN extends Terminal("Formula") {
  override def regexp: Regex = """Formula""".r
}

///////////
// Section: Terminal signals for tool files.
///////////
private object LEMMA_BEGIN extends Terminal("Lemma") {
  override def regexp: Regex = """Lemma""".r
}
private object TOOL_BEGIN extends Terminal("Tool") {
  override def regexp: Regex = """Tool""".r
}
private object HASH_BEGIN extends Terminal("Hash") {
  override def regexp: Regex = """Hash""".r
}
private case class TOOL_VALUE(var s: String) extends Terminal("<string>") {
  override def regexp: Regex = TOOL_VALUE_PAT.regexp
}
private object TOOL_VALUE_PAT {
  // values are nested into quadruple ", because they can contain single, double, or triple " themselves (arbitrary Scala code)
  def regexp: Regex = "\"{4}(([^\"]|\"(?!\"\"\")|\"\"(?!\"\")|\"\"\"(?!\"))*)\"{4}".r
//  def regexp = "\"([^\"]*)\"".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

private object SHARED_DEFINITIONS_BEGIN extends Terminal("SharedDefinitions") {}

private case class ARCHIVE_ENTRY_BEGIN(name: String) extends Terminal("ArchiveEntry|Lemma|Theorem|Exercise") {
  override def toString: String = name
  override def regexp: Regex = ARCHIVE_ENTRY_BEGIN.regexp
}
private object ARCHIVE_ENTRY_BEGIN {
  def regexp: Regex = "(ArchiveEntry|Lemma|Theorem|Exercise)".r
  val startPattern: Regex = ("^" + regexp.pattern.pattern + "[\\s\\S]*").r
}

///////////
// Section: Terminal signals for tactics.
///////////
private object BACKTICK extends Terminal("`") {}

/**
 * Lexer for KeYmaera X turns string into list of tokens.
  *
  * @author Andre Platzer
 * @author nfulton
 */
object KeYmaeraXLexer extends ((String) => List[Token]) with Logging {
  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /** Normalize all new lines in input to a s*/
  def normalizeNewlines(input: String): String = input.replace("\r\n", "\n").replace("\r", "\n").replaceAll(" *\n", "\n")
  /**
   * The lexer has multiple modes for the different sorts of files that are supported by KeYmaeraX.
   * The lexer will disallow non-expression symbols from occuring when the lexer is in expression mode.
   * This also ensures that reserved symbols are never used as function names.
    *
    * @param input The string to lex.
   * @param mode The lexer mode.
   * @return A stream of symbols corresponding to input.
   */
  //@todo performance bottleneck
  def inMode(input: String, mode: LexerMode): KeYmaeraXLexer.TokenStream = {
    val correctedInput = normalizeNewlines(input)
    logger.debug("LEX: " + correctedInput)
    val output = lex(correctedInput, SuffixRegion(1,1), mode)
    require(!output.exists(x => x.tok == ANYTHING), "output should not contain ??")
    require(output.last.tok.equals(EOF), "Expected EOF but found " + output.last.tok)
    output
  }

  def apply(input: String): KeYmaeraXLexer.TokenStream = inMode(input, ExpressionMode)

  /**
   * The lexer.
    *
    * @todo optimize
   * @param input The input to lex.
   * @param inputLocation The position of the input (e.g., wrt a source file).
   * @param mode The mode of the lexer.
   * @return A token stream.
   */
//  //@todo //@tailrec
//  private def lex(input: String, inputLocation:Location, mode: LexerMode): TokenStream =
//    if(input.trim.length == 0) {
//      List(Token(EOF))
//    }
//    else {
//      findNextToken(input, inputLocation, mode) match {
//        case Some((nextInput, token, nextLoc)) =>
//          //if (DEBUG) print(token)
//          token +: lex(nextInput, nextLoc, mode)
//        case None => List(Token(EOF)) //note: This case can happen if the input is e.g. only a comment or only whitespace.
//      }
//    }

  private def lex(input: String, inputLocation:Location, mode: LexerMode): TokenStream = {
    var remaining: String = input
    var loc: Location = inputLocation
    var output: scala.collection.mutable.ListBuffer[Token] = scala.collection.mutable.ListBuffer.empty
    while (!remaining.isEmpty) {
      findNextToken(remaining, loc, mode) match {
        case Some((nextInput, token, nextLoc)) =>
          output.append(token)
          remaining = nextInput
          loc = nextLoc
        case None => //note: This case can happen if the input is e.g. only a comment or only whitespace.
          output.append(Token(EOF, loc))
          return replaceAnything(output).to
      }
    }
    output.append(Token(EOF, loc))
    replaceAnything(output).to
  }

  /** Replace all instances of LPAREN,ANYTHING,RPAREN with LBANANA,RBANANA. */
  private def replaceAnything(output: scala.collection.mutable.ListBuffer[Token]): scala.collection.mutable.ListBuffer[Token] = {
    output.find(x => x.tok == ANYTHING) match {
      case None => output
      case Some(anyTok) =>
        val pos = output.indexOf(anyTok)
        replaceAnything(output.patch(pos-1, Token(LBANANA, anyTok.loc) :: Token(RBANANA, anyTok.loc) :: Nil, 3))
    }
  }

  /**
   * Finds the next token in a string.
    *
    * @todo Untested correctness condition: If a token's regex pattern contains another's, then the more restrictive token is processed first in the massive if/else.
    * @param s The string to process.
   * @param loc The location of s.
   * @param mode The mode of the lexer.
   * @return A triple containing:
   *          _1: the next token,
   *          _2: the portion of the string following the next token,
   *          _3: The location of the beginning of the next string.
   */
  @tailrec
  private def findNextToken(s: String, loc: Location, mode: LexerMode): Option[(String, Token, Location)] = {
    val whitespace = """^(\s+)[\s\S]*""".r
    val newline = """(?s)(^\n)[\s\S]*""".r //@todo use something more portable.
    val comment = """(?s)(^/\*[\s\S]*?\*/)[\s\S]*""".r

    /**
     *
     * @param cols Number of columns to move cursor.
     * @param terminal terminal to generate a token for.
     * @param location Current location.
     * @return Return value of findNextToken
     */
    def consumeColumns(cols: Int, terminal: Terminal, location: Location) : Option[(String, Token, Location)] = {
      assert(cols > 0, "Cannot move cursor less than 1 columns.")
      Some((
        s.substring(cols),
        Token(terminal, spanningRegion(loc, cols-1)),
        suffixOf(loc, cols)))
    }

    def consumeTerminalLength(terminal: Terminal, location: Location): Option[(String, Token, Location)] =
      consumeColumns(terminal.img.length, terminal, location)

    def consumeUnicodeTerminalLength(terminal: Terminal, location: Location, replacementTerminal: Terminal): Option[(String, Token, Location)] = {
      val result: Option[(String, Token, Location)] = consumeColumns(terminal.img.length, terminal, location)

      result match {
        case None => None
        case Some((s,t,l)) => Some((s, Token(replacementTerminal, t.loc), l))
      }
    }

    def swapOutFor(found: Option[(String, Token, Location)], repl: Terminal): Option[(String, Token, Location)] = found match {
      case None => None
      case Some((s,tok,cur)) => Some((s,Token(repl,tok.loc),cur))
    }

    s match {
      //update location if we encounter whitespace/comments.
      case comment(theComment) => {
        val comment = s.substring(0, theComment.length)
        val lastLineCol = comment.lines.toList.last.length //column of last line.
        val lineCount = comment.lines.length
        findNextToken(s.substring(theComment.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl, sc, el, ec) => Region(sl + lineCount - 1, lastLineCol, el, ec)
          case SuffixRegion(sl, sc) => SuffixRegion(sl + lineCount - 1, sc + theComment.length)
        }, mode)
      }

      case newline(_*) =>
        findNextToken(s.tail, loc match {
          case UnknownLocation     => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl+1,1,el,ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl+1, 1)
        }, mode)

      case whitespace(spaces) =>
        findNextToken(s.substring(spaces.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl, sc+spaces.length, el, ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl, sc+ spaces.length)
        }, mode)

      //Lemma file cases
      case LEMMA_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(LEMMA_BEGIN, loc)
        case ProblemFileMode => consumeColumns(LEMMA_BEGIN.img.length, ARCHIVE_ENTRY_BEGIN("Lemma"), loc)
        case _ => throw new Exception("Encountered ``Lemma`` in non-lemma lexing mode.")
      }
      case TOOL_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(TOOL_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Tool`` in non-lemma lexing mode.")
      }
      case HASH_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(HASH_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Tool`` in non-lemma lexing mode.")
      }
      case SEQUENT_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(SEQUENT_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Sequent`` in a non-lemma file.")
      }
      case TURNSTILE.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(TURNSTILE, loc)
        case _ => throw new Exception("Encountered a turnstile symbol ==> in a non-lemma file.")
      }
      case FORMULA_BEGIN.startPattern(_*) => mode match {
        case LemmaFileMode => consumeTerminalLength(FORMULA_BEGIN, loc)
        case _ => throw new Exception("Encountered a formula begin symbol (Formula:) in a non-lemma file.")
      }

      case DOT.startPattern(dot) => val (_, idx) = splitName(dot); consumeTerminalLength(DOT(idx), loc)

      // File cases
      case PERIOD.startPattern(_*) => consumeTerminalLength(PERIOD, loc) //swapOutFor(consumeTerminalLength(PERIOD, loc), DOT)
        /*mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(PERIOD, loc)
        case _ => throw new Exception("Periods should only occur when processing files.")
      }*/
      case ARCHIVE_ENTRY_BEGIN.startPattern(kind) => mode match {
        case ProblemFileMode => consumeColumns(kind.length, ARCHIVE_ENTRY_BEGIN(kind), loc)
        case LemmaFileMode if kind == "Lemma" => consumeTerminalLength(LEMMA_BEGIN, loc)
        case _ => throw new Exception("Encountered ``" + ARCHIVE_ENTRY_BEGIN(kind).img + "`` in non-problem file lexing mode.")
      }
      case FUNCTIONS_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(FUNCTIONS_BLOCK, loc)
        case _ => throw new Exception("Functions. should only occur when processing files.")
      }
      case DEFINITIONS_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(DEFINITIONS_BLOCK, loc)
        case _ => throw new Exception("Definitions. should only occur when processing files.")
      }
      case PROGRAM_VARIABLES_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(PROGRAM_VARIABLES_BLOCK, loc)
        case _ => throw new Exception("ProgramVariables. should only occur when processing files.")
      }
      case VARIABLES_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(VARIABLES_BLOCK, loc)
        case _ => throw new Exception("Variables. should only occur when processing files.")
      }
      case BOOL.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(BOOL, loc)
        case _ => throw new Exception("Bool symbol declaration should only occur when processing files.")
      }
      case REAL.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(REAL, loc)
        case _ => throw new Exception("Real symbol declaration should only occur when processing files.")
      }
      case TERM.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(TERM, loc)
        case _ => throw new Exception("Term symbol declaration should only occur when processing files.")
      }
      case PROGRAM.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(PROGRAM, loc)
        case _ => throw new Exception("Program symbol declaration should only occur when processing files.")
      }
      case CP.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(CP, loc)
        case _ => throw new Exception("CP symbol declaration should only occur when processing files.")
      }
      case MFORMULA.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(MFORMULA, loc)
        case _ => throw new Exception("MFORMULA symbol declaration should only occur when processing files.")
      }
      //.kyx file cases
      case PROBLEM_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode => consumeTerminalLength(PROBLEM_BLOCK, loc)
        case _ => throw new Exception("Problem./End. sections should only occur when processing .kyx files.")
      }
      case TACTIC_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode => consumeTerminalLength(TACTIC_BLOCK, loc)
        case _ => throw new Exception("Tactic./End. sections should only occur when processing .kyx files.")
      }
      case BACKTICK.startPattern(_*) => mode match {
        case ProblemFileMode => consumeTerminalLength(BACKTICK, loc)
        case _ => throw new Exception("Backtick ` should only occur when processing .kyx files.")
      }
      case SHARED_DEFINITIONS_BEGIN.startPattern(_*) => mode match {
        case ProblemFileMode => consumeTerminalLength(SHARED_DEFINITIONS_BEGIN, loc)
        case _ => throw new Exception("SharedDefinitions./End. sections should only occur when processing .kyx files.")
      }
      //Lemma file cases (2)
      case TOOL_VALUE_PAT.startPattern(str, _) => mode match { //@note must be before DOUBLE_QUOTES_STRING
        case LemmaFileMode =>
          //A tool value looks like """"blah"""" but only blah gets grouped, so there are eight
          // extra characters to account for.
          consumeColumns(str.length + 8, TOOL_VALUE(str), loc)
        case _ => throw new Exception("Encountered delimited string in non-lemma lexing mode.")
      }
      //Axiom file cases
      case AXIOM_BEGIN.startPattern(_*) => mode match {
        case AxiomFileMode => consumeTerminalLength(AXIOM_BEGIN, loc)
        case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
      }
      case END_BLOCK.startPattern(_*) => mode match {
        case AxiomFileMode | ProblemFileMode | LemmaFileMode => consumeTerminalLength(END_BLOCK, loc)
        case _ => throw new Exception("Encountered ``Axiom.`` in non-axiom lexing mode.")
      }
      case DOUBLE_QUOTES_STRING_PAT.startPattern(str) => mode match {
        case AxiomFileMode | LemmaFileMode | ProblemFileMode =>
          //An axiom name looks like "blah". but only blah gets grouped, so there are three
          // extra characters to account for.
          consumeColumns(str.length + 2, DOUBLE_QUOTES_STRING(str), loc)
        case _ => throw new Exception("Encountered delimited string in non-axiom lexing mode.")
      }

      //These have to come before LBOX,RBOX because otherwise <= becopmes LDIA, EQUALS
      case GREATEREQ.startPattern(_*) => consumeTerminalLength(GREATEREQ, loc)
      case GREATEREQ_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(GREATEREQ_UNICODE, loc, GREATEREQ)
      case LESSEQ.startPattern(_*) => consumeTerminalLength(LESSEQ, loc)
      case LESSEQ_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(LESSEQ_UNICODE, loc, LESSEQ)
      case NOTEQ.startPattern(_*) => consumeTerminalLength(NOTEQ, loc)

      case LBANANA.startPattern(_*) => consumeTerminalLength(LBANANA, loc)
      case RBANANA.startPattern(_*) => consumeTerminalLength(RBANANA, loc)
      case LPAREN.startPattern(_*) => consumeTerminalLength(LPAREN, loc)
      case RPAREN.startPattern(_*) => consumeTerminalLength(RPAREN, loc)
      case LBOX.startPattern(_*) => consumeTerminalLength(LBOX, loc)
      case RBOX.startPattern(_*) => consumeTerminalLength(RBOX, loc)
      case LBARB.startPattern(_*) => consumeTerminalLength(LBARB, loc)
      case RBARB.startPattern(_*) => consumeTerminalLength(RBARB, loc)
      case LBRACE.startPattern(_*) => consumeTerminalLength(LBRACE, loc)
      case RBRACE.startPattern(_*) => consumeTerminalLength(RBRACE, loc)

      case COMMA.startPattern(_*) => consumeTerminalLength(COMMA, loc)

      case IF.startPattern(_*) => consumeTerminalLength(IF, loc)
      case ELSE.startPattern(_*) => consumeTerminalLength(ELSE, loc)
      //This has to come before PLUS because otherwise ++ because PLUS,PLUS instead of CHOICE.
      case CHOICE.startPattern(_*) => consumeTerminalLength(CHOICE, loc)
      //This has to come before MINUS because otherwise -- because MINUS,MINUS instead of DCHOICE.
      //@TODO case DCHOICE.startPattern(_*) => consumeTerminalLength(DCHOICE, loc)
      //@note must be before POWER
      case DUAL.startPattern(_*) => consumeTerminalLength(DUAL, loc)

      case PRIME.startPattern(_*) => consumeTerminalLength(PRIME, loc)
      case SLASH.startPattern(_*) => consumeTerminalLength(SLASH, loc)
      case POWER.startPattern(_*) => consumeTerminalLength(POWER, loc)
      case STAR.startPattern(_*) => consumeTerminalLength(STAR, loc)
      case PLUS.startPattern(_*) => consumeTerminalLength(PLUS, loc)


      case AMP.startPattern(_*) => consumeTerminalLength(AMP, loc)
      case AND_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(AND_UNICODE, loc, AMP)
      case NOT.startPattern(_*) => consumeTerminalLength(NOT, loc)
      case OR.startPattern(_*) => consumeTerminalLength(OR, loc)
      case OR_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(OR_UNICODE, loc, OR)
      case EQUIV.startPattern(_*) => consumeTerminalLength(EQUIV, loc)
      case EQUIV_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(EQUIV_UNICODE, loc, EQUIV)
      case IMPLY.startPattern(_*) => consumeTerminalLength(IMPLY, loc)
      case IMPLY_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(IMPLY_UNICODE, loc, IMPLY)
      case REVIMPLY.startPattern(_*) => consumeTerminalLength(REVIMPLY, loc)
      case REVIMPLY_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(REVIMPLY_UNICODE, loc, REVIMPLY)

      case FORALL.startPattern(_*) => consumeTerminalLength(FORALL, loc)
      case FORALL_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(FORALL_UNICODE, loc, FORALL)
      case EXISTS.startPattern(_*) => consumeTerminalLength(EXISTS, loc)
      case EXISTS_UNICODE.startPattern(_*) => consumeUnicodeTerminalLength(EXISTS_UNICODE, loc, EXISTS)

      /** 15624: For DAL */
      case DEXISTS.startPattern(_*) => consumeTerminalLength(DEXISTS, loc)

      case EQ.startPattern(_*) => consumeTerminalLength(EQ, loc)
      case UNEQUAL_UNICODE.startPattern(_*) => ???
      case TRUE.startPattern(_*) => consumeTerminalLength(TRUE, loc)
      case FALSE.startPattern(_*) => consumeTerminalLength(FALSE, loc)

      case ANYTHING.startPattern(_*) => consumeTerminalLength(ANYTHING, loc) //@note this token is stripped out and replaced with (! !) in [[fin`dNextToken]].

      case ASSIGNANY.startPattern(_*) => consumeTerminalLength(ASSIGNANY, loc)
      case ASSIGN.startPattern(_*) => consumeTerminalLength(ASSIGN, loc)
      case TEST.startPattern(_*) => consumeTerminalLength(TEST, loc)
      case SEMI.startPattern(_*) => consumeTerminalLength(SEMI, loc)


      case PLACE.startPattern(_*) => consumeTerminalLength(PLACE, loc)
      case PSEUDO.startPattern(_*) => consumeTerminalLength(PSEUDO, loc)

      case INVARIANT.startPattern(_*) => consumeTerminalLength(INVARIANT, loc)

      case IDENT.startPattern(name) => {
        val (s, idx) = splitName(name)
        consumeTerminalLength(IDENT(s, idx), loc)
      }
      case NUMBER.startPattern(n) => consumeTerminalLength(NUMBER(n), loc)
      //@NOTE Minus has to come after number so that -9 is lexed as Number(-9) instead of as Minus::Number(9).
      //@NOTE Yet NUMBER has been demoted not to feature - signs, so it has become irrelevant for now.
      case MINUS.startPattern(_*) => consumeTerminalLength(MINUS, loc)

      case LDIA.startPattern(_*) => consumeTerminalLength(LDIA, loc)
      case RDIA.startPattern(_*) => consumeTerminalLength(RDIA, loc)

      case PRG_DEF.startPattern(_*) => consumeTerminalLength(PRG_DEF, loc)
      case COLON.startPattern(_*) => consumeTerminalLength(COLON, loc)

      case _ if s.isEmpty => None
        //@todo should be LexException inheriting
      case _ => throw LexException(loc.begin + " Lexer does not recognize input at " + loc + " in `\n" + s +"\n` beginning with character `" + s(0) + "`=" + s(0).getNumericValue, loc).inInput(s)
    }
  }

  /**
   * Returns the region containing everything between the starting position of the current location
   * location and the indicated offset of from the starting positiong of the current location,
   * inclusive.
    *
    * @param location Current location
   * @param endColOffset Column offset of the region
   * @return The region spanning from the start of ``location" to the offset from the start of ``location".
   */
  private def spanningRegion(location: Location, endColOffset: Int) =
    location match {
      case UnknownLocation        => UnknownLocation
      case Region(sl, sc, el, ec) => Region(sl, sc, sl, sc + endColOffset)
      case SuffixRegion(sl, sc)   => Region(sl, sc, sl, sc + endColOffset)
    }

  /**
   *
   * @param location Current location
   * @param colOffset Number of columns to chop off from the starting position of location.
   * @return A region containing all of location except the indicated columns in the initial row.
   *         I.e., the colOffset-suffix of location.
   */
  private def suffixOf(location: Location, colOffset: Int) : Location =
    location match {
      case UnknownLocation        => UnknownLocation
      case Region(sl, sc, el, ec) => Region(sl, sc + colOffset, el, ec)
      case SuffixRegion(sl, sc)   => SuffixRegion(sl, sc + colOffset)
    }

  private def splitName(s : String) : (String, Option[Int]) =
    if(s.contains("_") && !s.endsWith("_")) {
      // a_b_2 ==> "a_b", 2
      val (namePart, idxPart) = {
        val finalUnderscoreIdx = s.lastIndexOf("_")
        ( s.substring(0, finalUnderscoreIdx),
          s.substring(finalUnderscoreIdx + 1, s.length) )
      }

      val idx = Some(Integer.parseInt(idxPart))

      (namePart, idx)
    } else (s, None)
}

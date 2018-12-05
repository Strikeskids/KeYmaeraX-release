package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.BelleToken
import edu.cmu.cs.ls.keymaerax.parser._
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable.List

/**
  * A lexer for the Bellerophon tactics language.
  *
  * @author Nathan Fulton
  */
object BelleLexer extends ((String) => List[BelleToken]) with Logging {
  type TokenStream = List[BelleToken]

  def apply(s: String) : List[BelleToken] = {
    //Avoids importing a thing with lots of potential name clashes.
    val correctedInput = edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.normalizeNewlines(s)
    //@todo not sure if this position is Ok. This is what's used in the KeYmaera X lexer.
    val startingLocation = SuffixRegion(1,1)

    logger.debug("LEX: " + correctedInput)
    lex(s, startingLocation)
  }

  /**
    *
    * @param input The input
    * @param inputLocation The location of this input.
    *                      If this is a recursive call, then inputLocation might not be (0,0).
    */
  private def lex(input: String, inputLocation: Location): TokenStream =
    if(input.trim.length == 0) {
      List(BelleToken(EOF, inputLocation))
    }
    else {
      findNextToken(input, inputLocation) match {
        case Some((nextInput, token, nextLoc)) =>
          //if (DEBUG) print(token)
          token +: lex(nextInput, nextLoc)
        case None => List(BelleToken(EOF, inputLocation)) //note: This case can happen if the input is e.g. only a comment or only whitespace.
      }
    }

  private def findNextToken(input: String, loc: Location): Option[(String, BelleToken, Location)] = {
    /** Helper method for findNextToken */
    def consumeTerminalLength(terminal: BelleTerminal, location: Location) = {
      val token = terminal.img
      advanceRegion(location, token) match {
        case (tokenRegion, nextRegion) =>
          Some((
            input.substring(token.length),
            BelleToken(terminal, tokenRegion),
            nextRegion
          ))
      }
    }

    input match {
      //Comments, newlines, and white-space. These are all copied from the KeYmaera X lexer.
      case comment(theComment) =>
        val comment = input.substring(0, theComment.length)
        findNextToken(input.substring(theComment.length), advanceRegion(loc, theComment)._2)

      case newline(_*) =>
        findNextToken(input.tail, advanceRegion(loc, "\n")._2)

      case whitespace(spaces) =>
        findNextToken(input.substring(spaces.length), loc match {
          case UnknownLocation => UnknownLocation
          case Region(sl,sc,el,ec) => Region(sl, sc+spaces.length, el, ec)
          case SuffixRegion(sl,sc) => SuffixRegion(sl, sc+ spaces.length)
        })

      //Stuff that could be confused as an identifier.
      case ON_ALL.startPattern(_*) => consumeTerminalLength(ON_ALL, loc)
      case PENDING.startPattern(_*) => consumeTerminalLength(PENDING, loc)
      case US_MATCH.startPattern(_*) => consumeTerminalLength(US_MATCH, loc)
      case PARTIAL.startPattern(_*) => consumeTerminalLength(PARTIAL, loc)
      case LET.startPattern(_*) => consumeTerminalLength(LET, loc)
      case IN.startPattern(_*) => consumeTerminalLength(IN, loc)
      case TACTIC.startPattern(_*) => consumeTerminalLength(TACTIC, loc)
      case AS.startPattern(_*) => consumeTerminalLength(AS, loc)
      case DEF.startPattern(_*) => consumeTerminalLength(DEF, loc)
      case EXPAND.startPattern(_*) => consumeTerminalLength(EXPAND, loc)

      //build-in tactics.
      case IDENT.startPattern(name) => consumeTerminalLength(IDENT(name), loc)

      case N_TIMES.startPattern(n) => consumeTerminalLength(N_TIMES(Integer.parseInt(n.tail)), loc)

      //Combinators
      case SEQ_COMBINATOR.startPattern(_*) => consumeTerminalLength(SEQ_COMBINATOR, loc)
      case DEPRECATED_SEQ_COMBINATOR.startPattern(_*) => consumeTerminalLength(DEPRECATED_SEQ_COMBINATOR, loc)
      case EITHER_COMBINATOR.startPattern(_*) => consumeTerminalLength(EITHER_COMBINATOR, loc)
      case AFTER_COMBINATOR.startPattern(_*) => consumeTerminalLength(AFTER_COMBINATOR, loc)
      case KLEENE_STAR.startPattern(_*) => consumeTerminalLength(KLEENE_STAR, loc)
      case SATURATE.startPattern(_*) => consumeTerminalLength(SATURATE, loc)
      case BRANCH_COMBINATOR.startPattern(_*) => consumeTerminalLength(BRANCH_COMBINATOR, loc)
      case OPTIONAL.startPattern(_*) => consumeTerminalLength(OPTIONAL, loc)

      //Positions
      case ABSOLUTE_POSITION.startPattern(positionString) => consumeTerminalLength(ABSOLUTE_POSITION(positionString), loc)
      case LAST_SUCCEDENT.startPattern(_*) => consumeTerminalLength(LAST_SUCCEDENT, loc)
      case LAST_ANTECEDENT.startPattern(_*) => consumeTerminalLength(LAST_ANTECEDENT, loc)
      case SEARCH_SUCCEDENT.startPattern(_*) => consumeTerminalLength(SEARCH_SUCCEDENT, loc)
      case SEARCH_ANTECEDENT.startPattern(_*) => consumeTerminalLength(SEARCH_ANTECEDENT, loc)
      case SEARCH_EVERYWHERE.startPattern(_*) => consumeTerminalLength(SEARCH_EVERYWHERE, loc)
      case EXACT_MATCH.startPattern(_*) => consumeTerminalLength(EXACT_MATCH, loc)
      case UNIFIABLE_MATCH.startPattern(_*) => consumeTerminalLength(UNIFIABLE_MATCH, loc)

      //Delimited expressions
      case EXPRESSION.startPattern(contents, _*) => consumeTerminalLength(EXPRESSION(contents), loc)

      //Misc.
      case OPEN_PAREN.startPattern(_*) => consumeTerminalLength(OPEN_PAREN, loc)
      case CLOSE_PAREN.startPattern(_*) => consumeTerminalLength(CLOSE_PAREN, loc)
      case COMMA.startPattern(_*) => consumeTerminalLength(COMMA, loc)
      case RIGHT_ARROW.startPattern(_*) => consumeTerminalLength(RIGHT_ARROW, loc)

      //Error messages
      case _ => throw LexException(s"Could not lex $input", loc)
    }
  }

  private val whitespace = """^(\s+)[\s\S]*""".r
  //@note Assuming all newlines are just \n is OK because we normalize newlines prior to lexing.
  private val newline = """(?s)(^\n)[\s\S]*""".r
  private val comment = """(?s)(^/\*[\s\S]*?\*/)[\s\S]*""".r

  /**
    * Compute the two regions corresponding to a consumed token
    * @param loc The location of the consumed token
    * @param consumed The token that was consumed
    * @return (The region corresponding to the token, The region after the token)
    */
  private def advanceRegion(loc: Location, consumed: String): (Location, Location) = {
    val length = consumed.length()
    val lines = consumed.count(_ == '\n')
    val lastLineLength = length - consumed.lastIndexOf('\n') - 1
    loc match {
      case UnknownLocation => (UnknownLocation, UnknownLocation)
      case Region(sl, sc, el, ec) =>
        val lastLinePos = if (lines == 0) sc + length else lastLineLength + 1
        (Region(sl, sc, sl + lines, lastLinePos), Region(sl + lines, lastLinePos, el, ec))
      case SuffixRegion(sl, sc) =>
        val lastLinePos = if (lines == 0) sc + length else lastLineLength + 1
        (Region(sl, sc, sl + lines, lastLinePos), SuffixRegion(sl + lines, lastLinePos))
    }
  }

}

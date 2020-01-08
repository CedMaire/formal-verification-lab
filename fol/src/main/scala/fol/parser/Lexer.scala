package fol
package parser

import scallion.input._
import scallion.lexical._

object Lexer {

  private object definitions
      extends Lexers[Token, Char, Position]
      with CharRegExps {
    val lexer = Lexer(
      word("/\\") | word("∧") | word("&&") |> { (cs, p) =>
        Token.And(p._1)
      },
      word("\\/") | word("∨") | word("||") |> { (cs, p) =>
        Token.Or(p._1)
      },
      word("=>") | word("→") | word("⇒") |> { (cs, p) =>
        Token.Implies(p._1)
      },
      word("<=>") | word("↔") | word("⇔") |> { (cs, p) =>
        Token.Iff(p._1)
      },
      word("~") | word("¬") |> { (cs, p) =>
        Token.Not(p._1)
      },
      elem('(') |> { (cs, p) =>
        Token.Parenthesis(true, p._1)
      },
      elem(')') |> { (cs, p) =>
        Token.Parenthesis(false, p._1)
      },
      word("forall") | word("∀") |> { (cs, p) =>
        Token.Forall(p._1)
      },
      word("exists") | word("∃") |> { (cs, p) =>
        Token.Exists(p._1)
      },
      word(".") |> { (cs, p) =>
        Token.Dot(p._1)
      },
      word("..") |> { (cs, p) =>
        Token.DotDot(p._1)
      },
      word(",") |> { (cs, p) =>
        Token.Comma(p._1)
      },
      word("'") |> { (cs, p) =>
        Token.Tick(p._1)
      },
      word("=") |> { (cs, p) =>
        Token.Equals(p._1)
      },
      word("!=") | word("≠") |> { (cs, p) =>
        Token.NotEquals(p._1)
      },
      word("true") | word("⊤") |> { (cs, p) =>
        Token.BooleanLiteral(true, p._1)
      },
      word("false") | word("⊥") |> { (cs, p) =>
        Token.BooleanLiteral(false, p._1)
      },
      (elem(_.isLetter) | elem('_')) ~ many(elem(_.isLetterOrDigit) | elem('_')) |> {
        (cs, p) =>
          Token.Identifier(cs.mkString, p._1)
      },
      many1(whiteSpace) |> { (cs, p) =>
        Token.Ignore(p._1)
      }
    ).onError {
      case (cs, p) => Token.Error(cs.mkString, p._1)
    }
  }

  def apply(characters: Iterator[Char], part: Int = 0): Iterator[Token] = {
    definitions
      .lexer(Source.fromIterator(characters, new PartPositioner(part)))
      .filter(Kind.of(_) != Kind.Ignore)
  }

  def unapply(token: Token): String = token match {
    case Token.And(_)                   => "∧"
    case Token.Or(_)                    => "∨"
    case Token.Implies(_)               => "⇒"
    case Token.Iff(_)                   => "⇔"
    case Token.Not(_)                   => "¬"
    case Token.Parenthesis(true, _)     => "("
    case Token.Parenthesis(false, _)    => ")"
    case Token.Forall(_)                => "∀"
    case Token.Exists(_)                => "∃"
    case Token.Dot(_)                   => "."
    case Token.DotDot(_)                => ".."
    case Token.Comma(_)                 => ","
    case Token.Tick(_)                  => "'"
    case Token.Equals(_)                => "="
    case Token.NotEquals(_)             => "≠"
    case Token.BooleanLiteral(true, _)  => "⊤"
    case Token.BooleanLiteral(false, _) => "⊥"
    case Token.Identifier(name, _)      => name
    case Token.Placeholder(_, _)        => "$"
    case Token.Error(content, _)        => "<error: " + content + ">"
    case Token.Ignore(_)                => "<ignored>"
  }

  def unapply(tokens: Seq[Token]): String = {

    def needsSpace(left: Kind, right: Kind): Boolean = (left, right) match {
      case (Kind.Identifier, Kind.Identifier) => true
      case (Kind.Dot, _)                      => true
      case (Kind.Comma, _)                    => true
      case (Kind.EquSign, _)                  => true
      case (_, Kind.EquSign)                  => true
      case (Kind.And, _)                      => true
      case (_, Kind.And)                      => true
      case (Kind.Or, _)                       => true
      case (_, Kind.Or)                       => true
      case (Kind.Implies, _)                  => true
      case (_, Kind.Implies)                  => true
      case (Kind.Iff, _)                      => true
      case (_, Kind.Iff)                      => true
      case _                                  => false
    }

    val spaces = tokens.zip(tokens.drop(1)).map {
      case (left, right) =>
        if (needsSpace(Kind.of(left), Kind.of(right))) " " else ""
    }

    val strings = tokens.map(unapply(_))

    if (tokens.isEmpty) {
      ""
    } else {
      spaces.zip(strings.tail).foldLeft(strings.head) {
        case (acc, (space, string)) => acc + space + string
      }
    }
  }
}

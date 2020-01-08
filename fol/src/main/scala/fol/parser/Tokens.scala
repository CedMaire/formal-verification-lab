package fol
package parser

sealed trait Token {
  val position: Position
}

object Token {
  case class And(position: Position) extends Token
  case class Or(position: Position) extends Token
  case class Implies(position: Position) extends Token
  case class Iff(position: Position) extends Token
  case class Not(position: Position) extends Token
  case class Parenthesis(isOpen: Boolean, position: Position) extends Token
  case class BooleanLiteral(value: Boolean, position: Position) extends Token
  case class Identifier(name: String, position: Position) extends Token
  case class Placeholder(index: Int, position: Position) extends Token
  case class Forall(position: Position) extends Token
  case class Exists(position: Position) extends Token
  case class Equals(position: Position) extends Token
  case class NotEquals(position: Position) extends Token
  case class Dot(position: Position) extends Token
  case class Comma(position: Position) extends Token
  case class Tick(position: Position) extends Token
  case class Ignore(position: Position) extends Token
  case class DotDot(position: Position) extends Token
  case class Error(content: String, position: Position) extends Token
}

sealed trait Kind
object Kind {

  case object And extends Kind
  case object Or extends Kind
  case object Implies extends Kind
  case object Iff extends Kind
  case object Not extends Kind
  case class Parenthesis(isOpen: Boolean) extends Kind
  case object Literal extends Kind
  case object Identifier extends Kind
  case object Placeholder extends Kind
  case object Quantifier extends Kind
  case object EquSign extends Kind
  case object Dot extends Kind
  case object Comma extends Kind
  case object Tick extends Kind
  case object Ignore extends Kind
  case object DotDot extends Kind
  case object Error extends Kind

  def of(token: Token): Kind = token match {
    case Token.And(_)                 => Kind.And
    case Token.Or(_)                  => Kind.Or
    case Token.Implies(_)             => Kind.Implies
    case Token.Iff(_)                 => Kind.Iff
    case Token.Not(_)                 => Kind.Not
    case Token.Parenthesis(isOpen, _) => Kind.Parenthesis(isOpen)
    case Token.BooleanLiteral(_, _)   => Kind.Literal
    case Token.Identifier(_, _)       => Kind.Identifier
    case Token.Placeholder(_, _)      => Kind.Placeholder
    case Token.Forall(_)              => Kind.Quantifier
    case Token.Exists(_)              => Kind.Quantifier
    case Token.Equals(_)              => Kind.EquSign
    case Token.NotEquals(_)           => Kind.EquSign
    case Token.Dot(_)                 => Kind.Dot
    case Token.Comma(_)               => Kind.Comma
    case Token.Tick(_)                => Kind.Tick
    case Token.Ignore(_)              => Kind.Ignore
    case Token.DotDot(_)              => Kind.DotDot
    case Token.Error(_, _)            => Kind.Error
  }
}

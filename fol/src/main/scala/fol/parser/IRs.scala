package fol
package parser

object IRs {

  sealed trait IdentifierIR
  case class Id(id: Identifier) extends IdentifierIR
  case class IdPlaceholder(index: Int) extends IdentifierIR

  sealed trait FunctionIR
  case class Fun(fun: Function) extends FunctionIR
  case class FunPlaceholder(index: Int) extends FunctionIR

  sealed trait PredicateIR
  case class Pred(pref: Predicate) extends PredicateIR
  case class PredPlaceholder(index: Int) extends PredicateIR

  sealed trait ConstantIR
  case class Con(pref: Constant) extends ConstantIR
  case class ConPlaceholder(index: Int) extends ConstantIR

  sealed trait ExprIR
  case class ConVal(prim: ConstantIR) extends ExprIR
  case class Var(id: Identifier) extends ExprIR
  case class FunctionApp(
      function: FunctionIR,
      args: Seq[ExprIR],
      varargsPlaceholder: Option[Int]
  ) extends ExprIR
  case class ExprPlaceholder(index: Int) extends ExprIR

  sealed trait FormulaIR
  case class UnaryApp(op: UnaryOp, inner: FormulaIR) extends FormulaIR
  case class BinaryApp(op: BinaryOp, lhs: FormulaIR, rhs: FormulaIR)
      extends FormulaIR
  case class BoolLiteral(value: Boolean) extends FormulaIR
  case class PredicateApp(
      pred: PredicateIR,
      args: Seq[ExprIR],
      varargsPlaceholder: Option[Int]
  ) extends FormulaIR
  case class Equals(lhs: ExprIR, rhs: ExprIR) extends FormulaIR
  case class Quantified(
      quantifier: Quantifier,
      id: IdentifierIR,
      inner: FormulaIR
  ) extends FormulaIR
  case class FormulaPlaceholder(index: Int) extends FormulaIR

  sealed trait Quantifier
  case object Forall extends Quantifier
  case object Exists extends Quantifier

  sealed trait UnaryOp
  case object Not extends UnaryOp

  sealed trait BinaryOp
  case object And extends BinaryOp
  case object Or extends BinaryOp
  case object Implies extends BinaryOp
  case object Iff extends BinaryOp
}

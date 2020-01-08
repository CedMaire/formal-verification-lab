package fol
package parser

import scala.language.experimental.macros
import scala.reflect.macros.whitebox.Context

class Macros(final val c: Context) {
  import c.universe._

  def getString(expr: c.Tree): String = expr match {
    case Literal(Constant(s: String)) => s
    case _                            => c.abort(c.enclosingPosition, "Unexpected macro use.")
  }

  val rawParts = c.prefix.tree match {
    case Select(Apply(_, List(Apply(_, parts))), _) => parts
    case _                                          => c.abort(c.enclosingPosition, "Unexpected macro use.")
  }

  val parts = rawParts.map(getString)

  import fol.parser._

  val actualTokens = parts.zipWithIndex.map {
    case (part, index) => Lexer(part.toIterator, index)
  }

  val placeHolders =
    Seq.tabulate(parts.length - 1)(Token.Placeholder(_, parser.NoPosition))

  val tokens =
    (placeHolders.zip(actualTokens.tail)).foldLeft(actualTokens.head) {
      case (acc, (ph, ts)) => acc ++ Iterator(ph) ++ ts
    }

  def pretty(kind: Kind): String = kind match {
    case Kind.And                => "the symbol `∧`"
    case Kind.Or                 => "the symbol `∨`"
    case Kind.Implies            => "the symbol `⇒`"
    case Kind.Iff                => "the symbol `⇔`"
    case Kind.Not                => "the symbol `¬`"
    case Kind.Parenthesis(true)  => "an open parenthesis"
    case Kind.Parenthesis(false) => "a close parenthesis"
    case Kind.Literal            => "a literal formula"
    case Kind.Identifier         => "an identifier"
    case Kind.Placeholder        => "a placeholder"
    case Kind.DotDot             => "a varargs placeholder"
    case Kind.Quantifier         => "a quantifier"
    case Kind.EquSign            => "an equality sign"
    case Kind.Dot                => "the symbol `.`"
    case Kind.Comma              => "the symbol `,`"
    case Kind.Tick               => "a constant"
    case _                       => "a token of kind " + kind
  }

  def exprIr = Parsers.expr(tokens) match {
    case Parsers.Parsed(value, _) => value
    case Parsers.UnexpectedToken(token, rest) => {

      val msg = token match {
        case Token.Error(content, pos) => "Unrecognized symbol " + content + "."
        case _ => {
          "Unexpected symbol `" + parser.Lexer
            .unapply(token) + "` in expr quasiquote.\n" +
            "The following symbols are accepted at that position: " +
            rest.first.map(pretty).toSeq.sorted.mkString(", ") + "."
        }
      }

      c.abort(c.enclosingPosition, msg)
    }
    case Parsers.UnexpectedEnd(rest) => {
      val msg =
        "Unexpected end of the expression in expr quasiquote.\n" +
          "The following symbols can follow: " +
          rest.first.map(pretty).toSeq.sorted.mkString(", ") + "."

      c.abort(c.enclosingPosition, msg)
    }
  }

  def formulaIr = Parsers.formula(tokens) match {
    case Parsers.Parsed(value, _) => value
    case Parsers.UnexpectedToken(token, rest) => {

      val msg = token match {
        case Token.Error(content, pos) => "Unrecognized symbol " + content + "."
        case _ => {
          "Unexpected symbol `" + parser.Lexer
            .unapply(token) + "` in fol quasiquote.\n" +
            "The following symbols are accepted at that position: " +
            rest.first.map(pretty).toSeq.sorted.mkString(", ") + "."
        }
      }

      c.abort(c.enclosingPosition, msg)
    }
    case Parsers.UnexpectedEnd(rest) => {
      val msg =
        "Unexpected end of the formula in fol quasiquote.\n" +
          "The following symbols can follow: " +
          rest.first.map(pretty).toSeq.sorted.mkString(", ") + "."

      c.abort(c.enclosingPosition, msg)
    }
  }

  object apply {

    def goC(con: IRs.ConstantIR, args: Seq[c.Expr[Any]]): c.Tree = con match {
      case IRs.Con(name)             => q"$name"
      case IRs.ConPlaceholder(index) => q"${args(index)}"
    }

    def goE(expr: IRs.ExprIR, args: Seq[c.Expr[Any]]): c.Tree = expr match {
      case IRs.ConVal(con) => q"_root_.fol.Con(${goC(con, args)})"
      case IRs.Var(id)     => q"_root_.fol.Var($id)"
      case IRs.FunctionApp(function, funArgs, None) =>
        q"_root_.fol.FunApp(${goG(function, args)}, _root_.scala.collection.Seq(..${funArgs
          .map(goE(_, args))}))"
      case IRs.FunctionApp(function, funArgs, Some(index)) =>
        q"_root_.fol.FunApp(${goG(function, args)}, _root_.scala.collection.Seq(..${funArgs
          .map(goE(_, args))}) ++ ${args(index)})"
      case IRs.ExprPlaceholder(index) => {
        val arg = args(index)
        if (c.typecheck(q"$arg").tpe <:< typeOf[Identifier]) {
          q"_root_.fol.Var($arg)"
        } else {
          q"$arg"
        }
      }
    }

    def goI(id: IRs.IdentifierIR, args: Seq[c.Expr[Any]]): c.Tree = id match {
      case IRs.Id(name)             => q"$name"
      case IRs.IdPlaceholder(index) => q"${args(index)}"
    }

    def goP(pred: IRs.PredicateIR, args: Seq[c.Expr[Any]]): c.Tree =
      pred match {
        case IRs.Pred(name)             => q"$name"
        case IRs.PredPlaceholder(index) => q"${args(index)}"
      }

    def goG(fun: IRs.FunctionIR, args: Seq[c.Expr[Any]]): c.Tree = fun match {
      case IRs.Fun(name)             => q"$name"
      case IRs.FunPlaceholder(index) => q"${args(index)}"
    }

    def goF(formula: IRs.FormulaIR, args: Seq[c.Expr[Any]]): c.Tree =
      formula match {
        case IRs.UnaryApp(IRs.Not, inner) =>
          q"_root_.fol.Not(${goF(inner, args)})"
        case IRs.BinaryApp(IRs.And, left, right) =>
          q"_root_.fol.And(${goF(left, args)}, ${goF(right, args)})"
        case IRs.BinaryApp(IRs.Or, left, right) =>
          q"_root_.fol.Or(${goF(left, args)}, ${goF(right, args)})"
        case IRs.BinaryApp(IRs.Implies, left, right) =>
          q"_root_.fol.Implies(${goF(left, args)}, ${goF(right, args)})"
        case IRs.BinaryApp(IRs.Iff, left, right) =>
          q"_root_.fol.Iff(${goF(left, args)}, ${goF(right, args)})"
        case IRs.BoolLiteral(true)  => q"_root_.fol.True"
        case IRs.BoolLiteral(false) => q"_root_.fol.False"
        case IRs.PredicateApp(pred, predArgs, None) =>
          q"_root_.fol.PredApp(${goP(pred, args)}, _root_.scala.collection.Seq(..${predArgs
            .map(goE(_, args))}))"
        case IRs.PredicateApp(pred, predArgs, Some(index)) =>
          q"_root_.fol.PredApp(${goP(pred, args)}, _root_.scala.collection.Seq(..${predArgs
            .map(goE(_, args))}) ++ ${args(index)})"
        case IRs.Equals(left, right) =>
          q"_root_.fol.Equals(${goE(left, args)}, ${goE(right, args)})"
        case IRs.Quantified(IRs.Forall, id, inner) =>
          q"_root_.fol.Forall(${goI(id, args)}, ${goF(inner, args)})"
        case IRs.Quantified(IRs.Exists, id, inner) =>
          q"_root_.fol.Exists(${goI(id, args)}, ${goF(inner, args)})"
        case IRs.FormulaPlaceholder(index) => q"${args(index)}"
      }
  }

  object unapply {

    def goC(con: IRs.ConstantIR, names: Seq[TermName]): c.Tree = con match {
      case IRs.Con(name)             => pq"$name"
      case IRs.ConPlaceholder(index) => pq"${names(index)}"
    }

    def goE(expr: IRs.ExprIR, names: Seq[TermName]): c.Tree = expr match {
      case IRs.ConVal(con) => pq"_root_.fol.Con(${goC(con, names)})"
      case IRs.Var(id)     => pq"_root_.fol.Var($id)"
      case IRs.FunctionApp(function, args, None) =>
        pq"_root_.fol.FunApp(${goG(function, names)}, _root_.scala.collection.Seq(..${args
          .map(goE(_, names))}))"
      case IRs.FunctionApp(function, args, Some(index)) =>
        pq"_root_.fol.FunApp(${goG(function, names)}, _root_.scala.collection.Seq(..${args
          .map(goE(_, names))}, ${names(index)} @ _*))"
      case IRs.ExprPlaceholder(index) => pq"${names(index)}"
    }

    def goI(id: IRs.IdentifierIR, names: Seq[TermName]): c.Tree = id match {
      case IRs.Id(name)             => pq"$name"
      case IRs.IdPlaceholder(index) => pq"${names(index)}"
    }

    def goP(pred: IRs.PredicateIR, names: Seq[TermName]): c.Tree = pred match {
      case IRs.Pred(name)             => pq"$name"
      case IRs.PredPlaceholder(index) => pq"${names(index)}"
    }

    def goG(fun: IRs.FunctionIR, names: Seq[TermName]): c.Tree = fun match {
      case IRs.Fun(name)             => pq"$name"
      case IRs.FunPlaceholder(index) => pq"${names(index)}"
    }

    def goF(formula: IRs.FormulaIR, names: Seq[TermName]): c.Tree =
      formula match {
        case IRs.UnaryApp(IRs.Not, inner) =>
          pq"_root_.fol.Not(${goF(inner, names)})"
        case IRs.BinaryApp(IRs.And, left, right) =>
          pq"_root_.fol.And(${goF(left, names)}, ${goF(right, names)})"
        case IRs.BinaryApp(IRs.Or, left, right) =>
          pq"_root_.fol.Or(${goF(left, names)}, ${goF(right, names)})"
        case IRs.BinaryApp(IRs.Implies, left, right) =>
          pq"_root_.fol.Implies(${goF(left, names)}, ${goF(right, names)})"
        case IRs.BinaryApp(IRs.Iff, left, right) =>
          pq"_root_.fol.Iff(${goF(left, names)}, ${goF(right, names)})"
        case IRs.BoolLiteral(true)  => pq"_root_.fol.True"
        case IRs.BoolLiteral(false) => pq"_root_.fol.False"
        case IRs.PredicateApp(pred, args, None) =>
          pq"_root_.fol.PredApp(${goP(pred, names)}, _root_.scala.collection.Seq(..${args
            .map(goE(_, names))}))"
        case IRs.PredicateApp(pred, args, Some(index)) =>
          pq"_root_.fol.PredApp(${goP(pred, names)}, _root_.scala.collection.Seq(..${args
            .map(goE(_, names))}, ${names(index)} @ _*))"
        case IRs.Equals(left, right) =>
          pq"_root_.fol.Equals(${goE(left, names)}, ${goE(right, names)})"
        case IRs.Quantified(IRs.Forall, id, inner) =>
          pq"_root_.fol.Forall(${goI(id, names)}, ${goF(inner, names)})"
        case IRs.Quantified(IRs.Exists, id, inner) =>
          pq"_root_.fol.Exists(${goI(id, names)}, ${goF(inner, names)})"
        case IRs.FormulaPlaceholder(index) => pq"${names(index)}"
      }
  }

  def fol_apply(args: c.Expr[Any]*): c.Tree = {

    q"${apply.goF(formulaIr, args)}"
  }

  def fol_unapply(arg: c.Tree): c.Tree = {

    val names = Seq.fill(parts.length - 1)(TermName(c.freshName()))

    if (parts.length >= 2) {

      q"""
        new {
          def unapply(f: _root_.fol.Formula) = f match {
            case ${unapply.goF(formulaIr, names)} => _root_.scala.Some((..$names))
            case _ => _root_.scala.None
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          def unapplySeq(f: _root_.fol.Formula) = f match {
            case ${unapply.goF(formulaIr, names)} => _root_.scala.Some(_root_.scala.collection.Seq[_root_.scala.Nothing]())
            case _ => _root_.scala.None
          }
        }.unapplySeq($arg)
      """
    }
  }

  def expr_apply(args: c.Expr[Any]*): c.Tree = {

    q"${apply.goE(exprIr, args)}"
  }

  def expr_unapply(arg: c.Tree): c.Tree = {

    val names = Seq.fill(parts.length - 1)(TermName(c.freshName()))

    if (parts.length >= 2) {

      q"""
        new {
          def unapply(f: _root_.fol.Expr) = f match {
            case ${unapply.goE(exprIr, names)} => _root_.scala.Some((..$names))
            case _ => _root_.scala.None
          }
        }.unapply($arg)
      """
    } else {
      q"""
        new {
          def unapplySeq(f: _root_.fol.Expr) = f match {
            case ${unapply.goE(exprIr, names)} => _root_.scala.Some(_root_.scala.collection.Seq[_root_.scala.Nothing]())
            case _ => _root_.scala.None
          }
        }.unapplySeq($arg)
      """
    }
  }
}

package fol

import Utils._

/** Expressions. */
sealed abstract class Expr {

  lazy val pretty: String = {
    val ir = parser.Converter.toIR(this)
    val it = parser.Parsers.expr.unapply(ir)

    if (it.hasNext) {
      parser.Lexer.unapply(it.next)
    } else {
      throw new Exception("No representation for such expression.")
    }
  }

  /** Free identifiers of `this` expression. */
  lazy val free: Set[Identifier] = this match {
    case Con(_)  => Set.empty
    case Var(id) => Set(id)
    case FunApp(_, args) =>
      args.foldLeft(Set.empty[Identifier]) {
        case (acc, arg) => acc union arg.free
      }
  }

  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////

  /** Identifiers of `this` expression. */
  lazy val ids: Set[Identifier] = this match {
    case Con(id) => Set(id)
    case Var(id) => Set(id)
    case FunApp(id, args) =>
      args.foldLeft(Set(id)) {
        case (acc, arg) => acc union arg.ids
      }
  }
}

/** Constant expression. */
case class Con(constant: Constant) extends Expr

/** Variable. */
case class Var(id: Identifier) extends Expr

/** Function application. */
case class FunApp(function: Function, args: Seq[Expr]) extends Expr

object Expr {
  def random(
      functions: Array[Function],
      constants: Array[Constant],
      ids: Array[Identifier]
  ): Expr = {
    val r = util.Random.nextInt(100)
    if (r <= 40) Var(randomElem(ids))
    else if (r <= 80) Con(randomElem(constants))
    else
      FunApp(
        randomElem(functions),
        (1 to util.Random.nextInt(3))
          .map(i => random(functions, constants, ids))
      )
  }
}

/** First-order logic formula. */
sealed abstract class Formula {

  lazy val pretty: String = {
    val ir = parser.Converter.toIR(this)
    val it = parser.Parsers.formula.unapply(ir)

    if (it.hasNext) {
      parser.Lexer.unapply(it.next)
    } else {
      throw new Exception("No representation for such formula.")
    }
  }

  /** Free identifiers of `this` formula. */
  lazy val free: Set[Identifier] = this match {
    case True              => Set.empty
    case False             => Set.empty
    case Not(inner)        => inner.free
    case And(lhs, rhs)     => lhs.free union rhs.free
    case Or(lhs, rhs)      => lhs.free union rhs.free
    case Implies(lhs, rhs) => lhs.free union rhs.free
    case Iff(lhs, rhs)     => lhs.free union rhs.free
    case Forall(id, inner) => inner.free - id
    case Exists(id, inner) => inner.free - id
    case Equals(lhs, rhs)  => lhs.free union rhs.free
    case PredApp(_, args) =>
      args.foldLeft(Set.empty[Identifier]) {
        case (acc, arg) => acc union arg.free
      }
  }

  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////

  /** Identifiers of `this` formula. */
  lazy val ids: Set[Identifier] = this match {
    case True              => Set.empty
    case False             => Set.empty
    case Not(inner)        => inner.ids
    case And(lhs, rhs)     => lhs.ids union rhs.ids
    case Or(lhs, rhs)      => lhs.ids union rhs.ids
    case Implies(lhs, rhs) => lhs.ids union rhs.ids
    case Iff(lhs, rhs)     => lhs.ids union rhs.ids
    case Forall(id, inner) => inner.ids
    case Exists(id, inner) => inner.ids
    case Equals(lhs, rhs)  => lhs.ids union rhs.ids
    case PredApp(id, args) =>
      args.foldLeft(Set(id)) {
        case (acc, arg) => acc union arg.ids
      }
  }
}

/** Literal true. */
case object True extends Formula

/** Literal false. */
case object False extends Formula

/** Negation. */
case class Not(inner: Formula) extends Formula

/** Conjunction. */
case class And(lhs: Formula, rhs: Formula) extends Formula

/** Disjunction. */
case class Or(lhs: Formula, rhs: Formula) extends Formula

/** Implication. */
case class Implies(lhs: Formula, rhs: Formula) extends Formula

/** Equivalence. */
case class Iff(lhs: Formula, rhs: Formula) extends Formula

/** Universal quantification. */
case class Forall(id: Identifier, inner: Formula) extends Formula

/** Existential quantification. */
case class Exists(id: Identifier, inner: Formula) extends Formula

/** Equality between expressions. */
case class Equals(lhs: Expr, rhs: Expr) extends Formula

/** Predicate application. */
case class PredApp(predicate: Predicate, args: Seq[Expr]) extends Formula

object Formula {
  def random(
      preds: Array[Predicate],
      functions: Array[Function],
      constants: Array[Constant],
      ids: Array[Identifier]
  ): Formula = {
    val r = util.Random.nextInt(100)
    if (r <= 15) True
    else if (r <= 30) False
    else if (r <= 45)
      PredApp(
        randomElem(preds),
        (1 to util.Random.nextInt(3))
          .map(_ => Expr.random(functions, constants, ids))
      )
    else if (r <= 60)
      Equals(
        Expr.random(functions, constants, ids),
        Expr.random(functions, constants, ids)
      )
    else if (r <= 66)
      And(
        random(preds, functions, constants, ids),
        random(preds, functions, constants, ids)
      )
    else if (r <= 72)
      Or(
        random(preds, functions, constants, ids),
        random(preds, functions, constants, ids)
      )
    else if (r <= 78)
      Implies(
        random(preds, functions, constants, ids),
        random(preds, functions, constants, ids)
      )
    else if (r <= 83)
      Iff(
        random(preds, functions, constants, ids),
        random(preds, functions, constants, ids)
      )
    else if (r <= 89)
      Forall(randomElem(ids), random(preds, functions, constants, ids))
    else if (r <= 94)
      Exists(randomElem(ids), random(preds, functions, constants, ids))
    else Not(random(preds, functions, constants, ids))
  }
}

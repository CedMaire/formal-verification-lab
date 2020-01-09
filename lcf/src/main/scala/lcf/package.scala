
import fol._

/** Minimal proof system for first-order logic.
  *
  * Heavily inspired by John Harrison's implementation in OCaml:
  * https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/lcf.ml
  */
package object lcf {

  /** Theorem. Always contains a provable formula.
    *
    * The constructor of the class is private so that the only way to
    * obtain a theorem is to use the provided axioms and combinators.
    */
  final class Theorem private(val formula: Formula) {

    override def equals(that: Any): Boolean = {
      that.isInstanceOf[Theorem] && that.asInstanceOf[Theorem].formula == formula
    }

    override def toString: String = formula.toString

    def pretty: String = "⊢ " + formula.pretty

    /** Try to apply `this` theorem to another theorem.
      *
      * The exact meaning of the operation depends on the formula
      * contained in `this` theorem, but is always a flavour of `modusPonens`.
      */
    def apply(that: Theorem): Theorem = this.formula match {
      case Implies(_, _) => modusPonens(this, that)
      case Iff(lhs, rhs) if rhs == that.formula =>
        modusPonens(modusPonens(iffToImplies2(lhs, rhs), this), that)
      case Iff(lhs, rhs) =>
        modusPonens(modusPonens(iffToImplies1(lhs, rhs), this), that)
      case Forall(identifier, Implies(lhs, rhs)) =>
        modusPonens(modusPonens(forallImplies(identifier, lhs, rhs), this), that)
      case _ => throw new IllegalArgumentException("Invalid application.")
    }
  }

  /** Private factory of theorems, crucially only available internally to this object. */
  private object Theorem {
    def apply(formula: Formula): Theorem = new Theorem(formula)
  }

  // Rules.

  /** Modus ponens rule.
    *
    * Given a theorem of `P => Q`, and a theorem of `P`, produces a theorem of `Q`.
    */
  def modusPonens(pq: Theorem, p: Theorem): Theorem = pq.formula match {
    case Implies(pf, qf) if p.formula == pf => Theorem(qf)
    case _ => throw new IllegalArgumentException("Illegal application of modusPonens.")
  }

  /** Generalisation.
    *
    * Given a theorem of `P` and an identifier `x`, produces a theorem of `forall x. P`.
    */
  def generalize(p: Theorem, x: Identifier): Theorem = {
    Theorem(Forall(x, p.formula))
  }

  // Axioms schemas.

  /** Axiom `P => Q => P`. */
  def addImplies(p: Formula, q: Formula): Theorem =
    Theorem(Implies(p, Implies(q, p)))

  /** Axiom `(P => Q => R) => (P => Q) => P => R`. */
  def impliesDistr(p: Formula, q: Formula, r: Formula): Theorem =
    Theorem(Implies(Implies(p, Implies(q, r)), Implies(Implies(p, q), Implies(p, r))))

  /** Axiom `((P => False) => False) => P` */
  def doubleNegation(p: Formula): Theorem =
    Theorem(Implies(Implies(Implies(p, False), False), p))

  /** Axiom `(forall x. P => Q) => (forall x. P) => forall x. Q`. */
  def forallImplies(x: Identifier, p: Formula, q: Formula): Theorem =
    Theorem(Implies(Forall(x, Implies(p, q)), Implies(Forall(x, p), Forall(x, q))))

  /** Axiom `P => forall x. P`, given that x is not free in P. */
  def forallIntro(x: Identifier, p: Formula): Theorem = {
    if (p.free.contains(x)) {
      throw new IllegalArgumentException(
        "Illegal application of forallIntro: identifier is free in the formula.")
    }

    Theorem(Implies(p, Forall(x, p)))
  }

  /** Axiom `exists x. x = e`, given that x is not free in e. */
  def existsEquals(x: Identifier, e: Expr): Theorem = {
    if (e.free.contains(x)) {
      throw new IllegalArgumentException(
        "Illegal application of existsEquals: identifier is free in the expression.")
    }

    Theorem(Exists(x, Equals(Var(x), e)))
  }

  /** Axiom `e = e`. */
  def refl(e: Expr): Theorem =
    Theorem(Equals(e, e))

  /** Axiom `a1 = b1 => ... => an = bn => f(a1, ..., an) = f(b1, ..., bn)`. */
  def funCongruence(f: Function, as: Seq[Expr], bs: Seq[Expr]): Theorem = {
    if (as.length != bs.length) {
      throw new IllegalArgumentException(
        "Illegal application of funCongruence: Sequences do not have matching lengths.")
    }

    val base: Formula = Equals(FunApp(f, as), FunApp(f, bs))

    val formula: Formula = as.zip(bs).foldRight(base) {
      case ((a, b), acc) => Implies(Equals(a, b), acc)
    }

    Theorem(formula)
  }

  /** Axiom `a1 = b1 => ... => an = bn => P(a1, ..., an) => P(b1, ..., bn)`. */
  def predCongruence(p: Predicate, as: Seq[Expr], bs: Seq[Expr]): Theorem = {
    if (as.length != bs.length) {
      throw new IllegalArgumentException(
        "Illegal application of predCongruence: Sequences do not have matching lengths.")
    }

    val base: Formula = Implies(PredApp(p, as), PredApp(p, bs))

    val formula: Formula = as.zip(bs).foldRight(base) {
      case ((a, b), acc) => Implies(Equals(a, b), acc)
    }

    Theorem(formula)
  }

  /** Axiom `a1 = b1 => a2 = b2 => a1 = a2 => b1 = b2`. */
  def equCongruence(a1: Expr, a2: Expr, b1: Expr, b2: Expr): Theorem = {
    Theorem(Implies(Equals(a1, b1), Implies(Equals(a2, b2), Implies(Equals(a1, a2), Equals(b1, b2)))))
  }

  /** Axiom `(p => q) => (q => p) => (p <=> q)`. */
  def impliesToIff(p: Formula, q: Formula): Theorem =
    Theorem(Implies(Implies(p, q), Implies(Implies(q, p), Iff(p, q))))

  /** Axiom `(p <=> q) => p => q`. */
  def iffToImplies1(p: Formula, q: Formula): Theorem =
    Theorem(Implies(Iff(p, q), Implies(p, q)))

  /** Axiom `(p <=> q) => q => p`. */
  def iffToImplies2(p: Formula, q: Formula): Theorem =
    Theorem(Implies(Iff(p, q), Implies(q, p)))

  /** Axiom `True <=> (False => False)`. */
  val trueIff: Theorem =
    Theorem(Iff(True, Implies(False, False)))

  /** Axiom `¬p <=> (p => False)`. */
  def notIff(p: Formula): Theorem =
    Theorem(Iff(Not(p), Implies(p, False)))

  /** Axiom `p /\ q <=> ((p => q => false) => false)`. */
  def andIff(p: Formula, q: Formula): Theorem =
    Theorem(Iff(And(p, q), Implies(Implies(p, Implies(q, False)), False)))

  /** Axiom `p \/ q <=> ¬(¬p /\ ¬q)`. */
  def orIff(lhs: Formula, rhs: Formula): Theorem =
    Theorem(Iff(Or(lhs, rhs), Not(And(Not(lhs), Not(rhs)))))

  /** Axiom `(exists x. P) <=> ¬(forall x. ¬P)`. */
  def existsIff(x: Identifier, p: Formula): Theorem =
    Theorem(Iff(Exists(x, p), Not(Forall(x, Not(p)))))

  /** Axiom `p => q <=> (~p \/ q)`. */
  def orImpliesIff(p: Formula, q: Formula): Theorem =
    Theorem(Iff(Implies(p,q), Or(Not(p), q)))
  

  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////

  /**
    * These might not always be axioms but we don't know how far to go for the lab.
    */
  /** Axiom `(p => q) <=> (¬p \/ q)`. */
  def impliesDef(p: Formula, q: Formula): Theorem =
    Theorem(Iff(Implies(p, q), Or(Not(p), q)))

  /** Axiom `(p \/ (q /\ r)) <=> ((p \/ q) /\ (p \/ r))`. */
  def orDistriAnd(p: Formula, q: Formula, r: Formula): Theorem =
    Theorem(Iff(Or(p, And(q, r)), And(Or(p, q), Or(p, r))))

  /** Axiom `(p /\ (q \/ r)) <=> ((p /\ q) \/ (p /\ r))`. */
  def andDistriOr(p: Formula, q: Formula, r: Formula): Theorem =
    Theorem(Iff(And(p, Or(q, r)), Or(And(p, q), And(p, r))))

  /** Axiom `P <=> forall x. P`, given that x is not an identifier in P. */
  def forallIffPNF(x: Identifier, p: Formula): Theorem = {
    if (p.ids.contains(x)) {
      throw new IllegalArgumentException(
        "Illegal application of forallIffPNF: identifier is in the formula."
      )
    }

    Theorem(Iff(p, Forall(x, p)))
  }

  /** Axiom `P <=> exists x. P`, given that x is not an identifier in P. */
  def existsIffPNF(x: Identifier, p: Formula): Theorem = {
    if (p.ids.contains(x)) {
      throw new IllegalArgumentException(
        "Illegal application of existsIffPNF: identifier is in the formula."
      )
    }

    Theorem(Iff(p, Exists(x, p)))
  }

  /** Axiom `forall x. (P /\ Q) <=> (forall x. P /\ forall x. Q)`. */
  def forallDistriAnd(x: Identifier, p: Formula, q: Formula): Theorem =
    Theorem(Iff(Forall(x, And(p, q)), And(Forall(x, p), Forall(x, q))))

  /** Axiom `exists x. (P /\ Q) <=> (exists x. P /\ exists x. Q)`, given that x is not an identifier in both P and Q. */
  def existsDistriAnd(x: Identifier, p: Formula, q: Formula): Theorem = {
    if (p.ids.contains(x) && q.ids.contains(x)) {
      throw new IllegalArgumentException(
        "Illegal application of existsDistriAnd: identifier is in both formulae P and Q."
      )
    }

    Theorem(Iff(Exists(x, And(p, q)), And(Exists(x, p), Exists(x, q))))
  }

  /** Axiom `forall x. (P \/ Q) <=> (forall x. P \/ forall x. Q)`, given that x is not an identifier in both P and Q. */
  def forallDistriOr(x: Identifier, p: Formula, q: Formula): Theorem = {
    if (p.ids.contains(x) && q.ids.contains(x)) {
      throw new IllegalArgumentException(
        "Illegal application of forallDistriOr: identifier is in both formulae P and Q."
      )
    }

    Theorem(Iff(Forall(x, Or(p, q)), Or(Forall(x, p), Forall(x, q))))
  }

  /** Axiom `exists x. (P \/ Q) <=> (exists x. P \/ exists x. Q)`. */
  def existsDistriOr(x: Identifier, p: Formula, q: Formula): Theorem =
    Theorem(Iff(Exists(x, Or(p, q)), Or(Exists(x, p), Exists(x, q))))

  /** ONLY USED FOR TESTING PURPOSES */
  def unsafeTheorem(formula: Formula): Theorem = Theorem(formula)
}


import fol._
import lcf._
import Theorems._

object NF {

  /** Checks that a formula only contains implications, equalities, predicates,
    * False, and forall quantifiers.
    */
  def isNormalForm(formula: Formula): Boolean = formula match {
    case True => false
    // ALLOWED
    case False         => true
    case Not(inner)    => false
    case And(lhs, rhs) => false
    case Or(lhs, rhs)  => false
    // ALLOWED
    case Implies(lhs, rhs) => isNormalForm(lhs) && isNormalForm(rhs)
    case Iff(lhs, rhs)     => false
    // ALLOWED
    case Forall(id, inner) => isNormalForm(inner)
    case Exists(id, inner) => false
    // ALLOWED
    case Equals(lhs, rhs) => true
    // ALLOWED
    case PredApp(predicate, args) => true
    case _                        => throw new Exception("unwanted case in isNormalForm")
  }

  /** Converts a formula to an equivalent formula in normal form. */
  def toNormalForm(formula: Formula): Formula = {
    var changed: Boolean = false
    var finalForm: Formula = formula

    def change(formula: Formula): Formula = formula match {
      case True => {
        changed = true
        Implies(False, False)
      }
      // ALLOWED
      case False => False
      case Not(inner) => {
        changed = true
        Implies(toNormalForm(inner), False)
      }
      case And(lhs, rhs) => {
        changed = true
        Implies(
          Implies(toNormalForm(lhs), Implies(toNormalForm(rhs), False)),
          False
        )
      }
      case Or(lhs, rhs) => {
        changed = true
        Not(And(Not(toNormalForm(lhs)), Not(toNormalForm(rhs))))
      }
      // ALLOWED
      case Implies(lhs, rhs) => Implies(toNormalForm(lhs), toNormalForm(rhs))
      case Iff(lhs, rhs) => {
        changed = true
        And(
          Implies(toNormalForm(lhs), toNormalForm(rhs)),
          Implies(toNormalForm(rhs), toNormalForm(lhs))
        )
      }
      // ALLOWED
      case Forall(id, inner) => Forall(id, toNormalForm(inner))
      case Exists(id, inner) => {
        changed = true
        Not(Forall(id, Not(toNormalForm(inner))))
      }
      // ALLOWED
      case Equals(lhs, rhs) => Equals(lhs, rhs)
      // ALLOWED
      case PredApp(predicate, args) => PredApp(predicate, args)
      case _                        => throw new Exception("unwanted case in toNormalForm")
    }

    do {
      changed = false
      finalForm = change(finalForm)
    } while (changed)

    finalForm
  }

  // Lemma `¬p <=> (pn => False)` when given a theorem `p <=> pn`.
  def lemmaNot(ppn: Theorem): Theorem = ppn.formula match {
    case fol"$p <=> $pn" =>
      impliesIff(
        impliesTrans(contraposition(iffImplies2(ppn)), iffImplies1(notIff(pn))),
        impliesTrans(iffImplies2(notIff(pn)), contraposition(iffImplies1(ppn)))
      )
    case _ => throw new IllegalArgumentException("illegal form in lemmaNot")
  }

  // Lemma `p /\ q <=> ((pn => qn => false) => false)` when given theorems `p <=> pn` and `q <=> qn`.
  def lemmaAnd(ppn: Theorem, qqn: Theorem): Theorem =
    (ppn.formula, qqn.formula) match {
      case (fol"$p <=> $pn", fol"$q <=> $qn") =>
        iffTrans(
          andIff(p, q),
          lemmaImplies(
            lemmaImplies(ppn, lemmaImplies(qqn, iffRefl(False))),
            iffRefl(False)
          )
        )
      case _ => throw new IllegalArgumentException("illegal form in lemmaAnd")
    }

  // Lemma `p \/ q <=> (((pn => false) => (qn => false) => false) => false) => false` when given
  // theorems `p <=> pn` and `q <=> qn`.
  def lemmaOr(ppn: Theorem, qqn: Theorem): Theorem =
    (ppn.formula, qqn.formula) match {
      case (fol"$p <=> $pn", fol"$q <=> $qn") =>
        iffTrans(
          iffTrans(
            iffTrans(orIff(p, q), notIff(fol"¬$p /\ ¬$q")),
            lemmaImplies(andIff(Not(p), Not(q)), iffRefl(False))
          ),
          lemmaImplies(
            lemmaImplies(
              lemmaImplies(
                lemmaNot(ppn),
                lemmaImplies(lemmaNot(qqn), iffRefl(False))
              ),
              iffRefl(False)
            ),
            iffRefl(False)
          )
        )
      case _ => throw new IllegalArgumentException("illegal form in lemmaOr")
    }

  // Lemma `(p => q) <=> (pn => qn)` when given theorems `p <=> pn` and `q <=> qn`.
  def lemmaImplies(ppn: Theorem, qqn: Theorem): Theorem =
    (ppn.formula, qqn.formula) match {
      case (fol"$p <=> $pn", fol"$q <=> $qn") =>
        impliesIff(
          impliesMonoThm(p, pn, q, qn)(iffImplies2(ppn))(iffImplies1(qqn)),
          impliesMonoThm(pn, p, qn, q)(iffImplies1(ppn))(iffImplies2(qqn))
        )
      case _ =>
        throw new IllegalArgumentException("illegal form in lemmaImplies")
    }

  // Lemma `(p <=> q) <=> ((pn => qn) => (qn => pn) => false) => false` when given theorems `p <=> pn` and `q <=> qn`.
  def lemmaIff(ppn: Theorem, qqn: Theorem): Theorem =
    (ppn.formula, qqn.formula) match {
      case (fol"$p <=> $pn", fol"$q <=> $qn") =>
        iffTrans(
          iffIff(p, q),
          lemmaAnd(lemmaImplies(ppn, qqn), lemmaImplies(qqn, ppn))
        )
      case _ => throw new IllegalArgumentException("illegal form in lemmaIff")
    }

  // Lemma `(forall x. p) <=> (forall x. pn)` when given theorem `p <=> pn`.
  def lemmaForall(id: Identifier, ppn: Theorem): Theorem = ppn.formula match {
    case fol"$p <=> $pn" =>
      impliesIff(
        forallImplies(id, p, pn)(generalize(iffImplies1(ppn), id)),
        forallImplies(id, pn, p)(generalize(iffImplies2(ppn), id))
      )
    case _ => throw new IllegalArgumentException("illegal form in lemmaForall")
  }

  // Lemma `(exists x. p) <=> (forall x. pn => false) => false` when given theorem `p <=> pn`.
  def lemmaExists(id: Identifier, ppn: Theorem): Theorem = ppn.formula match {
    case fol"$p <=> $pn" => {
      iffTrans(
        iffTrans(
          existsIff(id, p),
          lemmaNot(
            lemmaForall(
              id,
              impliesIff(
                contraposition(iffImplies2(ppn)),
                contraposition(iffImplies1(ppn))
              )
            )
          )
        ),
        lemmaImplies(lemmaForall(id, notIff(pn)), iffRefl(False))
      )
    }
    case _ => throw new IllegalArgumentException("illegal form in lemmaExists")
  }

  // Lemma `(e0 = e1 <=> en0 = en1` when given theorems `e0 = en0` and `e1 = en1`.
  def lemmaEquals(e0en0: Theorem, e1en1: Theorem): Theorem =
    (e0en0.formula, e1en1.formula) match {
      case (fol"$e0 = $en0", fol"$e1 = $en1") =>
        impliesIff(
          equCongruence(e0, e1, en0, en1)(e0en0)(e1en1),
          equCongruence(en0, en1, e0, e1)(
            equCongruence(e0, e0, en0, e0)(e0en0)(refl(e0))(refl(e0))
          )(
            equCongruence(e1, e1, en1, e1)(e1en1)(refl(e1))(refl(e1))
          )
        )
      case _ =>
        throw new IllegalArgumentException("illegal form in lemmaEquals")
    }

  // Lemma `P(e0, e1, ..., en) <=> P(en0, en1, ..., enn)` when given theorems `ei = eni` for all i and a predicate.
  def lemmaPredApp(predicate: Predicate, eieni: Seq[Theorem]): Theorem = {
    if (!eieni.forall(
          t =>
            t.formula match {
              case fol"$e0 = $en0" => true
              case default         => false
            }
        )) {
      throw new IllegalArgumentException("illegal form in lemmaPredApp")
    }

    var finalTheoremRight: Theorem = predCongruence(
      predicate,
      eieni.map(
        t =>
          t.formula match {
            case fol"$e0 = $en0" => e0
            case default =>
              throw new IllegalArgumentException(
                "illegal form in lemmaPredApp"
              )
          }
      ),
      eieni.map(
        t =>
          t.formula match {
            case fol"$e0 = $en0" => en0
            case default =>
              throw new IllegalArgumentException(
                "illegal form in lemmaPredApp"
              )
          }
      )
    )

    eieni.foreach(t => {
      finalTheoremRight = finalTheoremRight(t)
    })

    val eniei = eieni.map(
      t =>
        t.formula match {
          case fol"$e0 = $en0" =>
            equCongruence(e0, e0, en0, e0)(t)(refl(e0))(refl(e0))
          case default =>
            throw new IllegalArgumentException("illegal form in lemmaPredApp")
        }
    )

    var finalTheoremLeft: Theorem = predCongruence(
      predicate,
      eniei.map(
        t =>
          t.formula match {
            case fol"$en0 = $e0" => en0
            case default =>
              throw new IllegalArgumentException(
                "illegal form in lemmaPredApp"
              )
          }
      ),
      eniei.map(
        t =>
          t.formula match {
            case fol"$en0 = $e0" => e0
            case default =>
              throw new IllegalArgumentException(
                "illegal form in lemmaPredApp"
              )
          }
      )
    )

    eniei.foreach(t => {
      finalTheoremLeft = finalTheoremLeft(t)
    })

    impliesIff(finalTheoremRight, finalTheoremLeft)
  }

  /** Given a `formula`, generate a theorem for the equivalence with its normal form:
    *   formula <=> toNormalForm(formula)
    */
  def toNormalFormThm(formula: Formula): Theorem = formula match {
    case True => trueIff
    // ALLOWED
    case False         => iffRefl(False)
    case Not(inner)    => lemmaNot(toNormalFormThm(inner))
    case And(lhs, rhs) => lemmaAnd(toNormalFormThm(lhs), toNormalFormThm(rhs))
    case Or(lhs, rhs)  => lemmaOr(toNormalFormThm(lhs), toNormalFormThm(rhs))
    // ALLOWED
    case Implies(lhs, rhs) =>
      lemmaImplies(toNormalFormThm(lhs), toNormalFormThm(rhs))
    case Iff(lhs, rhs) => lemmaIff(toNormalFormThm(lhs), toNormalFormThm(rhs))
    // ALLOWED
    case Forall(id, inner) => lemmaForall(id, toNormalFormThm(inner))
    case Exists(id, inner) => lemmaExists(id, toNormalFormThm(inner))
    // ALLOWED
    case Equals(lhs, rhs) => iffRefl(Equals(lhs, rhs))
    // ALLOWED
    case PredApp(predicate, args) => iffRefl(PredApp(predicate, args))
    case _                        => throw new Exception("unwanted case in toNormalFormThm")
  }
}

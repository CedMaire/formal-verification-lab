import NF._
import NNF._
import fol._
import lcf._
import Theorems._

object PNF {

  val FOR_ALL: String = "a"
  val EXISTS: String = "e"

  /*
    Tests wether the given `formula` is in prenex normal form.
   */
  def isPNF(formula: Formula): Boolean = {
    def check(formula: Formula, quantifierAllowed: Boolean): Boolean =
      formula match {
        case True              => true
        case False             => true
        case Not(inner)        => check(inner, false)
        case And(lhs, rhs)     => check(lhs, false) && check(rhs, false)
        case Or(lhs, rhs)      => check(lhs, false) && check(rhs, false)
        case Implies(lhs, rhs) => check(lhs, false) && check(rhs, false)
        case Iff(lhs, rhs)     => check(lhs, false) && check(rhs, false)
        case Forall(id, inner) =>
          quantifierAllowed match {
            case true  => check(inner, true)
            case false => false
          }
        case Exists(id, inner) =>
          quantifierAllowed match {
            case true  => check(inner, true)
            case false => false
          }
        case Equals(lhs, rhs)         => true
        case PredApp(predicate, args) => true
        case _                        => throw new Exception("unwanted case in isPNF")
      }

    formula match {
      case Forall(id, inner) => check(inner, true)
      case Exists(id, inner) => check(inner, true)
      case _                 => check(formula, false)
    }
  }

  /*
    Makes any quantified variable in `formula` unique.
   */
  def uniqueVars(formula: Formula): Formula = {
    var counter_fa = -1
    var counter_e = -1

    def subst(formula: Formula, mapping: Map[Identifier, Identifier]): Formula =
      formula match {
        case True          => True
        case False         => False
        case Not(inner)    => Not(subst(inner, mapping))
        case And(lhs, rhs) => And(subst(lhs, mapping), subst(rhs, mapping))
        case Or(lhs, rhs)  => Or(subst(lhs, mapping), subst(rhs, mapping))
        case Implies(lhs, rhs) =>
          Implies(subst(lhs, mapping), subst(rhs, mapping))
        case Iff(lhs, rhs) => Iff(subst(lhs, mapping), subst(rhs, mapping))
        case Forall(id, inner) => {
          counter_fa += 1
          val newVar: Identifier = FOR_ALL + counter_fa

          Forall(newVar, subst(inner, mapping.+((id, newVar))))
        }
        case Exists(id, inner) => {
          counter_e += 1
          val newVar = EXISTS + counter_e

          Exists(newVar, subst(inner, mapping.+((id, newVar))))
        }
        case Equals(lhs, rhs) => {
          var lhs_new = lhs
          lhs match {
            case Var(id) => lhs_new = Var(mapping.getOrElse(id, id))
            case _       => Unit
          }

          var rhs_new = rhs
          rhs match {
            case Var(id) => rhs_new = Var(mapping.getOrElse(id, id))
            case _       => Unit
          }

          Equals(lhs_new, rhs_new)
        }
        case PredApp(predicate, args) =>
          PredApp(
            predicate,
            args.map(
              expression =>
                expression match {
                  case Var(id) => Var(mapping.getOrElse(id, id))
                  case default => default
                }
            )
          )
        case _ => throw new Exception("unwanted case in uniqueVars")
      }

    subst(formula, Map())
  }

  /*
    Transforms the given `formula` in prenex normal form.
   */
  def toPNF(formula: Formula): Formula = {
    if (!isNNF(formula)) {
      throw new Exception(
        "toPNF requires the formula to be in negation normal form"
      )
    }

    val formulaUV = uniqueVars(formula)

    var quantifiers: Seq[Pair[String, Identifier]] = Seq()
    def extractQuantifiers(formula: Formula): Formula = formula match {
      case True       => True
      case False      => False
      case Not(inner) => Not(extractQuantifiers(inner))
      case And(lhs, rhs) =>
        And(extractQuantifiers(lhs), extractQuantifiers(rhs))
      case Or(lhs, rhs) => Or(extractQuantifiers(lhs), extractQuantifiers(rhs))
      case Implies(lhs, rhs) =>
        Implies(extractQuantifiers(lhs), extractQuantifiers(rhs))
      case Iff(lhs, rhs) =>
        Iff(extractQuantifiers(lhs), extractQuantifiers(rhs))
      case Forall(id, inner) => {
        quantifiers = quantifiers.:+(FOR_ALL, id)

        extractQuantifiers(inner)
      }
      case Exists(id, inner) => {
        quantifiers = quantifiers.:+(EXISTS, id)

        extractQuantifiers(inner)
      }
      case Equals(lhs, rhs)         => Equals(lhs, rhs)
      case PredApp(predicate, args) => PredApp(predicate, args)
      case _                        => throw new Exception("unwanted case in toPNF:extractQuantifiers")
    }

    val formulaUVQF = extractQuantifiers(formulaUV)

    var formulaPNF: Formula = formulaUVQF
    quantifiers.reverse.foreach(
      pair =>
        pair._1 match {
          case FOR_ALL => formulaPNF = Forall(pair._2, formulaPNF)
          case EXISTS  => formulaPNF = Exists(pair._2, formulaPNF)
          case _       => throw new Exception("unwanted case in toPNF:foreach")
        }
    )

    formulaPNF
  }

  // Lemma `(p /\ q) <=> (pn /\ qn)` when given theorems `p <=> pn` and `q <=> qn`.
  def lemmaAndPNF(ppn: Theorem, qqn: Theorem): Theorem =
    (ppn.formula, qqn.formula) match {
      case (fol"$p <=> $pn", fol"$q <=> $qn") =>
        iffTrans(
          iffTrans(
            andIff(p, q),
            lemmaImplies(
              lemmaImplies(ppn, lemmaImplies(qqn, iffRefl(False))),
              iffRefl(False)
            )
          ),
          iffSym(andIff(pn, qn))
        )
      case _ =>
        throw new IllegalArgumentException("illegal form in lemmaAndPNF")
    }

  // Lemma `(forall x. (inner /\ rhs)) <=> ((forall x. inner) /\ rhs)` when given formula `(forall x. inner) /\ rhs`.
  // Given that x does not occur at all in rhs.
  def lemmaAndLeftForall(formula: Formula): Theorem = formula match {
    case And(lhs, rhs) =>
      lhs match {
        case Forall(id, inner) =>
          iffSym(
            iffTrans(
              lemmaAndPNF(iffRefl(lhs), forallIffPNF(id, rhs)),
              iffSym(forallDistriAnd(id, inner, rhs))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaAndLeftForall:lhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaAndLeftForall:And"
      )
  }

  // Lemma `exists x. (inner /\ rhs) <=> (exists x. inner) /\ rhs` when given formula `(exists x. inner) /\ rhs`.
  // Given that x does not occur at all in rhs.
  def lemmaAndLeftExists(formula: Formula): Theorem = formula match {
    case And(lhs, rhs) =>
      lhs match {
        case Exists(id, inner) =>
          iffSym(
            iffTrans(
              lemmaAndPNF(iffRefl(lhs), existsIffPNF(id, rhs)),
              iffSym(existsDistriAnd(id, inner, rhs))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaAndLeftExists:lhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaAndLeftExists:And"
      )
  }

  // Lemma `forall x. (lhs /\ inner) <=> lhs /\ (forall x. inner)` when given formula `lhs /\ (forall x. inner)`.
  // Given that x does not occur at all in lhs.
  def lemmaAndRightForall(formula: Formula): Theorem = formula match {
    case And(lhs, rhs) =>
      rhs match {
        case Forall(id, inner) =>
          iffSym(
            iffTrans(
              lemmaAndPNF(forallIffPNF(id, lhs), iffRefl(rhs)),
              iffSym(forallDistriAnd(id, lhs, inner))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaAndRightForall:rhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaAndRightForall:And"
      )
  }

  // Lemma `exists x. (lhs /\ inner) <=> lhs /\ (exists x. inner)` when given formula `lhs /\ (exists x. inner)`.
  // Given that x does not occur at all in lhs.
  def lemmaAndRightExists(formula: Formula): Theorem = formula match {
    case And(lhs, rhs) =>
      rhs match {
        case Exists(id, inner) =>
          iffSym(
            iffTrans(
              lemmaAndPNF(existsIffPNF(id, lhs), iffRefl(rhs)),
              iffSym(existsDistriAnd(id, lhs, inner))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaAndRightExists:rhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaAndRightExists:And"
      )
  }

  // Lemma `(p \/ q) <=> (pn \/ qn)` when given theorems `p <=> pn` and `q <=> qn`.
  def lemmaOrPNF(ppn: Theorem, qqn: Theorem): Theorem =
    (ppn.formula, qqn.formula) match {
      case (fol"$p <=> $pn", fol"$q <=> $qn") =>
        iffTrans(
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
          ),
          iffSym(
            iffTrans(
              iffTrans(
                iffTrans(orIff(pn, qn), notIff(fol"¬$pn /\ ¬$qn")),
                lemmaImplies(andIff(Not(pn), Not(qn)), iffRefl(False))
              ),
              lemmaImplies(
                lemmaImplies(
                  lemmaImplies(
                    notIff(pn),
                    lemmaImplies(notIff(qn), iffRefl(False))
                  ),
                  iffRefl(False)
                ),
                iffRefl(False)
              )
            )
          )
        )
      case _ =>
        throw new IllegalArgumentException("illegal form in lemmaOrPNF")
    }

  // Lemma `forall x. (inner \/ rhs) <=> (forall x. inner) \/ rhs` when given formula `(forall x. inner) \/ rhs`.
  // Given that x does not occur at all in rhs.
  def lemmaOrLeftForall(formula: Formula): Theorem = formula match {
    case Or(lhs, rhs) =>
      lhs match {
        case Forall(id, inner) =>
          iffSym(
            iffTrans(
              lemmaOrPNF(iffRefl(lhs), forallIffPNF(id, rhs)),
              iffSym(forallDistriOr(id, inner, rhs))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaOrLeftForall:lhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaOrLeftForall:Or"
      )
  }

  // Lemma `exists x. (inner \/ rhs) <=> (exists x. inner) \/ rhs` when given formula `(exists x. inner) \/ rhs`.
  // Given that x does not occur at all in rhs.
  def lemmaOrLeftExists(formula: Formula): Theorem = formula match {
    case Or(lhs, rhs) =>
      lhs match {
        case Exists(id, inner) =>
          iffSym(
            iffTrans(
              lemmaOrPNF(iffRefl(lhs), existsIffPNF(id, rhs)),
              iffSym(existsDistriOr(id, inner, rhs))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaOrLeftExists:lhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaOrLeftExists:Or"
      )
  }

  // Lemma `forall x. (lhs \/ inner) <=> lhs \/ (forall x. inner)` when given formula `lhs \/ (forall x. inner)`.
  // Given that x does not occur at all in lhs.
  def lemmaOrRightForall(formula: Formula): Theorem = formula match {
    case Or(lhs, rhs) =>
      rhs match {
        case Forall(id, inner) =>
          iffSym(
            iffTrans(
              lemmaOrPNF(forallIffPNF(id, lhs), iffRefl(rhs)),
              iffSym(forallDistriOr(id, lhs, inner))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaOrRightForall:rhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaOrRightForall:Or"
      )
  }

  // Lemma `exists x. (lhs \/ inner) <=> lhs \/ (exists x. inner)` when given formula `lhs \/ (exists x. inner)`.
  // Given that x does not occur at all in lhs.
  def lemmaOrRightExists(formula: Formula): Theorem = formula match {
    case Or(lhs, rhs) =>
      rhs match {
        case Exists(id, inner) =>
          iffSym(
            iffTrans(
              lemmaOrPNF(existsIffPNF(id, lhs), iffRefl(rhs)),
              iffSym(existsDistriOr(id, lhs, inner))
            )
          )
        case _ =>
          throw new IllegalArgumentException(
            "illegal form in lemmaOrRightExists:rhs"
          )
      }
    case _ =>
      throw new IllegalArgumentException(
        "illegal form in lemmaOrRightExists:Or"
      )
  }

  // Lemma `(forall x. p) <=> (forall x. pn)` when given theorem `p <=> pn`.
  def lemmaForallPNF(id: Identifier, ppn: Theorem): Theorem =
    ppn.formula match {
      case fol"$p <=> $pn" =>
        impliesIff(
          forallImplies(id, p, pn)(generalize(iffImplies1(ppn), id)),
          forallImplies(id, pn, p)(generalize(iffImplies2(ppn), id))
        )
      case _ =>
        throw new IllegalArgumentException("illegal form in lemmaForallPNF")
    }

  // Lemma `(exists x. p) <=> (exists x. pn)` when given theorem `p <=> pn`.
  def lemmaExistsPNF(id: Identifier, ppn: Theorem): Theorem =
    ppn.formula match {
      case fol"$p <=> $pn" =>
        iffTrans(
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
          ),
          iffSym(
            iffTrans(
              iffTrans(
                existsIff(id, pn),
                notIff(Forall(id, Not(pn)))
              ),
              lemmaImplies(lemmaForall(id, notIff(pn)), iffRefl(False))
            )
          )
        )
      case _ =>
        throw new IllegalArgumentException("illegal form in lemmaExistsPNF")
    }

  /** Given a `formula`, generate a theorem for the equivalence with a SINGLE step towards its prenex normal form:
    *   formula <=> toPNFSingleStep(formula)
    */
  def toPNFThmSingleStep(formula: Formula): (Theorem, Boolean) = {
    if (!isNNF(formula)) {
      throw new Exception(
        "toPNFThmSingleStep requires the formula to be in negation normal form"
      )
    }

    formula match {
      case True  => (trueIff, false)
      case False => (iffRefl(False), false)
      case Not(inner) =>
        inner match {
          case True                     => (iffRefl(Not(inner)), false)
          case False                    => (iffRefl(Not(inner)), false)
          case Equals(lhs, rhs)         => (iffRefl(Not(inner)), false)
          case PredApp(predicate, args) => (iffRefl(Not(inner)), false)
          case _ =>
            throw new Exception("incorrect not case in toPNFThmSingleStep")
        }
      case And(lhs, rhs) =>
        lhs match {
          case Forall(id, inner) => (lemmaAndLeftForall(And(lhs, rhs)), true)
          case Exists(id, inner) => (lemmaAndLeftExists(And(lhs, rhs)), true)
          case _ =>
            rhs match {
              case Forall(id, inner) =>
                (lemmaAndRightForall(And(lhs, rhs)), true)
              case Exists(id, inner) =>
                (lemmaAndRightExists(And(lhs, rhs)), true)
              case _ => {
                val (lhsPNFThm, lhsChanged) = toPNFThmSingleStep(lhs)

                if (lhsChanged) {
                  (lemmaAndPNF(lhsPNFThm, iffRefl(rhs)), true)
                } else {
                  val (rhsPNFThm, rhsChanged) = toPNFThmSingleStep(rhs)

                  (lemmaAndPNF(iffRefl(lhs), rhsPNFThm), rhsChanged)
                }
              }
            }
        }
      case Or(lhs, rhs) =>
        lhs match {
          case Forall(id, inner) => (lemmaOrLeftForall(Or(lhs, rhs)), true)
          case Exists(id, inner) => (lemmaOrLeftExists(Or(lhs, rhs)), true)
          case _ =>
            rhs match {
              case Forall(id, inner) => (lemmaOrRightForall(Or(lhs, rhs)), true)
              case Exists(id, inner) => (lemmaOrRightExists(Or(lhs, rhs)), true)
              case _ => {
                val (lhsPNFThm, lhsChanged) = toPNFThmSingleStep(lhs)

                if (lhsChanged) {
                  (lemmaOrPNF(lhsPNFThm, iffRefl(rhs)), true)
                } else {
                  val (rhsPNFThm, rhsChanged) = toPNFThmSingleStep(rhs)

                  (lemmaOrPNF(iffRefl(lhs), rhsPNFThm), rhsChanged)
                }
              }
            }
        }
      // DISALLOWED
      case Implies(lhs, rhs) =>
        throw new Exception("implies case in toPNFThmSingleStep")
      // DISALLOWED
      case Iff(lhs, rhs) =>
        throw new Exception("iff case in toPNFThmSingleStep")
      case Forall(id, inner) => {
        val (innerPNFThm, innerChanged) = toPNFThmSingleStep(inner)

        (lemmaForallPNF(id, innerPNFThm), innerChanged)
      }
      case Exists(id, inner) => {
        val (innerPNFThm, innerChanged) = toPNFThmSingleStep(inner)

        (lemmaExistsPNF(id, innerPNFThm), innerChanged)
      }
      case Equals(lhs, rhs) => (iffRefl(Equals(lhs, rhs)), false)
      case PredApp(predicate, args) =>
        (iffRefl(PredApp(predicate, args)), false)
      case _ => throw new Exception("unwanted case in toPNFThmSingleStep")
    }
  }

  /** Given a `formula`, generate a theorem for the equivalence with its prenex normal form:
    *   formula <=> toPNF(formula)
    */
  def toPNFThm(formula: Formula): Theorem = {
    if (!isNNF(formula)) {
      throw new Exception(
        "toPNFThm requires the formula to be in negation normal form"
      )
    }

    var thmSeq: Seq[Theorem] = Nil

    var formulaPNFed: Formula = formula
    var stepThm: Theorem = null
    var changed: Boolean = true
    while (changed) {
      val step = toPNFThmSingleStep(formulaPNFed)
      stepThm = step._1
      changed = step._2

      formulaPNFed = stepThm.formula match {
        case Iff(lhs, rhs) => lhs
        case _             => throw new Exception("unwanted case in toPNFThm:do_while")
      }

      if (changed) {
        thmSeq = thmSeq.:+(stepThm)
      }
    }
    thmSeq = thmSeq.reverse

    if (thmSeq.size == 0) {
      return iffRefl(formula)
    }

    var thmPNF: Theorem = thmSeq(0)
    thmSeq.tail.foreach(thm => {
      thmPNF = iffTrans(thmPNF, thm)
    })

    iffSym(thmPNF)
  }
}

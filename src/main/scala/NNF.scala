import fol._
import lcf._
import Theorems._

object NNF {

  /** Checks that a formula only contains implications, equalities, predicates,
    * False, and forall quantifiers.
    */
    def isAtomic(formula: Formula): Boolean = formula match {
        case Equals(lhs, rhs) => true
        case False => true
        case True => true
        case PredApp(predicate, args) => true
        case _ => false
    }
    def isNNF(formula: Formula): Boolean = formula match {
        case f if isAtomic(f) => true
        case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
        case Exists(id, inner) => isNNF(inner)
        case Forall(id, inner) => isNNF(inner)
        //case Iff(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
        //case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
        case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
        case Not(f) if isAtomic(f) => true
        case _ => false 
    }


  /** Converts a formula to an equivalent formula in normal form. */
  def toNNF(f: Formula): Formula = f match {
    // Transformation of operator not needed :
    case Not(p) if isAtomic(p) => f
    case _ if isAtomic(f) => f

    // Transformation needed
    case Not(And(p,q)) => Or(toNNF(Not(p)), toNNF(Not(q)))
    case Not(Or(p,q)) => And(toNNF(Not(p)), toNNF(Not(q)))
    case Not(Implies(p,q)) => And(toNNF(p), toNNF(Not(q)))
    case Not(Iff(p,q)) => Or(And(toNNF(p), toNNF(Not(q))), And(toNNF(q), toNNF(Not(p))))
    case Not(Forall(x, p)) => Exists(x, toNNF(Not(p)))
    case Not(Exists(x, p)) => Forall(x, toNNF(Not(p)))
    case Not(Not(p)) => toNNF(p)

    // Recursive transformation
    case And(p,q) => And(toNNF(p), toNNF(q))
    case Or(p,q) => Or(toNNF(p), toNNF(q))
    case Implies(p, q) => Or(toNNF(Not(p)), toNNF(q))
    case Iff(p, q) => {
      val (pn1, qn1) = (toNNF(Not(p)), toNNF(q))
      val (pn2, qn2) = (toNNF(p), toNNF(Not(q)))
      And(Or(pn1, qn1), Or(qn2, pn2)) }
    case Forall(x, p) => Forall(x, toNNF(p))
    case Exists(x, p) => Exists(x, toNNF(p))
  }

  /** Given a `formula`, generate a theorem for the equivalence with its normal form:
    *   formula <=> toNNF(formula)
    */
  def toNNF_thm(f: Formula): Theorem = {
    tnnfth(f, toNNF(f))
  }

  def tnnfth(f: Formula, nnf_f: Formula): Theorem = (f, nnf_f) match {
    // Transformation of operator not needed :
    case (f1,f2) if (f1 == f2) => iffRefl(f)

    // Transformation needed
    case (Not(And(p,q)), Or(pn, qn)) => 
      iffTrans(
        notAnd(p,q), 
        orIff2(tnnfth(Not(p), pn), tnnfth(Not(q), qn)))
    case (Not(Or(p,q)), And(pn, qn)) => notOr2(tnnfth(Not(p), pn), tnnfth(Not(q), qn))
    case (Not(Implies(p,q)), And(pn, qn)) => 
      iffTrans(
        notImplies(p, q),
        andIff2(tnnfth(p, pn), tnnfth(Not(q), qn)))
    case (Not(Iff(p,q)), Or(And(pn1, qn1), And(qn2, pn2))) => 
      val ppn1 = tnnfth(p, pn1)
      val qqn1 = tnnfth(Not(q), qn1)
      val ppn2 = tnnfth(Not(p), pn2)
      val qqn2 = tnnfth(q, qn2)
      iffTrans(
        notIff2(p, q),
        orIff2(andIff2(ppn1, qqn1), andIff2(qqn2, ppn2))
      )
    case (Not(Forall(x, p)), Exists(xn, pn)) if (x == xn) => notForall2(x, tnnfth(Not(p), pn))
    case (Not(Exists(x, p)), Forall(xn, pn)) if (x == xn) => notExists2(x, tnnfth(Not(p), pn))
    case (Not(Not(p)), pn) => iffTrans(iffNotNot(p), tnnfth(p, pn))

    // Recursive transformation
    case (And(p,q), And(pn, qn)) => andIff2(tnnfth(p, pn), tnnfth(q, qn))
    case (Or(p,q), Or(pn, qn)) => orIff2(tnnfth(p, pn), tnnfth(q, qn))
    case (Implies(p, q), Or(pn, qn)) => iffTrans(
      orImpliesIff(p, q), 
      orIff2(tnnfth(Not(p), pn), tnnfth(q, qn))
    )
    case (Iff(p, q), And(Or(pn1, qn1), Or(qn2, pn2))) => 
      val ppn1 = tnnfth(Not(p), pn1)
      val qqn1 = tnnfth(q, qn1)
      val ppn2 = tnnfth(p, pn2)
      val qqn2 = tnnfth(Not(q), qn2)
      iffTrans(
        iffIff(p, q), 
        iffTrans( //(p => q) /\ (q => p)
          andIff2(orImpliesIff(p, q), orImpliesIff(q, p)), // (~p \/ q) /\ (p \/ ~q)
          andIff2(orIff2(ppn1, qqn1), orIff2(qqn2, ppn2))
        )
      )
    case (Forall(x, p), Forall(xn, pn)) if (x == xn) => forallIff(x, tnnfth(p, pn))
    case (Exists(x, p), Exists(xn, pn)) if (x == xn) => existsIff2(x, tnnfth(p, pn))

    case _ => throw new IllegalArgumentException(s"Invalid form in tnnfth : \nf = ${f.pretty}\nnnf_f = ${nnf_f.pretty}.")
  }
}
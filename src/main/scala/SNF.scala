import PNF._
import fol._
import lcf._
import Theorems._

object SNF {

  val CONSTANT: String = "c"
  val FUNCTION: String = "f"

  /*
    Tests wether the given `formula` is in skolem normal form.
   */
  def isSNF(formula: Formula): Boolean = {
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
        case Exists(id, inner)        => false
        case Equals(lhs, rhs)         => true
        case PredApp(predicate, args) => true
        case _                        => throw new Exception("unwanted case in isSNF")
      }

    formula match {
      case Forall(id, inner) => check(inner, true)
      case _                 => check(formula, false)
    }
  }

  /*
    Transforms the given `formula` in skolem normal form.
   */
  def toSNF(formula: Formula): Formula = {
    if (!isPNF(formula)) {
      throw new Exception(
        "toSNF requires the formula to be in prenex normal form"
      )
    }

    var counter_f = -1
    var context: Map[Identifier, Seq[Identifier]] = Map()
    var universallyQuantified: Seq[Identifier] = Nil
    var assignedFunction: Map[Identifier, Function] = Map()

    def transformExpr(expression: Expr): Expr = expression match {
      case Con(constant) => Con(constant)
      case Var(id) => {
        if (context.contains(id)) {
          val idContext: Seq[Identifier] = context.get(id).get
          if (idContext.isEmpty) {
            Con(CONSTANT + id.drop(1))
          } else {
            if (assignedFunction.contains(id)) {
              FunApp(
                assignedFunction.get(id).get,
                idContext.map(ele => Var(ele))
              )
            } else {
              counter_f += 1
              assignedFunction = assignedFunction.+((id, FUNCTION + counter_f))

              FunApp(FUNCTION + counter_f, idContext.map(ele => Var(ele)))
            }
          }
        } else {
          Var(id)
        }
      }
      case FunApp(function, args) =>
        FunApp(function, args.map(ele => transformExpr(ele)))
    }

    def transform(formula: Formula): Formula = formula match {
      case True              => True
      case False             => False
      case Not(inner)        => Not(transform(inner))
      case And(lhs, rhs)     => And(transform(lhs), transform(rhs))
      case Or(lhs, rhs)      => Or(transform(lhs), transform(rhs))
      case Implies(lhs, rhs) => Implies(transform(lhs), transform(rhs))
      case Iff(lhs, rhs)     => Iff(transform(lhs), transform(rhs))
      case Forall(id, inner) => {
        universallyQuantified = universallyQuantified.:+(id)

        Forall(id, transform(inner))
      }
      case Exists(id, inner) => {
        context = context.+((id, universallyQuantified))

        transform(inner)
      }
      case Equals(lhs, rhs) => Equals(transformExpr(lhs), transformExpr(rhs))
      case PredApp(predicate, args) =>
        PredApp(predicate, args.map(ele => transformExpr(ele)))
      case _ => throw new Exception("unwanted case in toSNF:transform")
    }

    transform(formula)
  }

  /** Given a `formula`, generate a theorem for the equisatisfiability with its skolem normal form:
    *  Theorem(Equisat(formula, toSNF(formula)))
    */ // TODO
  def toSNFThmEqui(formula: Formula): Theorem = ???
}

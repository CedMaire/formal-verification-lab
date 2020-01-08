import lcf._
import fol._
import Tests._
import Theorems._

object Main {
  def main(args: Array[String]): Unit = {
    // testIsPNF()
    // testUniqueVars()
    // testToPNF()
    // testPNFLemmas()
    // testToPNFThm()
    // testIsSNF()
    // testToSNF()
  }
}

/** Tests for `toNormalFormThm` **/
// val predicates: Array[Predicate] = Array("p", "q", "r")
// val functions: Array[Predicate] = Array("f", "g")
// val constants: Array[Constant] = Array("a", "b", "c")
// val ids: Array[Identifier] = Array("x", "y", "z")

// Uncomment this to test your code
// assert(
//   testRandom(
//     50000,
//     (f: Formula) ⇒ f.pretty,
//     Formula.random(predicates, functions, constants, ids),
//     checkNormalFormTheorem
//   )
// )

// println(True)
// println(False)
// println(Not(False))
// println(And(False, False))
// println(Or(False, False))
// println(Implies(False, False))
// println(Iff(False, False))
// println(Forall("\"x\"", False))
// println(Exists("\"x\"", False))
// println(Equals(Var("\"x\""), Var("\"y\"")))
// println(PredApp("\"P\"", (0 to 2).map(i => Var("\"x" + i + "\""))))
// True
// False
// Not(False)
// And(False, False)
// Or(False, False)
// Implies(False, False)
// Iff(False, False)
// Forall("x", False)
// Exists("x", False)
// Equals(Var("x"), Var("y"))
// PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))

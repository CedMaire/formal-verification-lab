import lcf._
import fol._
import Tests._
import Theorems._

object Main {
  def main(args: Array[String]): Unit = {
    assert(
      testThese(
        Seq(
          And(
            Or(
              Forall("x0", Not(PredApp("P", Vector(Var("x0"))))),
              Forall("x0", Not(PredApp("Q", Vector(Var("x0"), Con("u")))))
            ),
            And(
              Implies(False, False),
              Exists("x0", Forall("x1", Not(Equals(Var("x0"), Var("x1")))))
            )
          )
        ),
        (f: Formula) ⇒ f.pretty,
        checkNNFPNFSKNFlow
      )
    )
  }
}

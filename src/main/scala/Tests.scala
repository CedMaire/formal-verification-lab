import NF._
import NNF._
import PNF._
import SNF._
import lcf._
import fol._

object Tests {

  def checkNormalFormTheorem(f: Formula): Boolean = {
    val nf = toNormalForm(f)
    lazy val prettyF = f.pretty
    toNormalFormThm(f).formula match {
      case Iff(f1, f2) =>
        assert(
          f1 == f,
          s"The left-hand-side of `toNormalFormThm($prettyF)` should be $prettyF. Got ${f1.pretty} instead."
        )
        assert(
          f2 == nf,
          s"The right-hand side of `toNormalFormThm($prettyF)` should be ${nf.pretty}. Got ${f2.pretty} instead."
        )
        assert(
          isNormalForm(nf),
          s"The normal form of $f should be in normal form. Got ${nf.pretty} instead."
        )
      case _ =>
        throw new Exception(
          s"`toNormalFormThm($prettyF)` should return an `Iff` formula"
        )
    }
    true
  }

  def testThese[T](
      toTest: Iterable[T],
      toString: T => String,
      f: T => Boolean
  ): Boolean = {
    for (e <- toTest) {
      println("Testing: " + toString(e))
      if (f(e))
        println(s"  ==> OK")
      else {
        println(s"  ==> Error")
        return false
      }
    }
    return true
  }

  def testRandom[T](
      n: Int,
      toString: T => String,
      random: => T,
      f: T => Boolean
  ): Boolean = {
    for (i <- 1 to n) {
      if (!f(random)) {
        return false
      }
      if (i % 1000 == 0)
        println(s"Did $i random (successful) tests.")
    }
    return true
  }

  def testIsPNF() {
    assert(isPNF(True))
    assert(isPNF(False))
    assert(isPNF(Not(False)))
    assert(isPNF(And(False, False)))
    assert(isPNF(Or(False, False)))
    assert(isPNF(Implies(False, False)))
    assert(isPNF(Iff(False, False)))
    assert(isPNF(Forall("x", False)))
    assert(isPNF(Exists("x", False)))
    assert(isPNF(Equals(Var("x"), Var("y"))))
    assert(isPNF(PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))))
    assert(
      isPNF(
        Forall(
          "x0",
          Exists(
            "x1",
            Not(
              And(
                Or(
                  Iff(Equals(Var("x0"), Var("x1")), False),
                  Equals(Var("x0"), Var("x1"))
                ),
                Implies(
                  False,
                  PredApp("P", Vector(Var("x0"), Var("x1")))
                )
              )
            )
          )
        )
      )
    )
    assert(
      !isPNF(
        Forall(
          "x0",
          Exists(
            "x1",
            Not(
              And(
                Or(
                  Iff(Equals(Var("x0"), Var("x1")), False),
                  Equals(Var("x0"), Var("x1"))
                ),
                Implies(
                  Forall("x2", False),
                  PredApp("P", Vector(Var("x0"), Var("x1")))
                )
              )
            )
          )
        )
      )
    )
  }

  def testUniqueVars() {
    println(uniqueVars(True).pretty)
    println(uniqueVars(False).pretty)
    println(uniqueVars(Not(False)).pretty)
    println(uniqueVars(And(False, False)).pretty)
    println(uniqueVars(Or(False, False)).pretty)
    println(uniqueVars(Implies(False, False)).pretty)
    println(uniqueVars(Iff(False, False)).pretty)
    println(uniqueVars(Forall("x", False)).pretty)
    println(uniqueVars(Exists("x", False)).pretty)
    println(uniqueVars(Equals(Var("x"), Var("y"))).pretty)
    println(
      uniqueVars(PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))).pretty
    )
    println(
      uniqueVars(
        Forall(
          "x0",
          And(
            Forall(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Forall(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    println(
      uniqueVars(
        Exists(
          "x0",
          And(
            Exists(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Exists(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    println(
      uniqueVars(
        Forall(
          "x0",
          And(
            Exists(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Exists(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    println(
      uniqueVars(
        Exists(
          "x0",
          And(
            Forall(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Forall(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
  }

  def testToPNF() {
    println(toPNF(True).pretty)
    println(toPNF(False).pretty)
    println(toPNF(Not(False)).pretty)
    println(toPNF(And(False, False)).pretty)
    println(toPNF(Or(False, False)).pretty)
    println(toPNF(Implies(False, False)).pretty)
    println(toPNF(Iff(False, False)).pretty)
    println(toPNF(Forall("x", False)).pretty)
    println(toPNF(Exists("x", False)).pretty)
    println(toPNF(Equals(Var("x"), Var("y"))).pretty)
    println(
      toPNF(PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))).pretty
    )
    println(
      toPNF(
        Forall(
          "x0",
          And(
            Forall(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Forall(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    println(
      toPNF(
        Exists(
          "x0",
          And(
            Exists(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Exists(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    println(
      toPNF(
        Forall(
          "x0",
          And(
            Exists(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Exists(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    println(
      toPNF(
        Exists(
          "x0",
          And(
            Forall(
              "x1",
              Not(
                Or(
                  Iff(
                    Equals(Var("x0"), Var("x1")),
                    Equals(Var("x1"), Var("x0"))
                  ),
                  PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                )
              )
            ),
            Forall(
              "x1",
              Implies(
                PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
              )
            )
          )
        )
      ).pretty
    )
    assert(
      isPNF(
        toPNF(
          Forall(
            "x0",
            And(
              Forall(
                "x1",
                Not(
                  Or(
                    Iff(
                      Equals(Var("x0"), Var("x1")),
                      Equals(Var("x1"), Var("x0"))
                    ),
                    PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                  )
                )
              ),
              Forall(
                "x1",
                Implies(
                  PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                  PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
                )
              )
            )
          )
        )
      )
    )
    assert(
      isPNF(
        toPNF(
          Exists(
            "x0",
            And(
              Exists(
                "x1",
                Not(
                  Or(
                    Iff(
                      Equals(Var("x0"), Var("x1")),
                      Equals(Var("x1"), Var("x0"))
                    ),
                    PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                  )
                )
              ),
              Exists(
                "x1",
                Implies(
                  PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                  PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
                )
              )
            )
          )
        )
      )
    )
    assert(
      isPNF(
        toPNF(
          Forall(
            "x0",
            And(
              Exists(
                "x1",
                Not(
                  Or(
                    Iff(
                      Equals(Var("x0"), Var("x1")),
                      Equals(Var("x1"), Var("x0"))
                    ),
                    PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                  )
                )
              ),
              Exists(
                "x1",
                Implies(
                  PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                  PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
                )
              )
            )
          )
        )
      )
    )
    assert(
      isPNF(
        toPNF(
          Exists(
            "x0",
            And(
              Forall(
                "x1",
                Not(
                  Or(
                    Iff(
                      Equals(Var("x0"), Var("x1")),
                      Equals(Var("x1"), Var("x0"))
                    ),
                    PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
                  )
                )
              ),
              Forall(
                "x1",
                Implies(
                  PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
                  PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
                )
              )
            )
          )
        )
      )
    )
  }

  def testPNFLemmas() {
    val p: Formula = PredApp("p", Nil)
    val pn: Formula = PredApp("pn", Nil)
    val q: Formula = PredApp("q", Nil)
    val qn: Formula = PredApp("qn", Nil)
    val r: Formula = PredApp("r", Nil)

    println(
      lemmaAndPNF(unsafeTheorem(Iff(p, pn)), unsafeTheorem(Iff(q, qn))).pretty
    )
    println(lemmaAndLeftForall(And(Forall("x", p), q)).pretty)
    println(lemmaAndLeftExists(And(Exists("x", p), q)).pretty)
    println(lemmaAndRightForall(And(p, Forall("x", q))).pretty)
    println(lemmaAndRightExists(And(p, Exists("x", q))).pretty)
    println(
      lemmaOrPNF(unsafeTheorem(Iff(p, pn)), unsafeTheorem(Iff(q, qn))).pretty
    )
    println(lemmaOrLeftForall(Or(Forall("x", p), q)).pretty)
    println(lemmaOrLeftExists(Or(Exists("x", p), q)).pretty)
    println(lemmaOrRightForall(Or(p, Forall("x", q))).pretty)
    println(lemmaOrRightExists(Or(p, Exists("x", q))).pretty)
    println(lemmaForallPNF("x", unsafeTheorem(Iff(p, pn))).pretty)
    println(lemmaExistsPNF("x", unsafeTheorem(Iff(p, pn))).pretty)

    println(impliesDef(p, q).pretty)
    println(orDistriAnd(p, q, r).pretty)
    println(andDistriOr(p, q, r).pretty)
    println(forallIffPNF("x", p).pretty)
    println(existsIffPNF("x", p).pretty)
    println(forallDistriAnd("x", p, q).pretty)
    println(existsDistriAnd("x", p, q).pretty)
    println(forallDistriOr("x", p, q).pretty)
    println(existsDistriOr("x", p, q).pretty)
  }

  def testToPNFThm() {
    val formula0: Formula =
      Exists("e", Or(Not(False), Forall("a", Equals(Var("e"), Var("a")))))
    val formula1: Formula =
      And(
        Or(
          Forall("x0", PredApp("P", Vector(Var("x0")))),
          Forall("x0", Forall("x1", Or(False, True)))
        ),
        And(
          False,
          Exists("x0", Forall("x1", Not(Equals(Var("x0"), Var("x1")))))
        )
      )

    println(toPNFThm(uniqueVars(formula0)).pretty)
    println(toPNFThm(uniqueVars(formula1)).pretty)
  }

  def testIsSNF() {
    assert(isSNF(True))
    assert(isSNF(False))
    assert(isSNF(Not(False)))
    assert(isSNF(And(False, False)))
    assert(isSNF(Or(False, False)))
    assert(isSNF(Implies(False, False)))
    assert(isSNF(Iff(False, False)))
    assert(isSNF(Forall("x", False)))
    assert(!isSNF(Exists("x", False)))
    assert(isSNF(Equals(Var("x"), Var("y"))))
    assert(isSNF(PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))))

    assert(
      isSNF(
        Forall("x", Forall("x", Forall("x", Forall("x", Forall("x", False)))))
      )
    )
    assert(
      !isSNF(
        Forall("x", Forall("x", Forall("x", Forall("x", Exists("x", False)))))
      )
    )
    assert(
      !isSNF(
        Forall("x", Forall("x", Exists("x", Forall("x", Forall("x", False)))))
      )
    )
    assert(
      !isSNF(
        Forall("x", Forall("x", Not(Forall("x", Forall("x", False)))))
      )
    )
    assert(
      isSNF(
        Forall(
          "x",
          Forall(
            "x",
            Forall(
              "x",
              Forall(
                "x",
                Forall(
                  "x",
                  Not(
                    And(
                      Or(
                        Implies(True, False),
                        Iff(
                          False,
                          PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))
                        )
                      ),
                      Equals(Var("x"), Var("y"))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    assert(
      !isSNF(
        Forall(
          "x",
          Forall(
            "x",
            Forall(
              "x",
              Forall(
                "x",
                Forall(
                  "x",
                  Not(
                    And(
                      Or(
                        Exists("x", False),
                        Iff(
                          False,
                          PredApp("P", Vector(Var("x0"), Var("x1"), Var("x2")))
                        )
                      ),
                      Equals(Var("x"), Var("y"))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  }

  def testToSNF() {
    val formula0 = toPNF(
      Forall(
        "x0",
        And(
          Forall(
            "x1",
            Not(
              Or(
                Iff(
                  Equals(Var("x0"), Var("x1")),
                  Equals(Var("x1"), Var("x0"))
                ),
                PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
              )
            )
          ),
          Forall(
            "x1",
            Implies(
              PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
              PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
            )
          )
        )
      )
    )
    val formula1 = toPNF(
      Exists(
        "x0",
        And(
          Exists(
            "x1",
            Not(
              Or(
                Iff(
                  Equals(Var("x0"), Var("x1")),
                  Equals(Var("x1"), Var("x0"))
                ),
                PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
              )
            )
          ),
          Exists(
            "x1",
            Implies(
              PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
              PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
            )
          )
        )
      )
    )
    val formula2 = toPNF(
      Forall(
        "x0",
        And(
          Exists(
            "x1",
            Not(
              Or(
                Iff(
                  Equals(Var("x0"), Var("x1")),
                  Equals(Var("x1"), Var("x0"))
                ),
                PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
              )
            )
          ),
          Exists(
            "x1",
            Implies(
              PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
              PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
            )
          )
        )
      )
    )
    val formula3 = toPNF(
      Exists(
        "x0",
        And(
          Forall(
            "x1",
            Not(
              Or(
                Iff(
                  Equals(Var("x0"), Var("x1")),
                  Equals(Var("x1"), Var("x0"))
                ),
                PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
              )
            )
          ),
          Forall(
            "x1",
            Implies(
              PredApp("P", Vector(Con("x0"), Con("x1"), Var("x0"))),
              PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
            )
          )
        )
      )
    )
    val formula4 = toPNF(
      Forall(
        "x0",
        And(
          Forall(
            "x1",
            Not(
              Or(
                Iff(
                  Exists("x2", Implies(PredApp("P", Vector(Var("x2"))), True)),
                  Equals(Var("x1"), Var("x0"))
                ),
                PredApp("P", Vector(Var("x0"), Var("x1"), Con("x2")))
              )
            )
          ),
          Forall(
            "x1",
            Implies(
              Exists("x2", Implies(False, PredApp("P", Vector(Var("x2"))))),
              PredApp("P", Vector(Con("x0"), Var("x1"), Con("x2")))
            )
          )
        )
      )
    )

    val formula5 = toPNF(
      Forall(
        "x0",
        Forall(
          "x1",
          Exists(
            "x2",
            Forall(
              "x3",
              Forall(
                "x4",
                Exists(
                  "x5",
                  Implies(
                    PredApp("P", Vector(Var("x2"))),
                    PredApp("Q", Vector(Var("x5")))
                  )
                )
              )
            )
          )
        )
      )
    )

    println(formula0.pretty)
    println(toSNF(formula0).pretty)
    println(formula1.pretty)
    println(toSNF(formula1).pretty)
    println(formula2.pretty)
    println(toSNF(formula2).pretty)
    println(formula3.pretty)
    println(toSNF(formula3).pretty)
    println(formula4.pretty)
    println(toSNF(formula4).pretty)
    println(formula5.pretty)
    println(toSNF(formula5).pretty)
  }
}

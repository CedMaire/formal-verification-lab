In `fol/src/main/scala/fol/Formulas.scala` we added the following values that compute a set of all identifiers in a given formula (constants, vars, functions, predicates):

```scala
/** Identifiers of `this` expression. */
lazy val ids: Set[Identifier] = ???

/** Identifiers of `this` formula. */
lazy val ids: Set[Identifier] = ???
```

In `lcf/src/main/scala/lcf/package.scala` we added the following "axioms":

```scala
/** These might not always be axioms but we don't know how far to go for the lab. */

/** Axiom `(p => q) <=> (¬p \/ q)`. */
def impliesDef(p: Formula, q: Formula): Theorem = ???

/** Axiom `(p \/ (q /\ r)) <=> ((p \/ q) /\ (p \/ r))`. */
def orDistriAnd(p: Formula, q: Formula, r: Formula): Theorem = ???

/** Axiom `(p /\ (q \/ r)) <=> ((p /\ q) \/ (p /\ r))`. */
def andDistriOr(p: Formula, q: Formula, r: Formula): Theorem = ???

/** Axiom `P <=> forall x. P`, given that x is not an identifier in P. */
def forallIffPNF(x: Identifier, p: Formula): Theorem = ???

/** Axiom `P <=> exists x. P`, given that x is not an identifier in P. */
def existsIffPNF(x: Identifier, p: Formula): Theorem = ???

/** Axiom `forall x. (P /\ Q) <=> (forall x. P /\ forall x. Q)`. */
def forallDistriAnd(x: Identifier, p: Formula, q: Formula): Theorem = ???

/** Axiom `exists x. (P /\ Q) <=> (exists x. P /\ exists x. Q)`. */
def existsDistriAnd(x: Identifier, p: Formula, q: Formula): Theorem = ???

/** Axiom `forall x. (P \/ Q) <=> (forall x. P \/ forall x. Q)`. */
def forallDistriOr(x: Identifier, p: Formula, q: Formula): Theorem = ???

/** Axiom `exists x. (P \/ Q) <=> (exists x. P \/ exists x. Q)`. */
def existsDistriOr(x: Identifier, p: Formula, q: Formula): Theorem = ???

/** ONLY USED FOR TESTING PURPOSES */
def unsafeTheorem(formula: Formula): Theorem = ???
```

We moved lab04 in `src/main/scala/NF.scala`.

`src/main/scala/NNF.scala` contains everyting related to the Negation Normal Form:

```scala
???
```

`src/main/scala/PNF.scala` contains everything related to the Prenex Normal Form:

```scala
/*
  Tests wether the given `formula` is in prenex normal form.
*/
def isPNF(formula: Formula): Boolean = ???

/*
  Transforms the given `formula` in prenex normal form.
*/
def toPNF(formula: Formula): Formula = ???

/** Given a `formula`, generate a theorem for the equivalence with its prenex normal form:
  *   formula <=> toPNF(formula)
*/
def toPNFThm(formula: Formula): Theorem = ???
```

`src/main/scala/SNF.scala` contains everything related to the Skolem Normal Form:

```scala
/*
  Tests wether the given `formula` is in skolem normal form.
*/
def isSNF(formula: Formula): Boolean = ???

/*
  Transforms the given `formula` in skolem normal form.
*/
def toSNF(formula: Formula): Formula = ???

/** Given a `formula`, generate a theorem for the equisatisfiability with its skolem normal form:
  *  Theorem(Equisat(formula, toSNF(formula)))
*/
def toSNFThmEqui(formula: Formula): Theorem = ???
```

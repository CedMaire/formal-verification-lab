# LAB7 - personalized
### Cédric Maine & Clément Blaudeau

## Introduction
In this lab we extended the transformation functions of lab4 in an lcf style. Given a formula `F` we are able to do the following transformations:

 * Negation normal form
 * Prenex normal form
 * Skolem normal form

The corresponding scala functions are the following :

```scala
F_nnf = toNNF(F)
F_pnf = toPNF(F_nnf)
F_snf = toSNF(F_pnf)
```

Alongside the transformation, we provide functions that generate the following theorems:

```scala
F <=> toNNF(F)
F <=> toPNF(F)
```

As the skolem normal form is not equivalent to the inital formula (but only equisatisfiable), we don't have an equivalence theorem for it.


## 1) Modifications of the lab4 files

In `fol/src/main/scala/fol/Formulas.scala` we added the following values that compute a set of all identifiers in a given formula (constants, vars, functions, predicates):

```scala
/** Identifiers of `this` expression. */
lazy val ids: Set[Identifier] = ...

/** Identifiers of `this` formula. */
lazy val ids: Set[Identifier] = ...
```

In `lcf/src/main/scala/lcf/package.scala` we added the following "axioms" to simplify proofs :

```scala
/** These might not always be axioms but we don't know how far to go for the lab. */

/** Axiom `(p => q) <=> (¬p \/ q)`. */
def impliesDef(p: Formula, q: Formula): Theorem = ...

/** Axiom `(p \/ (q /\ r)) <=> ((p \/ q) /\ (p \/ r))`. */
def orDistriAnd(p: Formula, q: Formula, r: Formula): Theorem = ...

/** Axiom `(p /\ (q \/ r)) <=> ((p /\ q) \/ (p /\ r))`. */
def andDistriOr(p: Formula, q: Formula, r: Formula): Theorem = ...

/** Axiom `P <=> forall x. P`, given that x is not an identifier in P. */
def forallIffPNF(x: Identifier, p: Formula): Theorem = ...

/** Axiom `P <=> exists x. P`, given that x is not an identifier in P. */
def existsIffPNF(x: Identifier, p: Formula): Theorem = ...

/** Axiom `forall x. (P /\ Q) <=> (forall x. P /\ forall x. Q)`. */
def forallDistriAnd(x: Identifier, p: Formula, q: Formula): Theorem = ...

/** Axiom `exists x. (P /\ Q) <=> (exists x. P /\ exists x. Q)`, given that x is not an identifier in both P and Q. */
def existsDistriAnd(x: Identifier, p: Formula, q: Formula): Theorem = ...

/** Axiom `forall x. (P \/ Q) <=> (forall x. P \/ forall x. Q)`, given that x is not an identifier in both P and Q. */
def forallDistriOr(x: Identifier, p: Formula, q: Formula): Theorem = ...

/** Axiom `exists x. (P \/ Q) <=> (exists x. P \/ exists x. Q)`. */
def existsDistriOr(x: Identifier, p: Formula, q: Formula): Theorem = ...

```

We moved lab04 in `src/main/scala/NF.scala`.

## 2) Negation normal form

`src/main/scala/NNF.scala` contains everyting related to the Negation Normal Form. A formula in NNF only has negation over atomic formulas, and only uses AND and OR operators (and quantifiers).

```scala
/*
  Tests wether the given `formula` is in negation normal form.
*/
def isNNF(formula: Formula): Boolean = ...

/*
  Transforms the given `formula` in negation normal form.
*/
def toNNF(formula: Formula): Formula = ...

/** Given a `formula`, generate a theorem for the equivalence with its negation normal form:
  *   formula <=> toNNF(formula)
*/
def toNNFThm(formula: Formula): Theorem = ...
```

## 3) Prenex normal form
`src/main/scala/PNF.scala` contains everything related to the Prenex Normal Form. A formula in PNF factors all the quantifiers at the top level of the formula.

```scala
/*
  Tests wether the given `formula` is in prenex normal form.
*/
def isPNF(formula: Formula): Boolean = ...

/*
  Transforms the given `formula` in prenex normal form.
*/
def toPNF(formula: Formula): Formula = ...

/** Given a `formula`, generate a theorem for the equivalence with its prenex normal form:
  *   formula <=> toPNF(formula)
*/
def toPNFThm(formula: Formula): Theorem = ...
```

## 4) Skolem normal form
`src/main/scala/SNF.scala` contains everything related to the Skolem Normal Form. *Skolemization* is used to remove existential quantifiers. Equivalence is not guaranteed.

```scala
/*
  Tests wether the given `formula` is in skolem normal form.
*/
def isSNF(formula: Formula): Boolean = ...

/*
  Transforms the given `formula` in skolem normal form.
*/
def toSNF(formula: Formula): Formula = ...
```

## 5) Equisatisfiability problem
As the original axioms were designed to facilitate the "Implication normal form" of lab4, we found it quite challenging to write the equivalence theorems for negation and prenex normal form. Running short of time, we were not able to write an *equisatisfiability* theorem. To do so, we would need to define a notion of *model* of a first order logic formula, and an *evaluation* function.

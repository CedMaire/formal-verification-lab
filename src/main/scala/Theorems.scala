object Theorems {

  import fol._
  import lcf._

  /** Theorem `p => p`. */
  def impliesRefl(p: Formula): Theorem = {
    impliesDistr(p, fol"$p => $p", p)(addImplies(p, fol"$p => $p"))(
      addImplies(p, p)
    )
  }

  def iffRefl(p: Formula): Theorem = {
    val pp = impliesRefl(p)
    impliesIff(pp, pp)
  }

  /** Theorem `p => q` given `p => p => q`. */
  def impliesUndup(ppq: Theorem): Theorem = ppq.formula match {
    case fol"$p => $_ => $q" => impliesDistr(p, p, q)(ppq)(impliesRefl(p))
    case _ =>
      throw new IllegalArgumentException("Invalid form in impliesUndup.")
  }

  /** Theorem `p => q` given `q`. */
  def addAssumption(p: Formula, q: Theorem): Theorem =
    addImplies(q.formula, p)(q)

  /** Theorem `(p => q) => p => r` given `q => r`. */
  def impliesAddAssumption(p: Formula, qr: Theorem): Theorem =
    qr.formula match {
      case fol"$q => $r" => impliesDistr(p, q, r)(addAssumption(p, qr))
      case _ =>
        throw new IllegalArgumentException(
          "Invalid form in impliesAddAssumption."
        )
    }

  /** Theorem `p => r` given `p => q` and `q => r`. */
  def impliesTrans(pq: Theorem, qr: Theorem): Theorem = pq.formula match {
    case fol"$p => $_" => impliesAddAssumption(p, qr)(pq)
    case _ =>
      throw new IllegalArgumentException("Invalid form in impliesTrans.")
  }

  /** Theorem `(q => r) => (p => q) => p => r`. */
  def impliesTransThm(p: Formula, q: Formula, r: Formula): Theorem =
    impliesTrans(addImplies(Implies(q, r), p), impliesDistr(p, q, r))

  /** Theorem `p => q => r` given `p => r`. */
  def impliesInsert(pr: Theorem, q: Formula): Theorem = pr.formula match {
    case fol"$p => $r" => impliesTrans(pr, addImplies(r, q))
    case _ =>
      throw new IllegalArgumentException("Invalid form in impliesInsert.")
  }

  /** Theorem `q => p => r` given `p => q => r`. */
  def impliesSwap(pqr: Theorem): Theorem = pqr.formula match {
    case fol"$p => $q => $r" =>
      impliesTrans(addImplies(q, p), impliesDistr(p, q, r)(pqr))
    case _ => throw new IllegalArgumentException("Invalid form in impliesSwap.")
  }

  /** Theorem `(p => q => r) => q => p => r. */
  def impliesSwapThm(p: Formula, q: Formula, r: Formula): Theorem =
    impliesTrans(
      impliesDistr(p, q, r),
      addConclusion(addImplies(q, p), Implies(p, r))
    )

  /** Theorem `(q => r) => (p => r)` given `p => q`. */
  def addConclusion(pq: Theorem, r: Formula): Theorem = pq.formula match {
    case fol"$p => $q" => impliesSwap(impliesTransThm(p, q, r))(pq)
    case _ =>
      throw new IllegalArgumentException("Invalid form in addConclusion.")
  }

  /** Theorem `(q => p => r) => (t => s => u)` given `(p => q => r) => (s => t => u)`. */
  def impliesSwap2(pqrstu: Theorem): Theorem = pqrstu.formula match {
    case fol"($p => $q => $r) => ($s => $t => $u)" =>
      impliesTrans(
        impliesSwapThm(q, p, r),
        impliesTrans(pqrstu, impliesSwapThm(s, t, u))
      )
    case _ =>
      throw new IllegalArgumentException("Invalid form in impliesSwap2.")
  }

  /** Theorem `p => r` from `p => q => r` and `p => q`. */
  def rightModusPonens(pqr: Theorem, pq: Theorem): Theorem =
    impliesUndup(impliesTrans(pq, impliesSwap(pqr)))

  /** Theorem `p => q` from `p <=> q`. */
  def iffImplies1(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => iffToImplies1(p, q)(pq)
    case _              => throw new IllegalArgumentException("Invalid form in iffImplies1.")
  }

  /** Theorem `q => p` from `p <=> q`. */
  def iffImplies2(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => iffToImplies2(p, q)(pq)
    case _              => throw new IllegalArgumentException("Invalid form in iffImplies1.")
  }

  /** Theorem `p <=> q` given `p => q` and `q => p`. */
  def impliesIff(pq: Theorem, qp: Theorem) = pq.formula match {
    case fol"$p => $q" => impliesToIff(p, q)(pq)(qp)
    case _             => throw new IllegalArgumentException("Invalid form in impliesIff.")
  }

  /** Theorem `p => q` given `p => (q => false) => false`. */
  def rightDoubleNegation(pqff: Theorem): Theorem = pqff.formula match {
    case fol"$_ => ($q => false) => false" =>
      impliesTrans(pqff, doubleNegation(q))
    case _ =>
      throw new IllegalArgumentException("Invalid form in rightDoubleNegation.")
  }

  /** Theorem `false => p`. */
  def exFalso(p: Formula): Theorem =
    rightDoubleNegation(addImplies(fol"false", fol"$p => false"))

  /** Theorem `p => q => s` given `p => q => r` and `r => s`. */
  def impliesTrans2(pqr: Theorem, rs: Theorem): Theorem =
    (pqr.formula, rs.formula) match {
      case (fol"$p => $q => $r", fol"$_ => $s") =>
        impliesAddAssumption(p, impliesTransThm(q, r, s)(rs))(pqr)
      case _ =>
        throw new IllegalArgumentException("Invalid form in impliesTrans2.")
    }

  /** Theorem `p => r` from theorems `p => qi` and theorem `q1 => ... => qn => r`. */
  def impliesTransChain(pqis: Seq[Theorem], qisr: Theorem): Theorem =
    if (pqis.isEmpty) {
      throw new IllegalArgumentException("Empty chain in impliesTransChain.")
    } else {
      pqis.tail.reverse.foldRight(impliesTrans(pqis.head, qisr)) {
        case (qi, r) => impliesUndup(impliesTrans(qi, impliesSwap(r)))
      }
    }

  /** Theorem `(q => false) => p => (p => q) => false`. */
  def impliesTrueFalse(p: Formula, q: Formula): Theorem =
    impliesTrans(
      impliesTransThm(p, q, fol"false"),
      impliesSwapThm(fol"$p => $q", p, fol"false")
    )

  /** Theorem `(p2 => p1) => (q1 => q2) => (p1 => q1) => (p2 => q2)`. */
  def impliesMonoThm(
      p1: Formula,
      p2: Formula,
      q1: Formula,
      q2: Formula
  ): Theorem = {
    val thm1 =
      impliesTransThm(fol"$p1 => $q1", fol"$p2 => $q1", fol"$p2 => $q2")
    val thm2 = impliesTransThm(p2, q1, q2)
    val thm3 = impliesSwap(impliesTransThm(p2, p1, q1))
    impliesTrans(thm3, impliesSwap(impliesTrans(thm2, thm1)))
  }

  /** Theorem `true`. */
  lazy val truth: Theorem = iffImplies2(trueIff)(impliesRefl(fol"false"))

  /** Theorem `~q => ~p` given `p => q`. */
  def contraposition(pq: Theorem): Theorem = pq.formula match {
    case fol"$p => $q" =>
      impliesTrans(
        impliesTrans(iffImplies1(notIff(q)), addConclusion(pq, fol"false")),
        iffImplies2(notIff(p))
      )
    case _ =>
      throw new IllegalArgumentException("Invalid form in impliesTrans2.")
  }

  /** Theorem `p /\ q => p`. */
  def andLeft(p: Formula, q: Formula): Theorem = {
    val thm1 = impliesAddAssumption(p, addImplies(fol"false", q))
    val thm2 = rightDoubleNegation(addConclusion(thm1, fol"false"))
    val thm3 = iffImplies1(andIff(p, q))
    impliesTrans(thm3, thm2)
  }

  /** Theorem `p /\ q => q`. */
  def andRight(p: Formula, q: Formula): Theorem = {
    val thm1 = addImplies(fol"$q => false", p)
    val thm2 = rightDoubleNegation(addConclusion(thm1, fol"false"))
    val thm3 = iffImplies1(andIff(p, q))
    impliesTrans(thm3, thm2)
  }

  /** Theorems `p1 /\ ... /\ pn => pi`. */
  def conjuncts(pis: Formula): Seq[Theorem] = pis match {
    case fol"""$p /\ $q""" =>
      andLeft(p, q) +: conjuncts(q).map({
        impliesTrans(andRight(p, q), _)
      })
    case p => Seq(impliesRefl(p))
  }

  /** Theorem `p => q => p /\ q`. */
  def andPair(p: Formula, q: Formula): Theorem = {
    val thm1 = iffImplies2(andIff(p, q))
    val thm2 = impliesSwapThm(fol"$p => $q => false", q, fol"false")
    val thm3 = impliesAddAssumption(p, impliesTrans2(thm2, thm1))
    thm3(impliesSwap(impliesRefl(fol"$p => $q => false")))
  }

  /** Theorem `p => q => r` given `p /\ q => r`. */
  def shunt(pqr: Theorem): Theorem = pqr.formula match {
    case fol"""$p /\ $q => $r""" => {
      val thm1 = impliesAddAssumption(q, pqr)
      val thm2 = impliesAddAssumption(p, thm1)
      thm2(andPair(p, q))
    }
    case _ => throw new IllegalArgumentException("Invalid form in shunt.")
  }

  /** Theorem `p /\ q => r` given `p => q => r`. */
  def unshunt(pqr: Theorem): Theorem = pqr.formula match {
    case fol"""$p => $q => $r""" =>
      impliesTransChain(Seq(andLeft(p, q), andRight(p, q)), pqr)
    case _ => throw new IllegalArgumentException("Invalid form in shunt.")
  }

  /** Theorem `(p <=> q) <=> (p => q) /\ (q => p)`. */
  def iffIff(p: Formula, q: Formula): Theorem = {
    val thm1 = andPair(fol"$p => $q", fol"$q => $p")
    val thm2 = iffToImplies1(p, q)
    val thm3 = iffToImplies2(p, q)
    impliesIff(
      impliesTransChain(Seq(thm2, thm3), thm1),
      unshunt(impliesToIff(p, q))
    )
  }

  /** Theorem `p => (p => q) => q`. **/
  def modusPonensThm(p: Formula, q: Formula): Theorem =
    impliesSwapThm(fol"$p => $q", p, q)(impliesAddAssumption(p, impliesRefl(q)))

  /** Theorem `p => (p => false) => false`. **/
  def doubleNegationIntro(p: Formula): Theorem = {
    modusPonensThm(p, False)
  }

  /** Theorem `q <=> p` given `p <=> q`. **/
  def iffSym(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" =>
      impliesToIff(q, p)(iffImplies2(pq))(iffImplies1(pq))
    case _ => throw new IllegalArgumentException("Illegal form in iffSym.")
  }

  /** Theorem `p <=> r` given `p <=> q` and `q <=> r`. **/
  def iffTrans(pq: Theorem, qr: Theorem): Theorem =
    (pq.formula, qr.formula) match {
      case (fol"$p <=> $q", fol"$q2 <=> $r") if q == q2 =>
        impliesToIff(p, r)(
          impliesTrans(iffToImplies1(p, q)(pq), iffToImplies1(q, r)(qr))
        )(
          impliesTrans(
            iffToImplies1(r, q)(iffSym(qr)),
            iffToImplies1(q, p)(iffSym(pq))
          )
        )
      case _ => throw new IllegalArgumentException("Invalid form in iffTrans.")
    }
}

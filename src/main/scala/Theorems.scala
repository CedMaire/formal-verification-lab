
object Theorems {

  import fol._
  import lcf._

  /** Theorem `p => p`. */
  def impliesRefl(p: Formula): Theorem = {
    impliesDistr(p, fol"$p => $p", p)(addImplies(p, fol"$p => $p"))(addImplies(p, p))
  }

  /** Theorem `p <=> p` */
  def iffRefl(p: Formula): Theorem = {
    val pp = impliesRefl(p)
    impliesIff(pp, pp)
  }

  /** Theorem `p => q` given `p => p => q`. */
  def impliesUndup(ppq: Theorem): Theorem = ppq.formula match {
    case fol"$p => $_ => $q" => impliesDistr(p, p, q)(ppq)(impliesRefl(p))
    case _ => throw new IllegalArgumentException("Invalid form in impliesUndup.")
  }

  /** Theorem `p => q` given `q`. */
  def addAssumption(p: Formula, q: Theorem): Theorem =
    addImplies(q.formula, p)(q)

  /** Theorem `(p => q) => p => r` given `q => r`. */
  def impliesAddAssumption(p: Formula, qr: Theorem): Theorem = qr.formula match {
    case fol"$q => $r" => impliesDistr(p, q, r)(addAssumption(p, qr))
    case _ => throw new IllegalArgumentException("Invalid form in impliesAddAssumption.")
  }

  /** Theorem `(p => q) <=> (p => r)` given `q <=> r`. */
  def impliesAddAssumption2(p: Formula, qr: Theorem): Theorem = qr.formula match {
    case fol"$q <=> $r" => impliesIff(impliesAddAssumption(p, iffImplies1(qr)), impliesAddAssumption(p, iffImplies2(qr)))
    case _ => throw new IllegalArgumentException("Invalid form in impliesAddAssumption2.")
  }

  /** Theorem `(p1 => q) <=> (p2 => r)` given `q <=> r` and `p1 <=> p2`. */
  def impliesAddAssumptionIff(p12: Theorem, qr: Theorem): Theorem = (qr.formula, p12.formula) match {
    case (fol"$q <=> $r", fol"$p1 <=> $p2") =>  iffTrans(impliesAddAssumption2(p1, qr), addConclusion2(p12, r))
    case _ => throw new IllegalArgumentException("Invalid form in impliesAddAssumptionIff.")
  }

  /** Theorem `p => r` given `p => q` and `q => r`. */
  def impliesTrans(pq: Theorem, qr: Theorem): Theorem = pq.formula match {
    case fol"$p => $_" => impliesAddAssumption(p, qr)(pq)
    case _ => throw new IllegalArgumentException("Invalid form in impliesTrans.")
  }

  /** Theorem `(q => r) => (p => q) => p => r`. */
  def impliesTransThm(p: Formula, q: Formula, r: Formula): Theorem =
    impliesTrans(addImplies(Implies(q, r), p), impliesDistr(p, q, r))

  /** Theorem `p => q => r` given `p => r`. */
  def impliesInsert(pr: Theorem, q: Formula): Theorem = pr.formula match {
    case fol"$p => $r" => impliesTrans(pr , addImplies(r, q))
    case _ => throw new IllegalArgumentException("Invalid form in impliesInsert.")
  }

  /** Theorem `q => p => r` given `p => q => r`. */
  def impliesSwap(pqr: Theorem): Theorem = pqr.formula match {
    case fol"$p => $q => $r" => impliesTrans(addImplies(q, p), impliesDistr(p, q, r)(pqr))
    case _ => throw new IllegalArgumentException("Invalid form in impliesSwap.")
  }

  /** Theorem `(p => q => r) => q => p => r. */
  def impliesSwapThm(p: Formula, q: Formula, r: Formula): Theorem =
    impliesTrans(impliesDistr(p, q, r), addConclusion(addImplies(q, p), Implies(p, r)))

  /** Theorem `(q => r) => (p => r)` given `p => q`. */
  def addConclusion(pq: Theorem, r: Formula): Theorem = pq.formula match {
    case fol"$p => $q" => impliesSwap(impliesTransThm(p, q, r))(pq)
    case _ => throw new IllegalArgumentException("Invalid form in addConclusion.")
  }

  /** Theorem `(p => r) <=> (q => r)` given `p <=> q`. */
  def addConclusion2(pq: Theorem, r: Formula): Theorem = pq.formula match {
    case fol"$p <=> $q" => impliesIff(addConclusion(iffImplies2(pq), r), addConclusion(iffImplies1(pq), r))
    case _ => throw new IllegalArgumentException("Invalid form in addConclusion2.")
  }

  /** Theorem `(p => r1) <=> (q => r2)` given `p <=> q` and `r1 <=> r2`. */
  def addConclusionIff(pq: Theorem, r12: Theorem): Theorem = (pq.formula, r12.formula) match {
    case (fol"$p <=> $q", fol"$r1 <=> $r2") => iffTrans(addConclusion2(pq, r1), impliesAddAssumption2(q, r12))
    case _ => throw new IllegalArgumentException("Invalid form in addConclusionIff.")
  }

  /** Theorem `(q => p => r) => (t => s => u)` given `(p => q => r) => (s => t => u)`. */
  def impliesSwap2(pqrstu: Theorem): Theorem = pqrstu.formula match {
    case fol"($p => $q => $r) => ($s => $t => $u)" =>
      impliesTrans(impliesSwapThm(q, p, r), impliesTrans(pqrstu, impliesSwapThm(s, t, u)))
    case _ => throw new IllegalArgumentException("Invalid form in impliesSwap2.")
  }

  /** Theorem `p => r` from `p => q => r` and `p => q`. */
  def rightModusPonens(pqr: Theorem, pq: Theorem): Theorem =
    impliesUndup(impliesTrans(pq, impliesSwap(pqr)))

  /** Theorem `p => q` from `p <=> q`. */
  def iffImplies1(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => iffToImplies1(p, q)(pq)
    case _ => throw new IllegalArgumentException("Invalid form in iffImplies1.")
  }

  /** Theorem `q => p` from `p <=> q`. */
  def iffImplies2(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => iffToImplies2(p, q)(pq)
    case _ => throw new IllegalArgumentException("Invalid form in iffImplies1.")
  }

  /** Theorem `p <=> q` given `p => q` and `q => p`. */
  def impliesIff(pq: Theorem, qp: Theorem) = pq.formula match {
    case fol"$p => $q" => impliesToIff(p, q)(pq)(qp)
    case _ => throw new IllegalArgumentException("Invalid form in impliesIff.")
  }

  /** Theorem `p => q` given `p => (q => false) => false`. */
  def rightDoubleNegation(pqff: Theorem): Theorem = pqff.formula match {
    case fol"$_ => ($q => false) => false" => impliesTrans(pqff, doubleNegation(q))
    case _ => throw new IllegalArgumentException("Invalid form in rightDoubleNegation.")
  }

  /** Theorem `false => p`. */
  def exFalso(p: Formula): Theorem =
    rightDoubleNegation(addImplies(fol"false", fol"$p => false"))

  /** Theorem `p => q => s` given `p => q => r` and `r => s`. */
  def impliesTrans2(pqr: Theorem, rs: Theorem): Theorem = (pqr.formula, rs.formula) match {
    case (fol"$p => $q => $r", fol"$_ => $s") =>
      impliesAddAssumption(p, impliesTransThm(q, r, s)(rs))(pqr)
    case _ => throw new IllegalArgumentException("Invalid form in impliesTrans2.")
  }

  /** Theorem `p => r` from theorems `p => qi` and theorem `q1 => ... => qn => r`. */
  def impliesTransChain(pqis: Seq[Theorem], qisr: Theorem): Theorem =
    if (pqis.isEmpty) {
      throw new IllegalArgumentException("Empty chain in impliesTransChain.")
    }
    else {
      pqis.tail.reverse.foldRight(impliesTrans(pqis.head, qisr)) {
        case (qi, r) => impliesUndup(impliesTrans(qi, impliesSwap(r)))
      }
    }

  /** Theorem `(q => false) => p => (p => q) => false`. */
  def impliesTrueFalse(p: Formula, q: Formula): Theorem =
    impliesTrans(impliesTransThm(p, q, fol"false"), impliesSwapThm(fol"$p => $q", p, fol"false"))

  /** Theorem `(p2 => p1) => (q1 => q2) => (p1 => q1) => (p2 => q2)`. */
  def impliesMonoThm(p1: Formula, p2: Formula, q1: Formula, q2: Formula): Theorem = {
    val thm1 = impliesTransThm(fol"$p1 => $q1", fol"$p2 => $q1", fol"$p2 => $q2")
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
        impliesTrans(
          iffImplies1(notIff(q)),
          addConclusion(pq, fol"false")),
        iffImplies2(notIff(p)))
    case _ => throw new IllegalArgumentException("Invalid form in impliesTrans2.")
  }

  /** Theorem `~p <=> ~q` given `p <=> q`. */
  def contraposition2(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => impliesIff(contraposition(iffImplies1(pq)), contraposition(iffImplies2(pq)))
    case _ => throw new IllegalArgumentException("Invalid form in contraposition2.")
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


  /** Theorem `p1 /\ q1 <=> p2 /\ q2` given `p1 <=> p2` and `q1 <=> q2`. */
  /** 1 : (p1 /\ q1) <=> (((p1 => q1 => false) => false)) by andIff
      2 : ((p1 => q1 => false) => false) <=> ((p2 => q2 => false) => false) 
        by addConclusion2 given
          (p1 => q1 => false) <=> (p2 => q2 => false) 
          by addConclusion2 given
            (p1 => q1) <=> (p2 => q2) by addConclusionIff 
      3 : ((p2 => q2 => false) => false) <=> (p2 /\ q2) by andIff
  **/
  def andIff2(p12: Theorem, q12: Theorem): Theorem = {
    (p12.formula, q12.formula) match {
      case (fol"""$p1 <=> $p2""", fol"""$q1 <=> $q2""") => {
        iffTrans(
          andIff(p1, q1), 
          iffTrans(
            addConclusion2(
              addConclusionIff(
                p12,
                addConclusion2(q12, False)),
              False), 
            iffSym(andIff(p2, q2))))
      }
      case _ => throw new IllegalArgumentException("Invalid form in andIff2")
    }
  }

  /** Theorem `p1 \/ q1 <=> p2 \/ q2` given `p1 <=> p2` and `q1 <=> q2`. */
  def orIff2(p12: Theorem, q12: Theorem): Theorem = {
    (p12.formula, q12.formula) match {
      case (fol"""$p1 <=> $p2""", fol"""$q1 <=> $q2""") => {
        iffTrans(
          orIff(p1, q1), 
          iffTrans(
            iffNotSwap(andIff2(iffNotSwap(p12), iffNotSwap(q12))),
            iffSym(orIff(p2, q2))))
      }
      case _ => throw new IllegalArgumentException("Invalid form in orIff2")
    }
  }


  /** Theorems `p1 /\ ... /\ pn => pi`. */
  def conjuncts(pis: Formula): Seq[Theorem] = pis match {
    case fol"""$p /\ $q""" => andLeft(p, q) +: conjuncts(q).map({
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
    impliesIff(impliesTransChain(Seq(thm2, thm3), thm1), unshunt(impliesToIff(p, q)))
  }

  /** Theorem `p => (p => q) => q`. **/
  def modusPonensThm(p: Formula, q: Formula): Theorem = {
    impliesSwap(impliesAddAssumption(p, impliesRefl(q)))
  }

  /** Theorem `p => (p => false) => false`. **/
  def doubleNegationIntro(p: Formula): Theorem = {
    modusPonensThm(p, False)
  }

  /** Theorem `q <=> p` given `p <=> q` **/
  def iffSym(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" =>
      impliesIff(iffImplies2(pq), iffImplies1(pq))
    case _ => throw new IllegalArgumentException("Illegal form in iffSym.")
  }

  /** Theorem `p <=> r` given `p <=> q` and `q <=> r` **/
  def iffTrans(pq: Theorem, qr: Theorem): Theorem = (pq.formula, qr.formula) match {
    case (fol"$p <=> $q", fol"$q2 <=> $r") if q == q2 =>
      impliesIff(impliesTrans(iffImplies1(pq), iffImplies1(qr)), impliesTrans(iffImplies2(qr), iffImplies2(pq)))
    case (fol"$p <=> $q", fol"$q2 <=> $r") if q != q2 =>
    throw new IllegalArgumentException(s"Invalid form in iffTrans (q!=q2) : ${pq.formula.pretty} and ${qr.formula.pretty} with \nq = ${q.pretty}\nq2 = ${q2.pretty}.")
    case _ => throw new IllegalArgumentException(s"Invalid form in iffTrans : ${pq.formula.pretty} and ${qr.formula.pretty}.")
  }

  /** Theorem `¬p <=> (q => false)` given `p <=> q` **/
  def iffNot(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => iffTrans(notIff(p), addConclusion2(pq, False))
    case _ => throw new IllegalArgumentException("Invalid form in iffNot.")
  }

  /** Theorem `~~p <=> p` */
  def iffNotNot(p : Formula): Theorem = {
    /*
    notIff(Not(p)) // ~~p <=> (~p => False)
    notIff(p) // ~p <=> (p => False)
    addConclusion(notIff(p), False) // (~p => False) <=> (p => False => False)
    impliesIff(doubleNegation(p), doubleNegationIntro(p)) // (p => False => False) <=> p
    */
    iffTrans(notIff(Not(p)), iffTrans(addConclusion2(notIff(p), False), impliesIff(doubleNegation(p), doubleNegationIntro(p))))
  }

  /** Theorem `~p <=> ~q` given `p <=> q` ***/
  def iffNotSwap(pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => 
      iffTrans(iffNot(pq), iffSym(notIff(q)))
    case _ => throw new IllegalArgumentException("Invalid form in iffNotSwap.")
  }


  /** Theorem `p <=> ~q` given `~p <=> q` ***/
  def iffNotSwitch(pq: Theorem): Theorem = pq.formula match {
    case fol"¬$p <=> $q" => 
      iffTrans(
        iffSym(iffNotNot(p)),
        iffNotSwap(pq)
      )
    case _ => throw new IllegalArgumentException("Invalid form in iffNotSwap.")
  }

  /** Theorem `~p <=> q` given `p <=> ~q` ***/
  def iffNotSwitch2(pq: Theorem): Theorem = pq.formula match {
    case fol"¬$p <=> $q" => iffSym(iffNotSwitch(iffSym(pq)))
    case _ => throw new IllegalArgumentException("Invalid form in iffNotSwap.")
  }

  /** Theorem `~(p/\q) <=> (~p \/ ~q)` */
  /**
   * 1: ~(p/\q) <=> ~(~~p/\~~q) 
   * by iffNotSwap given
   *    ~~p/\~~q <=> p/\q
   *    by andIff2 given
   *       ~~p <=> p and ~~q <=> q by iffNotNot
   * 2: ~(~~p/\~~q) <=> ~p \/ ~ q
   * by orIff **/ 
  def notAnd(p: Formula, q: Formula) = { 
    iffTrans(
      iffSym(iffNotSwap(andIff2(iffNotNot(p), iffNotNot(q)))),
      iffSym(orIff(Not(p), Not(q)))
    )
  }

  /** Theorem `~(p1 /\ q1) <=> (p2 \/ q2)` given `~p1 <=> p2` and `~q1 <=> q2`*/
  def notAnd2(p12: Theorem, q12:Theorem): Theorem = (p12.formula, q12.formula) match {
    case (fol"$p1 <=> $p2", fol"$q1 <=> $q2") => 
      iffTrans(
        notAnd(p1, q1),
        orIff2(p12, q12)
      )
    case _ => throw new IllegalArgumentException("Invalid form in notAnd2.")
  }

  /** Theorem `~(p \/ q) <=> (~p /\ ~q)` **/
  /**
   * 1: ~(p\/q) <=> ~~(~p/\~q)
   * by iffNotSwap given
   *    p\/q <=> ~(~p \/ ~q) 
   *    by orIff
   * 2: ~~(~p/\~q) <=> (~p /\ ~q)
   * by iffNotNot
   **/
  def notOr(p: Formula, q: Formula) = {
    iffTrans(
      iffNotSwap(orIff(p, q)), 
      iffNotNot(And(Not(p), Not(q))))
  }

  /** Theorem `~(p1 \/ q1) <=> (p2 /\ q2)` given `~p1 <=> p2` and `~q1 <=> q2` **/ 
  /**
   * 1: ~(p1\/q1) <=> (~p1 /\ ~q1) 
   * by notOr(p1, q1)
   * 2: (~p1/\~q1) <=> (p2 /\ q2)
   * by andIff2
   **/
  def notOr2(p12: Theorem, q12: Theorem): Theorem = (p12.formula, q12.formula) match {
    case (fol"¬$p1 <=> $p2", fol"¬$q1 <=> $q2") => 
      iffTrans(
        notOr(p1, q1),
        andIff2(p12, q12)
      )
    case _ => throw new IllegalArgumentException("Invalid form in notOr2.")
  }


  /** Theorem `~(p => q) <=> (p /\ ~q)` .*/
  /**
   * 1: ~(p => q) <=> ~(~p \/ q)
   * by iffNotSwap given orImpliesIff
   * 2: ~(~p \/ q) <=> (~~p /\ ~q)
   * by notOr2 given iffNotNot and ifRefl
   * 3: (~~p /\ ~q) <=> (p /\ ~q)
   **/
  def notImplies(p: Formula, q: Formula) =
    iffTrans(
      iffNotSwap(orImpliesIff(p, q)),
      iffTrans(
        notOr(Not(p), q),
        andIff2(iffNotNot(p), iffNotSwap(iffRefl(q)))
      )
    )

  /** Theorem `~(exists x. p) <=> (forall x. ~p)` .*/
  /**
   * 1: ~(exists x. p) <=> ~~(forall x. ~p)
   * by iffNotSwap given existsIff
   * 2: ~~(forall x. ~p) <=> forall x. ~p
   * by iffNotNot 
   **/
  def notExists(x: Identifier, p: Formula) = {
    iffTrans(
      iffNotSwap(existsIff(x, p)),
      iffNotNot(Forall(x, Not(p)))
    )
  }
   
  /** Theorem `~(exists x. p) <=> (forall x. q)` given `~p <=> q` .*/
  def notExists2(x: Identifier, pq: Theorem) = pq.formula match {
    case fol"¬$p <=> $q" => 
      iffTrans(
        notExists(x, p),
        forallIff(x, pq)
      )
    case _ => throw new IllegalArgumentException("Invalid form in notExists2.")
  }
  
  /** Theorem `~(forall x. p) <=> (exists x. ~p)` .*/
  /**
   * 1 : ~(forall x. p) <=> ~(forall x. ~~p)
   * by iffNotSwap given forallIff
   * 2 : ~(forall x. ~~p) <=> (exists x. ~p)
   * by iffSym given existsIff
   * **/
  def notForall(x: Identifier, p: Formula) = {
    iffTrans(
      iffNotSwap(forallIff(x, iffSym(iffNotNot(p)))),
      iffSym(existsIff(x, Not(p))))
  }
   
  /** Theorem `~(forall x. p) <=> (exists x. q)` given `~p <=> q` .*/
  def notForall2(x: Identifier, pq: Theorem) = pq.formula match {
    case fol"¬$p <=> $q" => 
      iffTrans(
        notForall(x, p),
        existsIff2(x, pq)
      )
    case _ => throw new IllegalArgumentException("Invalid form in notForall2.")
  }
    
  /** Theorem `~(p <=> q) <=> ((p /\ ~q) \/ (~p /\ q))` .*/
  /**
   * 1: ~(p <=> q) <=> ~((p => q) /\ (q => p))
   * by iffNotSwap given iffIff
   * 2: ~((p => q) /\ (q => p)) <=> (~(p=>q) \/ ~(q=>p))
   * by notAnd
   * 3: (~(p=>q) \/ ~(q=>p)) <=> ((p/\~q) \/ (~p/\q))
   **/
  def notIff2(p: Formula, q: Formula): Theorem = {
    iffTrans(
      iffNotSwap(iffIff(p, q)),
      iffTrans(
        notAnd(Implies(p, q), Implies(q,p)),
        orIff2(notImplies(p, q), notImplies(q, p))
      )
    )
  }
   
  
  /** Theorem `(forall x. p) <=> (forall x. q)` given `p <=> q` .*/
  def forallIff(x : Identifier, pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => 
      impliesIff(
        forallImplies(x, p, q)(generalize(iffImplies1(pq), x)), forallImplies(x, q, p)(generalize(iffImplies2(pq), x)))
    case _ => throw new IllegalArgumentException("Invalid form in forallIff.")
  }

  /** Theorem `(exists x. p) <=> (exists x. q)` given `p <=> q` .*/
  def existsIff2(x: Identifier, pq: Theorem): Theorem = pq.formula match {
    case fol"$p <=> $q" => 
      iffTrans(
        existsIff(x, p),
        iffTrans(
          iffNotSwap(forallIff(x, iffNotSwap(pq))),
          iffSym(existsIff(x, q))
        ))
    case _ => throw new IllegalArgumentException("Invalid form in forallIff.")
  }

  /** Theorem `(p1 /\ q1) <=> ((p2 => (q2 => false)) => false)` given `p1 <=> p2` and `q1 <=> q2` **/
  
  def iffAnd(p12: Theorem, q12: Theorem): Theorem = (p12.formula, q12.formula) match {
    case (fol"$p1 <=> $p2", fol"$q1 <=> $q2") => iffTrans(andIff(p1, q1), addConclusion2(impliesAddAssumptionIff(p12, addConclusion2(q12, False)), False))
    case _ => throw new IllegalArgumentException("Invalid form in andIff.")
  }


}



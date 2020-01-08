package fol
package parser

import scallion.syntactic._

object Parsers extends Syntaxes[Token, Kind] with Operators {

  import IRs._
  import SafeImplicits._

  override def getKind(token: Token): Kind = Kind.of(token)

  val quantifier: Syntax[Quantifier] = accept(Kind.Quantifier)({
    case Token.Forall(_) => Forall
    case Token.Exists(_) => Exists
  }, {
    case Forall => Seq(Token.Forall(NoPosition))
    case Exists => Seq(Token.Exists(NoPosition))
    case _ => Seq()
  })

  // Punctuation.
  val dot: Syntax[Unit] = elem(Kind.Dot).unit(Token.Dot(NoPosition))
  val dotDot: Syntax[Unit] = elem(Kind.DotDot).unit(Token.DotDot(NoPosition))
  val comma: Syntax[Unit] = elem(Kind.Comma).unit(Token.Comma(NoPosition))
  val open: Syntax[Unit] = elem(Kind.Parenthesis(true)).unit(Token.Parenthesis(true, NoPosition))
  val close: Syntax[Unit] = elem(Kind.Parenthesis(false)).unit(Token.Parenthesis(false, NoPosition))
  val tick: Syntax[Unit] = elem(Kind.Tick).unit(Token.Tick(NoPosition))

  // Binary operators.
  val and: Syntax[BinaryOp] = accept(Kind.And)({
    case Token.And(_) => And
  }, {
    case And => Seq(Token.And(NoPosition))
    case _ => Seq()
  })
  val or: Syntax[BinaryOp] = accept(Kind.Or)({
    case Token.Or(_) => Or
  }, {
    case Or => Seq(Token.Or(NoPosition))
    case _ => Seq()
  })
  val implies: Syntax[BinaryOp] = accept(Kind.Implies)({
    case Token.Implies(_) => Implies
  }, {
    case Implies => Seq(Token.Implies(NoPosition))
    case _ => Seq()
  })
  val iff: Syntax[BinaryOp] = accept(Kind.Iff)({
    case Token.Iff(_) => Iff
  }, {
    case Iff => Seq(Token.Iff(NoPosition))
    case _ => Seq()
  })

  // Placeholder.
  val placeholder: Syntax[Token.Placeholder] = accept(Kind.Placeholder)({
    case token@Token.Placeholder(_, _) => token
  }, {
    case token => Seq(token)
  })

  // Unary operators.
  val not: Syntax[UnaryOp] = accept(Kind.Not)({
    case Token.Not(_) => Not
  }, {
    case Not => Seq(Token.Not(NoPosition))
    case _ => Seq()
  })

  // True and false.
  val literal: Syntax[FormulaIR] = accept(Kind.Literal)({
    case Token.BooleanLiteral(value, _) => BoolLiteral(value)
    case _ => throw new Error("Unreachable")
  }, {
    case BoolLiteral(value) => Seq(Token.BooleanLiteral(value, NoPosition))
    case _ => Seq()
  })

  // Names.
  val name: Syntax[Token] = elem(Kind.Identifier) | elem(Kind.Placeholder)

  // Identifiers.
  val identifier: Syntax[IdentifierIR] = name.map({
    case Token.Identifier(name, _) => Id(name)
    case Token.Placeholder(index, _) => IdPlaceholder(index)
    case _ => throw new Error("Unreachable")
  }, {
    case Id(name) => Seq(Token.Identifier(name, NoPosition))
    case IdPlaceholder(index) => Seq(Token.Placeholder(index, NoPosition))
    case _ => Seq()
  })

  // Constants.
  val constant: Syntax[ConstantIR] = tick ~>~ (name.map({
    case Token.Identifier(name, _) => Con(name)
    case Token.Placeholder(index, _) => ConPlaceholder(index)
    case _ => throw new Error("Unreachable")
  }, {
    case Con(name) => Seq(Token.Identifier(name, NoPosition))
    case ConPlaceholder(index) => Seq(Token.Placeholder(index, NoPosition))
    case _ => Seq()
  }))

  // Expressions.
  lazy val expr: Syntax[ExprIR] = recursive {
    (name ~ opt(params)).map[ExprIR]({
      case Token.Placeholder(index, _) ~ None =>
        ExprPlaceholder(index)
      case Token.Identifier(name, _) ~ None =>
        Var(name)
      case Token.Placeholder(index, _) ~ Some((args, varargs)) =>
        FunctionApp(FunPlaceholder(index), args, varargs)
      case Token.Identifier(name, _) ~ Some((args, varargs)) =>
        FunctionApp(Fun(name), args, varargs)
      case _ => throw new Error("Unreachable")
    }, {
      case ExprPlaceholder(index) =>
        Seq(Token.Placeholder(index, NoPosition) ~ None)
      case Var(name) =>
        Seq(Token.Identifier(name, NoPosition) ~ None)
      case FunctionApp(FunPlaceholder(index), args, varargs) =>
        Seq(Token.Placeholder(index, NoPosition) ~ Some((args, varargs)))
      case FunctionApp(Fun(name), args, varargs) =>
        Seq(Token.Identifier(name, NoPosition) ~ Some((args, varargs)))
      case _ =>
        Seq()
    }) | constant.map({
      case con => ConVal(con)
    }, {
      case ConVal(con) => Seq(con)
      case _ => Seq()
    })
  }

  // Parameters.
  lazy val params: Syntax[(Seq[ExprIR], Option[Int])] = {
    lazy val res: Syntax[(Seq[ExprIR], Option[Int])] = recursive {
      (dotDot ~>~ placeholder).map[(Seq[ExprIR], Option[Int])]({
        case Token.Placeholder(index, _) => (Seq(), Some(index))
        case _ => throw new Error("Unreachable")
      }, {
        case (Seq(), Some(index)) => Seq(Token.Placeholder(index, NoPosition))
        case _ => Seq()
      }) |
      (expr ~ opt(comma ~>~ res)).map({
        case e ~ None => (Seq(e), None)
        case e ~ Some((es, o)) => (e +: es, o)
      }, {
        case (Seq(e), None) => Seq(e ~ None)
        case (Seq(e, es @ _*), o) => Seq(e ~ Some((es, o)))
      })
    }

    open ~>~ (res | epsilon((Seq(), None))) ~<~ close
  }

  val eqSign: Syntax[Boolean] = accept(Kind.EquSign)({
    case Token.Equals(_) => true
    case Token.NotEquals(_) => false
  }, {
    case true => Seq(Token.Equals(NoPosition))
    case false => Seq(Token.NotEquals(NoPosition))
  })

  // Atomic formula.
  lazy val atomicFormula: Syntax[FormulaIR] = atomicFromName | atomicFromConstant | literal

  // Atomic formula starting with a name (identifier or placeholder).
  lazy val atomicFromName: Syntax[FormulaIR] = (name ~ (params ~ opt(eqSign ~ expr) || opt(eqSign ~ expr))).map({
    case Token.Identifier(name, _) ~ Left((args, varargs) ~ None) => {
      PredicateApp(Pred(name), args, varargs)
    }
    case Token.Identifier(name, _) ~ Left((args, varargs) ~ Some(sign ~ right)) => {

      val left = FunctionApp(Fun(name), args, varargs)

      val base = Equals(left, right)

      if (!sign) {
        UnaryApp(Not, base)
      }
      else {
        base
      }
    }
    case Token.Identifier(name, _) ~ Right(Some(sign ~ right)) => {

      val left = Var(name)

      val base = Equals(left, right)

      if (!sign) {
        UnaryApp(Not, base)
      }
      else {
        base
      }
    }
    case Token.Identifier(name, _) ~ Right(None) => {
      PredicateApp(Pred(name), Seq(), None)
    }
    case Token.Placeholder(index, _) ~ Left((args, varargs) ~ None) => {
      PredicateApp(PredPlaceholder(index), args, varargs)
    }
    case Token.Placeholder(index, _) ~ Left((args, varargs) ~ Some(sign ~ right)) => {

      val left = FunctionApp(FunPlaceholder(index), args, varargs)

      val base = Equals(left, right)

      if (!sign) {
        UnaryApp(Not, base)
      }
      else {
        base
      }
    }
    case Token.Placeholder(index, _) ~ Right(None) => {
      FormulaPlaceholder(index)
    }
    case Token.Placeholder(index, _) ~ Right(Some(sign ~ right)) => {

      val left = ExprPlaceholder(index)

      val base = Equals(left, right)

      if (!sign) {
        UnaryApp(Not, base)
      }
      else {
        base
      }
    }
    case _ => throw new Error("Unreachable")
  }, {
    case PredicateApp(Pred(name), args, varargs) => {
      if (args.isEmpty && varargs.isEmpty) {
        Seq(
          Token.Identifier(name, NoPosition) ~ Right(None),
          Token.Identifier(name, NoPosition) ~ Left((args, varargs) ~ None))
      }
      else {
        Seq(Token.Identifier(name, NoPosition) ~ Left((args, varargs) ~ None))
      }
    }
    case PredicateApp(PredPlaceholder(index), args, varargs) => {
      Seq(Token.Placeholder(index, NoPosition) ~ Left((args, varargs) ~ None))
    }
    case Equals(left, right) => {
      left match {
        case FunctionApp(Fun(name), args, varargs) => {
          Seq(Token.Identifier(name, NoPosition) ~ Left((args, varargs) ~ Some(true ~ right)))
        }
        case FunctionApp(FunPlaceholder(index), args, varargs) => {
          Seq(Token.Placeholder(index, NoPosition) ~ Left((args, varargs) ~ Some(true ~ right)))
        }
        case Var(name) => {
          Seq(Token.Identifier(name, NoPosition) ~ Right(Some(true ~ right)))
        }
        case ExprPlaceholder(index) => {
          Seq(Token.Placeholder(index, NoPosition) ~ Right(Some(true ~ right)))
        }
        case _ => Seq()
      }
    }
    case UnaryApp(Not, Equals(left, right)) => {
      left match {
        case FunctionApp(Fun(name), args, varargs) => {
          Seq(Token.Identifier(name, NoPosition) ~ Left((args, varargs) ~ Some(false ~ right)))
        }
        case FunctionApp(FunPlaceholder(index), args, varargs) => {
          Seq(Token.Placeholder(index, NoPosition) ~ Left((args, varargs) ~ Some(false ~ right)))
        }
        case Var(name) => {
          Seq(Token.Identifier(name, NoPosition) ~ Right(Some(false ~ right)))
        }
        case ExprPlaceholder(index) => {
          Seq(Token.Placeholder(index, NoPosition) ~ Right(Some(false ~ right)))
        }
        case _ => Seq()
      }
    }
    case FormulaPlaceholder(index) => {
      Seq(Token.Placeholder(index, NoPosition) ~ Right(None))
    }
    case _ => Seq()
  })

  lazy val atomicFromConstant: Syntax[FormulaIR] = (constant ~ eqSign ~ expr).map({
    case p ~ s ~ right => {
      val left = ConVal(p)

      val base = Equals(left, right)

      if (!s) {
        UnaryApp(Not, base)
      }
      else {
        base
      }
    }
  }, {
    case Equals(ConVal(p), right) => Seq(p ~ true ~ right)
    case UnaryApp(Not, Equals(ConVal(p), right)) => Seq(p ~ false ~ right)
    case _ => Seq()
  })

  lazy val simpleFormula: Syntax[FormulaIR] = atomicFormula | open ~>~ formula ~<~ close

  lazy val negatedFormula: Syntax[FormulaIR] = prefixes(not, simpleFormula)({
    case (op, f) => UnaryApp(op, f)
  }, {
    case UnaryApp(op, f) => (op, f)
  })

  lazy val operationFormula: Syntax[FormulaIR] = operators(negatedFormula)(
    and is RightAssociative,
    or is RightAssociative,
    implies is RightAssociative,
    iff is RightAssociative,
  )({
    case (left, op, right) => BinaryApp(op, left, right)
  }, {
    case BinaryApp(op, left, right) => (left, op, right)
  })

  lazy val formula: Syntax[FormulaIR] = recursive {
    val withQuantifier: Syntax[FormulaIR] = (quantifier ~ many1(identifier) ~ dot.skip ~ formula).map({
      case q ~ is ~ f =>
        is.foldRight(f) {
          case (i, acc) => Quantified(q, i, acc)
        }
    }, {
      case Quantified(q, i, f) => {
        val isfs = Unfolds.unfoldRight[IdentifierIR, FormulaIR]({
          case Quantified(`q`, j, rest) => (j, rest)
        })(f)

        isfs.map({
          case is ~ g => q ~ (i +: is) ~ g
        })
      }
      case _ => Seq()
    })

    withQuantifier | operationFormula
  }
}

object Converter {

  // Conversion from IRs to actual Formulas and co.
  private def sequence[A](options: Seq[Option[A]]): Option[Seq[A]] = {
    if (options.isEmpty) {
      Some(List())
    }
    else for {
      h <- options.head
      t <- sequence(options.tail)
    } yield h +: t
  }

  private def getHole[A: Manifest](holes: Seq[Any], index: Int): Option[A] = {
    if (index >= holes.length) {
      None
    }
    else holes(index) match {
      case value: A => Some(value)
      case _ => None
    }
  }

  def fromIR(id: IRs.IdentifierIR, holes: Seq[Any]): Option[Identifier] = id match {
    case IRs.Id(result) => Some(result)
    case IRs.IdPlaceholder(index) => getHole[Identifier](holes, index)
  }

  def fromIR(fun: IRs.FunctionIR, holes: Seq[Any]): Option[Function] = fun match {
    case IRs.Fun(result) => Some(result)
    case IRs.FunPlaceholder(index) => getHole[Function](holes, index)
  }

  def fromIR(pred: IRs.PredicateIR, holes: Seq[Any]): Option[Predicate] = pred match {
    case IRs.Pred(result) => Some(result)
    case IRs.PredPlaceholder(index) => getHole[Predicate](holes, index)
  }

  def fromIR(pred: IRs.ConstantIR, holes: Seq[Any]): Option[Constant] = pred match {
    case IRs.Con(result) => Some(result)
    case IRs.ConPlaceholder(index) => getHole[Constant](holes, index)
  }

  def fromIR(expr: IRs.ExprIR, holes: Seq[Any]): Option[Expr] = expr match {
    case IRs.ConVal(con) => for {
      c <- fromIR(con, holes)
    } yield Con(c)
    case IRs.Var(id) => Some(Var(id))
    case IRs.FunctionApp(fun, args, varargsPlaceholder) => for {
      f  <- fromIR(fun, holes)
      as <- sequence(args.map(fromIR(_, holes)))
      ov <- varargsPlaceholder.map(getHole[Seq[Expr]](holes, _)).orElse(Some(Some(Seq())))
      va <- ov
    } yield FunApp(f, as ++ va)
    case IRs.ExprPlaceholder(index) => getHole[Expr](holes, index).orElse {
      getHole[Identifier](holes, index).map(Var(_))
    }
  }

  def fromIR(formula: IRs.FormulaIR, holes: Seq[Any]): Option[Formula] = formula match {
    case IRs.UnaryApp(IRs.Not, inner) => for {
      i <- fromIR(inner, holes)
    } yield Not(i)
    case IRs.BinaryApp(op, lhs, rhs) => for {
      l <- fromIR(lhs, holes)
      r <- fromIR(rhs, holes)
    } yield op match {
      case IRs.And => And(l, r)
      case IRs.Or => Or(l, r)
      case IRs.Implies => Implies(l, r)
      case IRs.Iff => Iff(l, r)
    }
    case IRs.BoolLiteral(value) => Some(if (value) True else False)
    case IRs.PredicateApp(pred, args, varargsPlaceholder) => for {
      p  <- fromIR(pred, holes)
      as <- sequence(args.map(fromIR(_, holes)))
      ov <- varargsPlaceholder.map(getHole[Seq[Expr]](holes, _)).orElse(Some(Some(Seq())))
      va <- ov
    } yield PredApp(p, as ++ va)
    case IRs.Equals(lhs, rhs) => for {
      l <- fromIR(lhs, holes)
      r <- fromIR(rhs, holes)
    } yield Equals(l, r)
    case IRs.Quantified(quantifier, id, inner) => for {
      x <- fromIR(id, holes)
      i <- fromIR(inner, holes)
    } yield quantifier match {
      case IRs.Forall => Forall(x, i)
      case IRs.Exists => Exists(x, i)
    }
    case IRs.FormulaPlaceholder(index) => getHole[Formula](holes, index)
  }

  def toIR(formula: Formula): IRs.FormulaIR = formula match {
    case And(left, right) => IRs.BinaryApp(IRs.And, toIR(left), toIR(right))
    case Or(left, right) => IRs.BinaryApp(IRs.Or, toIR(left), toIR(right))
    case Implies(left, right) => IRs.BinaryApp(IRs.Implies, toIR(left), toIR(right))
    case Iff(left, right) => IRs.BinaryApp(IRs.Iff, toIR(left), toIR(right))
    case Not(inner) => IRs.UnaryApp(IRs.Not, toIR(inner))
    case PredApp(name, args) => IRs.PredicateApp(IRs.Pred(name), args.map(toIR(_)), None)
    case Equals(left, right) => IRs.Equals(toIR(left), toIR(right))
    case Forall(name, inner) => IRs.Quantified(IRs.Forall, IRs.Id(name), toIR(inner))
    case Exists(name, inner) => IRs.Quantified(IRs.Exists, IRs.Id(name), toIR(inner))
    case True => IRs.BoolLiteral(true)
    case False => IRs.BoolLiteral(false)
  }

  def toIR(expr: Expr): IRs.ExprIR = expr match {
    case Con(name) => IRs.ConVal(IRs.Con(name))
    case Var(name) => IRs.Var(name)
    case FunApp(name, args) => IRs.FunctionApp(IRs.Fun(name), args.map(toIR(_)), None)
  }
}
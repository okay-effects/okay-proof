package okay.policy

/** what a decision reads: the facts answered (the call's own among them), the states' values, and the call's lists,
 * each with all its elements */
final case class Known(facts: Map[FactRef, Answer], states: Map[FactRef, Value],
                       lists: Map[FactRef, List[Value]] = Map.empty)

/**
 * THE EVALUATOR, untrusted: a condition's truth under a call and what is known — `None` where a fact it needs is
 * unknown. It only chooses; the kernel proves (`Prove`).
 */
object Eval:
  def plus(a: Value, b: Value): Value = (a, b) match
    case (Value.I(x), Value.I(y)) => Value.I(x + y)
    case (Value.D(x), Value.D(y)) => Value.D(x + y)
    case _ => throw IllegalArgumentException(s"$a + $b")

  def minus(a: Value, b: Value): Value = (a, b) match
    case (Value.I(x), Value.I(y)) => Value.I(x - y)
    case (Value.D(x), Value.D(y)) => Value.D(x - y)
    case _ => throw IllegalArgumentException(s"$a - $b")

  /** a fact applied, its arguments' values known: `owns(ann, acc1)` for `owns(caller, account)` */
  def ref(name: String, args: List[TExpr], env: Map[String, Value], known: Known): Option[FactRef] =
    val vs = args.map(value(_, env, known))
    Option.when(vs.forall(_.isDefined))(FactRef(name, vs.flatten))

  /** every fact and state an expression or condition reads, under `env`, as far as known: an argument of the call is
   * known from the call, so the fact of it (`balance(account)`) is known to be `balance(acc1)` */
  def refs(e: TExpr, env: Map[String, Value], known: Known): List[(Boolean, FactRef)] = e match
    case TExpr.Fact(n, as, _) => as.flatMap(refs(_, env, known)) ++ ref(n, as, env, known).map(false -> _)
    case TExpr.State(n, as, _) => as.flatMap(refs(_, env, known)) ++ ref(n, as, env, known).map(true -> _)
    case TExpr.Add(a, b, _) => refs(a, env, known) ++ refs(b, env, known)
    case TExpr.Sub(a, b, _) => refs(a, env, known) ++ refs(b, env, known)
    case TExpr.Mul(a, _, _) => refs(a, env, known)
    case TExpr.ToDec(a) => refs(a, env, known)
    case _ => Nil

  def refs(c: TCond, env: Map[String, Value], known: Known): List[(Boolean, FactRef)] = c match
    case TCond.Compare(a, _, b) => refs(a, env, known) ++ refs(b, env, known)
    case TCond.In(a, os) => refs(a, env, known) ++ os.flatMap(refs(_, env, known))
    case TCond.Holds(n, as) => as.flatMap(refs(_, env, known)) ++ ref(n, as, env, known).map(false -> _)
    case TCond.Text(a, _, b) => refs(a, env, known) ++ refs(b, env, known)
    case TCond.And(a, b) => refs(a, env, known) ++ refs(b, env, known)
    case TCond.Or(a, b) => refs(a, env, known) ++ refs(b, env, known)
    case TCond.Not(a) => refs(a, env, known)
    case TCond.Every(x, l, b) => elements(l, env, known).toList.flatten.flatMap(e => refs(b, env + (x -> e), known))
    case TCond.Exists(x, l, b) => elements(l, env, known).toList.flatten.flatMap(e => refs(b, env + (x -> e), known))

  /** a list's elements, if the call gave it */
  def elements(l: TList, env: Map[String, Value], known: Known): Option[List[Value]] =
    value(l.base, env, known).flatMap(b => known.lists.get(FactRef(l.name, List(b))))

  def value(e: TExpr, env: Map[String, Value], known: Known): Option[Value] = e match
    case TExpr.Lit(v) => Some(v)
    case TExpr.Var(n, _) => env.get(n)
    case TExpr.Fact(n, as, _) => ref(n, as, env, known).flatMap(known.facts.get) match
      case Some(Answer.Is(v)) => Some(v)
      case _ => None
    case TExpr.State(n, as, _) => ref(n, as, env, known).flatMap(known.states.get)
    case TExpr.Add(a, b, _) => for x <- value(a, env, known); y <- value(b, env, known) yield plus(x, y)
    case TExpr.Sub(a, b, _) => for x <- value(a, env, known); y <- value(b, env, known) yield minus(x, y)
    case TExpr.Mul(a, by, _) => value(a, env, known).map(x => (x, by) match
      case (Value.I(p), Value.I(q)) => Value.I(p * q)
      case (Value.D(p), Value.D(q)) => Value.D(p * q)
      case _ => throw IllegalArgumentException(s"$x * $by"))
    case TExpr.ToDec(a) => value(a, env, known).map {
      case Value.I(i) => Value.D(BigDecimal(i))
      case v => v
    }

  private def compare(a: Value, b: Value): Int = (a, b) match
    case (Value.I(x), Value.I(y)) => x.compare(y)
    case (Value.D(x), Value.D(y)) => x.compare(y)
    case _ => throw IllegalArgumentException(s"$a compared with $b")

  private def same(a: Value, b: Value): Boolean = (a, b) match
    case (Value.D(x), Value.D(y)) => x.compare(y) == 0
    case _ => a == b

  /** the condition's truth; `None`: a fact it needs is unknown */
  def holds(c: TCond, env: Map[String, Value], known: Known): Option[Boolean] = c match
    case TCond.Compare(a, cmp, b) =>
      for x <- value(a, env, known); y <- value(b, env, known) yield cmp match
        case Cmp.Eq => same(x, y)
        case Cmp.Ne => !same(x, y)
        case Cmp.Lt => compare(x, y) < 0
        case Cmp.Le => compare(x, y) <= 0
        case Cmp.Gt => compare(x, y) > 0
        case Cmp.Ge => compare(x, y) >= 0
    case TCond.In(a, os) =>
      value(a, env, known).flatMap { x =>
        val vs = os.map(value(_, env, known))
        if vs.exists(_.exists(same(x, _))) then Some(true) else if vs.forall(_.isDefined) then Some(false) else None
      }
    case TCond.Holds(n, as) => ref(n, as, env, known).flatMap(known.facts.get) match
      case Some(Answer.Holds(t)) => Some(t)
      case _ => None
    case TCond.Text(a, op, b) =>
      for case Value.T(x) <- value(a, env, known); case Value.T(y) <- value(b, env, known) yield op match
        case TextOp.Starts => x.startsWith(y)
        case TextOp.Ends => x.endsWith(y)
        case TextOp.Contains => x.contains(y)
    case TCond.And(a, b) => (holds(a, env, known), holds(b, env, known)) match
      case (Some(false), _) | (_, Some(false)) => Some(false)
      case (Some(true), Some(true)) => Some(true)
      case _ => None
    case TCond.Or(a, b) => (holds(a, env, known), holds(b, env, known)) match
      case (Some(true), _) | (_, Some(true)) => Some(true)
      case (Some(false), Some(false)) => Some(false)
      case _ => None
    case TCond.Not(a) => holds(a, env, known).map(!_)
    case TCond.Every(x, l, b) => elements(l, env, known).flatMap { es =>
      val each = es.map(e => holds(b, env + (x -> e), known))
      if each.contains(Some(false)) then Some(false) else if each.forall(_.isDefined) then Some(true) else None
    }
    case TCond.Exists(x, l, b) => elements(l, env, known).flatMap { es =>
      val each = es.map(e => holds(b, env + (x -> e), known))
      if each.contains(Some(true)) then Some(true) else if each.forall(_.isDefined) then Some(false) else None
    }

  /** why a condition does not hold: the parts that fail, with the values read */
  def why(c: TCond, env: Map[String, Value], known: Known): List[String] = c match
    case TCond.And(a, b) => why(a, env, known) ++ why(b, env, known)
    case TCond.Or(a, b) =>
      if holds(c, env, known).contains(true) then Nil else List((why(a, env, known) ++ why(b, env, known)).mkString(
        "neither ", " nor ", ""))
    case _ => holds(c, env, known) match
      case Some(true) => Nil
      case Some(false) => List(s"${show(c, env, known)} is false")
      case None => List(s"${show(c, env, known)}: unknown")

  /** a condition as written, its variables and facts with their values */
  def show(c: TCond, env: Map[String, Value], known: Known): String = c match
    case TCond.Compare(a, cmp, b) => s"${show(a, env, known)} ${cmp.text} ${show(b, env, known)}"
    case TCond.In(a, os) => s"${show(a, env, known)} in [${os.map(show(_, env, known)).mkString(", ")}]"
    case TCond.Holds(n, as) =>
      ref(n, as, env, known).fold(s"$n(${as.map(show(_, env, known)).mkString(", ")})")(_.toString)
    case TCond.Text(a, op, b) => s"${show(a, env, known)} ${op.word} ${show(b, env, known)}"
    case TCond.And(a, b) => s"${show(a, env, known)} and ${show(b, env, known)}"
    case TCond.Or(a, b) => s"(${show(a, env, known)} or ${show(b, env, known)})"
    case TCond.Not(a) => s"not ${show(a, env, known)}"
    case TCond.Every(x, l, _) => s"every $x in ${l.name.stripPrefix("arg:")}: (...)"
    case TCond.Exists(x, l, _) => s"some $x in ${l.name.stripPrefix("arg:")}: (...)"

  def show(e: TExpr, env: Map[String, Value], known: Known): String = e match
    case TExpr.Lit(v) => v.toString
    case TExpr.Var(n, _) => env.get(n).fold(n)(v => s"$n ($v)")
    case TExpr.Fact(n, List(TExpr.Var("call", _)), _) if n.startsWith("arg:") =>
      s"${n.stripPrefix("arg:")} (${value(e, env, known).fold("missing")(_.toString)})"
    case TExpr.Fact(n, as, _) => ref(n, as, env, known).fold(n)(_.toString) +
      s" (${value(e, env, known).fold("unknown")(_.toString)})"
    case TExpr.State(n, as, _) => ref(n, as, env, known).fold(n)(_.toString) +
      s" (${value(e, env, known).fold("unknown")(_.toString)})"
    case TExpr.Add(a, b, _) => s"${show(a, env, known)} + ${show(b, env, known)}"
    case TExpr.Sub(a, b, _) => s"${show(a, env, known)} - ${show(b, env, known)}"
    case TExpr.Mul(a, by, _) => s"${show(a, env, known)} * $by"
    case TExpr.ToDec(a) => s"dec(${show(a, env, known)})"

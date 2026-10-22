package okay.proof

import scala.collection.mutable

/**
 * A CERTIFICATE: a theorem's proof as data — its steps in order, each a rule and the earlier steps it uses, shared
 * where the proof shares them — so another process, another language, an auditor later can check it. Checking is the
 * kernel's: every step derived again (`check`); a certificate is never trusted as a theorem by itself.
 */
object Certificate:
  import Rule.*

  /** the proof of `t` as JSON: `{"theory": …, "hypotheses": […], "conclusion": …, "steps": [{"rule": …}, …]}` */
  def of(t: Thm): String =
    val ids = mutable.LinkedHashMap.empty[Thm, Int]
    val steps = mutable.ArrayBuffer.empty[Json]
    // post-order, by identity: a premise before the step that uses it; a shared premise once
    def visit(t: Thm): Int = ids.getOrElse(t, {
      val prem = premises(t.by).map(visit)
      val id = steps.length
      steps += node(t.by, prem)
      ids(t) = id
      id
    })
    visit(t)
    Json.Obj(List(
      "theory" -> Json.Str(t.kernel.theory.name),
      "hypotheses" -> Json.Arr(t.hyps.toList.map(Codec.formula)),
      "conclusion" -> Codec.formula(t.concl),
      "steps" -> Json.Arr(steps.toList))).render

  /** the certificate's proof checked by `k`, every step derived again: its theorem, if it is the one claimed */
  def check(text: String, k: Kernel): Either[String, Thm] =
    for
      json <- Json.parse(text)
      steps <- json.get("steps").collect { case Json.Arr(xs) => xs }.toRight("no steps")
      claimed <- json.get("conclusion").toRight("no conclusion").flatMap(Codec.formula)
      thms <- steps.foldLeft[Either[String, Vector[Thm]]](Right(Vector.empty)) { (acc, s) =>
        acc.flatMap(done => rule(s, done).flatMap(k.derive).map(done :+ _))
      }
      last <- thms.lastOption.toRight("an empty proof")
      _ <- Either.cond(last.concl == claimed, (), s"the proof proves ${last.concl}, not the claimed $claimed")
    yield last

  private def premises(r: Rule): List[Thm] = r match
    case AndI(a, b) => List(a, b)
    case AndE1(t) => List(t)
    case AndE2(t) => List(t)
    case OrI1(t, _) => List(t)
    case OrI2(_, t) => List(t)
    case OrE(t, l, rt) => List(t, l, rt)
    case ImpI(_, t) => List(t)
    case ImpE(i, a) => List(i, a)
    case NotI(_, t) => List(t)
    case NotE(n, t) => List(n, t)
    case Classic(t) => List(t)
    case FalseE(t, _) => List(t)
    case AllI(_, t) => List(t)
    case AllE(t, _) => List(t)
    case ExI(_, _, _, t) => List(t)
    case ExE(e, _, t) => List(e, t)
    case Subst(eq, _, _, t) => List(eq, t)
    case Induct(_, _, b, s) => List(b, s)
    case LinComb(ps) => ps.map(_._1)
    case Antisym(a, b) => List(a, b)
    case Tighten(t) => List(t)
    case MulNonneg(a, b) => List(a, b)
    case _ => Nil

  private def node(r: Rule, p: List[Int]): Json =
    import Codec.{formula as f, term as t, variable as v}
    def ids(ns: (String, Int)*) = ns.map((k, i) => k -> Json.Num(i.toString)).toList
    val name = r.productPrefix
    val fields: List[(String, Json)] = r match
      case Assume(g) => List("f" -> f(g))
      case Axiom(n) => List("name" -> Json.Str(n))
      case Compute(g) => List("f" -> f(g))
      case OrI1(_, g) => List("right" -> f(g))
      case OrI2(g, _) => List("left" -> f(g))
      case ImpI(g, _) => List("f" -> f(g))
      case NotI(g, _) => List("f" -> f(g))
      case FalseE(_, g) => List("f" -> f(g))
      case AllI(x, _) => List("x" -> v(x))
      case AllE(_, by) => List("by" -> t(by))
      case ExI(x, g, by, _) => List("x" -> v(x), "f" -> f(g), "by" -> t(by))
      case ExE(_, y, _) => List("y" -> v(y))
      case Refl(u) => List("t" -> t(u))
      case Subst(_, x, g, _) => List("x" -> v(x), "f" -> f(g))
      case Induct(x, g, _, _) => List("x" -> v(x), "f" -> f(g))
      case Norm(g) => List("f" -> f(g))
      case Square(u) => List("t" -> t(u))
      case LinComb(ps) => List("by" -> Json.Arr(ps.map((_, c) => Json.Str(c.bigDecimal.toPlainString))))
      case _ => Nil
    Json.Obj(("rule" -> Json.Str(name)) :: ("of" -> Json.Arr(p.map(i => Json.Num(i.toString)))) :: fields)

  private def rule(s: Json, done: Vector[Thm]): Either[String, Rule] =
    import Codec.{formula as f, term as t, variable as v}
    def field(k: String): Either[String, Json] = s.get(k).toRight(s"a step without '$k'")
    val of: Either[String, List[Thm]] = field("of").flatMap {
      case Json.Arr(xs) => xs.foldLeft[Either[String, List[Thm]]](Right(Nil)) { (acc, j) =>
          acc.flatMap(l => j match
            case Json.Num(n) => n.toIntOption.filter(i => i >= 0 && i < done.length).map(done)
              .toRight(s"a premise $n not proved before").map(l :+ _)
            case _ => Left("a premise that is not a number"))
        }
      case _ => Left("'of' not a list")
    }
    def fm(k: String) = field(k).flatMap(f)
    of.flatMap { p =>
      (field("rule").toOption, p) match
        case (Some(Json.Str("Assume")), Nil) => fm("f").map(Assume(_))
        case (Some(Json.Str("Axiom")), Nil) => field("name").flatMap {
            case Json.Str(n) => Right(Axiom(n))
            case _ => Left("an axiom's name not a string")
          }
        case (Some(Json.Str("Compute")), Nil) => fm("f").map(Compute(_))
        case (Some(Json.Str("AndI")), List(a, b)) => Right(AndI(a, b))
        case (Some(Json.Str("AndE1")), List(a)) => Right(AndE1(a))
        case (Some(Json.Str("AndE2")), List(a)) => Right(AndE2(a))
        case (Some(Json.Str("OrI1")), List(a)) => fm("right").map(OrI1(a, _))
        case (Some(Json.Str("OrI2")), List(a)) => fm("left").map(OrI2(_, a))
        case (Some(Json.Str("OrE")), List(a, b, c)) => Right(OrE(a, b, c))
        case (Some(Json.Str("ImpI")), List(a)) => fm("f").map(ImpI(_, a))
        case (Some(Json.Str("ImpE")), List(a, b)) => Right(ImpE(a, b))
        case (Some(Json.Str("NotI")), List(a)) => fm("f").map(NotI(_, a))
        case (Some(Json.Str("NotE")), List(a, b)) => Right(NotE(a, b))
        case (Some(Json.Str("Classic")), List(a)) => Right(Classic(a))
        case (Some(Json.Str("FalseE")), List(a)) => fm("f").map(FalseE(a, _))
        case (Some(Json.Str("AllI")), List(a)) => field("x").flatMap(v).map(AllI(_, a))
        case (Some(Json.Str("AllE")), List(a)) => field("by").flatMap(t).map(AllE(a, _))
        case (Some(Json.Str("ExI")), List(a)) =>
          for x <- field("x").flatMap(v); g <- fm("f"); by <- field("by").flatMap(t) yield ExI(x, g, by, a)
        case (Some(Json.Str("ExE")), List(a, b)) => field("y").flatMap(v).map(ExE(a, _, b))
        case (Some(Json.Str("Refl")), Nil) => field("t").flatMap(t).map(Refl(_))
        case (Some(Json.Str("Subst")), List(a, b)) => for x <- field("x").flatMap(v); g <- fm("f") yield Subst(a, x, g, b)
        case (Some(Json.Str("Induct")), List(a, b)) =>
          for x <- field("x").flatMap(v); g <- fm("f") yield Induct(x, g, a, b)
        case (Some(Json.Str("Norm")), Nil) => fm("f").map(Norm(_))
        case (Some(Json.Str("LinComb")), ps) if ps.nonEmpty => field("by").flatMap {
            case Json.Arr(cs) if cs.length == ps.length =>
              cs.foldRight[Either[String, List[BigDecimal]]](Right(Nil)) {
                case (Json.Str(c), acc) => acc.flatMap(l => scala.util.Try(BigDecimal(c, java.math.MathContext.UNLIMITED))
                    .toOption.toRight(s"not a coefficient: $c").map(_ :: l))
                case (_, _) => Left("a coefficient that is not a string")
              }.map(cs => LinComb(ps.zip(cs)))
            case _ => Left("as many coefficients as premises")
          }
        case (Some(Json.Str("Antisym")), List(a, b)) => Right(Antisym(a, b))
        case (Some(Json.Str("Tighten")), List(a)) => Right(Tighten(a))
        case (Some(Json.Str("MulNonneg")), List(a, b)) => Right(MulNonneg(a, b))
        case (Some(Json.Str("Square")), Nil) => field("t").flatMap(t).map(Square(_))
        case (r, _) => Left(s"not a step: ${r.map(_.render).getOrElse("no rule")} of ${p.length} premises")
    }

/** formulas and terms as JSON: `["and", a, b]`, `["v", "x", "Int"]`, `["ap", "limit", ["#Role"], "Dec", [args]]` */
object Codec:
  import Formula.*
  import Term.*

  def sort(s: Sort): Json = Json.Str(s match
    case Sort.Int => "Int"
    case Sort.Dec => "Dec"
    case Sort.Str => "Str"
    case Sort.Named(n) => "#" + n)

  def sort(j: Json): Either[String, Sort] = j match
    case Json.Str("Int") => Right(Sort.Int)
    case Json.Str("Dec") => Right(Sort.Dec)
    case Json.Str("Str") => Right(Sort.Str)
    case Json.Str(n) if n.startsWith("#") => Right(Sort.Named(n.drop(1)))
    case other => Left(s"not a sort: ${other.render}")

  def variable(x: V): Json = Json.Arr(List(Json.Str("v"), Json.Str(x.name), sort(x.sort)))
  def variable(j: Json): Either[String, V] = term(j).flatMap {
    case x: V => Right(x)
    case other => Left(s"not a variable: $other")
  }

  def term(t: Term): Json = t match
    case V(n, s) => Json.Arr(List(Json.Str("v"), Json.Str(n), sort(s)))
    case I(v) => Json.Arr(List(Json.Str("i"), Json.Str(v.toString)))
    case D(v) => Json.Arr(List(Json.Str("d"), Json.Str(v.bigDecimal.toPlainString)))
    case S(v) => Json.Arr(List(Json.Str("s"), Json.Str(v)))
    case Ap(fn, as) => Json.Arr(List(Json.Str("ap"), Json.Str(fn.name), Json.Arr(fn.args.map(sort)), sort(fn.result),
      Json.Arr(as.map(term))))

  def term(j: Json): Either[String, Term] = j match
    case Json.Arr(List(Json.Str("v"), Json.Str(n), s)) => sort(s).map(V(n, _))
    case Json.Arr(List(Json.Str("i"), Json.Str(v))) => v.toIntOption.map(BigInt(_)).orElse(scala.util.Try(BigInt(v)).toOption)
        .map(I(_)).toRight(s"not an integer: $v")
    case Json.Arr(List(Json.Str("d"), Json.Str(v))) => scala.util.Try(BigDecimal(v, java.math.MathContext.UNLIMITED))
        .toOption.map(D(_)).toRight(s"not a decimal: $v")
    case Json.Arr(List(Json.Str("s"), Json.Str(v))) => Right(S(v))
    case Json.Arr(List(Json.Str("ap"), Json.Str(n), Json.Arr(ss), r, Json.Arr(as))) =>
      for
        args <- each(ss)(sort)
        res <- sort(r)
        ts <- each(as)(term)
      yield Ap(Fn(n, args, res), ts)
    case other => Left(s"not a term: ${other.render}")

  def formula(f: Formula): Json =
    def op(name: String, xs: Json*) = Json.Arr(Json.Str(name) :: xs.toList)
    f match
      case True => op("true")
      case False => op("false")
      case Eq(a, b) => op("=", term(a), term(b))
      case Lt(a, b) => op("<", term(a), term(b))
      case Le(a, b) => op("<=", term(a), term(b))
      case P(p, as) => op("p", Json.Str(p.name), Json.Arr(p.args.map(sort)), Json.Arr(as.map(term)))
      case Not(g) => op("not", formula(g))
      case And(a, b) => op("and", formula(a), formula(b))
      case Or(a, b) => op("or", formula(a), formula(b))
      case Imp(a, b) => op("imp", formula(a), formula(b))
      case All(x, g) => op("all", variable(x), formula(g))
      case Ex(x, g) => op("ex", variable(x), formula(g))

  def formula(j: Json): Either[String, Formula] = j match
    case Json.Arr(Json.Str(name) :: xs) => (name, xs) match
      case ("true", Nil) => Right(True)
      case ("false", Nil) => Right(False)
      case ("=", List(a, b)) => for x <- term(a); y <- term(b) yield Eq(x, y)
      case ("<", List(a, b)) => for x <- term(a); y <- term(b) yield Lt(x, y)
      case ("<=", List(a, b)) => for x <- term(a); y <- term(b) yield Le(x, y)
      case ("p", List(Json.Str(n), Json.Arr(ss), Json.Arr(as))) =>
        for args <- each(ss)(sort); ts <- each(as)(term) yield P(Pred(n, args), ts)
      case ("not", List(a)) => formula(a).map(Not(_))
      case ("and", List(a, b)) => for x <- formula(a); y <- formula(b) yield And(x, y)
      case ("or", List(a, b)) => for x <- formula(a); y <- formula(b) yield Or(x, y)
      case ("imp", List(a, b)) => for x <- formula(a); y <- formula(b) yield Imp(x, y)
      case ("all", List(x, a)) => for v <- variable(x); g <- formula(a) yield All(v, g)
      case ("ex", List(x, a)) => for v <- variable(x); g <- formula(a) yield Ex(v, g)
      case _ => Left(s"not a formula: ${j.render}")
    case _ => Left(s"not a formula: ${j.render}")

  private def each[A](js: List[Json])(f: Json => Either[String, A]): Either[String, List[A]] =
    js.foldRight[Either[String, List[A]]](Right(Nil))((j, acc) => for a <- f(j); l <- acc yield a :: l)

/** JSON, small: what certificates are written in */
enum Json:
  case Null
  case Bool(b: Boolean)
  case Num(text: String)
  case Str(s: String)
  case Arr(xs: List[Json])
  case Obj(fields: List[(String, Json)])

  def get(k: String): Option[Json] = this match
    case Obj(fs) => fs.collectFirst { case (`k`, v) => v }
    case _ => None

  def render: String =
    val b = StringBuilder()
    def str(s: String): Unit =
      b += '"'
      s.foreach {
        case '"' => b ++= "\\\""
        case '\\' => b ++= "\\\\"
        case '\n' => b ++= "\\n"
        case '\r' => b ++= "\\r"
        case '\t' => b ++= "\\t"
        case c if c < ' ' => b ++= f"\\u${c.toInt}%04x"
        case c => b += c
      }
      b += '"'
    def go(j: Json): Unit = j match
      case Null => b ++= "null"
      case Bool(v) => b ++= v.toString
      case Num(t) => b ++= t
      case Str(s) => str(s)
      case Arr(xs) =>
        b += '['
        xs.zipWithIndex.foreach((x, i) => { if i > 0 then b += ','; go(x) })
        b += ']'
      case Obj(fs) =>
        b += '{'
        fs.zipWithIndex.foreach { case ((k, v), i) => if i > 0 then b += ','; str(k); b += ':'; go(v) }
        b += '}'
    go(this)
    b.result()

object Json:
  def parse(s: String): Either[String, Json] =
    var i = 0
    def ws(): Unit = while i < s.length && " \n\r\t".indexOf(s(i)) >= 0 do i += 1
    def fail(what: String) = throw IllegalArgumentException(s"$what at $i")
    def value(): Json =
      ws()
      if i >= s.length then fail("end of text")
      s(i) match
        case '{' =>
          i += 1; ws()
          val fs = mutable.ListBuffer.empty[(String, Json)]
          if s(i) == '}' then i += 1
          else
            var more = true
            while more do
              ws(); val k = string(); ws()
              if s(i) != ':' then fail("':' expected")
              i += 1
              fs += k -> value(); ws()
              s(i) match
                case ',' => i += 1
                case '}' => i += 1; more = false
                case _ => fail("',' or '}' expected")
          Obj(fs.toList)
        case '[' =>
          i += 1; ws()
          val xs = mutable.ListBuffer.empty[Json]
          if s(i) == ']' then i += 1
          else
            var more = true
            while more do
              xs += value(); ws()
              s(i) match
                case ',' => i += 1
                case ']' => i += 1; more = false
                case _ => fail("',' or ']' expected")
          Arr(xs.toList)
        case '"' => Str(string())
        case 't' if s.startsWith("true", i) => i += 4; Bool(true)
        case 'f' if s.startsWith("false", i) => i += 5; Bool(false)
        case 'n' if s.startsWith("null", i) => i += 4; Null
        case c if c == '-' || c.isDigit =>
          val start = i
          while i < s.length && "+-.eE0123456789".indexOf(s(i)) >= 0 do i += 1
          Num(s.substring(start, i))
        case _ => fail("a value expected")
    def string(): String =
      if s(i) != '"' then fail("'\"' expected")
      i += 1
      val b = StringBuilder()
      while s(i) != '"' do
        if s(i) == '\\' then
          i += 1
          s(i) match
            case 'n' => b += '\n'
            case 't' => b += '\t'
            case 'r' => b += '\r'
            case 'b' => b += '\b'
            case 'f' => b += '\f'
            case 'u' => b += Integer.parseInt(s.substring(i + 1, i + 5), 16).toChar; i += 4
            case c => b += c
        else b += s(i)
        i += 1
      i += 1
      b.result()
    try
      val j = value()
      ws()
      if i != s.length then Left(s"text after the JSON value at $i") else Right(j)
    catch
      case e: IllegalArgumentException => Left(e.getMessage)
      case _: IndexOutOfBoundsException => Left("the text ends inside a value")

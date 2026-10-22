package okay.proof

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*
import Formula.*
import Rule.*
import Term.*

/** certificates of every kind this prover makes: its tests' proofs, the lemmas, the Omega test's, one of each rule */
object Corpus:
  private def get(e: Either[String, Option[Thm]]): Option[Thm] = e.toOption.flatten

  def all: List[(String, Thm)] =
    import Bank.*
    val policyK = Kernel(policy)
    val bounded = facts.map { case Eq(s, v) if s == spent(ann) => Le(spent(ann), v); case f => f }
    val policies = List("500.00", "1000.00", "999.99").flatMap(a => get(Auto.prove(policyK, facts, transfer(ann, acc1, a))).map(s"policy $a" -> _)) ++
      get(Auto.prove(policyK, bounded, transfer(ann, acc1, "900.00"))).map("policy from bounds" -> _)
    val k = Kernel(Theory.empty)
    val (x, y, z, w) = (V("x", Sort.Int), V("y", Sort.Int), V("z", Sort.Int), V("w", Sort.Int))
    val (a, b, p, q) = (V("a", Sort.Dec), V("b", Sort.Dec), V("p", Sort.Dec), V("q", Sort.Dec))
    def add(s: Term, t: Term) = Ap(Fns.add, List(s, t))
    def mul(n: Int, s: Term): Term = Ap(Fns.mul, List(I(n), s))
    def lin2(m: Int, s: Term, n: Int, t: Term) = add(mul(m, s), mul(n, t))
    def d(v: String): Term = D(BigDecimal(v))
    def arith(name: String, goal: Formula, fs: Formula*) = get(Linarith.decide(k, goal, fs.toList)).map(name -> _)
    val falsum = Lt(I(1), I(0))
    val arithmetic = List(
      arith("chain", Le(x, w), Le(x, y), Le(y, z), Le(z, w)),
      arith("strict", Lt(x, z), Lt(x, y), Le(y, z)),
      arith("equation", Eq(x, I(4)), Eq(x, add(y, I(1))), Eq(y, I(3))),
      arith("decimals", Eq(Ap(Fns.dadd, List(a, b)), d("0.30")), Eq(a, d("0.10")), Eq(b, d("0.20"))),
      arith("integers", Not(Lt(x, y)), Lt(y, add(x, I(1)))),
      arith("cut", falsum, Eq(mul(2, x), I(1))),
      arith("pugh", falsum, Le(I(27), lin2(11, x, 13, y)), Le(lin2(11, x, 13, y), I(45)),
        Le(I(-10), lin2(7, x, -9, y)), Le(lin2(7, x, -9, y), I(4))),
      arith("mod-hat", falsum, Eq(lin2(3, x, 5, y), I(1)), Le(I(0), x), Le(x, I(1)), Le(I(0), y), Le(y, I(1))),
      arith("gcd", falsum, Eq(lin2(6, x, 9, y), I(4))),
      arith("x·y", Le(I(0), Ap(Fns.mul, List(x, y))), Le(I(0), x), Le(I(0), y)),
      arith("p·q", Le(Ap(Fns.dmul, List(p, q)), d("50.00")), Le(d("0"), p), Le(p, d("10.00")), Le(d("0"), q), Le(q, d("5"))),
      arith("4 ≤ x·x", Le(I(4), Ap(Fns.mul, List(x, x))), Le(I(2), x)),
      arith("0 ≤ p²", Le(d("0"), Ap(Fns.dmul, List(p, p))))).flatten
    val rnd = scala.util.Random(11)
    val strips = (1 to 120).flatMap { i =>
      def c() = (3 + rnd.nextInt(13)) * (if rnd.nextBoolean() then 1 else -1)
      val (a1, b1, a2, b2) = (c(), c(), c(), c())
      val (l1, w1, l2, w2) = (rnd.nextInt(81) - 40, rnd.nextInt(7), rnd.nextInt(81) - 40, rnd.nextInt(7))
      val box = List(x, y).flatMap(v => List(Le(I(-40), v), Le(v, I(40))))
      arith(s"strip $i", falsum, (box ++ List(Le(I(l1), lin2(a1, x, b1, y)), Le(lin2(a1, x, b1, y), I(l1 + w1)),
        Le(I(l2), lin2(a2, x, b2, y)), Le(lin2(a2, x, b2, y), I(l2 + w2))))*)
    }.take(40)
    val lemmas = Lemmas(Kernel(Theory.empty))
    val pp = P(Pred("open", Nil), Nil)
    val qq = P(Pred("funded", Nil), Nil)
    val schemas = List("excludedMiddle" -> lemmas.excludedMiddle(pp), "contrapositive" -> lemmas.contrapositive(pp, qq),
      "deMorganAnd" -> lemmas.deMorganAnd(pp, qq), "deMorganOr" -> lemmas.deMorganOr(pp, qq),
      "eqSym Account" -> lemmas.eqSym(Sort.Named("Account")))
    // FalseE, and induction (Induct, Axiom), by hand
    def ok(kk: Kernel, r: Rule) = kk.derive(r).toOption.get
    val contra = ok(k, NotE(ok(k, Compute(Not(Lt(I(1), I(0))))), ok(k, Assume(Lt(I(1), I(0))))))
    val exFalso = ok(k, ImpI(Lt(I(1), I(0)), ok(k, FalseE(contra, Eq(I(5), I(6))))))
    val sumFn = Fn("sum", List(Sort.Int), Sort.Int)
    def sum(t: Term) = Ap(sumFn, List(t))
    val n = V("n", Sort.Int)
    val sums = Theory("sums", "sum0" -> Eq(sum(I(0)), I(0)),
      "sumS" -> All(n, Imp(Le(I(0), n), Eq(sum(add(n, I(1))), add(sum(n), add(n, I(1)))))))
    val ks = Kernel(sums)
    val f = Le(I(0), sum(x))
    val base = get(Linarith.decide(ks, Le(I(0), sum(I(0))), Nil, List(ok(ks, Axiom("sum0"))))).get
    val hyp = And(Le(I(0), x), f)
    val h = ok(ks, Assume(hyp))
    val unfold = ok(ks, ImpE(ok(ks, AllE(ok(ks, Axiom("sumS")), x)), ok(ks, AndE1(h))))
    val next = get(Linarith.decide(ks, Le(I(0), sum(add(x, I(1)))), Nil, List(ok(ks, AndE1(h)), ok(ks, AndE2(h)), unfold))).get
    val induction = ok(ks, Induct(x, f, base, ok(ks, AllI(x, ok(ks, ImpI(hyp, next))))))
    policies ++ arithmetic ++ strips ++ lemmas.all ++ schemas ++ List("ex falso" -> exFalso, "induction" -> induction)

/** okay-lean's checker against this kernel: every certificate and its mutants, the same verdict from both */
class DifferentialSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(600, "s")
  val checker: Path = Paths.get(sys.env.getOrElse("OKAY_LEAN", sys.props("user.home") + "/work/my/okay-lean"))
    .resolve(".lake/build/bin/okay-check")
  override def munitIgnore: Boolean = !Files.isExecutable(checker)

  /** a JSON tree with its n-th node satisfying `p` replaced by `f` of it; the count of such nodes */
  def nodes(j: Json, p: Json => Boolean): Int =
    (if p(j) then 1 else 0) + (j match
      case Json.Arr(xs) => xs.map(nodes(_, p)).sum
      case Json.Obj(fs) => fs.map(f => nodes(f._2, p)).sum
      case _ => 0)
  def replace(j: Json, p: Json => Boolean, n: Int, f: Json => Json): Json =
    var i = -1
    def go(j: Json): Json =
      val here = if p(j) then { i += 1; i == n } else false
      if here then f(j)
      else j match
        case Json.Arr(xs) => Json.Arr(xs.map(go))
        case Json.Obj(fs) => Json.Obj(fs.map((k, v) => k -> go(v)))
        case other => other
    go(j)
  def set(j: Json, key: String, v: Json): Json = j match
    case Json.Obj(fs) => Json.Obj(fs.map((k, x) => if k == key then k -> v else k -> x))
    case other => other

  def mutants(cert: String, rnd: scala.util.Random): List[(String, String)] =
    val j = Json.parse(cert).toOption.get
    val Json.Arr(steps) = j.get("steps").get: @unchecked
    val literal: Json => Boolean = {
      case Json.Arr(List(Json.Str("i" | "d"), Json.Str(_))) => true
      case _ => false
    }
    def bump(x: Json): Json = x match
      case Json.Arr(List(Json.Str("i"), Json.Str(v))) => Json.Arr(List(Json.Str("i"), Json.Str((BigInt(v) + 1).toString)))
      case Json.Arr(List(Json.Str("d"), Json.Str(v))) => Json.Arr(List(Json.Str("d"), Json.Str(Logic.plain((BigDecimal(v) + 1).bigDecimal))))
      case other => other
    val out = List.newBuilder[(String, String)]
    val lits = nodes(Json.Arr(steps), literal)
    if lits > 0 then
      out += "a literal" -> set(j, "steps", replace(Json.Arr(steps), literal, rnd.nextInt(lits), bump)).render
    val withPremise = steps.zipWithIndex.filter((s, i) => i > 1 && s.get("of").exists { case Json.Arr(xs) => xs.nonEmpty; case _ => false })
    if withPremise.nonEmpty then
      val (s, i) = withPremise(rnd.nextInt(withPremise.length))
      val Json.Arr(of) = s.get("of").get: @unchecked
      val changed = of.updated(rnd.nextInt(of.length), Json.Num(rnd.nextInt(i).toString))
      out += "a premise" -> set(j, "steps", Json.Arr(steps.updated(i, set(s, "of", Json.Arr(changed))))).render
    val combs = steps.zipWithIndex.filter((s, _) => s.get("rule").contains(Json.Str("LinComb")))
    if combs.nonEmpty then
      val (s, i) = combs(rnd.nextInt(combs.length))
      val Json.Arr(cs) = s.get("by").get: @unchecked
      val at = rnd.nextInt(cs.length)
      val Json.Str(c) = cs(at): @unchecked
      out += "a coefficient" -> set(j, "steps", Json.Arr(steps.updated(i,
        set(s, "by", Json.Arr(cs.updated(at, Json.Str((BigDecimal(c) + 1).bigDecimal.toPlainString))))))).render
    val swaps = steps.zipWithIndex.filter((s, _) => s.get("rule").exists(r => r == Json.Str("AndE1") || r == Json.Str("AndE2")))
    if swaps.nonEmpty then
      val (s, i) = swaps(rnd.nextInt(swaps.length))
      val other = if s.get("rule").contains(Json.Str("AndE1")) then "AndE2" else "AndE1"
      out += "a rule" -> set(j, "steps", Json.Arr(steps.updated(i, set(s, "rule", Json.Str(other))))).render
    if steps.length > 2 then
      val at = rnd.nextInt(steps.length - 1)
      out += "a step dropped" -> set(j, "steps", Json.Arr(steps.patch(at, Nil, 1))).render
    out += "the conclusion" -> set(j, "conclusion", Json.Arr(List(Json.Str("not"), j.get("conclusion").get))).render
    j.get("hypotheses") match
      case Some(Json.Arr(h :: rest)) => out += "a hypothesis dropped" -> set(j, "hypotheses", Json.Arr(rest)).render
      case _ => out += "a hypothesis added" -> set(j, "hypotheses", Json.Arr(List(Json.Arr(List(Json.Str("true")))))).render
    val Json.Str(dg) = j.get("digest").get: @unchecked
    out += "the digest" -> set(j, "digest", Json.Str(dg.init + (if dg.last == '0' then "1" else "0"))).render
    j.get("axioms") match
      case Some(ax @ Json.Arr(_ :: _)) if nodes(ax, literal) > 0 =>
        val changed = replace(ax, literal, 0, bump)
        val th = Certificate.theory(set(set(j, "axioms", changed), "digest", Json.Str("")).render)
        // the axioms changed and the digest made theirs: a certificate of another theory, the proof the same
        val name = j.get("theory").collect { case Json.Str(n) => n }.get
        val pairs = changed match
          case Json.Arr(xs) => xs.collect { case Json.Arr(List(Json.Str(n), f)) => n -> Codec.formula(f).toOption.get }
          case _ => Nil
        out += "an axiom, its digest recomputed" -> set(set(j, "axioms", changed), "digest",
          Json.Str(Certificate.digest(Theory(name, pairs*)))).render
      case _ => ()
    out.result()

  test("okay-lean's checker and this kernel agree: every certificate accepted alike, every mutant judged alike") {
    val corpus = Corpus.all
    // every rule of the kernel in some certificate
    val rules = corpus.flatMap((_, t) => "\"rule\":\"(\\w+)\"".r.findAllMatchIn(Certificate.of(t)).map(_.group(1))).toSet
    assertEquals(rules, Set("Assume", "Axiom", "Compute", "AndI", "AndE1", "AndE2", "OrI1", "OrI2", "OrE", "ImpI", "ImpE",
      "NotI", "NotE", "Classic", "FalseE", "AllI", "AllE", "ExI", "ExE", "Refl", "Subst", "Induct", "Norm", "LinComb",
      "Antisym", "Tighten", "MulNonneg", "Square"))
    val dir = Files.createTempDirectory("okay-proof-certs")
    val rnd = scala.util.Random(2026)
    val cases = corpus.zipWithIndex.flatMap { case ((name, t), i) =>
      val cert = Certificate.of(t)
      (s"$name" -> cert) :: mutants(cert, rnd).map((kind, text) => s"$name, $kind" -> text)
    }.zipWithIndex.map { case ((label, text), i) =>
      val f = dir.resolve(f"$i%05d.json")
      Files.writeString(f, text)
      (f.toString, label, text)
    }
    val t0 = System.nanoTime()
    val p = ProcessBuilder((checker.toString :: cases.map(_._1)).asJava).redirectErrorStream(true).start()
    val lines = String(p.getInputStream.readAllBytes()).linesIterator.toList
    p.waitFor()
    val leanMs = (System.nanoTime() - t0) / 1_000_000
    val lean = lines.flatMap(l => Json.parse(l).toOption).map(j => j.get("file").collect { case Json.Str(f) => f }.get -> j).toMap
    assertEquals(lean.size, cases.length, lines.take(3).mkString("\n"))
    var (accepted, refused) = (0, 0)
    for (file, label, text) <- cases do
      val scala = Certificate.checkAlone(text)
      val l = lean(file)
      val leanOk = l.get("ok").contains(Json.Bool(true))
      assertEquals(leanOk, scala.isRight, s"$label: this kernel says ${scala.left.toOption.getOrElse("yes")}, okay-lean says ${l.render}")
      scala match
        case Right(t) =>
          accepted += 1
          assertEquals(l.get("conclusion").map(_.render), Some(Codec.formula(t.concl).render), label)
          assertEquals(l.get("digest"), Some(Json.Str(Certificate.digest(t.kernel.theory))), label)
          assertEquals(l.get("hypotheses"), Some(Json.Num(t.hyps.size.toString)), label)
        case Left(_) => refused += 1
    println(s"${cases.length} certificates (${corpus.length} proofs and their mutants): $accepted accepted, $refused refused by both; okay-lean checked them in $leanMs ms")
    assert(accepted >= corpus.length && refused > corpus.length * 4, s"accepted $accepted, refused $refused")
  }

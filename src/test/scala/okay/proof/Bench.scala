package okay.proof

import Bank.*
import Formula.*
import Rule.*
import Term.*

/** what a prover in the run costs: `sbt "Test/runMain okay.proof.Bench"` — each lane warmed, then timed; the
 * median of five rounds */
object Bench:
  def time(name: String, n: Int)(body: => Any): Unit =
    var sink: Any = null
    def round(): Double =
      val t0 = System.nanoTime()
      var i = 0
      while i < n do { sink = body; i += 1 }
      (System.nanoTime() - t0).toDouble / n
    for _ <- 1 to 3 do round()
    val rs = (1 to 5).map(_ => round()).sorted
    println(f"$name%-62s ${rs(2)}%10.0f ns   (${rs.head}%.0f–${rs.last}%.0f)")
    if sink == null then println("")

  def main(args: Array[String]): Unit =
    val k = Kernel(policy)
    val a = k.derive(Compute(Lt(I(2), I(5)))).toOption.get
    val ax = k.derive(Axiom("transfer")).toOption.get
    val money = Eq(Ap(Fns.round, List(Ap(Fns.dmul, List(dec("1234.567"), dec("0.19"))), I(2))), dec("234.57"))
    val goal = transfer(ann, acc1, "500.00")
    val proof = Auto.prove(k, facts, goal).toOption.flatten.get
    val cert = Certificate.of(proof)
    println(s"the decision's proof: ${steps(proof)} steps, its certificate ${cert.length} bytes")
    time("a step: ∧ of two theorems", 2_000_000)(k.derive(AndI(a, a)))
    time("a step: compute round(1234.567 · 0.19, 2) = 234.57, exact", 1_000_000)(k.derive(Compute(money)))
    time("a step: ∀ out, the policy's first variable", 1_000_000)(k.derive(AllE(ax, ann)))
    time("a DECISION: transfer allowed, searched on effects, proved", 50_000)(Auto.prove(k, facts, goal))
    time("a decision refused: no proof, every branch tried", 50_000)(Auto.prove(k, facts, transfer(ann, acc1, "1250.00")))
    val bounded = facts.map {
      case Eq(s, v) if s == spent(ann) => Le(spent(ann), v)
      case f => f
    }
    time("a DECISION from bounds: spent(ann) ≤ 300, linear arithmetic", 50_000)(Auto.prove(k, bounded, transfer(ann, acc1, "900.00")))
    val (x, y, z, w) = (V("x", Sort.Int), V("y", Sort.Int), V("z", Sort.Int), V("w", Sort.Int))
    val empty = Kernel(Theory.empty)
    time("Linarith: x ≤ y, y ≤ z, z ≤ w ⊢ x ≤ w (Int)", 100_000)(Linarith.decide(empty, Le(x, w), List(Le(x, y), Le(y, z), Le(z, w))))
    time("Linarith: 2x = 1 ⊢ false (Int, a cut)", 100_000)(Linarith.decide(empty, Lt(I(1), I(0)), List(Eq(Ap(Fns.mul, List(I(2), x)), I(1)))))
    val (a2, b2) = (V("a", Sort.Dec), V("b", Sort.Dec))
    time("Linarith: a = 0.10, b = 0.20 ⊢ a + b = 0.30 (Dec, two refutations)", 100_000)(
      Linarith.decide(empty, Eq(Ap(Fns.dadd, List(a2, b2)), dec("0.30")), List(Eq(a2, dec("0.10")), Eq(b2, dec("0.20")))))
    time("Norm: x + y = y + x, one step", 1_000_000)(empty.derive(Norm(Eq(Ap(Fns.add, List(x, y)), Ap(Fns.add, List(y, x))))))
    time("the lemma library: 42 lemmas proved", 200)(Lemmas(Kernel(Theory.empty)).all)
    time("its certificate written (JSON)", 50_000)(Certificate.of(proof))
    time("its certificate checked: parsed, every step derived again", 50_000)(Certificate.check(cert, k))

  def steps(t: Thm): Int =
    val seen = java.util.IdentityHashMap[Thm, Unit]()
    def go(t: Thm): Unit = if !seen.containsKey(t) then
      seen.put(t, ())
      t.by match
        case AndI(x, y) => go(x); go(y)
        case ImpE(x, y) => go(x); go(y)
        case AllE(x, _) => go(x)
        case Subst(x, _, _, y) => go(x); go(y)
        case _ => ()
    go(t)
    seen.size

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

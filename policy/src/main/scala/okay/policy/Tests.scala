package okay.policy

import okay.scala3.*

/** a test's outcome: passed, or what was decided instead */
final case class Outcome(test: TTest, decision: Decision):
  def passed: Boolean =
    decision.verdict == test.expect && test.because.forall(b => decision.reasons.contains(b))
  override def toString: String =
    (if passed then "passed" else s"FAILED: expected ${test.expect.word}${test.because.fold("")(b => s" \"$b\"")}, " +
      s"decided $decision") + s" — ${test.name}"

/** A POLICY'S TESTS RUN: each test's `given` its facts and states, in memory; its call decided */
object Tests:
  def run(policy: Compiled): List[Outcome] = policy.checked.tests.map(one(policy, _))

  def one(policy: Compiled, t: TTest): Outcome =
    val facts = t.givens.filter(g => policy.checked.facts.contains(g.name)).map { g =>
      FactRef(g.name, g.args) -> g.value.fold(Answer.Holds(_), Answer.Is(_))
    }.toMap
    val store = Store.Memory(policy.checked, () => 0L)
    t.givens.filter(g => policy.checked.states.contains(g.name)).foreach(g =>
      g.value.foreach(v => store.set(FactRef(g.name, g.args), v)))
    type Row[X] = (Store + Facts)[X]
    val call = Call(t.tool, t.caller, t.args)
    Outcome(t, okay.scala3.run(store.handler(Facts.known(facts)(Decide[Row](policy, call)))))

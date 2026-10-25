package okay.policy

import okay.scala3.*

/** what a decision costs: `sbt "policyJVM/Test/runMain okay.policy.PolicyBench"` */
object PolicyBench:
  def time(what: String, n: Int)(f: => Any): Unit =
    for _ <- 1 to n do f
    val runs = (1 to 7).map { _ =>
      val t0 = System.nanoTime()
      for _ <- 1 to n do f
      (System.nanoTime() - t0) / n
    }.sorted
    println(f"$what%-62s ${runs(3)}%8d ns   (${runs.head}–${runs.last})")

  def main(args: Array[String]): Unit =
    time("parsed and checked, the spec's policy", 20_000)(Types(Examples.payments))
    val policy = Compiled(Examples.payments).toOption.get
    val ann = Value.E("User", "ann")
    val acc1 = Value.E("Account", "acc1")
    val call = Call.flat("stripe.create_payment", ann, Map("account" -> acc1, "amount" -> Value.D(BigDecimal("50.00")),
      "currency" -> Value.T("usd")))
    val facts = Map(FactRef("owns", List(ann, acc1)) -> Answer.Holds(true),
      FactRef("balance", List(acc1)) -> Answer.Is(Value.D(BigDecimal("900.00"))))
    val store = States.Memory(policy.checked, () => 0L)
    type Row[X] = (States + Facts)[X]
    def decide = run(store.handler(Facts.known(facts)(Decide[Row](policy, call))))
    println(s"the decision: $decide, its proof's certificate ${decide.certificate.get.length} bytes")
    time("a DECISION: allow, facts asked, rules evaluated, proved", 200_000)(decide)
    val big = call.copy(args = call.args.updated("amount", Data.Leaf(Value.D(BigDecimal("800.00")))))
    time("a decision: ask (the allow tried first)", 200_000)(
      run(store.handler(Facts.known(facts)(Decide[Row](policy, big)))))
    val none = call.copy(args = call.args.updated("amount", Data.Leaf(Value.D(BigDecimal("8000.00")))))
    time("a decision: the default deny, explained", 200_000)(
      run(store.handler(Facts.known(facts)(Decide[Row](policy, none)))))
    time("its certificate written", 50_000)(decide.certificate)

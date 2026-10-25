package okay.policy

import okay.scala3.*

/** a decision timed on each platform (printed; a bound far above the JVM's ~8 µs, to catch a collapse) */
class SpeedSuite extends munit.FunSuite:
  test("a decision, timed") {
    val policy = Compiled(Examples.payments).toOption.get
    val ann = Value.E("User", "ann")
    val acc1 = Value.E("Account", "acc1")
    val call = Call("stripe.create_payment", ann, Map("account" -> acc1, "amount" -> Value.D(BigDecimal("50.00")),
      "currency" -> Value.T("usd")))
    val facts = Map(FactRef("owns", List(ann, acc1)) -> Answer.Holds(true),
      FactRef("balance", List(acc1)) -> Answer.Is(Value.D(BigDecimal("900.00"))))
    val store = States.Memory(policy.checked, () => 0L)
    type Row[X] = (States + Facts)[X]
    def decide = run(store.handler(Facts.known(facts)(Decide[Row](policy, call))))
    for _ <- 1 to 20_000 do decide
    val n = 20_000
    val t0 = System.nanoTime()
    for _ <- 1 to n do decide
    val each = (System.nanoTime() - t0) / n
    println(s"a decision, allowed and proved: $each ns")
    assert(each < 1_000_000, s"$each ns")
  }

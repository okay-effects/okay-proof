package okay.proof

import okay.proof.syntax.*
import Formula.*
import Term.*

/** the syntax builds what the constructors build, reads as Scala's precedence says, and refuses a wrong sort */
class SyntaxSuite extends munit.FunSuite:
  import Bank.{ann, acc1, teller, hasRole, mayUse, mayTransfer, limitFn, dailyFn, spentFn, u, r, a, amt}

  test("the bank's policy, written as it reads, is the policy"):
    val policy = forall(u, r, a, amt)(
      hasRole(u, r) && mayUse(r, a) && amt <= limitFn(r) && spentFn(u) + amt <= dailyFn(r)
        implies mayTransfer(u, a, amt))
    assertEquals(policy, Bank.policy.axioms("transfer"))

  test("a literal takes the sort of its place"):
    assertEquals(mayTransfer(ann, acc1, 700), Bank.transfer(ann, acc1, "700"))
    assertEquals(mayTransfer(ann, acc1, 700.01), Bank.transfer(ann, acc1, "700.01"))
    assertEquals(spentFn(ann) <= 300, Le(Bank.spent(ann), D(BigDecimal(300))))
    val n = v("n", Sort.Int)
    assertEquals(n * 2 + 1 > n, Lt(n, Ap(Fns.add, List(Ap(Fns.mul, List(n, I(2))), I(1)))))
    assertEquals(-n === 3, Eq(Ap(Fns.neg, List(n)), I(3)))
    assertEquals(str("a") + "b" =/= "ab", Not(Eq(Ap(Fns.concat, List(S("a"), S("b"))), S("ab"))))

  test("decisions from the syntax"):
    val k = Kernel(Bank.policy)
    val facts = List(hasRole(ann, teller), mayUse(teller, acc1), limitFn(teller) === 1000, dailyFn(teller) === 1500,
      spentFn(ann) <= 300)
    assert(Auto.prove(k, facts, mayTransfer(ann, acc1, 1000)).toOption.flatten.isDefined)
    assertEquals(Auto.prove(k, facts, mayTransfer(ann, acc1, 1000.01)), Right(None))

  test("a wrong sort is refused at once"):
    val n = v("n", Sort.Int)
    intercept[IllegalArgumentException](n + 1.5)
    intercept[IllegalArgumentException](n < amt)
    intercept[IllegalArgumentException](mayTransfer(acc1, ann, 1))
    intercept[IllegalArgumentException](mayTransfer(ann, acc1))
    intercept[IllegalArgumentException](spentFn("ann"))
    intercept[IllegalArgumentException](u + u)

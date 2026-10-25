package okay.proof

import Formula.*
import Term.*

/** the tests' words: a bank's sorts, constants, functions of one's own and predicates, and its transfer policy */
object Bank:
  val User = Sort.Named("User")
  val Role = Sort.Named("Role")
  val Account = Sort.Named("Account")

  def const(name: String, sort: Sort): Term = Ap(Fn(name, Nil, sort), Nil)
  val ann = const("ann", User)
  val bob = const("bob", User)
  val teller = const("teller", Role)
  val acc1 = const("acc1", Account)
  val acc2 = const("acc2", Account)

  val hasRole = Pred("hasRole", List(User, Role))
  val mayUse = Pred("mayUse", List(Role, Account))
  val mayTransfer = Pred("mayTransfer", List(User, Account, Sort.Dec))
  val limitFn = Fn("limit", List(Role), Sort.Dec)
  val dailyFn = Fn("daily", List(Role), Sort.Dec)
  val spentFn = Fn("spent", List(User), Sort.Dec)
  def limit(r: Term) = Ap(limitFn, List(r))
  def daily(r: Term) = Ap(dailyFn, List(r))
  def spent(u: Term) = Ap(spentFn, List(u))

  def dec(s: String): Term = D(BigDecimal(s))
  def plus(a: Term, b: Term): Term = Ap(Fns.dadd, List(a, b))

  val u = V("u", User)
  val r = V("r", Role)
  val a = V("a", Account)
  val amt = V("amt", Sort.Dec)

  /** a transfer is allowed to a user of a role that may use the account, within the role's limit for one transfer
   * and its daily limit with what the user spent today */
  val policy: Theory = Theory("bank",
    "transfer" -> Formula.all(u, r, a, amt)(
      P(hasRole, List(u, r)) && P(mayUse, List(r, a)) && Le(amt, limit(r)) && Le(plus(spent(u), amt), daily(r))
        implies P(mayTransfer, List(u, a, amt))))

  /** what a request knows */
  val facts: List[Formula] = List(
    P(hasRole, List(ann, teller)),
    P(mayUse, List(teller, acc1)),
    Eq(limit(teller), dec("1000.00")),
    Eq(daily(teller), dec("1500.00")),
    Eq(spent(ann), dec("300.00")))

  def transfer(user: Term, account: Term, amount: String): Formula = P(mayTransfer, List(user, account, dec(amount)))

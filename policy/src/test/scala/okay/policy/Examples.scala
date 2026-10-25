package okay.policy

/** the tests' policies */
object Examples:
  /** specs/policy.md's example */
  val payments: String =
    """policy payments
      |
      |type User
      |type Account
      |
      |-- what the guard may ask: a fact is a function (one value) or a relation (true or not)
      |fact owns(user: User, account: Account)
      |fact role(user: User): Text
      |fact balance(account: Account): Dec from stripe
      |
      |state spent(user: User): Dec per day = 0.00
      |state calls(user: User): Int per minute = 0
      |
      |call stripe.create_payment(account: Account, amount: Dec, currency: Text)
      |call stripe.refund(payment: Text)
      |
      |allow stripe.create_payment
      |  when owns(caller, account)
      |   and currency in ["usd", "eur"]
      |   and amount <= 500.00
      |   and spent(caller) + amount <= 2000.00
      |   and amount <= balance(account)
      |  then spent(caller) += amount
      |
      |ask stripe.create_payment
      |  when owns(caller, account) and amount <= 5000.00
      |  because "a large payment"
      |
      |deny *
      |  when calls(caller) >= 60
      |  because "too many calls"
      |
      |count * then calls(caller) += 1        -- every call that goes ahead
      |
      |allow stripe.refund when role(caller) = "teller"
      |
      |""".stripMargin

  /** its tests, in their own file */
  val paymentsTests: String =
    """tests for payments
      |
      |test "a small payment is allowed"
      |  given owns(ann, acc1), role(ann) = "teller", balance(acc1) = 900.00, spent(ann) = 100.00
      |  when ann calls stripe.create_payment(account: acc1, amount: 50.00, currency: "usd")
      |  expect allow
      |
      |test "a payment over the limit of one is asked"
      |  given owns(ann, acc1), balance(acc1) = 9000.00
      |  when ann calls stripe.create_payment(account: acc1, amount: 800.00, currency: "usd")
      |  expect ask "a large payment"
      |
      |test "a payment from an account not one's own is denied"
      |  given not owns(bob, acc1), balance(acc1) = 9000.00
      |  when bob calls stripe.create_payment(account: acc1, amount: 5.00, currency: "usd")
      |  expect deny
      |""".stripMargin

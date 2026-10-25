# okay-policy — a language of policies, each decision a theorem

Status: SPEC, 2026-10-25. Module `policy` of okay-proof (a cross project: the JVM and the browser).

## Why

okay-guard stands between an agent and its MCP servers. For every call it must decide — allow, ask a human, deny — and
be able to show WHY: from which facts, by which rule. A policy is written by people (in the studio, in the browser) and
by agents (who propose and edit policies); both must read it as the business reads its rules, and both must get an
error at once when it is wrong.

So the language is:

- **small and readable**: declarations of what is known, rules of what is allowed — no general programming;
- **typed**: every fact, call argument and state has a type; a rule using a field a tool does not have, comparing an
  amount with a text, or a fact never declared, is an error in the editor, before anything runs;
- **decidable and fast**: a decision is a finite evaluation (microseconds), not a search that may not end;
- **proved**: every decision is a THEOREM of okay-proof's kernel, from the policy's axioms and the call's facts, its
  certificate written for the audit — the evaluator that finds it is not trusted, the kernel checks every step;
- **on effects**: facts come through an effect whose handlers are the request, the guard's state, an external service
  (Stripe, a database — asynchronous), or memory in a test; state changes are an effect too; the kernel's steps are
  `Infer`, seen by any interceptor;
- **everywhere**: parser, checker, evaluator and kernel are Scala 3 cross-built for the JVM and Scala.js — the same code
  in the studio's editor (live errors, live tests) and in the guard at run time (Node, a Cloudflare Worker, the JVM).
  Compiling a policy to Scala source is a later step; first a fast interpreter.

## A policy

```text
policy payments

type User
type Account

-- what the guard may ask: a fact is a function (one value) or a relation (true or not)
fact owns(user: User, account: Account)
fact role(user: User): Text
fact balance(account: Account): Dec            -- from Stripe: an external fact, asked when a rule needs it

-- state the guard keeps between calls, changed only by a rule's `then`
state spent(user: User): Dec per day = 0.00
state calls(user: User): Int per minute = 0

-- the calls this policy decides: a tool of an MCP server and its arguments' types (or imported from its schema)
call stripe.create_payment(account: Account, amount: Dec, currency: Text)
call stripe.refund(payment: Text)

-- every call has `caller: User` and `tool: Text`

allow stripe.create_payment
  when owns(caller, account)
   and currency in ["usd", "eur"]
   and amount <= 500.00
   and spent(caller) + amount <= 2000.00
   and amount <= balance(account)
  then spent(caller) += amount

ask stripe.create_payment
  when owns(caller, account) and amount <= 5000.00
  because "a large payment"

deny *
  when calls(caller) >= 60
  because "too many calls"

allow * then calls(caller) += 1        -- a rule may only count: it allows nothing alone (see Decisions)

test "a small payment is allowed"
  given owns(ann, acc1), role(ann) = "teller", balance(acc1) = 900.00, spent(ann) = 100.00
  when ann calls stripe.create_payment(account: acc1, amount: 50.00, currency: "usd")
  expect allow

test "a payment over the limit of one is asked"
  given owns(ann, acc1), balance(acc1) = 9000.00
  when ann calls stripe.create_payment(account: acc1, amount: 800.00, currency: "usd")
  expect ask "a large payment"
```

## Syntax

```text
policy    ::= "policy" name decl*
decl      ::= type | fact | state | call | rule | test
type      ::= "type" Name                                   -- an entity sort: values are names (ann, acc1)
fact      ::= "fact" name "(" params ")" (":" sort)? ("from" name)?
state     ::= "state" name "(" params ")" ":" sort ("per" window)? "=" literal
call      ::= "call" tool "(" params ")" | "import" "tools" "from" text   -- a server's JSON schema
rule      ::= verdict target ("when" cond)? ("then" update ("," update)*)? ("because" text)?
verdict   ::= "allow" | "ask" | "deny"
target    ::= tool | server ".*" | "*"
cond      ::= cond "and" cond | cond "or" cond | "not" cond | "(" cond ")" | atom
atom      ::= expr cmp expr | expr "in" "[" exprs "]" | name "(" exprs ")"      -- a relation fact
cmp       ::= "=" | "!=" | "<" | "<=" | ">" | ">="
expr      ::= expr ("+" | "-") expr | expr "*" literal | "(" expr ")" | literal | var | name "(" exprs ")"
update    ::= name "(" exprs ")" ("=" | "+=" | "-=") expr
window    ::= "minute" | "hour" | "day"
test      ::= "test" text "given" given ("," given)* "when" name "calls" tool "(" args ")" "expect" verdict text?
sort      ::= "Int" | "Dec" | "Text" | Name
literal   ::= int | dec | text
```

Comments `--` to the end of the line. Names of types start with a capital; names of facts, states, variables with a
small letter. `caller`, `tool` and the call's argument names are the variables of a rule; there are no others — a rule
has no quantifiers of its own, so a decision never searches.

Multiplication is by a literal only (`amount * 1.2`): the conditions stay LINEAR, which the kernel's arithmetic decides
completely (Fourier–Motzkin with Farkas certificates; the Omega test over `Int`).

## Types

Sorts: `Int` (unbounded), `Dec` (exact decimals: money), `Text`, and the entity types a policy declares; what is true
or not is a relation fact (`fact verified(user: User)`), not a value. The checker gives each expression a sort and refuses, with the place in the text:

- an unknown name: a fact, a state, a variable, a tool, a type;
- a call's argument used by a rule whose target does not have it (`amount` in `allow stripe.refund`);
- a comparison or sum of different sorts (`amount < currency`); an order on `Text`, `Bool` or an entity;
- a fact applied to arguments of the wrong number or sorts; a relation used as a value, a function as a condition;
- an update of a fact (only states change), or of a state with a value of another sort;
- a nonlinear product;
- `!=` between entities (the kernel has no axiom that two names are two things: equal names are provable,
  different ones are not), and a fact applied to a fact (`role(owner(account))`) — both left for later;
- a `test` naming a call, an argument or a fact the policy does not have.

`Int` and `Dec` are not mixed silently: `count * 1.5` is an error; `dec(count)` converts.

## Decisions

For a call, the rules whose target matches it (the tool's own, its server's `.*`, `*`) are candidates. A rule APPLIES
if its condition holds under the facts. Then:

1. if a `deny` applies, the call is denied;
2. otherwise, if an `allow` WITH a condition applies, it is allowed;
3. otherwise, if an `ask` applies, a human is asked;
4. otherwise it is denied: nothing is allowed without a rule that proves it (fail closed).

An `allow` without a condition (`allow * then calls(caller) += 1`) does not allow by itself: it only adds its updates
to a call allowed by another rule. Among several applying rules of one verdict, all their updates are made; the
`because` texts are all reported.

Every verdict but the last is a THEOREM: `deny(call)`, `allow(call)`, `ask(call)` proved in the kernel of the policy's
theory from the call's facts. The last one, the default deny, is reported with the rules that were tried and why each
did not apply (the facts it lacked, the comparison that failed) — a refusal needs no proof, an allowance always does.

## The logic underneath

A policy is translated to an okay-proof `Theory`:

- an entity type is a `Sort.Named`; a value (`ann`) a constant of it; `Text` values are text terms;
- a fact `f(x: A): B` is a function symbol; a relation fact `r(x: A, y: B)` a predicate; a state the same as a function
  of its key, its current value a fact given by the store;
- a call `t(a: A, ...)` gives the predicates `allow_t`, `ask_t`, `deny_t` over (caller, arguments);
- a rule `allow t when C` is the axiom `∀ caller, args. C ⇒ allow_t(caller, args)`; a `*` rule one axiom per tool;
- a call's question: its arguments as constants; the facts read as ground formulas (`owns(ann, acc1)`,
  `balance(acc1) = 900.00`, `spent(ann) = 100.00`), each a hypothesis of the theorem.

The evaluator decides each candidate by direct evaluation (closures over the call and the facts, no search) and, for an
applying rule, BUILDS ITS PROOF from the evaluation's trace: the axiom, ∀ out with the call's values, each conjunct by
its fact or by computation, `ImpE`. An atom with facts in it (`spent(ann) + 50.00 <= 2000.00`, the fact
`spent(ann) = 100.00`) is proved closed by `Compute` with the facts' values in their places (`100.00 + 50.00 <=
2000.00`), then each value turned back into its fact by `Subst` with the fact's equation reversed — no search. The kernel checks every step (`Infer`); so a bug in the
evaluator can make a decision fail, never a wrong decision proved. The theorem's hypotheses are exactly the facts it
used: what the audit shows.

## Facts and state: effects

```text
enum Facts[X]:
  case Ask(fact: String, args: List[Value]) extends Facts[Option[Value]]     -- None: unknown
enum Store[X]:
  case Read(state: String, key: List[Value]) extends Store[Value]
  case Update(changes: List[Change]) extends Store[Unit]                     -- all of a decision's, at once
```

Handlers: the call's own facts; `Store` in memory, in a Durable Object, in a file; an external service's facts through
`Async` (Stripe's balance) — asked only if a candidate rule needs them, all of a call's at once (`parTraverse`), each
call's answers cached for the decision. A test's `given` is a handler in memory. A relation fact is true, false (then `¬r(...)`
is the hypothesis a `not` rests on) or unknown; an unknown fact makes its atom fail, with or without `not` — a rule
needing it does not apply, so a missing fact can deny or ask, never allow. Windows (`per day`) are the store's:
a value read after its window ended is the initial one.

Updates are made after the decision, only if the call is allowed (or asked and then approved), all at once; their
values computed from the facts the decision read — so two calls racing cannot both spend the same budget if the store
updates atomically (a Durable Object does).

## Speed

A policy is parsed and checked once; each tool's candidate rules are compiled to closures. A decision: facts asked
(the external ones' time aside), conditions evaluated, one proof built and checked by the kernel, its certificate
written. Target: under 50 µs for a policy of tens of rules, on the JVM; measured in the browser too. A certificate's
full re-check (≈60 µs) is the audit's, not each call's.

## In the browser

The studio's editor runs the parser and the checker on each change (errors with line and column), the tests on each
save, and shows each decision's proof. The module has no JVM-only code; the JVM-only parts stay in tests.

## Plan

1. AST, parser with positions, pretty printer (round trip) — `PolicySyntaxSuite`.
2. Type checker with every error above — `PolicyTypesSuite`.
3. Translation to a `Theory`; evaluator; proof building; decisions — `DecideSuite` (each verdict, the default, a
   refused forged proof, the hypotheses exactly the facts used).
4. Effects: `Facts`, `Store`, windows, updates; async external facts — `FactsSuite`.
5. `test` blocks run — `policy test file.policy` and in the studio.
6. Speed: `PolicyBench`; the JVM and Scala.js.
7. Later: tools imported from an MCP server's schema; arguments rewritten (`then set amount = ...`); compilation to
   Scala.

# Certificates

`Certificate.of(t)`: a theorem's proof as JSON — what another process, another language, an auditor later can check.

```text
{ "version": 1,
  "theory": "bank",
  "axioms": [["transfer", ["all", ["v","u","#User"], …]]],      // the theory, by value
  "digest": "9b8d6fe54e806692",                                  // FNV-1a 64 of the axioms' JSON
  "hypotheses": [ … ], "conclusion": ["p", "mayTransfer", …],
  "steps": [ {"rule": "Axiom", "of": [], "name": "transfer"},
             {"rule": "AllE", "of": [0], "by": ["ap","ann",[],"#User",[]]}, …,
             {"rule": "LinComb", "of": [7, 9], "by": ["1", "1"]}, … ] }
```

Steps in order, each a rule, the earlier steps it uses (`of`), its own data; shared steps once. Formulas and terms are
arrays: `["<=", a, b]`, `["v", "x", "Int"]`, `["d", "1000"]` (decimals canonical: no trailing zero), `["ap", name,
[argument sorts], result sort, [arguments]]`.

## Checking

A certificate is never a theorem by itself: checking derives every step again.

- `Certificate.check(json, kernel)`: under a kernel whose theory is the one the certificate carries (otherwise refused).
- `Certificate.checkAlone(json)`: under the theory it carries — that theory is the auditor's to judge;
  `Certificate.theory(json)` gives it, its digest pins it.
- The claimed conclusion and hypotheses must be what the steps derive.

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val x = V("x", Sort.Int)
val k = Kernel(Theory.empty)
val Right(Some(t)) = Linarith.decide(k, Le(x, I(9)), List(Le(x, I(7)))): @unchecked
val json = Certificate.of(t)
assert(Certificate.checkAlone(json).map(_.concl) == Right(Le(x, I(9))))
assert(Certificate.theory(json).map(Certificate.digest) == Right(Certificate.digest(Theory.empty)))
assert(Certificate.checkAlone(json.replace("\"7\"", "\"8\"")).isLeft)
```

## A second checker, in Lean

okay-lean's `okay-check` is this kernel written again in Lean — the logic, the exact decimals (rounded as
`java.math.BigDecimal` rounds), the polynomial forms, all 28 rules — a mistake in one unlikely to be the other's:

```text
okay-lean$ lake build okay-check
okay-lean$ .lake/build/bin/okay-check decision.json
{"file":"decision.json","ok":true,"theory":"bank","digest":"9b8d6fe54e806692","steps":25,"conclusion":[…],"hypotheses":5}
```

The two agree on data, not only on yes and no: the same conclusions, built alike (a polynomial's atoms ordered by
`Term.key`, a text both compute), the same digest. `DifferentialSuite` holds them to one verdict on 806 certificates —
106 proofs of every kind (each of the 28 rules at least once) and 700 mutants of them (a number, a premise, a
coefficient, a rule, a step dropped, the conclusion, a hypothesis, the digest, an axiom): 140 accepted, 666 refused,
by both. It runs when `okay-check` is built (`OKAY_LEAN`, by default `~/work/my/okay-lean`).

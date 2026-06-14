# cold-start

Number theory from nothing — built so that *nothing is trusted but a small
checker re-deriving proofs from inert data*.

This is a proof system in plain, dependency-free Python, organised around the
**De Bruijn criterion**: an (untrusted, possibly buggy or hostile) prover emits
a serializable *proof term*; one tiny trusted `check()` re-derives the
conclusion from scratch. You never have to trust that some object "is really a
theorem" — you trust that `check()` ran and didn't raise.

## Why not just an opaque `Theorem` type?

We started there (LCF-style: a guarded `Theorem` only the kernel can mint). In
Python that guarantee is unenforceable — `object.__new__`, reaching the
constructor token, or monkeypatching all forge one. Worse, any rule comparing
terms with `==` trusts `__eq__`, and a hostile `Term`/`str` **subclass** can
override it to derive `1 = 0` from reflexivity alone. (Both are regression tests
now: see `test_checker.py`.)

The De Bruijn design dissolves these: the checker consumes *recipes* (data),
not theorem objects, so there's nothing to forge but a proof that checks. And it
validates every term/formula with **exact-type** checks before trusting `==`, so
a lying subclass is rejected as non-canonical.

## The pieces

The code is the `cold_start/` package (flat, no src-layout):

- **`cold_start/syntax.py`** — the object language: terms (`Var`/`Fun`), formulas
  (`Eq`/`Implies`), free-vars/substitution, exact-type `validate_*`, and JSON
  ser/deser. *Not trusted* — a formula is a claim, not a proof.
- **`cold_start/proof.py`** — proof terms (`Axiom`, `Assume`, `Refl`, `Sym`,
  `Trans`, `Cong`, `MP`, `ImpIntro`, `Inst`): the inert recipe a prover emits.
  Serializable to JSON. *Not trusted.*
- **`cold_start/checker.py`** — **THE TRUSTED CORE.** `validate_proof` (one
  structural pass), `check(proof, theory) -> Sequent`, and the pure recursive
  `_derive`. A `Sequent` deliberately has no construction guard: holding one
  proves nothing; only `check()` returning it is authority.
- **`cold_start/peano.py`** — Peano as a *theory*: signature (`0`, `S`, `+`), the
  two addition axioms, and an induction-schema **recognizer**. Defining what
  counts as an axiom is part of choosing a theory, so the recognizer is trusted
  — and short. Induction is *derived* (two modus-ponens against the schema).
- **`cold_start/proofs.py`** — worked proofs. Currently `0 + n = n` by induction.
- **`cold_start/verify.py`** — a CLI that checks a JSON proof in a **separate
  process**, trusting only `checker.py` + the named theory. The De Bruijn payoff.
- **`test_checker.py`** — example tests: rules, the soundness attacks,
  serialization round-trip, cross-process verification.
- **`test_properties.py`** — Hypothesis property tests: round-trips, checker
  totality, substitution algebra, a sound proof generator the checker must
  agree with, and adversarial hammering of the induction recognizer.

## Run it

Managed with [uv](https://docs.astral.sh/uv/) — isolated `.venv`, locked deps.

```sh
uv run pytest                          # the whole suite
uv run python -m cold_start.proofs     # prints:  |- +(0, n) = n
uv run ruff check . && uv run pyright  # lint + type-check

# verify a proof in a fresh process, end to end:
uv run python -c "from cold_start.proof import to_json; from cold_start.proofs import left_identity_proof; print(to_json(left_identity_proof()))" \
    | uv run python -m cold_start.verify
```

## Design commitments (v0)

- **Trust the verifier, not the object.** Authority is `check()` re-deriving a
  sequent from serializable data — robust to every in-process forgery.
- **Validate untrusted input with exact types** before trusting `==`.
- **Free variables are implicitly universally quantified** (the Boyer–Moore
  instinct); `instantiate` is sound for variables not free in the hypotheses.
- **Minimal logic:** `Eq` and `Implies` only — enough to bootstrap addition.

## Roadmap / next holes to dig

- [x] De Bruijn checker over serializable proof terms
- [x] Soundness against lying `__eq__` / `__hash__` / mutable-args aliasing
- [x] Property-based tests (Hypothesis); uv-managed, locked deps
- [ ] `Not` (so we can state `0 != S(x)`, successor injectivity)
- [ ] `n + 0 = 0 + n` → commutativity of `+`, then associativity
- [ ] `*` and its laws; distributivity
- [ ] Ordering (`<=`), divisibility, primality
- [ ] A proof-term pretty-printer (proof trees / step listings)
- [ ] A *non-trusted* tactics layer that emits proof terms
- [ ] Explicit quantifiers, if/when we outgrow implicit-universal free vars

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
  (`Eq`/`Implies`), free-vars/substitution, exact-type `validate_*`, and hamblin
  byte ser/deser. *Not trusted* — a formula is a claim, not a proof.
- **`cold_start/proof.py`** — proof terms (`Axiom`, `Assume`, `Refl`, `Sym`,
  `Trans`, `Cong`, `MP`, `ImpIntro`, `Inst`): the inert recipe a prover emits.
  Serializable to hamblin bytes. *Not trusted.*
- **`cold_start/checker.py`** — **THE TRUSTED CORE.** `validate_proof` (one
  structural pass), `check(proof, theory) -> Sequent`, and the pure recursive
  `_derive`. A `Sequent` deliberately has no construction guard: holding one
  proves nothing; only `check()` returning it is authority.
- **`cold_start/peano.py`** — Peano as a *theory*: signature (`0`, `S`, `+`), the
  two addition axioms, and the theory's induction structure (`zero`/`succ`).
  Induction is a **first-class rule** (`Induct`), *not* an axiom formula —
  encoding the schema `P[0] -> ((P -> P[Sx]) -> P)` as an axiom is **unsound**
  under our implicit-∀ reading (its free `x` wrongly quantifies the whole
  implication, letting `P(n):=n=0`, x:=1 derive `1 = 0`). The rule keeps the
  step quantified correctly and enforces *var not free in the hypotheses*. The
  exploit is a permanent regression test.
- **`cold_start/proofs.py`** — worked proofs. Currently `0 + n = n` by induction.
- **`cold_start/verify.py`** — a CLI that checks a binary proof in a **separate
  process**, trusting only `checker.py` + the named theory. The De Bruijn payoff.
- **`test_checker.py`** — example tests: rules, the soundness attacks,
  serialization round-trip, cross-process verification.
- **`test_properties.py`** — Hypothesis property tests: round-trips, checker
  totality, substitution algebra, and a sound proof generator the checker must
  agree with.
- **`test_model.py`** — model-soundness probes: every closed theorem is true in
  ℕ, plus per-rule local soundness.
- **`test_algebra.py` / `test_rings.py` / `test_sorts.py`** — abstract theories
  (monoids, rings, a sorted monoid action) checked against multiple models,
  including non-commutative ones, with sort-checking invariants.

## Run it

Managed with [uv](https://docs.astral.sh/uv/) — isolated `.venv`, locked deps.

```sh
uv run pytest                          # the whole suite
uv run python -m cold_start.proofs     # prints:  |- +(0, n) = n
uv run ruff check . && uv run pyright  # lint + type-check

# verify a hamblin-encoded proof in a fresh process, end to end:
# tests/test_checker.py covers the exact to_bytes(...) -> verify stdin path.
uv run python -m cold_start.verify proof.hmb
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
- [x] Induction as a sound first-class rule (was an unsound axiom schema)
- [ ] `Not` (so we can state `0 != S(x)`, successor injectivity)
- [ ] `n + 0 = 0 + n` → commutativity of `+`, then associativity
- [ ] `*` and its laws; distributivity
- [ ] Ordering (`<=`), divisibility, primality
- [ ] A proof-term pretty-printer (proof trees / step listings)
- [ ] A *non-trusted* tactics layer that emits proof terms
- [ ] Explicit quantifiers, if/when we outgrow implicit-universal free vars

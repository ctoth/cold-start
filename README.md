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

- **`cold_start/syntax.py`** — the object language: terms (`Var`/`Fun`/`BVar`),
  formulas (`Eq`/`Rel`/`Implies`/`Bottom`/`Forall`/`Exists`, with `Not` as sugar),
  free-vars/substitution, exact-type `validate_*`, and hamblin byte ser/deser.
  *Not trusted* — a formula is a claim, not a proof.
- **`cold_start/proof.py`** — proof terms (`Axiom`, `Assume`, `Refl`, `Sym`,
  `Trans`, `Cong`, `MP`, `ImpIntro`, `Inst`, `Induct`, classical rules, and
  quantifier rules): the inert recipe a prover emits. Serializable to hamblin
  bytes. *Not trusted.*
- **`cold_start/checker.py`** — **THE TRUSTED CORE.** `validate_proof` (one
  exact-type structural gate), `check(proof, theory) -> Sequent`, and the
  trusted proof-rule methods it calls. A `Sequent` deliberately has no
  construction guard: holding one proves nothing; only `check()` returning it is
  authority.
- **`cold_start/presburger.py`** — Presburger arithmetic: signature (`0`, `S`,
  `+`), addition and successor axioms, and induction structure (`zero`/`succ`).
  Induction is a **first-class rule** (`Induct`), *not* an axiom formula —
  encoding the schema `P[0] -> ((P -> P[Sx]) -> P)` as an axiom is **unsound**
  under our implicit-∀ reading (its free `x` wrongly quantifies the whole
  implication, letting `P(n):=n=0`, x:=1 derive `1 = 0`). The rule keeps the
  step quantified correctly and enforces *var not free in the hypotheses*. The
  exploit is a permanent regression test.
- **`cold_start/peano.py`** — Peano arithmetic: Presburger plus recursive
  multiplication axioms.
- **`cold_start/tactics.py`** — the **untrusted prover** half of the split: a
  small equational engine (first-order matching, directed rewrite rules,
  leftmost-outermost rewriting under a `Cong` tower, normalization to a fixpoint,
  `prove_eq`, `by_induction`, and *ordered* rewriting so that commutativity can be
  a rule without looping) that *emits* proof terms. It may be arbitrarily
  clever, because it has no authority: a bug here yields a proof `check()`
  rejects, never a false theorem. Nothing in the trusted core imports it, and a
  test enforces that direction.
- **`cold_start/proofs.py`** — worked proofs, in two styles: built by hand
  (`left_identity_proof`) and built by tactics (`left_identity`, `succ_add`,
  `add_comm`, `add_assoc`, then the multiplication ladder up through
  `mul_comm`, `distrib_left`/`distrib_right` and `mul_assoc`). Both face the
  same `check()`, which cannot tell them apart.
- **`cold_start/robinson_proofs.py`** — Robinson's bridge proved in PEANO:
  `PEANO ⊢ S(a·(a+b))·S(b·(a+b)) = S(((a+b)·(a+b))·S(a·b))`, i.e. her definition
  of addition is *correct*, for all `a, b` at once. The converse is a checked
  theorem at every positive result: `bridge(a,b,S(c)) → a+b=S(c)`, resting on a
  derived nested-induction proof that positive multiplication factors cancel.
  Her §2 axioms A4' and A7' follow outright; A5' follows with that exact
  positivity guard. Unguarded A5' is false at `c = 0`, precisely where her
  positive-integer domain earns its keep.
- **`cold_start/rigidity.py`** — the first genuine *induction* proof in Robinson's
  `(1, S, ·)` theory, whose base is **1**. Extends `ROBINSON_PEANO` (with
  `dataclasses.replace`, never a subclass) by a fresh unary `f` and the successor
  half of a *brachymorphism* — `f(1) = 1`, `f(S x) = S(f x)` — and derives
  `|- f(x) = x`: every successor-preserving self-map of the positive integers is
  the identity. That rigidity is what kills the prime-permuting automorphisms of
  `(N, ·)` and so lets `+` be defined at all. Given it, the *other* brachymorphism
  law is a theorem rather than an axiom: `|- f(x·y) = f(x)·f(y)`, by rewriting
  alone. (Wehrung 2024, arXiv:2405.08364.)
- **`cold_start/prop.py`** — derived propositional sugar over the →/⊥ core:
  n-ary classical `And`/`Or` and `Iff`, with conjunction introduction and both
  (RAA) eliminations as untrusted combinators.
- **`cold_start/interp.py`** — **interpretations between theories as checked
  artifacts**. Function graphs and predicate symbols can be translated, with
  optional domain relativization; `verify` drives every axiom/definedness payment
  through `check()` and reports **bridge size** (translation nodes) against
  **toll** (proof nodes), ledgering unpaid obligations openly.
- **`cold_start/bridges.py`** — the concrete crossings. Robinson's §2 as two
  landed bridges: base-1 Presburger into `(1, S, ·)` (axioms land on A4'/A5',
  totality `∃c bridge(a,b,c)` is the repo's first existential theorem, proved
  by induction based at 1; uniqueness ledgered open), and the same **19-node
  bridge** into PEANO relativized to the positives — **every obligation paid**
  (toll: 484,089 proof nodes), with the previous campaign's converse theorem
  paying uniqueness. Unguarded PEANO is provably impassable (A5' fails at 0),
  so the relativization is forced, not decorative.
- **`cold_start/robinson_divisibility.py` / `divisibility.py`** — Robinson's exact
  Theorem 1.2 multiplication graph in **successor and divisibility only**, plus
  PEANO proofs of the elementary interpretation `a|b := ∃k. a·k=b`: reflexivity,
  transitivity, unit/zero laws, both product factors, and product closure.
- **`cold_start/divisibility_bridges.py`** — the boundary ledger. The predicate
  interpretation is a 6-node bridge with seven laws fully paid (9,953 proof
  nodes). Robinson's full formula (2) is a 331-node multiplication bridge with
  exactly its two deep debts exposed: totality and uniqueness.
- **`cold_start/verify.py`** — a CLI that checks a binary proof in a **separate
  process**, trusting only `checker.py` + the named theory. The De Bruijn payoff.
- **`cold_start/lean.py`** — untrusted **Lean 4 compat layer**: renders checked
  proofs as *conditional* Lean theorems (axioms become ∀-hypotheses — never
  `axiom`), parses back the statement fragment it emits, and writes
  `lean_export/ColdStart.lean`, which compiles under Lean 4 — an **independent
  kernel** re-checking our proofs, the other half of the De Bruijn promise.
- **`tests/test_checker.py`** — example tests: rules, the soundness attacks,
  serialization round-trip, cross-process verification.
- **`tests/test_properties.py`** — Hypothesis property tests: round-trips, checker
  totality, substitution algebra, and a sound proof generator the checker must
  agree with.
- **`tests/test_model.py`** — model-soundness probes: every closed theorem is true in
  ℕ, plus per-rule local soundness.
- **`tests/test_algebra.py` / `tests/test_rings.py` / `tests/test_sorts.py`** — abstract theories
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
- **Small logic:** equality, implication, falsum/negation, explicit quantifiers,
  induction, and classical rules are enough for the current arithmetic work.

## Roadmap / next holes to dig

- [x] De Bruijn checker over serializable proof terms
- [x] Soundness against lying `__eq__` / `__hash__` / mutable-args aliasing
- [x] Property-based tests (Hypothesis); uv-managed, locked deps
- [x] Induction as a sound first-class rule (was an unsound axiom schema)
- [x] `Bottom`/`Not`, successor disequality/injectivity, and classical rules
- [x] Explicit quantifiers with locally nameless binders
- [x] `n + 0 = 0 + n` → commutativity of `+`, then associativity
- [x] `*` and its laws; distributivity — the full ladder up to `(x·y)·z = x·(y·z)`,
      and with it Robinson's bridge `(1+ac)(1+bc) = 1+c²(1+ab)` at `c := a+b`
      proved in PEANO (`cold_start.robinson_proofs`)
- [x] Positive multiplication cancellation and Robinson's converse, proving the
      bridge is exactly the graph of addition on the positive domain; independently
      re-checked by the generated Lean 4 corpus
- [x] Interpretations between theories as first-class checked artifacts
      (`cold_start.interp`), with Robinson's §2 landed as two measured bridges
      (`cold_start.bridges`) — one fully paid into PEANO's positives
- [ ] Ordering (`<=`) and primality; divisibility foundations are now checked
- [ ] Pay Robinson Theorem 1.2's totality/uniqueness debts (the CRT/prime step);
      then Quine 1946 concatenation theory and Skolem arithmetic
- [ ] A proof-term pretty-printer (proof trees / step listings)
- [x] A *non-trusted* tactics layer that emits proof terms — including ordered
      rewriting, so commutativity can be a rule without looping

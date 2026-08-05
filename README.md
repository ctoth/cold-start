# cold-start

Number theory from nothing — built so that *nothing is trusted but a small
checker re-deriving proofs from inert data*.

This is a proof system in a small Python package with locked dependencies,
organised around the
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
  free-vars/substitution, and exact-type validation.
  *Not trusted* — a formula is a claim, not a proof.
- **`cold_start/proof.py`** — proof terms (`Axiom`, `Assume`, `Refl`, `Sym`,
  `Trans`, `Cong`, `MP`, `ImpIntro`, `Inst`, `Induct`, classical rules, and
  quantifier rules): the inert recipe a prover emits. *Not trusted as data; its
  guarded rule methods are part of checking.*
- **`cold_start/checker.py`** — drives the **trusted checking path**:
  `validate_proof`, `check(proof, theory) -> Sequent`, and the guarded structural,
  rule, sequent, and sort-checking methods in `syntax.py`, `proof.py`, and
  `sequent.py`. A `Sequent` deliberately has no
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
- **`cold_start/codec.py`** — the single untrusted Hamblin wire boundary. It owns
  registries and explicit term/formula/proof encode/decode APIs, validates exact
  roots and complete decoded structures, and is imported by `verify.py`, never by
  the trusted core.
- **`cold_start/emitter.py`** — one exact-type, iterative external-text emission
  mechanism used by notation and Lean adapters. Its metadata-only `@case`
  declarations are checked for complete canonical coverage at class creation.
- **`cold_start/notation.py`** — untrusted human parser/formatter ownership for
  terms and formulas; presentation state stays outside syntax nodes.
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
- **`cold_start/presburger_proofs.py`** — hand-built examples and tactic-built
  addition, induction, cancellation, and zero-case theorems that check in the
  Presburger fragment.
- **`cold_start/peano_proofs.py`** — multiplication examples and the ladder through
  commutativity, distributivity, associativity, and positive cancellation; it
  consumes the proved Presburger kit rather than a generic theorem bucket.
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
- **`cold_start/parity.py`** — the 2-adic kit in PEANO: every number is `m·2`
  or `S(m·2)`, even never equals odd, cancellation by 2, and **Euclid's lemma
  at the prime 2** (`¬2|d → d|x·2 → d|x`) — carried by parity alone, no order
  kit, no Bézout. The first rung of the formula (2) H1 debt.
- **`cold_start/order.py`** — the order kit: `≤` as `∃w. a+w=b`, discreteness
  (`a ≤ S(n) → a ≤ n ∨ a = S(n)`), the dyadic descent step, and
  **`course_of_values` — strong induction compiled to the structural `Induct`
  rule** through `reach(n) := ∀z (z≤n → P(z))`. `tactics.transport` (Leibniz's
  law as a combinator) moves whole formulas along proved equalities.
- **`cold_start/skolem.py`** — **Presburger interpreted into multiplication
  alone** (Mostowski's embedding into Skolem arithmetic): `0 ↦ 1`,
  `S(x) ↦ x·2`, `+ ↦ ·`, relativized to the powers of two, defined by
  divisibility only (`every divisor ≠ 1 is even`). A 16-node bridge into
  PEANO, **every obligation paid** (toll: 116,358): product closure fell to
  course-of-values descent through the dyadic layers.
- **`cold_start/quotient.py`** — **k-dimensional quotient interpretations**,
  the general Tarski–Mostowski–Robinson bridge: a source element becomes a
  k-tuple of target elements and source equality lands on a DEFINED
  equivalence, which the artifact must prove is an equivalence respected by
  every translated symbol (respect at identical arguments is uniqueness).
- **`cold_start/integers.py`** — the Grothendieck bridge, the quotient
  machinery's first crossing: **the abelian group of integers interpreted
  into PRESBURGER**, a pair `(a,b)` denoting `a−b`, equivalent when
  `a+d = c+b`; zero the diagonal, addition componentwise, negation the swap.
  A 28-node bridge, **every obligation paid** (toll: 155,545) — including
  `x + (−x) = 0`, an axiom about subtraction landed as a theorem of a theory
  with no negative numbers anywhere. Every payment is one cancellation
  recipe: `Cong`-sum the hypotheses, AC-shuffle, cancel the suffix.
- **`cold_start/ring_z.py`** — **the full commutative ring of integers
  interpreted into PEANO**, on the same pairs: `1` one step above the
  diagonal, multiplication the difference product `(x₁y₁+x₂y₂, x₁y₂+x₂y₁)`.
  A 51-node bridge, **all 23 obligations paid** (toll: 876,035) — ring
  axioms, multiplicative associativity, both distributive laws, and respect
  for `·` among them. The engine is `combination.by_combination`: linear
  combinations of hypotheses with *term coefficients*, shuffled into the
  polynomial normal form of `peano_proofs.ring_kit` and closed by one
  cancellation.
- **`cold_start/ledger.py`** — the bridge ledger: every landed artifact of
  either kind re-verified and measured in one table
  (`uv run python -m cold_start.ledger`).
- **`cold_start/verify.py`** — a CLI that checks a binary proof in a **separate
  process**, trusting only `checker.py` + the named theory. The De Bruijn payoff.
- **`cold_start/lean/syntax.py`**, **`cold_start/lean/proof.py`**,
  **`cold_start/lean/models.py`**, and **`cold_start/lean/corpus.py`** — untrusted
  Lean 4 statement, proof-export, exact semantic-model registry, and corpus
  owners. Checked proofs become *conditional* Lean theorems (axioms become
  hypotheses, never Lean `axiom` declarations); exact registered models cash
  them out unconditionally. `python -m cold_start.lean` writes
  `lean_export/ColdStart.lean`, which a pinned Lean 4 kernel compiles.
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
pwsh -File tools/gate.ps1              # pytest, Ruff, Pyright basic
uv run python -m cold_start.lean       # regenerate the checked-in Lean corpus

# verify a hamblin-encoded proof in a fresh process, end to end:
# cold_start.codec.encode_proof(...) produces the wire bytes.
uv run python -m cold_start.verify proof.hmb
```

The same lockfile-backed gate, generated-file check, and Lean compilation run in
`.github/workflows/ci.yml` on pushes and pull requests.

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
- [x] Skolem arithmetic: Presburger interpreted into multiplication on the
      powers of two (`cold_start.skolem`), riding Euclid's lemma at 2
      (`cold_start.parity`) — **complete**, every obligation paid
- [x] Ordering (`<=`), transport, and strong induction (`cold_start.order`);
      primality still open
- [x] k-dimensional quotient interpretations (`cold_start.quotient`) — the
      general TMR notion — with the integers landed as the first crossing
      (`cold_start.integers`): ℤ's abelian group into PRESBURGER, complete
- [x] The full commutative ring ℤ into PEANO (`cold_start.ring_z`):
      multiplication as the difference product, all 23 obligations paid,
      riding `ring_kit`'s semiring normal form and `by_combination`'s
      term-coefficient linear combinations
- [ ] Pay Robinson Theorem 1.2's totality/uniqueness debts (the CRT/prime
      step): the order kit and Euclid-at-2 now stock its H1/H2 frontier;
      then Quine 1946 concatenation theory
- [ ] A proof-term pretty-printer (proof trees / step listings)
- [x] A *non-trusted* tactics layer that emits proof terms — including ordered
      rewriting, so commutativity can be a rule without looping

# Architecture

`cold_start` is a number-theory proof checker built from nothing, to understand
how such a thing works by building the smallest honest one.

## The De Bruijn criterion
The design is the **De Bruijn criterion**: separate an untrusted, possibly-large
*prover* from a tiny, trusted *checker*.

- A **proof term** (`proof.py`) is inert structural data — a recipe. Building one
  asserts nothing; it may be nonsense.
- `check(proof, theory)` (`checker.py`) re-derives the `Sequent` the proof proves,
  or raises. A `Sequent(hyps, concl)` is plain data you
  can fabricate freely; its authority is `check()` *returning* it, never the value.
- `codec.py` is the single untrusted Hamblin boundary; `verify.py` decodes through
  it and re-checks the proof in a fresh process.

Trust = the exact-type gates and the structural/rule/sort-checking methods they
guard in `syntax.py`, `proof.py`, and `sequent.py`, driven by `checker.py`, plus
each theory's axioms and induction structure. Syntax/proof *values*, the codec,
notation, emitters, tactics, proof libraries, and Lean export are untrusted.

## The object language (`syntax.py`)
One `Node` root. Two thin markers under it, `Term` and `Formula` (kept so tests can
enumerate concrete subclasses), and the concrete frozen-dataclass nodes:

- terms: `Var(name, sort)`, `Fun(name, args)`, `BVar(index)`
- formulas: `Eq`, `Rel`, `Implies`, `Bottom`, `Forall(sort, body)`,
  `Exists(sort, body)`

**Binders are locally nameless.** A bound variable is a de Bruijn index `BVar(i)`
(0 = nearest enclosing binder); the binder records only the sort, not a name. So
α-equivalence is *literal `==`* — no chosen binder names, no capture-avoidance. Smart
constructors `forall(name, sort, body)` / `exists(...)` let you still write named
binders at the surface; they `abstract` the named variable to an index.

### Operations are methods (polymorphism, not type-switches)
`free_vars`, `subst`, `abstract`, `instantiate`, `sort_of`, and `sort_check` are
methods on the syntax nodes. `Node` supplies the generic structural operations over
a node's children; only the leaves or binders override where scope requires it.
Human notation parsing and printing live in `notation.py`, not on the syntax nodes.

### The scope (environment) — one concept, several payloads
The single thing threaded through a tree walk is the **scope**: a stack pushed under
each binder, indexed by `BVar`. What each slot holds depends on the operation:

| operation     | scope slot holds | `BVar(i)` does            |
|---------------|------------------|---------------------------|
| `validate`    | nothing          | check `i < depth`         |
| `evaluate`    | a value          | look up `scope[i]`        |
| `instantiate` | (depth only)     | `index == depth → repl`   |
| sort-checking | the bound sort   | `scope[i]` is that sort   |

Because the bound *sort* rides in the scope, **sorts and quantifiers coexist**:
`∀x:M. φ` sort-checks `φ` with `x:M` in scope. (Earlier versions rejected quantified
sorted formulas; this unifies them.)

### The trust gate guards the methods
`validate` (terms/formulas) and `validate_proof` (proofs) reject hostile
*subclasses* — a `Var` subtype with a lying `__eq__`, a `str` subtype, a forged `Fun`
with mutable args — before any `==` is trusted. A polymorphic method *could* be
overridden by exactly such a subclass, so each gate is a one-line **exact-type
check** (`type(x) in CANONICAL_NODE_TYPES` / `CANONICAL_PROOF_TYPES`,
reject-default) placed *in front
of* the node's own `_validate` method. The per-type field checks stay polymorphic
methods; the gate only confirms the exact type is canonical before any method runs,
and each method recurses through the same gate. It runs first; downstream code then
operates only on canonical nodes. This is the security property without a pile of
per-type handler functions.

## The checker (`checker.py`)
`check` runs the gate (`validate_proof`) then calls `pf.derive(theory)`. Each proof
term checks **itself**: derivation is a polymorphic `derive` method on the `Pf`
class (`_derive_rule` for the rule, with a `derive` wrapper that re-sort-checks the
produced sequent), living in `proof.py` beside the term. "Inert data" means a `Pf`
carries no pre-made theorem — you can build nonsense, and the checker rejects it —
*not* that the class has no methods: the methods are trusted code, and the
exact-type gate runs first so a hostile subclass's override never executes. (This
replaced an earlier `_DERIVE` dispatch table of free functions; the table was a pile
of shims, and a rule's logic is an operation over the proof tree, so it belongs on
the node.) `Sequent` lives in `sequent.py` so `proof.py` can return and recurse on
it without an import cycle. Side conditions are enforced in each rule's method:
induction's eigenvariable (not free in undischarged hypotheses — the side condition
that blocks the `1 = 0` exploit), `Inst`'s cross-sort guard, `ForallIntro`/
`ExistsElim` eigenvariables. `sort_of`/`sort_check` are polymorphic node methods;
sequents are re-sort-checked (`Sequent.sort_check`) when the theory has a signature.
`check` is **total**: it returns a `Sequent` or raises `TypeError` / `ValueError`,
nothing else — and it is **iterative end to end**. Every operation it reaches
(validation, derivation, `subst`/`abstract`/`instantiate`, `sort_of`/`sort_check`,
`free_vars`, and even `==`/`hash` on the nodes) walks a heap agenda rather than the
call stack, so a proof or term nested far past Python's recursion limit is checked
or cleanly rejected without a `RecursionError`. The only bound is memory, which
already held the input.

## External adapters (`codec.py`, `emitter.py`, and `notation.py`)

Serialization is not a syntax/proof responsibility. `codec.py` builds its registries
from the canonical owner sets and exposes explicit `encode_term`/`decode_term`,
`encode_formula`/`decode_formula`, and `encode_proof`/`decode_proof` boundaries.
Decoded structures are exact-root checked and validated before they can reach the
checker; the trusted core never imports the codec.

Human notation and Lean rendering are external tree interpretations. `emitter.py`
provides their one iterative mechanism: metadata-only `@case` declarations become
an immutable exact-type case table at class creation, with missing, duplicate, and
unexpected cases rejected. Adapter-specific precedence, binder scope, names, and
error policy remain in `notation.py` and `lean/*`; no visitor method or presentation
state is placed on the canonical data classes.

## The independent kernel (`lean/`)
The De Bruijn criterion's second promise is that the checker is small enough to be
*re-checked from outside*. `lean/syntax.py` and `lean/proof.py` (untrusted) render
each checked proof as a
**conditional Lean 4 theorem**: the theory's function symbols and axioms become
explicit hypotheses (never a Lean `axiom`), induction becomes an `ind` hypothesis,
and the proof term maps rule-for-rule onto Lean primitives (`Eq.trans`, `congrArg`,
application, lambda, `Nat.rec` at the ℕ instantiation). `lean_export/ColdStart.lean`
carries the `lean/corpus.py` corpus plus a semantic-model epilogue.
`lean/models.py` is the single owner of those model registrations: each is tied to
one exact `Theory` object and must interpret every function symbol, pay every axiom,
and supply the induction principle when present. PRESBURGER, PEANO, and
SQUARE_ARITHMETIC are registered at ℕ, so their exported theorems cash out
unconditionally; a structurally equal but unregistered theory stays conditional.
Robinson also stays conditional on purpose
(`S a ≠ 1` fails at 0, so ℕ is not a model of the positive-integer axioms). The
generated corpus compiles under Lean 4, so a foreign kernel re-derives both the
conditional proof and every registered semantic discharge. Importing Lean *proofs*
is out of scope (that would mean swallowing CIC); only the emitted statement
fragment parses back.

## The theories
- `presburger.py` — the addition fragment `(0, S, +)` with induction: **Presburger
  arithmetic**, complete and decidable.
- `peano.py` — `PEANO = PRESBURGER + {x·0=0, x·S(y)=x·y+x}`. Multiplication defined
  recursively from addition; with induction this is where incompleteness begins.
- `squaring.py` — PRESBURGER plus primitive `sq`, recursively characterized using
  only addition; multiplication is recovered through a paid polarization graph.
- `presburger_proofs.py` — addition, induction, cancellation, and zero-case proof
  builders whose smallest complete checking theory is Presburger.
- `peano_proofs.py` — multiplication laws and positive cancellation, consuming the
  proved Presburger kit.
- `algebra.py` — monoids, rings (incl. non-commutative models), and a many-sorted
  monoid action `M ↷ X` (the shape that points toward modules/Clifford).
- `robinson.py` — Robinson's `(1, S, ·)` arithmetic experiment: addition
  eliminated into a definable bridge over multiplication and successor.
- `robinson_proofs.py` — that bridge proved *inside* PEANO, plus two of Robinson's
  §2 axioms as theorems and a note on why the third is refutable instead.

## On `+` vs `×`: the honest foundational note
Peano defines `×` recursively from `+` (`x·S(y) = x·y + x`). That axiom *contains a
`+`* — the entanglement of addition and multiplication, which is the seat of
arithmetic's undecidability, is hidden inside it.

Julia Robinson (1949) showed the reverse: `+` is first-order definable from `·` and
`S` by the single equation
`S(a·c)·S(b·c) = S((c·c)·S(a·b))  ⟺  a+b=c` (positive integers),
and hence Peano can be axiomatized on `(1, S, ·)` alone, with `+` *defined*.
Undecidability enters precisely when successor is added to multiplication: `(ℕ, ·)`
alone is decidable (its prime-permuting automorphisms hide addition); `S` rigidifies
the integers, kills those automorphisms, and lets `+` be defined.

We keep `+`-primitive with recursive `×` as the trusted base, because it is small and
readable — Robinson herself called the eliminated-`+` axioms "complicated and
artificial." But we *exhibit* the Robinson basis (`robinson.py` + the `(S,·)` Peano
axioms), and concrete instances of her bridge are **derived theorems**: for positive
`a, b`, `robinson_proofs.robinson_add_proof(a, b)` chains Robinson's own §2 recursion laws
(A4' `a + 1 = S a`, A5' `a + b = c → a + S b = S c`) into a proof of
`bridge(a, b, a+b)`, which the trusted checker re-derives to a hypothesis-free
sequent — so `2 + 3 = 5` arrives as an identity in `S` and `·` with no `+` symbol in
it. `tests/test_robinson.py` checks that for every `a, b` in 1..5, and `verify.py
--theory robinson` re-checks it in a fresh process.

Half of Robinson's general definability theorem is now derived too, for **all** `a, b`
at once rather than per instance: `robinson_proofs.bridge_theorem()` proves
`PEANO ⊢ bridge(a, b, a+b)`. At `c := a+b` the bridge is a pure semiring identity —
both sides multiply out to `ab(a+b)² + (a+b)² + 1` — so it falls to normalising both
sides to one canonical polynomial over the multiplication laws in
`peano_proofs.py`, and it
needs no positivity: `a = b = 0` is covered like everything else. The **converse is
now derived as well** on precisely Robinson's domain:
`PEANO ⊢ bridge(a,b,S(c)) → a+b=S(c)`. Normalization first extracts
`(a+b)S(c)=S(c)²`; a nested-induction theorem proves that multiplication by `S(c)`
is cancellative, so the bridge is exactly the graph of addition for positive results.

Her §2 axioms A4' and A7' come out as unrestricted instances. A5' comes out with
the exact guard `c=S(k)`: `bridge(a,b,S(k)) → bridge(a,S(b),S(S(k)))`. The unguarded
formula is still false in the standard model at `c=0`, so by soundness it still has
no PEANO proof. This cleanly separates the theorem from its single boundary
obstruction. The generated Lean 4 corpus independently re-checks the cancellation
and converse proofs.

## Interpretations: bridges between theories, measured

`interp.py` promotes what Robinson's paper *is* — an interpretation of one theory
inside another — to a first-class checked artifact. An `Interpretation` names a
source and target theory, translates chosen source function symbols relationally
(the graph form of Tarski–Mostowski–Robinson, hoisting nested applications through
∀-guards), optionally relativizes to a domain formula, and owes obligations: one
per source axiom, totality and uniqueness per translated symbol, and — when
relativized — nonemptiness and closure of the domain. `verify` pushes each offered
payment through the trusted `check()` and reports **bridge size** (translation
nodes) against **toll** (proof nodes), with unpaid obligations ledgered openly: an
interpretation with open debts is a conjecture with a ledger, not a theorem.

`squaring_bridges.py` is the smallest complete seed currently measured. It maps
`x*y=z` to the subtraction-free 14-node graph
`(z+z)+sq(x)+sq(y)=sq(x+y)` in `SQUARE_ARITHMETIC`. Totality is an induction whose
witness advances from `z` to `z+x`; uniqueness cancels the square terms and uses
an addition-only proof that doubling is injective. Both debts are paid (toll:
20,230), and a proof-tree audit admits only `0`, `S`, `+`, and `sq`. The Lean model
registry interprets `sq(n)` as `Nat.mul n n`, so both payments cash out at the
standard naturals.

Predicate symbols cross the same layer without fake function obligations. In
particular, atomic `a | b` translates to PEANO's `∃k. a·k=b`; seven elementary
divisibility laws are checker-paid across that 6-node bridge (toll: 9,953 proof
nodes). Robinson's rendered Theorem 1.2 formula (2) is transcribed literally as
a multiplication graph containing only `S`, `|`, equality, and logic. It measures
331 nodes. Its report is deliberately incomplete with exactly `totality:*` and
`uniqueness:*` open: those are the Chinese-remainder/prime debts in Robinson's
argument, now isolated rather than blurred into the transcription.

`bridges.py` lands Robinson's §2 twice over the same 19-node translation
`x + y = z ↦ S(x·z)·S(y·z) = S((z·z)·S(x·y))`. Into her own `(1, S, ·)` theory,
the translator drops base-1 Presburger's axioms onto A4' and (the closure of) A5'
verbatim, and totality — `∃c bridge(a,b,c)`, the repo's first existential theorem —
is derived by induction based at 1; uniqueness stays an honest open ledger entry —
and deservedly so: it is exactly **Robinson's axiom A8**, which she *added* (p. 104,
"to guarantee the operational character of addition") rather than derived, leaving
the axioms' mutual independence open. The structural obstruction is itself a
checked theorem (`uniqueness_descends`): A5' maps bridge solutions injectively *up*
the second argument, so uniqueness propagates *downward* — while induction only
climbs, and no axiom inverts a bridge. Our open obligation is the paper's own open
question, with the reason it resists derivable and derived. Into PEANO relativized to the positives
(`δ(x) := ∃k. x = S(k)`), **every obligation is paid** (toll: 484,089 proof nodes):
the guarded A5' theorem settles the translated recursion axiom and the bridge
converse settles uniqueness — and the relativization is forced, since unguarded
A5' is false at zero. The δ-guard on `S(a) ≠ 1` earns its keep the same way: at
`a = 0` that translated axiom is false in PEANO, so only the relativized form has
a proof.

`skolem.py` reaches the opposite shore: instead of carrying addition *out of*
the additive world, it interprets Presburger arithmetic *into multiplication
alone* — Mostowski's classical embedding into Skolem arithmetic. On the powers
of two, multiplication is addition of exponents, so the whole additive
signature translates away: `0 ↦ 1`, `S(x) ↦ x·2`, `x + y ↦ x·y`, relativized to
`pow2(t) := ∀d (d|t → d≠1 → 2|d)` — "every divisor except 1 is even", a
definition of *power of two* with no exponentiation, spoken entirely in the
paid divisibility predicate. The 16-node bridge lands in PEANO **complete**
(toll: 116,358 proof nodes). The toll's engine is
`parity.py`: the 2-adic case split (`n = m·2 ∨ n = S(m·2)`), even ≠ odd, and
**Euclid's lemma at the prime 2** (`¬2|d → d|x·2 → d|x`) — proved by parity
alone, with no order relation and no Bézout — which yields closure of the
powers of two under doubling and, through it, both definedness debts of the
doubling graph *and* the translated successor injectivity. The last debt,
`totality:+` (product closure), fell to `order.py`: `≤` as a witnessed sum,
discreteness, the halving descent step, and `course_of_values` — **strong
induction compiled to the structural `Induct` rule** through
`reach(n) := ∀z (z≤n → P(z))`, with `tactics.transport` (Leibniz's law as a
combinator) carrying formulas along equalities at the seams. An odd divisor
of `S(n)·y` halves through the even `S(n)` and drops one dyadic layer by
Euclid-at-2, where the reach hypothesis refutes it.

`quotient.py` generalizes the bridge layer itself to the full
Tarski–Mostowski–Robinson notion: **k-dimensional interpretations with a
defined equality**. A source element becomes a k-tuple of target elements
(`x ↦ x.1 … x.k`), a hoisted application binds a block of k quantifiers, and
source `=` translates to a definable equivalence `~` — always the honest
ε-form, never the witness shortcut, so soundness needs no saturation
assumption. The artifact owes what the generality costs: `~` must be proved
an equivalence, and every translated symbol must *respect* it (equivalent
arguments force equivalent results — which at identical arguments is
uniqueness-up-to-~, so no separate uniqueness label exists to quietly
weaken). `interp.py`'s one-dimensional machinery is untouched; the report
types are shared. `integers.py` is the first crossing: the abelian group of
integers into PRESBURGER via Grothendieck pairs — `(a,b)` denoting `a−b`,
`~` the subtraction-free `a+d = c+b`, zero the diagonal, addition
componentwise, negation the swap. The 28-node bridge is **complete** (toll:
155,545), and `x + (−x) = 0` — false of the naturals — is a paid theorem of
their own additive theory. Every payment core is one recipe
(`combination.by_combination` with no coefficients): `Cong`-sum the oriented
hypotheses, AC-shuffle with `add_kit`'s ordered rewriting, cancel the common
suffix.

`ring_z.py` completes that crossing: **the full commutative ring of the
integers into PEANO**, same pairs, same `~`, plus `1` one step above the
diagonal and multiplication as the difference product
`(x₁y₁+x₂y₂, x₁y₂+x₂y₁)`. All 23 obligations are paid (bridge 51 nodes,
toll 876,035). Two tooling pieces carry it: `peano_proofs.ring_kit` extends
the addition kit with distribution and ordered multiplicative AC, giving
`prove_eq` a polynomial normal form (a decision procedure for
commutative-semiring identities); and `combination.by_combination` admits
TERM COEFFICIENTS — a hypothesis `L = R` may join the sum as `L·c = R·c` —
which is exactly what respect for `·` needs, since equal differences
multiply only after each `~` is scaled by the other factor's components.

`ledger.py` renders every landed artifact of either kind — bridge size,
toll, payments, open debts — as one table, re-verified through the trusted
checker on each run (`uv run python -m cold_start.ledger`).

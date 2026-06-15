# Architecture

`cold_start` is a number-theory proof checker built from nothing, to understand
how such a thing works by building the smallest honest one.

## The De Bruijn criterion
The design is the **De Bruijn criterion**: separate an untrusted, possibly-large
*prover* from a tiny, trusted *checker*.

- A **proof term** (`proof.py`) is inert, serializable data — a recipe. Building one
  asserts nothing; it may be nonsense.
- `check(proof, theory)` (`checker.py`) re-derives the `Sequent` the proof proves,
  or raises. It is the only trusted code. A `Sequent(hyps, concl)` is plain data you
  can fabricate freely; its authority is `check()` *returning* it, never the value.
- `verify.py` re-checks a proof from JSON in a fresh process, trusting only the
  checker module and the theory's axioms — the payoff of inert proof terms.

Trust = `checker.py` + each theory's axioms. Everything else (syntax, serialization,
notation, the prover) is untrusted and may be as clever as it likes.

## The object language (`syntax.py`)
One `Node` root. Two thin markers under it, `Term` and `Formula` (kept so tests can
enumerate concrete subclasses), and the concrete frozen-dataclass nodes:

- terms: `Var(name, sort)`, `Fun(name, args)`, `BVar(index)`
- formulas: `Eq`, `Implies`, `Bottom`, `Forall(sort, body)`, `Exists(sort, body)`

**Binders are locally nameless.** A bound variable is a de Bruijn index `BVar(i)`
(0 = nearest enclosing binder); the binder records only the sort, not a name. So
α-equivalence is *literal `==`* — no fresh names, no capture-avoidance. Smart
constructors `forall(name, sort, body)` / `exists(...)` let you still write named
binders at the surface; they `abstract` the named variable to an index.

### Operations are methods (polymorphism, not type-switches)
`free_vars`, `subst`, `abstract`, `instantiate`, `evaluate`, `format`, `to_dict` are
methods on `Node`. `Node` supplies the generic recursion over a node's children;
only `Var` (the variable leaf) and the binders (which raise the scope depth)
override. There is no external `if type(node) is …` dispatch.

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
check** (`type(x) in _CANONICAL` / `_PROOF_TYPES`, reject-default) placed *in front
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

## The theories
- `presburger.py` — the addition fragment `(0, S, +)` with induction: **Presburger
  arithmetic**, complete and decidable.
- `peano.py` — `PEANO = PRESBURGER + {x·0=0, x·S(y)=x·y+x}`. Multiplication defined
  recursively from addition; with induction this is where incompleteness begins.
- `algebra.py` — monoids, rings (incl. non-commutative models), and a many-sorted
  monoid action `M ↷ X` (the shape that points toward modules/Clifford).
- `skolem.py` (Phase 4) — the multiplication-only fragment, the decidable
  *multiplicative* twin of Presburger.

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
artificial." But we *exhibit* the Robinson basis (`skolem.py` + the `(S,·)` Peano
axioms) and make her bridge a **checked theorem**, so the `+`/`×` entanglement is on
display, paid for in a derivation rather than buried in an axiom. See
`papers/Robinson_1949_DefinabilityArithmetic/`.

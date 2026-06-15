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

### The trust gate
`validate` (terms/formulas) and `validate_proof` (proofs) are the one deliberately
non-polymorphic part. Their job is to reject hostile *subclasses* — a `Var` subtype
with a lying `__eq__`, a `str` subtype, a forged `Fun` with mutable args — before any
`==` is trusted. A polymorphic method would be overridden by exactly such a subclass,
so the gate dispatches on **exact type** (a `dict` keyed by the concrete class, with
a reject-default) and reads fields explicitly. It runs first; downstream code then
operates only on canonical nodes.

## The checker (`checker.py`)
`check = validate_proof` then `proof.derive(theory)`. Each proof rule
(`Axiom … ExistsElim`) is a class with a polymorphic `derive` returning a `Sequent`,
recursing into its sub-proofs. Side conditions are enforced where they live:
induction's eigenvariable (not free in undischarged hypotheses — the side condition
that blocks the `1 = 0` exploit), `Inst`'s cross-sort guard, `ForallIntro`/
`ExistsElim` eigenvariables. `sort_of` is a memoized function delegating to a
polymorphic term method; sequents are re-sort-checked when the theory has a
signature. `check` is **total**: it returns a `Sequent` or raises `TypeError` /
`ValueError`, nothing else.

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

# The Grothendieck bridge: the integers inside Presburger arithmetic

Scope: the machinery `cold_start/quotient.py` and the artifact
`integers_interpretation()` in `cold_start/integers.py`. Everything labeled
**checked** re-derived through `checker.check` with empty hypotheses and the
exact stated conclusion; the artifact has **no open labels**.

## 1. The reach

Every bridge so far was one-dimensional and kept equality absolute: a source
element became one target element, and source `=` stayed target `=`. The full
Tarski–Mostowski–Robinson notion is wider on both axes, and this wave lands
the general machinery plus its first crossing.

The integers do not embed in the naturals — `x + (-x) = 0` is flatly false
of them. Grothendieck's difference construction is the classical repair: a
PAIR `(a, b)` of naturals denotes the integer `a - b`, and two pairs are the
same integer when

    (a, b) ~ (c, d)   :=   a + d = c + b

— an equation the naturals *can* speak, since it never subtracts. Over that
defined equivalence the theory of abelian groups (`algebra.AB_GROUP`:
associativity, commutativity, zero, **inverses**) interprets into plain
PRESBURGER, dimension 2:

| source (AB_GROUP) | target (PRESBURGER, on pairs) |
|---|---|
| `0` | the diagonal `c.1 = c.2` |
| `x + y` | componentwise `(x.1 + y.1, x.2 + y.2)` |
| `neg(x)` | the swap `(x.2, x.1)` |

## 2. The tooling: quotient interpretations

`cold_start/quotient.py` generalizes `interp.py` (which is untouched):

* a source element is a k-tuple of target elements (`vec("x", k)` =
  `x.1 … x.k`); a hoisted application binds a block of k quantifiers;
* source equality translates to the DEFINED equivalence — the honest ε-form,
  never the witness shortcut, so soundness needs no saturation assumption;
* new obligations owed and reported: `equivalence:refl/sym/trans`, and per
  symbol `totality` plus `respect` (equivalent arguments force equivalent
  results — respect at identical arguments *is* uniqueness-up-to-~, so no
  separate uniqueness label exists to quietly weaken).

Report types are shared with `interp.py`, so `cold_start.ledger` reads both
artifact kinds in one table.

## 3. The measurement

    bridge:  28 nodes     (the equivalence + three graph instances)
    toll:    155,545 proof nodes across all thirteen obligations
    open:    ()           -- the bridge is COMPLETE

Paid (all checked in PRESBURGER): the three equivalence laws, totality and
respect for `0`, `+`, `neg`, and the four translated group axioms. The
headline: **`x + (-x) = 0`, an axiom about subtraction, is a paid theorem of
a theory with no negative numbers in it anywhere** — the inverse of `(a, b)`
is just the swap `(b, a)`, and the sum lands on the diagonal.

## 4. The toll's engine: one cancellation recipe

Every payment core is the same argument (`integers.by_cancellation`):

1. orient each hypothesis (`Sym` where needed) and **sum them with `Cong`**
   into one equation `H_L = H_R`;
2. `G_L + H_L = G_L + H_R` by congruence, `= G_R + H_L` by pure AC
   shuffling — `prove_eq` over `add_kit`'s ordered rewriting decides it,
   and the step is exactly the multiset identity `G_L + H_R == G_R + H_L`,
   so a wrong orientation fails loudly;
3. cancel the common suffix with `add_cancel_right`.

Totality is cheaper still: every witness is the image tuple itself, where
the graph collapses to a reflexive equation. Even the associativity axiom —
four hoisted graphs, eight quantifiers — is one cancellation at its core.

## 5. Reproduce

    uv run pytest tests/test_quotient.py tests/test_integers.py -q
    uv run python -m cold_start.integers   # the single-bridge report
    uv run python -m cold_start.ledger     # every bridge, one table

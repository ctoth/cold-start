"""A Lean 4 compatibility layer: our proofs, re-checked by a foreign kernel.

UNTRUSTED. Nothing in the trusted core (syntax/proof/sequent/checker) imports
this module; it imports them freely. Nothing here can make a bad proof good --
`check()` still decides what we have proved.

Why it exists: the De Bruijn criterion says trust the checker, not the prover.
The natural next move is to stop trusting *our* checker too. Rendering a checked
proof term as a Lean 4 term-mode proof makes Lean's kernel an independent
auditor: if `lean ColdStart.lean` exits 0, a second, unrelated implementation of
type theory agrees with our derivations.

The soundness-critical design decision is that the export NEVER emits `axiom`.
An `axiom` declaration would let Lean accept our theorems by fiat -- the foreign
kernel would be checking nothing but our transcription. Instead every proof is
exported in CONDITIONAL form, as a theorem over an abstract carrier:

    theorem t {M : Type} (zero : M) (succ : M -> M) (add : M -> M -> M)
        (ax_add_zero : forall x : M, add x zero = x) ...
        (ind : forall P : M -> Prop, P zero -> (forall n, P n -> P (succ n)) -> forall n, P n)
        : <conclusion> := <term proof>

Every assumption we use is a *hypothesis of the theorem*, so Lean verifies the
entailment "these axioms imply this conclusion" -- exactly the content of our
sequent -- with no new trust. A separate epilogue instantiates the arithmetic
theorems at Lean's own `Nat`, discharging each hypothesis with a core lemma, so
the conditional theorems yield unconditional facts about `Nat`.

Scope: the unsorted arithmetic theories (PRESBURGER, PEANO, ROBINSON_PEANO).
Exporting the many-sorted algebra (a signature with several carriers) is OUT of
scope -- one carrier `M` is baked into the rendering, and a sorted formula is
rejected.

Importing Lean *proofs* is likewise out of scope, and always will be: a Lean
proof term lives in the Calculus of Inductive Constructions -- dependent types,
universes, recursors, definitional unfolding -- and accepting one would mean
implementing (and trusting) a CIC kernel, which is enormously larger than the
first-order checker this project is. We import Lean *statements* only.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .syntax import (
    Bottom,
    BVar,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Node,
    Term,
    Var,
    children,
    forall,
    map_children,
)


class LeanError(ValueError):
    """Raised when a term/formula cannot be expressed in the exported fragment."""


CARRIER = "M"  # the abstract carrier type every exported theorem quantifies over

# Object-language function symbols -> Lean identifiers. A symbol outside this
# map is exported under a sanitized version of its own name.
SYMBOL_NAMES: dict[str, str] = {"0": "zero", "S": "succ", "+": "add", "*": "mul"}

# Names the exported code binds itself; a binder we generate must dodge them.
RESERVED = frozenset(
    {
        *SYMBOL_NAMES.values(),
        "M",
        "P",
        "ind",
        "False",
        "Type",
        "Prop",
        "Nat",
        "fun",
        "theorem",
        "example",
        "let",
        "have",
        "match",
        "with",
        "forall",
        "rfl",
    }
)

_NAME_CANDIDATES = ("x", "y", "z", "n", "m", "a", "b", "c", "u", "v", "w")


# ---------------------------------------------------------------------------
# Names
# ---------------------------------------------------------------------------


def lean_name(name: str) -> str:
    """A Lean 4 identifier for an object-language name. Identifier-shaped names
    pass through; anything else is French-quoted, which Lean accepts verbatim."""
    if name.isidentifier() and name not in RESERVED:
        return name
    if name in SYMBOL_NAMES:
        return SYMBOL_NAMES[name]
    if name.isidentifier():
        return f"{name}_"
    return "«" + name.replace("»", "") + "»"


def symbol_name(symbol: str) -> str:
    """The Lean identifier for a function symbol (`+` -> `add`, `S` -> `succ`)."""
    return SYMBOL_NAMES.get(symbol) or lean_name(symbol)


@dataclass(slots=True)
class _Names:
    """A fresh-name supply. `taken` grows monotonically, so a name handed out is
    never handed out again -- which is what lets the emitters be iterative: no
    scope has to be *restored*, because nothing is ever reused."""

    taken: set = field(default_factory=set)

    def fresh(self, base: str = "x") -> str:
        base = lean_name(base)
        if base not in self.taken and base not in RESERVED:
            self.taken.add(base)
            return base
        i = 1
        while f"{base}_{i}" in self.taken or f"{base}_{i}" in RESERVED:
            i += 1
        self.taken.add(f"{base}_{i}")
        return f"{base}_{i}"


# ---------------------------------------------------------------------------
# Substitution (simultaneous, iterative)
# ---------------------------------------------------------------------------


def substitute(node: Node, sigma: dict) -> Node:
    """Simultaneously replace free `Var`s by name, per `sigma: name -> Term`.

    Iterative (post-order over a heap agenda), and simultaneous -- so mapping
    `{x: y, y: x}` swaps rather than collapsing, which sequential `subst` calls
    would get wrong. Replacement terms contain no `BVar`s (they come from proof
    terms, which are closed at the object level), so no index shifting is needed
    and a node's image is independent of the binder depth it sits at."""
    if not sigma:
        return node
    order: list = []
    stack: list = [node]
    while stack:
        n = stack.pop()
        order.append(n)
        stack.extend(children(n))
    done: dict = {}
    for n in reversed(order):
        if type(n) is Var and n.name in sigma:
            done[id(n)] = sigma[n.name]
        else:
            done[id(n)] = map_children(n, lambda c: done[id(c)])
    return done[id(node)]


# ---------------------------------------------------------------------------
# Rendering terms and formulas
# ---------------------------------------------------------------------------
# Precedence levels: a node emits at its own level and wraps itself in parens
# when the position demands a tighter one. `->`/quantifiers extend as far right
# as possible (level 1), `=` binds tighter (3), application tighter still (9),
# and an atom never needs parens (10).

_L_IMPL = 1
_L_EQ = 3
_L_APP = 9
_L_ATOM = 10


def render_term(term: Term) -> str:
    """Render a term as a Lean 4 expression over the carrier's operations."""
    return _render(term, _Names(_free_names(term)), _L_IMPL)


def render_formula(formula: Formula) -> str:
    """Render a formula as a Lean 4 `Prop`, leaving free variables as free Lean
    identifiers (our implicit universal quantification is NOT applied here --
    see `render_statement`)."""
    return _render(formula, _Names(_free_names(formula)), _L_IMPL)


def render_statement(formula: Formula) -> str:
    """Render a formula as a standalone Lean 4 statement: free variables, which
    our theories read as implicitly universal, become leading `forall` binders in
    lexicographic order. That order is the contract instantiation relies on --
    `Inst` on the k-th name must line up with the k-th binder."""
    names = closure_names(formula)
    supply = _Names(_free_names(formula))
    body = _render(formula, supply, _L_IMPL)
    prefix = "".join(f"∀ {lean_name(n)} : {CARRIER}, " for n in names)
    return prefix + body


def closure_names(formula: Formula) -> tuple:
    """The free variable names of `formula`, in the order `render_statement`
    binds them (lexicographic)."""
    return tuple(sorted(formula.free_vars()))


def universal_closure(formula: Formula) -> Formula:
    """The locally-nameless universal closure over the free variables, in the
    same lexicographic order `render_statement` uses. This is the formula a
    round-trip through Lean text recovers."""
    out = formula
    for name in reversed(closure_names(formula)):
        out = forall(name, "", out)
    return out


def _free_names(node: Node) -> set:
    return {lean_name(n) for n in node.free_vars()}


def _render(node: Node, supply: _Names, prec: int) -> str:
    """Emit `node` as Lean text, ITERATIVELY and in O(tree size): a pre-order walk
    pushes `("emit", node, prec, scope)` and `("lit", text)` items and appends
    fragments left-to-right into `out`, joined once at the end. `scope` is the
    tuple of enclosing binder names (nearest last), carried *by value* on each
    item -- so a binder needs no matching "pop" continuation and a `BVar(i)`
    reads `scope[-1 - i]`."""
    out: list[str] = []
    stack: list = [("emit", node, prec, ())]
    while stack:
        item = stack.pop()
        if item[0] == "lit":
            out.append(item[1])
        else:
            _emit(item[1], supply, item[2], item[3], out, stack)
    return "".join(out)


def _push(stack: list, pieces: list) -> None:
    """Push `pieces` (forward order) so they pop left-to-right."""
    stack.extend(reversed(pieces))


def _wrapped(level: int, prec: int, pieces: list) -> list:
    return [("lit", "("), *pieces, ("lit", ")")] if level < prec else pieces


def _emit(node, supply: _Names, prec: int, scope: tuple, out: list, stack: list) -> None:
    kind = type(node)
    if kind is Var:
        if node.sort:
            raise LeanError(f"sorted variable {node!r}: the export has one carrier {CARRIER}")
        out.append(lean_name(node.name))
        return
    if kind is BVar:
        if not 0 <= node.index < len(scope):
            raise LeanError("dangling bound variable outside its binder")
        out.append(scope[-1 - node.index])
        return
    if kind is Fun:
        name = symbol_name(node.name)
        if not node.args:
            out.append(name)
            return
        pieces: list = [("lit", name)]
        for arg in node.args:
            pieces += [("lit", " "), ("emit", arg, _L_ATOM, scope)]
        _push(stack, _wrapped(_L_APP, prec, pieces))
        return
    if kind is Bottom:
        out.append("False")
        return
    if kind is Eq:
        pieces = [
            ("emit", node.lhs, _L_EQ, scope),
            ("lit", " = "),
            ("emit", node.rhs, _L_EQ, scope),
        ]
        _push(stack, _wrapped(_L_EQ, prec, pieces))
        return
    if kind is Implies:
        pieces = [
            ("emit", node.ant, _L_IMPL + 1, scope),
            ("lit", " → "),
            ("emit", node.con, _L_IMPL, scope),
        ]
        _push(stack, _wrapped(_L_IMPL, prec, pieces))
        return
    if kind is Forall or kind is Exists:
        if node.sort:
            raise LeanError(f"sorted binder :{node.sort}: the export has one carrier {CARRIER}")
        name = supply.fresh(_binder_base(supply))
        symbol = "∀" if kind is Forall else "∃"
        pieces = [
            ("lit", f"{symbol} {name} : {CARRIER}, "),
            ("emit", node.body, _L_IMPL, (*scope, name)),
        ]
        _push(stack, _wrapped(_L_IMPL, prec, pieces))
        return
    raise LeanError(f"cannot render {kind.__name__} in Lean")


def _binder_base(supply: _Names) -> str:
    """The next readable binder name that is still free."""
    for cand in _NAME_CANDIDATES:
        if cand not in supply.taken and cand not in RESERVED:
            return cand
    return "x"


__all__ = [
    "CARRIER",
    "LeanError",
    "closure_names",
    "lean_name",
    "render_formula",
    "render_statement",
    "render_term",
    "substitute",
    "symbol_name",
    "universal_closure",
]

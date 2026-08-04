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
from pathlib import Path
from typing import TypeVar, cast

from . import peano as _peano
from . import presburger as _presburger
from . import robinson as _robinson
from .checker import Theory, check
from .emitter import Emitter, Visit, case
from .proof import (
    CANONICAL_PROOF_TYPES,
    MP,
    RAA,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsElim,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Induct,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .proofs import (
    add_proof,
    left_identity_proof,
    mul_cancel_right_succ,
    mul_proof,
    robinson_add_proof,
)
from .robinson_proofs import bridge_converse_positive
from .sequent import Sequent
from .syntax import (
    CANONICAL_NODE_TYPES,
    Bottom,
    BVar,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Node,
    Not,
    Rel,
    Term,
    Var,
    children,
    exists,
    forall,
    instantiate,
    map_children,
)

_N = TypeVar("_N", bound=Node)  # substitution preserves the node's kind


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


def substitute(node: _N, sigma: dict) -> _N:
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
    return cast(_N, done[id(node)])


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


@dataclass(frozen=True, slots=True)
class _Style:
    """How the carrier and the function symbols are spelled. The abstract style
    is what a conditional theorem is stated over (`M`, with `zero`/`succ`/... as
    its parameters); the `Nat` style re-renders the very same formulas at Lean's
    own naturals, which is what lets the epilogue state the instantiated facts
    without any string surgery."""

    carrier: str
    symbols: dict

    def symbol(self, name: str) -> str:
        return self.symbols.get(name) or lean_name(name)


_ABSTRACT = _Style(CARRIER, SYMBOL_NAMES)
_NAT = _Style("Nat", {"0": "Nat.zero", "S": "Nat.succ", "+": "Nat.add", "*": "Nat.mul"})


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
    return _render_statement(formula, _ABSTRACT)


def _render_statement(formula: Formula, style: _Style) -> str:
    names = closure_names(formula)
    supply = _Names(_free_names(formula))
    body = _render(formula, supply, _L_IMPL, style)
    prefix = "".join(f"∀ {lean_name(n)} : {style.carrier}, " for n in names)
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


def _render(node: Node, supply: _Names, prec: int, style: _Style = _ABSTRACT) -> str:
    """Emit `node` as Lean text iteratively through exact external cases."""
    return _LeanSyntaxEmitter(supply, style).render(node, _LeanSyntaxContext(prec))


@dataclass(frozen=True, slots=True)
class _LeanSyntaxContext:
    prec: int
    scope: tuple[str, ...] = ()


def _wrapped(level: int, prec: int, pieces: list[object]) -> tuple[object, ...]:
    return ("(", *pieces, ")") if level < prec else tuple(pieces)


class _LeanSyntaxEmitter(
    Emitter[Node, _LeanSyntaxContext],
    covers=CANONICAL_NODE_TYPES,
):
    __slots__ = ("style", "supply")

    def __init__(self, supply: _Names, style: _Style) -> None:
        self.supply = supply
        self.style = style

    def unsupported(self, value: object, context: object) -> tuple[object, ...]:
        raise LeanError(f"cannot render {type(value).__name__} in Lean")

    @case(Var)
    def var(self, node: Var, context: _LeanSyntaxContext) -> tuple[object, ...]:
        if node.sort:
            raise LeanError(f"sorted variable {node!r}: the export has one carrier {CARRIER}")
        return (lean_name(node.name),)

    @case(BVar)
    def bvar(self, node: BVar, context: _LeanSyntaxContext) -> tuple[object, ...]:
        if not 0 <= node.index < len(context.scope):
            raise LeanError("dangling bound variable outside its binder")
        return (context.scope[-1 - node.index],)

    @case(Fun)
    def fun(self, node: Fun, context: _LeanSyntaxContext) -> tuple[object, ...]:
        name = self.style.symbol(node.name)
        if not node.args:
            return (name,)
        pieces: list[object] = [name]
        for arg in node.args:
            pieces += [" ", Visit(arg, _LeanSyntaxContext(_L_ATOM, context.scope))]
        return _wrapped(_L_APP, context.prec, pieces)

    @case(Bottom)
    def bottom(self, node: Bottom, context: _LeanSyntaxContext) -> tuple[object, ...]:
        return ("False",)

    @case(Eq)
    def eq(self, node: Eq, context: _LeanSyntaxContext) -> tuple[object, ...]:
        pieces = [
            Visit(node.lhs, _LeanSyntaxContext(_L_EQ, context.scope)),
            " = ",
            Visit(node.rhs, _LeanSyntaxContext(_L_EQ, context.scope)),
        ]
        return _wrapped(_L_EQ, context.prec, pieces)

    @case(Implies)
    def implies(self, node: Implies, context: _LeanSyntaxContext) -> tuple[object, ...]:
        pieces = [
            Visit(node.ant, _LeanSyntaxContext(_L_IMPL + 1, context.scope)),
            " → ",
            Visit(node.con, _LeanSyntaxContext(_L_IMPL, context.scope)),
        ]
        return _wrapped(_L_IMPL, context.prec, pieces)

    @case(Forall, Exists)
    def binder(self, node: Forall | Exists, context: _LeanSyntaxContext) -> tuple[object, ...]:
        if node.sort:
            raise LeanError(f"sorted binder :{node.sort}: the export has one carrier {CARRIER}")
        name = self.supply.fresh(_binder_base(self.supply))
        symbol = "∀" if type(node) is Forall else "∃"
        pieces = [
            f"{symbol} {name} : {self.style.carrier}, ",
            Visit(node.body, _LeanSyntaxContext(_L_IMPL, (*context.scope, name))),
        ]
        return _wrapped(_L_IMPL, context.prec, pieces)

    @case(Rel)
    def relation(self, node: Rel, context: _LeanSyntaxContext) -> tuple[object, ...]:
        raise LeanError(f"cannot render {type(node).__name__} in Lean")


def _binder_base(supply: _Names) -> str:
    """The next readable binder name that is still free."""
    for cand in _NAME_CANDIDATES:
        if cand not in supply.taken and cand not in RESERVED:
            return cand
    return "x"


# ---------------------------------------------------------------------------
# Reading Lean back: the statement fragment only
# ---------------------------------------------------------------------------
# We parse exactly what we emit -- forall/exists over the carrier, `=`, `→`,
# `False`, applications, parentheses -- and nothing else. That is enough to
# check the round trip (and to read a statement someone hands us), and it stops
# well short of Lean's real grammar, let alone its proof terms.

_SYMBOLS_BY_LEAN = {v: k for k, v in SYMBOL_NAMES.items()}
_ARITY = {"0": 0, "S": 1, "+": 2, "*": 2}

_P_IMPL = 1
_P_EQ = 2
_P_APP = 4  # application binds tightest; an argument parses at this level

_EOF = "EOF"
_ARROWS = {"→", "->"}
_FORALLS = {"∀", "forall"}
_EXISTSES = {"∃", "exists"}
_PENDING = object()


@dataclass(frozen=True, slots=True)
class _Token:
    text: str
    pos: int
    is_name: bool


def parse_term(text: str) -> Term:
    """Parse a Lean term of the exported fragment back into our syntax."""
    parser = _Parser(text)
    node = parser.run(_P_IMPL)
    parser.expect_eof()
    if not isinstance(node, Term):
        raise LeanError(f"expected a term, got {node!r}")
    return node


def parse_formula(text: str) -> Formula:
    """Parse a Lean statement of the exported fragment back into our syntax.

    Binders come back locally nameless, so `parse_formula(render_statement(f))`
    is literally `universal_closure(f)` -- the round trip is `==`, with no alpha
    relation in the way."""
    parser = _Parser(text)
    node = parser.run(0)
    parser.expect_eof()
    if not isinstance(node, Formula):
        raise LeanError(f"expected a formula, got {node!r}")
    return node


def _tokenize(text: str) -> list:
    tokens: list = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if text.startswith("->", i):
            tokens.append(_Token("->", i, False))
            i += 2
            continue
        if ch in "(),:=∀∃→":
            tokens.append(_Token(ch, i, False))
            i += 1
            continue
        if ch == "«":
            end = text.find("»", i)
            if end < 0:
                raise LeanError(f"unterminated quoted name at column {i + 1}")
            tokens.append(_Token(text[i + 1 : end], i, True))
            i = end + 1
            continue
        if ch.isalpha() or ch == "_":
            start = i
            while i < len(text) and (text[i].isalnum() or text[i] in "_'."):
                i += 1
            tokens.append(_Token(text[start:i], start, True))
            continue
        raise LeanError(f"unexpected character {ch!r} at column {i + 1}")
    tokens.append(_Token("", len(text), False))
    return tokens


class _Parser:
    """Iterative precedence-climbing (Pratt) parser, mirroring `notation._Parser`:
    the recursion of a descent parser is replaced by an explicit control stack, so
    a statement nested arbitrarily deep parses without touching the call stack.
    One expression grammar covers terms and formulas; the node constructors do the
    typing (`→` needs formulas, `=` needs terms)."""

    def __init__(self, text: str) -> None:
        self.tokens = _tokenize(text)
        self.i = 0
        self.bound: list = []  # enclosing binder names, nearest last

    # --- token helpers ------------------------------------------------------

    def peek(self) -> _Token:
        return self.tokens[self.i]

    def advance(self) -> _Token:
        tok = self.peek()
        self.i += 1
        return tok

    def at_eof(self) -> bool:
        return self.i >= len(self.tokens) - 1

    def expect(self, text: str) -> None:
        if self.peek().text != text or self.at_eof():
            self.error(f"expected {text!r}, got {self.peek().text!r}")
        self.advance()

    def expect_name(self) -> str:
        tok = self.peek()
        if not tok.is_name or self.at_eof():
            self.error(f"expected a name, got {tok.text!r}")
        self.advance()
        return tok.text

    def expect_eof(self) -> None:
        if not self.at_eof():
            self.error(f"unexpected token {self.peek().text!r}")

    def error(self, message: str):
        raise LeanError(f"{message} at column {self.peek().pos + 1}")

    def starts_atom(self) -> bool:
        tok = self.peek()
        return not self.at_eof() and (tok.is_name or tok.text == "(")

    # --- the iterative Pratt core -------------------------------------------

    def run(self, min_prec: int):
        ctrl: list = [("expr", min_prec)]
        result: object = _PENDING
        while ctrl:
            tag, *rest = ctrl.pop()
            if tag == "expr":
                ctrl.append(("loop", rest[0]))
                ctrl.append(("atom", rest[0]))
            elif tag == "atom":
                value = self._nud(ctrl, rest[0])
                if value is not _PENDING:
                    result = value
            elif tag == "loop":
                min_p = rest[0]
                prec = self._infix_prec(self.peek().text)
                if prec is not None and prec >= min_p and not self.at_eof():
                    op = self.advance().text
                    nxt = prec if prec == _P_IMPL else prec + 1  # `→` is right-associative
                    ctrl.append(("combine", op, result, min_p))
                    ctrl.append(("expr", nxt))
            elif tag == "combine":
                op, left, min_p = rest
                result = self._combine(op, left, result)
                ctrl.append(("loop", min_p))
            elif tag == "close":
                self.expect(")")
            elif tag == "quant":
                result = self._finish_quant(rest[0], rest[1], result)
            elif tag == "arg":
                result = self._continue_app(ctrl, rest[0], rest[1], result)
        return result

    def _infix_prec(self, text: str) -> int | None:
        if text in _ARROWS:
            return _P_IMPL
        if text == "=":
            return _P_EQ
        return None

    def _nud(self, ctrl: list, min_prec: int) -> object:
        tok = self.peek()
        if self.at_eof():
            self.error("unexpected end of input")
        if tok.text in _FORALLS or tok.text in _EXISTSES:
            return self._begin_quant(ctrl, forall if tok.text in _FORALLS else exists)
        if tok.text == "(":
            self.advance()
            ctrl.append(("close",))
            ctrl.append(("expr", 0))
            return _PENDING
        if tok.text == "False":
            self.advance()
            return Bottom()
        if not tok.is_name:
            self.error(f"expected a term or formula, got {tok.text!r}")
        name = self.advance().text
        if min_prec < _P_APP and self.starts_atom():
            ctrl.append(("arg", name, ()))
            ctrl.append(("expr", _P_APP))
            return _PENDING
        return self._build(name, ())

    def _begin_quant(self, ctrl: list, ctor) -> object:
        self.advance()  # the quantifier symbol
        name = self.expect_name()
        self.expect(":")
        sort = self.expect_name()
        if sort != CARRIER:
            self.error(f"the export has one carrier {CARRIER}, got {sort!r}")
        self.expect(",")
        if name in self.bound:
            # `forall`/`exists` abstract *every* free occurrence of the name, so a
            # shadowing binder would steal the outer one's occurrences. We never
            # emit shadowing names (the fresh supply is monotonic), so reject.
            self.error(f"shadowing binder {name!r} is outside the exported fragment")
        self.bound.append(name)
        ctrl.append(("quant", name, ctor))
        ctrl.append(("expr", 0))  # the body is greedy
        return _PENDING

    def _finish_quant(self, name: str, ctor, body: object) -> Formula:
        self.bound.pop()
        if not isinstance(body, Formula):
            self.error("a quantifier body must be a formula")
        # The body already carries `name` as a free `Var`; `ctor` abstracts it.
        return ctor(name, "", body)

    def _continue_app(self, ctrl: list, name: str, acc: tuple, arg: object) -> object:
        if not isinstance(arg, Term):
            self.error("function arguments must be terms")
        acc = (*acc, arg)
        if self.starts_atom():
            ctrl.append(("arg", name, acc))
            ctrl.append(("expr", _P_APP))
            return _PENDING
        return self._build(name, acc)

    def _build(self, name: str, args: tuple) -> Term:
        """A name applied to `args`: a known symbol at its arity, an uninterpreted
        function, or (unapplied) a variable -- free, or a binder's own name, which
        `_finish_quant` later abstracts into its de Bruijn index."""
        symbol = _SYMBOLS_BY_LEAN.get(name)
        if symbol is not None:
            if len(args) != _ARITY[symbol]:
                self.error(f"{name} takes {_ARITY[symbol]} argument(s), got {len(args)}")
            return Fun(symbol, args)
        return Fun(name, args) if args else Var(name)

    def _combine(self, op: str, left: object, right: object):
        if op in _ARROWS:
            if not (isinstance(left, Formula) and isinstance(right, Formula)):
                self.error("an implication needs formulas on both sides")
            return Implies(left, right)
        if not (isinstance(left, Term) and isinstance(right, Term)):
            self.error("an equality needs terms on both sides")
        return Eq(left, right)


# ---------------------------------------------------------------------------
# Proof export: one conditional theorem per checked proof
# ---------------------------------------------------------------------------

# Readable names for the axioms of the theories we export. Anything unrecognised
# gets `ax<n>` from a deterministic ordering, so the export never depends on a
# theory's `frozenset` iteration order.
AXIOM_LABELS: dict = {
    _presburger.ADD_ZERO_F: "ax_add_zero",
    _presburger.ADD_SUCC_F: "ax_add_succ",
    _presburger.SUCC_NEQ_ZERO: "ax_succ_ne_zero",
    _presburger.SUCC_INJ: "ax_succ_inj",
    _peano.MUL_ZERO_F: "ax_mul_zero",
    _peano.MUL_SUCC_F: "ax_mul_succ",
    _robinson.SUCC_NEQ_ONE: "ax_succ_ne_one",
    _robinson.SUCC_INJ: "ax_succ_inj",
    _robinson.ADD_ONE: "ax_add_one",
    _robinson.ADD_SUCC: "ax_add_succ",
    _robinson.MUL_ONE: "ax_mul_one",
    _robinson.MUL_SUCC: "ax_mul_succ",
}


def export_theorem(name: str, pf: object, theory: Theory) -> str:
    """Render a checked proof as a self-contained Lean 4 `theorem`.

    The proof is re-checked here (`check`), so an unproved recipe never reaches
    the file. What comes out is CONDITIONAL: the theory's function symbols and
    axioms -- and the induction principle, if the proof uses `Induct` -- are
    hypotheses of the theorem, over an abstract carrier `M`. No `axiom`, no
    `sorry`: Lean is asked to verify the entailment, not to believe us."""
    return _Export(pf, theory).theorem(name)


def uses_induction(pf: object) -> bool:
    """Whether the proof cites the `Induct` rule (so needs the `ind` hypothesis)."""
    return any(type(n) is Induct for n in _tree(pf))


def _tree(node: object):
    """Every dataclass node under `node` -- proof terms and the syntax they embed --
    iteratively (a proof term is a dataclass, so `children` walks it too)."""
    stack: list = [node]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(children(n))


def _symbols(nodes) -> dict:
    """`name -> arity` for every function symbol occurring in `nodes`."""
    arities: dict = {}
    for root in nodes:
        for n in _tree(root):
            if type(n) is Fun:
                arity = len(n.args)
                if arities.setdefault(n.name, arity) != arity:
                    raise LeanError(f"symbol {n.name!r} used at two arities")
    return arities


def _var_names(nodes) -> set:
    return {n.name for root in nodes for n in _tree(root) if type(n) is Var}


def _fun_type(arity: int) -> str:
    return " → ".join([CARRIER] * (arity + 1))


@dataclass(frozen=True, slots=True)
class _ProofContext:
    sigma: dict
    env: dict


@dataclass(slots=True)
class _Export(
    Emitter[Pf, _ProofContext],
    covers=CANONICAL_PROOF_TYPES,
):
    """One theorem's worth of export state: the naming decisions, then the
    emitters that consume them.

    The proof is rendered under a substitution environment `sigma` (object
    variable name -> the term it now stands for) threaded downward, which is what
    makes `Inst` free: instantiating a variable is not an operation in the Lean
    proof at all, it is a change to the environment the *same* sub-proof renders
    under. An axiom is then rendered as its hypothesis applied to the images of
    its own free variables, in `closure_names` order -- the one place where the
    lexicographic closure order is load-bearing."""

    pf: object
    theory: Theory
    seq: Sequent = field(init=False)
    supply: _Names = field(init=False)
    axiom_names: dict = field(init=False)
    open_names: dict = field(init=False)
    symbols: dict = field(init=False)
    sigma0: dict = field(init=False)
    concls: dict = field(init=False, default_factory=dict)

    def __post_init__(self) -> None:
        self.seq = check(self.pf, self.theory)
        roots = [self.pf, self.seq.concl, *self.seq.hyps, *self.theory.axioms]
        if self.theory.zero is not None:
            roots.append(self.theory.zero)
        self.symbols = _symbols(roots)
        self.supply = _Names({_ABSTRACT.symbol(s) for s in self.symbols})
        self.axiom_names = {}
        for i, ax in enumerate(sorted(self.theory.axioms, key=render_statement)):
            self.axiom_names[ax] = self.supply.fresh(AXIOM_LABELS.get(ax, f"ax{i + 1}"))
        if uses_induction(self.pf):
            self.supply.fresh("ind")
        # Object variables are renamed only when their name is not usable in Lean
        # (or is already a parameter); everything else keeps the name it had.
        self.sigma0 = {}
        for v in sorted(_var_names(roots)):
            target = self.supply.fresh(v)
            if target != v:
                self.sigma0[v] = Var(target)
        self.open_names = {}
        for hyp in sorted(self.seq.hyps, key=render_statement):
            self.open_names[self.subst(hyp)] = self.supply.fresh("h")

    # --- naming and substitution -------------------------------------------

    def subst(self, node):
        return substitute(node, self.sigma0)

    def conclusion(self, pf: object) -> Formula:
        """A sub-proof's derived conclusion (cached). Only the rules that cannot
        read their own conclusion off their fields -- `ExistsElim` -- need it."""
        hit = self.concls.get(id(pf))
        if hit is None:
            hit = cast(Pf, pf).derive(self.theory).concl
            self.concls[id(pf)] = hit
        return hit

    # --- the theorem --------------------------------------------------------

    def symbol_order(self) -> list:
        """The theory's function symbols as the theorem takes them: constants
        first, then by name -- so an arithmetic signature reads zero, succ, add,
        mul. Deterministic, and shared by the theorem and its `Nat` instance."""
        return sorted(self.symbols, key=lambda s: (self.symbols[s], _ABSTRACT.symbol(s)))

    def theorem(self, name: str) -> str:
        concl = self.subst(self.seq.concl)
        hyps = [self.subst(h) for h in sorted(self.seq.hyps, key=render_statement)]
        hyp_vars = sorted({v for h in hyps for v in h.free_vars()})
        concl_vars = [v for v in closure_names(concl) if v not in hyp_vars]

        params = [f"{{{CARRIER} : Type}}"]
        params += [
            f"({_ABSTRACT.symbol(s)} : {_fun_type(self.symbols[s])})" for s in self.symbol_order()
        ]
        params += [f"({lean_name(v)} : {CARRIER})" for v in hyp_vars]
        params += [f"({self.open_names[h]} : {render_formula(h)})" for h in hyps]
        params += [
            f"({self.axiom_names[ax]} : {render_statement(ax)})"
            for ax in sorted(self.theory.axioms, key=lambda a: self.axiom_names[a])
        ]
        if uses_induction(self.pf):
            params.append(f"(ind : {self.induction_type()})")

        statement = "".join(f"∀ {lean_name(v)} : {CARRIER}, " for v in concl_vars)
        statement += render_formula(concl)
        body = "".join(f"fun {lean_name(v)} : {CARRIER} => " for v in concl_vars)
        body += self.proof_text(self.pf, self.sigma0, {})

        head = f"theorem {name} " + " ".join(params[:4])
        rest = "".join(f"\n    {p}" for p in params[4:])
        return f"{head}{rest}\n    : {statement} :=\n  {body}\n"

    def nat_example(self, name: str) -> str:
        """The same theorem, instantiated at Lean's `Nat`: every hypothesis is
        supplied by a core lemma, so what remains is an unconditional `example`.
        Arguments are passed by NAME, so this never depends on parameter order."""
        if self.seq.hyps:
            raise LeanError("cannot instantiate a theorem with open hypotheses at Nat")
        statement = _render_statement(self.subst(self.seq.concl), _NAT)
        args = [f"({CARRIER} := Nat)"]
        args += [f"({_ABSTRACT.symbol(s)} := {_NAT.symbol(s)})" for s in self.symbol_order()]
        for ax in sorted(self.theory.axioms, key=lambda a: self.axiom_names[a]):
            label = self.axiom_names[ax]
            proof = NAT_AXIOM_PROOFS.get(label)
            if proof is None:
                raise LeanError(f"no Nat proof for the hypothesis {label}")
            args.append(f"({label} := {proof})")
        if uses_induction(self.pf):
            args.append(f"(ind := {NAT_INDUCTION})")
        applied = "\n    ".join([f"  {name} {args[0]}", *args[1:]])
        return f"example : {statement} :=\n{applied}\n"

    def induction_type(self) -> str:
        """The induction principle as a hypothesis: exactly the schema our
        `Induct` rule implements, with the theory's own base term."""
        zero = self.term_text(self.theory.zero, _L_ATOM)
        succ = _ABSTRACT.symbol(self.theory.succ or "S")
        return (
            f"∀ P : {CARRIER} → Prop, P {zero} → "
            f"(∀ n : {CARRIER}, P n → P ({succ} n)) → ∀ n : {CARRIER}, P n"
        )

    def term_text(self, term, prec: int = _L_ATOM) -> str:
        return _render(term, _Names(_free_names(term)), prec)

    # --- the proof term -----------------------------------------------------

    def proof_text(self, pf: object, sigma: dict, env: dict) -> str:
        """Render a proof iteratively with environments carried on each visit."""
        return self.render(cast(Pf, pf), _ProofContext(sigma, env))

    def unsupported(self, value: object, context: object) -> tuple[object, ...]:
        raise LeanError(f"cannot export the rule {type(value).__name__}")

    @case(Axiom)
    def _axiom(self, pf: Axiom, context: _ProofContext) -> tuple[object, ...]:
        name = self.axiom_names.get(pf.formula)
        if name is None:
            raise LeanError(f"not an axiom of the exported theory: {pf.formula!r}")
        args = [
            self.term_text(substitute(Var(v), context.sigma), _L_ATOM)
            for v in closure_names(pf.formula)
        ]
        return (f"({name} {' '.join(args)})" if args else name,)

    @case(Assume)
    def _assume(self, pf: Assume, context: _ProofContext) -> tuple[object, ...]:
        key = substitute(pf.formula, context.sigma)
        name = context.env.get(key) or self.open_names.get(key)
        if name is None:
            raise LeanError(f"no hypothesis in scope for {key!r}")
        return (name,)

    @case(Refl)
    def _refl(self, pf: Refl, context: _ProofContext) -> tuple[object, ...]:
        return (f"(Eq.refl {self.term_text(substitute(pf.term, context.sigma))})",)

    @case(Sym)
    def _sym(self, pf: Sym, context: _ProofContext) -> tuple[object, ...]:
        return ("(Eq.symm ", Visit(pf.sub, context), ")")

    @case(Trans)
    def _trans(self, pf: Trans, context: _ProofContext) -> tuple[object, ...]:
        return (
            "(Eq.trans ",
            Visit(pf.left, context),
            " ",
            Visit(pf.right, context),
            ")",
        )

    @case(Cong)
    def _cong(self, pf: Cong, context: _ProofContext) -> tuple[object, ...]:
        """`congrArg f h₁` gives `f a₁ = f b₁` (partially applied for an n-ary f);
        each further argument is folded on with `congr : f = g → a = b → f a = g b`."""
        name = _ABSTRACT.symbol(pf.fun)
        if not pf.args:
            return (f"(Eq.refl {name})",)
        pieces: list[object] = ["(congr " * (len(pf.args) - 1)]
        pieces += [f"(congrArg {name} ", Visit(pf.args[0], context), ")"]
        for sub in pf.args[1:]:
            pieces += [" ", Visit(sub, context), ")"]
        return tuple(pieces)

    @case(MP)
    def _mp(self, pf: MP, context: _ProofContext) -> tuple[object, ...]:
        return ("(", Visit(pf.imp, context), " ", Visit(pf.ant, context), ")")

    @case(ImpIntro)
    def _imp_intro(self, pf: ImpIntro, context: _ProofContext) -> tuple[object, ...]:
        hyp = substitute(pf.hyp, context.sigma)
        name = self.supply.fresh("h")
        return (
            f"(fun {name} : {render_formula(hyp)} => ",
            Visit(pf.body, _ProofContext(context.sigma, {**context.env, hyp: name})),
            ")",
        )

    @case(Inst)
    def _inst(self, pf: Inst, context: _ProofContext) -> tuple[object, ...]:
        """Instantiation emits nothing: it re-renders the sub-proof under an
        extended environment, so the variable is already gone by the time any
        axiom or hypothesis is printed."""
        sigma = {**context.sigma, pf.var: substitute(pf.term, context.sigma)}
        return (Visit(pf.sub, _ProofContext(sigma, context.env)),)

    @case(Induct)
    def _induct(self, pf: Induct, context: _ProofContext) -> tuple[object, ...]:
        """`ind (fun n => P n) <base at zero> (fun n => <step at n>) <the variable>`.
        Our `Induct` proves `pred` with `var` still free -- read as universally
        quantified -- so the Lean term applies the principle back to `var`'s
        current image, and base/step render under `var := zero` / `var := n`."""
        base_var = self.supply.fresh(pf.var)
        step_var = self.supply.fresh(pf.var)
        motive = render_formula(
            substitute(pf.pred, {**context.sigma, pf.var: Var(base_var)})
        )
        arg = self.term_text(substitute(Var(pf.var), context.sigma))
        return (
            f"(ind (fun {base_var} : {CARRIER} => {motive}) ",
            Visit(
                pf.base,
                _ProofContext({**context.sigma, pf.var: self.theory.zero}, context.env),
            ),
            f" (fun {step_var} : {CARRIER} => ",
            Visit(
                pf.step,
                _ProofContext({**context.sigma, pf.var: Var(step_var)}, context.env),
            ),
            f") {arg})",
        )

    @case(ExFalso)
    def _ex_falso(self, pf: ExFalso, context: _ProofContext) -> tuple[object, ...]:
        concl = render_formula(substitute(pf.concl, context.sigma))
        return ("(False.elim ", Visit(pf.sub, context), f" : {concl})")

    @case(RAA)
    def _raa(self, pf: RAA, context: _ProofContext) -> tuple[object, ...]:
        goal = substitute(pf.goal, context.sigma)
        negated = Not(goal)
        name = self.supply.fresh("h")
        return (
            f"(Classical.byContradiction (fun {name} : {render_formula(negated)} => ",
            Visit(pf.sub, _ProofContext(context.sigma, {**context.env, negated: name})),
            f") : {render_formula(goal)})",
        )

    @case(ForallElim)
    def _forall_elim(self, pf: ForallElim, context: _ProofContext) -> tuple[object, ...]:
        arg = self.term_text(substitute(pf.term, context.sigma))
        return ("(", Visit(pf.sub, context), f" {arg})")

    @case(ForallIntro)
    def _forall_intro(self, pf: ForallIntro, context: _ProofContext) -> tuple[object, ...]:
        if pf.sort:
            raise LeanError(f"sorted generalization :{pf.sort} is out of scope")
        name = self.supply.fresh(pf.var)
        return (
            f"(fun {name} : {CARRIER} => ",
            Visit(
                pf.sub,
                _ProofContext({**context.sigma, pf.var: Var(name)}, context.env),
            ),
            ")",
        )

    @case(ExistsIntro)
    def _exists_intro(self, pf: ExistsIntro, context: _ProofContext) -> tuple[object, ...]:
        claim = render_formula(substitute(pf.claim, context.sigma))
        witness = self.term_text(substitute(pf.witness, context.sigma))
        return (f"(Exists.intro {witness} ", Visit(pf.sub, context), f" : {claim})")

    @case(ExistsElim)
    def _exists_elim(self, pf: ExistsElim, context: _ProofContext) -> tuple[object, ...]:
        ex = self.conclusion(pf.sub_ex)
        if type(ex) is not Exists:
            raise LeanError(f"exists-elim needs an existential, got {ex!r}")
        name = self.supply.fresh(pf.eigenvar)
        inner = {**context.sigma, pf.eigenvar: Var(name)}
        instance = substitute(instantiate(ex, Var(pf.eigenvar)), inner)
        hyp = self.supply.fresh("h")
        phi = render_formula(substitute(self.conclusion(pf.sub_use), inner))
        return (
            "(Exists.elim ",
            Visit(pf.sub_ex, context),
            f" (fun {name} : {CARRIER} => fun {hyp} : {render_formula(instance)} => ",
            Visit(pf.sub_use, _ProofContext(inner, {**context.env, instance: hyp})),
            f") : {phi})",
        )


# ---------------------------------------------------------------------------
# The corpus: one self-contained Lean file
# ---------------------------------------------------------------------------

CORPUS_PATH = Path(__file__).resolve().parent.parent / "lean_export" / "ColdStart.lean"

# Discharging each abstract hypothesis at Lean's `Nat`. The recursion axioms are
# `rfl`: `Nat.add`/`Nat.mul` recurse on their second argument exactly as our
# axioms say, so the two sides are definitionally equal. The successor axioms are
# `noConfusion`, the injectivity/disjointness of constructors.
NAT_AXIOM_PROOFS: dict = {
    "ax_add_zero": "fun x => rfl",
    "ax_add_succ": "fun x y => rfl",
    "ax_mul_zero": "fun x => rfl",
    "ax_mul_succ": "fun x y => rfl",
    "ax_succ_ne_zero": "fun x h => Nat.noConfusion h",
    "ax_succ_inj": "fun x y h => Nat.noConfusion h (fun h' => h')",
}
NAT_INDUCTION = "fun P h0 hs n => Nat.rec (motive := P) h0 hs n"

_HEADER = """/-
  ColdStart.lean

  Generated by `uv run python -m cold_start.lean` -- do not edit by hand.

  Each theorem below is a proof term from the `cold_start` checker, re-rendered
  for Lean 4. The point is the De Bruijn criterion: our checker re-derives a
  proof instead of trusting it, and this file hands the same derivations to a
  completely independent kernel. If Lean accepts this file, two unrelated
  implementations agree.

  Nothing here is asserted. There are no `axiom` declarations, no placeholder
  proofs and no tactics: each theorem is CONDITIONAL, taking the operations and
  the axioms of its theory (and, where the proof uses induction, the induction
  principle) as hypotheses over an abstract carrier `M`. The epilogue then
  instantiates them at Lean's own `Nat`, discharging every hypothesis with a
  core lemma, which turns them into unconditional facts about the naturals.

  Lean core only: this file needs no `import`, no Std and no Mathlib.
-/

-- Every theorem takes its theory's WHOLE axiom set as hypotheses, whether or not
-- a given proof cites all of them, so that the axioms are visible in the
-- statement and the epilogue can discharge them by name. Lean would otherwise
-- report each uncited one as an unused binder.
set_option linter.unusedVariables false
"""

_EPILOGUE_HEADER = """/-
  The epilogue: `M := Nat`, with every hypothesis discharged, so the conditional
  theorems above become unconditional facts about Lean's own naturals.

  Robinson's theory is deliberately absent here. Its axioms describe the
  POSITIVE integers (A1 says `succ a ≠ 1`, which is false at `a := 0`), so `Nat`
  is not a model of it and the theorem above stays conditional -- as it should.
-/
"""


def corpus_entries() -> list:
    """The proofs the generated file carries: `(name, proof, theory, at_nat)`.
    `at_nat` says whether the epilogue may instantiate it at Lean's `Nat`."""
    return [
        ("coldstart_left_identity", left_identity_proof(), _presburger.PRESBURGER, True),
        ("coldstart_add_two_three", add_proof(2, 3), _presburger.PRESBURGER, True),
        ("coldstart_mul_two_three", mul_proof(2, 3), _peano.PEANO, True),
        (
            "coldstart_mul_cancel_right_positive",
            mul_cancel_right_succ(),
            _peano.PEANO,
            True,
        ),
        (
            "coldstart_robinson_bridge_converse_positive",
            bridge_converse_positive(),
            _peano.PEANO,
            True,
        ),
        (
            "coldstart_robinson_add_two_three",
            robinson_add_proof(2, 3),
            _robinson.ROBINSON_PEANO,
            False,
        ),
    ]


CORPUS_NAMES = tuple(name for name, _pf, _theory, _nat in corpus_entries())


def export_corpus() -> str:
    """The whole `ColdStart.lean`: header, one conditional theorem per corpus
    proof, then the `Nat` epilogue."""
    parts = [_HEADER]
    epilogue = [_EPILOGUE_HEADER]
    for name, pf, theory, at_nat in corpus_entries():
        export = _Export(pf, theory)
        parts.append(export.theorem(name))
        if at_nat:
            epilogue.append(export.nat_example(name))
    return "\n".join([*parts, *epilogue])


def write_corpus(path: Path | str | None = None) -> Path:
    """Write `export_corpus()` to `path` (default `lean_export/ColdStart.lean`),
    with LF endings so the checked-in file is stable across platforms."""
    target = Path(path) if path is not None else CORPUS_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("w", encoding="utf-8", newline="\n") as fh:
        fh.write(export_corpus())
    return target


__all__ = [
    "AXIOM_LABELS",
    "CARRIER",
    "CORPUS_NAMES",
    "CORPUS_PATH",
    "NAT_AXIOM_PROOFS",
    "NAT_INDUCTION",
    "corpus_entries",
    "export_corpus",
    "write_corpus",
    "LeanError",
    "closure_names",
    "export_theorem",
    "lean_name",
    "parse_formula",
    "parse_term",
    "render_formula",
    "render_statement",
    "render_term",
    "substitute",
    "universal_closure",
    "uses_induction",
]


if __name__ == "__main__":
    print(f"wrote {write_corpus()}")

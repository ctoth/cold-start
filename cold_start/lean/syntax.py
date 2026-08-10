"""Lean 4 rendering and parsing for first-order terms and formulas."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import Any, NoReturn, TypeAlias, TypeVar, cast

from ..emitter import Emitter, Visit, case
from ..syntax import (
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
    Rel,
    Term,
    Var,
    children,
    exists,
    forall,
    map_children,
)
from ..theory import Signature

_N = TypeVar("_N", bound=Node)  # substitution preserves the node's kind
_ControlFrame: TypeAlias = tuple[Any, ...]
_ControlStack: TypeAlias = list[_ControlFrame]
_QuantifierCtor: TypeAlias = Callable[[str, str, Formula], Formula]


class LeanError(ValueError):
    """Raised when a term/formula cannot be expressed in the exported fragment."""


CARRIER = "M"  # the abstract carrier type every exported theorem quantifies over

# Object-language function symbols -> Lean identifiers. A symbol outside this
# map is exported under a sanitized version of its own name.
SYMBOL_NAMES: dict[str, str] = {
    "0": "zero",
    "1": "one",
    "S": "succ",
    "+": "add",
    "*": "mul",
}

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
class LeanNames:
    """A fresh-name supply. `taken` grows monotonically, so a name handed out is
    never handed out again -- which is what lets the emitters be iterative: no
    scope has to be *restored*, because nothing is ever reused."""

    taken: set[str] = field(default_factory=set[str])

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


def substitute(node: _N, sigma: dict[str, Term]) -> _N:
    """Simultaneously replace free `Var`s by name, per `sigma: name -> Term`.

    Iterative (post-order over a heap agenda), and simultaneous -- so mapping
    `{x: y, y: x}` swaps rather than collapsing, which sequential `subst` calls
    would get wrong. Replacement terms contain no `BVar`s (they come from proof
    terms, which are closed at the object level), so no index shifting is needed
    and a node's image is independent of the binder depth it sits at."""
    if not sigma:
        return node
    order: list[Node] = []
    stack: list[Node] = [node]
    while stack:
        n = stack.pop()
        order.append(n)
        stack.extend(cast(list[Node], children(n)))
    done: dict[int, Node] = {}
    for n in reversed(order):
        if type(n) is Var and n.name in sigma:
            done[id(n)] = sigma[n.name]
        else:
            rebuilt = map_children(n, lambda c: done[id(c)])
            if not isinstance(rebuilt, Node):
                raise TypeError("syntax child mapping changed the node family")
            done[id(n)] = rebuilt
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
ATOM_PRECEDENCE = 10


@dataclass(frozen=True, slots=True)
class LeanStyle:
    """How the carrier and the function symbols are spelled. The abstract style
    is what a conditional theorem is stated over (`M`, with `zero`/`succ`/... as
    its parameters); the `Nat` style re-renders the very same formulas at Lean's
    own naturals, which is what lets the epilogue state the instantiated facts
    without any string surgery."""

    carrier: str
    symbols: dict[str, str]

    def symbol(self, name: str) -> str:
        return self.symbols.get(name) or lean_name(name)


ABSTRACT_STYLE = LeanStyle(CARRIER, SYMBOL_NAMES)
_NAT = LeanStyle("Nat", {"0": "Nat.zero", "S": "Nat.succ", "+": "Nat.add", "*": "Nat.mul"})


def render_term(term: Term) -> str:
    """Render a term as a Lean 4 expression over the carrier's operations."""
    return render_node(term, LeanNames(free_lean_names(term)), _L_IMPL)


def render_formula(formula: Formula) -> str:
    """Render a formula as a Lean 4 `Prop`, leaving free variables as free Lean
    identifiers (our implicit universal quantification is NOT applied here --
    see `render_statement`)."""
    return render_node(formula, LeanNames(free_lean_names(formula)), _L_IMPL)


def render_statement(formula: Formula) -> str:
    """Render a formula as a standalone Lean 4 statement: free variables, which
    our theories read as implicitly universal, become leading `forall` binders in
    lexicographic order. That order is the contract instantiation relies on --
    `Inst` on the k-th name must line up with the k-th binder."""
    return render_statement_with_style(formula, ABSTRACT_STYLE)


def render_statement_with_style(formula: Formula, style: LeanStyle) -> str:
    names = closure_names(formula)
    supply = LeanNames(free_lean_names(formula))
    body = render_node(formula, supply, _L_IMPL, style)
    prefix = "".join(f"∀ {lean_name(n)} : {style.carrier}, " for n in names)
    return prefix + body


def closure_names(formula: Formula) -> tuple[str, ...]:
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


def free_lean_names(node: Node) -> set[str]:
    return {lean_name(n) for n in node.free_vars()}


def render_node(
    node: Node,
    supply: LeanNames,
    prec: int,
    style: LeanStyle = ABSTRACT_STYLE,
) -> str:
    """Emit `node` as Lean text iteratively through exact external cases."""
    return _LeanSyntaxEmitter(supply, style).render(node, _LeanSyntaxContext(prec))


@dataclass(frozen=True, slots=True)
class _LeanSyntaxContext:
    prec: int
    scope: tuple[str, ...] = ()


def _wrapped(level: int, prec: int, pieces: Sequence[object]) -> tuple[object, ...]:
    return ("(", *pieces, ")") if level < prec else tuple(pieces)


class _LeanSyntaxEmitter(
    Emitter[Node, _LeanSyntaxContext],
    covers=CANONICAL_NODE_TYPES,
):
    __slots__ = ("style", "supply")

    def __init__(self, supply: LeanNames, style: LeanStyle) -> None:
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
            pieces += [" ", Visit(arg, _LeanSyntaxContext(ATOM_PRECEDENCE, context.scope))]
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
        name = self.style.symbol(node.name)
        if not node.args:
            return (name,)
        pieces: list[object] = [name]
        for arg in node.args:
            pieces += [" ", Visit(arg, _LeanSyntaxContext(ATOM_PRECEDENCE, context.scope))]
        return _wrapped(_L_APP, context.prec, pieces)


def _binder_base(supply: LeanNames) -> str:
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

# Arities are never a second hand-maintained table: they come from a `Signature`
# -- the caller's, when it knows which theory the text was stated over, and this
# one otherwise. It is the arithmetic vocabulary `SYMBOL_NAMES` re-spells, and
# the check below fails the import outright if the two ever drift apart, rather
# than letting an unranked symbol parse silently at any arity.
ARITHMETIC_SIGNATURE = Signature(
    sorts=frozenset({""}),
    ranks=(
        ("0", (), ""),
        ("1", (), ""),
        ("S", ("",), ""),
        ("+", ("", ""), ""),
        ("*", ("", ""), ""),
    ),
)

_UNRANKED = frozenset(SYMBOL_NAMES) - {name for name, _args, _result in ARITHMETIC_SIGNATURE.ranks}
if _UNRANKED:
    raise LeanError(f"the default parse signature does not rank {sorted(_UNRANKED)}")

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


def parse_term(text: str, *, signature: Signature | None = None) -> Term:
    """Parse a Lean term of the exported fragment back into our syntax."""
    parser = _Parser(text, signature)
    node = parser.run(_P_IMPL)
    parser.expect_eof()
    if not isinstance(node, Term):
        raise LeanError(f"expected a term, got {node!r}")
    return node


def parse_formula(text: str, *, signature: Signature | None = None) -> Formula:
    """Parse a Lean statement of the exported fragment back into our syntax.

    Binders come back locally nameless, so `parse_formula(render_statement(f))`
    is literally `universal_closure(f)` -- the round trip is `==`, with no alpha
    relation in the way.

    `signature` is the vocabulary the text was stated over. It is what tells a
    relation application from a function application -- `p x y` renders the same
    either way -- so a formula containing a `Rel` only round-trips when the
    theory's signature comes along."""
    parser = _Parser(text, signature)
    node = parser.run(0)
    parser.expect_eof()
    if not isinstance(node, Formula):
        raise LeanError(f"expected a formula, got {node!r}")
    return node


def _tokenize(text: str) -> list[_Token]:
    tokens: list[_Token] = []
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

    def __init__(self, text: str, signature: Signature | None = None) -> None:
        self.tokens = _tokenize(text)
        self.i = 0
        self.bound: list[str] = []  # enclosing binder names, nearest last
        self.signature = ARITHMETIC_SIGNATURE if signature is None else signature

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

    def error(self, message: str) -> NoReturn:
        raise LeanError(f"{message} at column {self.peek().pos + 1}")

    def starts_atom(self) -> bool:
        tok = self.peek()
        return not self.at_eof() and (tok.is_name or tok.text == "(")

    # --- the iterative Pratt core -------------------------------------------

    def run(self, min_prec: int) -> Term | Formula:
        ctrl: _ControlStack = [("expr", min_prec)]
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
        return cast(Term | Formula, result)

    def _infix_prec(self, text: str) -> int | None:
        if text in _ARROWS:
            return _P_IMPL
        if text == "=":
            return _P_EQ
        return None

    def _nud(self, ctrl: _ControlStack, min_prec: int) -> object:
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

    def _begin_quant(self, ctrl: _ControlStack, ctor: _QuantifierCtor) -> object:
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

    def _finish_quant(
        self, name: str, ctor: _QuantifierCtor, body: object
    ) -> Formula:
        self.bound.pop()
        if not isinstance(body, Formula):
            self.error("a quantifier body must be a formula")
        # The body already carries `name` as a free `Var`; `ctor` abstracts it.
        return ctor(name, "", body)

    def _continue_app(
        self,
        ctrl: _ControlStack,
        name: str,
        acc: tuple[Term, ...],
        arg: object,
    ) -> object:
        if not isinstance(arg, Term):
            self.error("function arguments must be terms")
        acc = (*acc, arg)
        if self.starts_atom():
            ctrl.append(("arg", name, acc))
            ctrl.append(("expr", _P_APP))
            return _PENDING
        return self._build(name, acc)

    def _build(self, name: str, args: tuple[Term, ...]) -> Term | Formula:
        """A name applied to `args`: a relation or function of the signature at
        its declared arity, an uninterpreted function, or (unapplied) a variable
        -- free, or a binder's own name, which `_finish_quant` later abstracts
        into its de Bruijn index."""
        symbol = _SYMBOLS_BY_LEAN.get(name, name)
        relation_rank = self.signature.relation(symbol)
        if relation_rank is not None:
            self._check_arity(name, len(relation_rank), args)
            return Rel(symbol, args)
        function_rank = self.signature.rank(symbol)
        if function_rank is not None:
            self._check_arity(name, len(function_rank[0]), args)
            return Fun(symbol, args)
        if symbol != name:  # a symbol we re-spell must be one the signature ranks
            self.error(f"{name} is not a symbol of this signature")
        return Fun(name, args) if args else Var(name)

    def _check_arity(self, name: str, arity: int, args: tuple[Term, ...]) -> None:
        if len(args) != arity:
            self.error(f"{name} takes {arity} argument(s), got {len(args)}")

    def _combine(self, op: str, left: object, right: object) -> Formula:
        if op in _ARROWS:
            if not (isinstance(left, Formula) and isinstance(right, Formula)):
                self.error("an implication needs formulas on both sides")
            return Implies(left, right)
        if not (isinstance(left, Term) and isinstance(right, Term)):
            self.error("an equality needs terms on both sides")
        return Eq(left, right)


__all__ = [
    "ABSTRACT_STYLE",
    "ARITHMETIC_SIGNATURE",
    "ATOM_PRECEDENCE",
    "CARRIER",
    "LeanNames",
    "LeanError",
    "LeanStyle",
    "closure_names",
    "free_lean_names",
    "lean_name",
    "parse_formula",
    "parse_term",
    "render_formula",
    "render_node",
    "render_statement",
    "render_statement_with_style",
    "render_term",
    "substitute",
    "universal_closure",
]

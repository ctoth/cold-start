"""Human notation for the object language.

This module is an untrusted surface convenience. It parses and prints math-ish
text, but only the existing syntax nodes and checker decide what is well-formed
or proved.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import NoReturn, cast

from .emitter import Emitter, Visit, case
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
    Not,
    Rel,
    Term,
    Var,
    exists,
    forall,
)


class ParseError(ValueError):
    """Raised when notation text is not in the supported surface language."""


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    text: str
    pos: int


_EOF = "EOF"
_MULTI = ("->", "=>", "!=", "<=", ">=")
_SINGLE = set("()[],.:=+-*/#|") | {"∀", "∃", "→", "⇒", "¬", "⊥", "≠", "≤", "≥"}
_IMPLIES = {"->", "=>", "→", "⇒"}
_NOT = {"¬", "not"}
_FORALL = {"∀", "forall"}
_EXISTS = {"∃", "exists"}
_NEQ = {"!=", "≠"}
_INFIX_PRECEDENCE = {"+": 20, "-": 20, "*": 30, "/": 30}
_DEFAULT_CONSTANTS = frozenset({"0", "1", "e"})
_NAME_CANDIDATES = ("x", "y", "z", "n", "m", "a", "b", "u", "v", "w")


def parse_term(text: str, *, constants: frozenset[str] = _DEFAULT_CONSTANTS) -> Term:
    """Parse a term such as ``x``, ``S(0)``, ``x + y`` or ``act(e, x)``."""
    parser = _Parser(text, constants)
    term = parser.parse_term()
    parser.expect_eof()
    return term


def parse_formula(text: str, *, constants: frozenset[str] = _DEFAULT_CONSTANTS) -> Formula:
    """Parse a formula such as ``∀x:N. x + 0 = x`` or ``S(x) ≠ 0``."""
    parser = _Parser(text, constants)
    formula = parser.parse_formula()
    parser.expect_eof()
    return formula


def format_term(term: Term, *, constants: frozenset[str] = _DEFAULT_CONSTANTS) -> str:
    """Render a term in notation accepted by :func:`parse_term`."""
    return _format_node(term, _Printer(constants))


def format_formula(formula: Formula, *, constants: frozenset[str] = _DEFAULT_CONSTANTS) -> str:
    """Render a formula in notation accepted by :func:`parse_formula`."""
    return _format_node(formula, _Printer(constants))


def _tokenize(text: str) -> list[_Token]:
    tokens: list[_Token] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "`":
            tokens.append(_read_quoted_name(text, i))
            i = tokens[-1].pos
            continue
        matched = next((op for op in _MULTI if text.startswith(op, i)), None)
        if matched is not None:
            tokens.append(_Token("SYM", matched, i))
            i += len(matched)
            continue
        if ch in _SINGLE:
            tokens.append(_Token("SYM", ch, i))
            i += 1
            continue
        if ch.isdecimal():
            start = i
            while i < len(text) and text[i].isdecimal():
                i += 1
            tokens.append(_Token("NAME", text[start:i], start))
            continue
        if _is_name_start(ch):
            start = i
            i += 1
            while i < len(text) and _is_name_continue(text[i]):
                i += 1
            tokens.append(_Token("NAME", text[start:i], start))
            continue
        raise ParseError(f"unexpected character {ch!r} at column {i + 1}")
    tokens.append(_Token(_EOF, "", len(text)))
    return tokens


def _read_quoted_name(text: str, start: int) -> _Token:
    out: list[str] = []
    i = start + 1
    while i < len(text):
        ch = text[i]
        if ch == "`":
            return _Token("NAME", "".join(out), i + 1)
        if ch == "\\":
            i += 1
            if i >= len(text):
                raise ParseError(f"unterminated escape in quoted name at column {start + 1}")
            out.append(text[i])
        else:
            out.append(ch)
        i += 1
    raise ParseError(f"unterminated quoted name at column {start + 1}")


def _is_name_start(ch: str) -> bool:
    return ch == "_" or ch.isalpha()


def _is_name_continue(ch: str) -> bool:
    return ch == "_" or ch == "'" or ch.isalpha() or ch.isdecimal()


# Parser binding powers (higher binds tighter), one unified expression grammar
# over terms and formulas. `->` is right-associative and loosest; `=`/`≠` sit
# between it and the term operators. `not`/`∀`/`∃` are prefixes -- `not` binds an
# operand down to `_PREC_NOT` (it grabs an equality but not an implication), while a
# quantifier body is greedy (a full implication). Function args and a bare term
# parse at `_PREC_ADD`, stopping before `=`/`->`.
_PREC_IMPLIES = 1
_PREC_NOT = 2  # not's operand: equalities, not implications
_PREC_ADD = 3  # also: function args and top-level terms
_OP_FUNC_NAMES = ("+", "-", "*", "/")
_PENDING = object()  # a nud that pushed sub-goals rather than producing a value now


class _Parser:
    """Iterative precedence-climbing (Pratt) parser. The recursion of a hand-rolled
    descent is replaced by an explicit control stack, so input nested arbitrarily
    deep parses without touching the call stack. One expression grammar covers both
    terms and formulas; the node constructors enforce the typing (`->` needs
    formulas, `+`/`=` need terms), and `(...)` is just a grouped expression -- no
    speculative backtracking."""

    def __init__(self, text: str, constants: frozenset[str]) -> None:
        self.tokens = _tokenize(text)
        self.i = 0
        self.constants = constants
        self.bound: dict[str, list[str]] = {}

    def parse_formula(self) -> Formula:
        node = self._run(0)
        if not isinstance(node, Formula):
            self.error("expected a formula")
        return node

    def parse_term(self) -> Term:
        node = self._run(_PREC_ADD)  # term level: bind +-*/, stop before = and ->
        if not isinstance(node, Term):
            self.error("expected a term")
        return node

    # --- token helpers ------------------------------------------------------

    def expect_eof(self) -> None:
        if self.peek().kind != _EOF:
            self.error(f"unexpected token {self.peek().text!r}")

    def peek(self) -> _Token:
        return self.tokens[self.i]

    def peek_next(self) -> _Token:
        return self.tokens[self.i + 1]

    def advance(self) -> _Token:
        tok = self.peek()
        self.i += 1
        return tok

    def accept(self, *texts: str) -> bool:
        if self.peek().text in texts:
            self.advance()
            return True
        return False

    def expect(self, text: str) -> None:
        if not self.accept(text):
            self.error(f"expected {text!r}, got {self.peek().text!r}")

    def expect_name(self) -> str:
        tok = self.peek()
        if tok.kind != "NAME":
            self.error(f"expected name, got {tok.text!r}")
        self.advance()
        return tok.text

    def error(self, message: str) -> NoReturn:
        tok = self.peek()
        raise ParseError(f"{message} at column {tok.pos + 1}")

    def bound_sort(self, name: str) -> str | None:
        sorts = self.bound.get(name)
        if not sorts:
            return None
        return sorts[-1]

    # --- the iterative Pratt core -------------------------------------------

    def _infix_prec(self, text: str) -> int | None:
        if text in _IMPLIES:
            return _PREC_IMPLIES
        if text == Eq.symbol or text in _NEQ or text == "|":
            return 2
        if text in ("+", "-"):
            return 3
        if text in ("*", "/"):
            return 4
        return None

    def _run(self, min_prec: int) -> Term | Formula:
        # The control stack interleaves goals ("expr"/"atom") with continuations
        # ("loop"/"combine"/"close"/"not"/"quant"/"arg"). `result` carries the most
        # recently completed node from a goal to the continuation that consumes it.
        ctrl: list = [("expr", min_prec)]
        result: object = _PENDING
        while ctrl:
            tag, *rest = ctrl.pop()
            if tag == "expr":
                ctrl.append(("loop", rest[0]))
                ctrl.append(("atom",))
            elif tag == "atom":
                value = self._nud(ctrl)
                if value is not _PENDING:
                    result = value
            elif tag == "loop":
                min_p = rest[0]
                prec = self._infix_prec(self.peek().text)
                if prec is not None and prec >= min_p:
                    op = self.advance().text
                    nxt = prec if prec == _PREC_IMPLIES else prec + 1  # `->` right-assoc
                    ctrl.append(("combine", op, result, min_p))
                    ctrl.append(("expr", nxt))
                # else: `result` is the finished operand; the next continuation reads it
            elif tag == "combine":
                op, left, min_p = rest
                result = self._combine(op, left, result)
                ctrl.append(("loop", min_p))  # keep folding more infix at this level
            elif tag == "close":
                self.expect(")")  # `result` is the inner expression, unchanged
            elif tag == "not":
                if not isinstance(result, Formula):
                    self.error("negation needs a formula")
                result = Not(result)
            elif tag == "quant":
                result = self._finish_quant(rest[0], rest[1], result)
            elif tag == "arg":
                result = self._continue_call(rest[0], rest[1], result, ctrl)
        return cast(Term | Formula, result)

    def _nud(self, ctrl: list) -> object:
        """Parse a nud (atom / prefix). Returns the node, or `_PENDING` after pushing
        sub-goals whose result will be filled in later."""
        tok = self.peek()
        text = tok.text
        if text == Bottom.symbol:
            self.advance()
            return Bottom()
        if text in _NOT:
            self.advance()
            ctrl.append(("not",))
            ctrl.append(("expr", _PREC_NOT))
            return _PENDING
        if text in _FORALL:
            return self._begin_quant(ctrl, forall)
        if text in _EXISTS:
            return self._begin_quant(ctrl, exists)
        if text == "(":
            self.advance()
            ctrl.append(("close",))
            ctrl.append(("expr", 0))  # a grouped expression: term or formula
            return _PENDING
        # a name, or an operator symbol used as a function name (e.g. +(a, b))
        if tok.kind == "NAME" or (text in _OP_FUNC_NAMES and self.peek_next().text == "("):
            name = self.advance().text
            if self.accept("("):
                if self.accept(")"):
                    return Fun(name, ())
                ctrl.append(("arg", name, []))
                ctrl.append(("expr", _PREC_ADD))
                return _PENDING
            if name.isdecimal() or name in self.constants:
                return Fun(name, ())
            sort = ""
            if self.accept(":"):
                sort = self.expect_name()
            bound = self.bound_sort(name)
            if bound is not None:
                if sort and sort != bound:
                    self.error(f"bound variable {name!r} has sort {bound!r}, not {sort!r}")
                return Var(name, bound)
            return Var(name, sort)
        self.error(f"expected term or formula, got {text!r}")

    def _begin_quant(self, ctrl: list, ctor) -> object:
        self.advance()  # the quantifier symbol
        specs: list[tuple[str, str]] = []
        while True:
            name = self.expect_name()
            sort = ""
            if self.accept(":"):
                sort = self.expect_name()
            specs.append((name, sort))
            if self.accept(","):
                continue
            break
        self.expect(".")
        for name, sort in specs:
            self.bound.setdefault(name, []).append(sort)
        ctrl.append(("quant", specs, ctor))
        ctrl.append(("expr", 0))  # body is greedy: a full implication
        return _PENDING

    def _finish_quant(self, specs: list, ctor, body: object) -> Formula:
        if not isinstance(body, Formula):
            self.error("quantifier body must be a formula")
        for name, _sort in reversed(specs):
            self.bound[name].pop()
            if not self.bound[name]:
                del self.bound[name]
        for name, sort in reversed(specs):
            body = ctor(name, sort, body)
        return cast(Formula, body)

    def _continue_call(self, name: str, acc: list, arg: object, ctrl: list) -> object:
        if not isinstance(arg, Term):
            self.error("function arguments must be terms")
        acc = [*acc, arg]
        if self.accept(")"):
            return Fun(name, tuple(acc))
        self.expect(",")
        ctrl.append(("arg", name, acc))
        ctrl.append(("expr", _PREC_ADD))
        return _PENDING

    def _combine(self, op: str, left: object, right: object) -> Term | Formula:
        if op in _IMPLIES:
            if not (isinstance(left, Formula) and isinstance(right, Formula)):
                self.error("implication needs formulas on both sides")
            return Implies(left, right)
        if op == Eq.symbol:
            if not (isinstance(left, Term) and isinstance(right, Term)):
                self.error("equality needs terms on both sides")
            return Eq(left, right)
        if op in _NEQ:
            if not (isinstance(left, Term) and isinstance(right, Term)):
                self.error("inequality needs terms on both sides")
            return Not(Eq(left, right))
        if op == "|":
            if not (isinstance(left, Term) and isinstance(right, Term)):
                self.error("relation needs terms on both sides")
            return Rel("|", (left, right))
        if not (isinstance(left, Term) and isinstance(right, Term)):
            self.error(f"{op!r} needs terms on both sides")
        return Fun(op, (left, right))


@dataclass(slots=True)
class _Printer:
    """Notation-owned formatting state.

    Two things keep printing linear in the tree size, even under deep binder nesting:

    * Bound occurrences are never re-opened. A `BVar(i)` is rendered straight from
      `scope` -- the stack of `(name, sort)` for the enclosing binders -- so there is
      no per-binder `instantiate` (which would rebuild an O(subtree) body and make
      formatting O(n^2)). `scope[-1]` is the nearest binder, so `BVar(i)` reads
      `scope[-1 - i]`.
    * A binder's surface name is chosen by *depth*, not by rescanning the body for
      free names. The formula's free names are computed once into `free`, and the
      d-th nested binder gets the d-th name not in `free` (cached in `_names`).
      Enclosing binders sit at smaller depths and so hold different names, and every
      name dodges the free set -- collision-free, at O(1) amortized per binder."""

    constants: frozenset[str]
    free: frozenset[str] = frozenset()  # free var names of the whole formula
    _names: list[str] = field(default_factory=list)  # binder name by depth (cached)
    _raw_pos: int = 0  # cursor into the raw candidate sequence

    def name(self, s: str) -> str:
        return _format_name(s)

    def binder_name(self, depth: int) -> str:
        while len(self._names) <= depth:
            self._names.append(self._next_name())
        return self._names[depth]

    def _next_name(self) -> str:
        # raw sequence: the readable candidates, then x0, x1, ...; skip free names.
        # The cursor only advances, so cached names stay distinct across depths.
        ncand = len(_NAME_CANDIDATES)
        while True:
            i = self._raw_pos
            self._raw_pos += 1
            cand = _NAME_CANDIDATES[i] if i < ncand else f"x{i - ncand}"
            if cand not in self.free:
                return cand


@dataclass(frozen=True, slots=True)
class _FormatContext:
    prec: int = 0
    scope: tuple[tuple[str, str], ...] = ()


def _wrapped(wrap: bool, pieces: list[object]) -> tuple[object, ...]:
    return ("(", *pieces, ")") if wrap else tuple(pieces)


class _NotationEmitter(
    Emitter[Term | Formula, _FormatContext],
    covers=CANONICAL_NODE_TYPES,
):
    __slots__ = ("printer",)

    def __init__(self, printer: _Printer) -> None:
        self.printer = printer

    @case(Var)
    def var(self, node: Var, context: _FormatContext) -> tuple[object, ...]:
        name = self.printer.name(node.name)
        return (f"{name}:{self.printer.name(node.sort)}" if node.sort else name,)

    @case(BVar)
    def bvar(self, node: BVar, context: _FormatContext) -> tuple[object, ...]:
        if not 0 <= node.index < len(context.scope):
            raise ValueError("cannot format a dangling bound variable outside a binder")
        return (self.printer.name(context.scope[-1 - node.index][0]),)

    @case(Bottom)
    def bottom(self, node: Bottom, context: _FormatContext) -> tuple[object, ...]:
        return (node.symbol,)

    @case(Fun)
    def fun(self, node: Fun, context: _FormatContext) -> tuple[object, ...]:
        infix = _INFIX_PRECEDENCE.get(node.name)
        if infix is not None and len(node.args) == 2:
            pieces: list[object] = [
                Visit(node.args[0], _FormatContext(infix, context.scope)),
                f" {node.name} ",
                Visit(node.args[1], _FormatContext(infix + 1, context.scope)),
            ]
            return _wrapped(infix < context.prec, pieces)
        name = self.printer.name(node.name)
        if not node.args and (node.name in self.printer.constants or node.name.isdecimal()):
            return (name,)
        pieces = [name, "("]
        for index, arg in enumerate(node.args):
            if index:
                pieces.append(", ")
            pieces.append(Visit(arg, _FormatContext(0, context.scope)))
        pieces.append(")")
        return tuple(pieces)

    @case(Eq)
    def eq(self, node: Eq, context: _FormatContext) -> tuple[object, ...]:
        return _wrapped(
            40 < context.prec,
            [
                Visit(node.lhs, _FormatContext(0, context.scope)),
                f" {node.symbol} ",
                Visit(node.rhs, _FormatContext(0, context.scope)),
            ],
        )

    @case(Rel)
    def rel(self, node: Rel, context: _FormatContext) -> tuple[object, ...]:
        if node.name != "|" or len(node.args) != 2:
            raise ValueError(f"notation has no surface form for relation {node.name!r}")
        return _wrapped(
            40 < context.prec,
            [
                Visit(node.args[0], _FormatContext(0, context.scope)),
                " | ",
                Visit(node.args[1], _FormatContext(0, context.scope)),
            ],
        )

    @case(Implies)
    def implies(self, node: Implies, context: _FormatContext) -> tuple[object, ...]:
        if type(node.con) is Bottom:
            return _wrapped(
                35 < context.prec,
                ["¬", Visit(node.ant, _FormatContext(35, context.scope))],
            )
        return _wrapped(
            10 < context.prec,
            [
                Visit(node.ant, _FormatContext(11, context.scope)),
                f" {node.symbol} ",
                Visit(node.con, _FormatContext(10, context.scope)),
            ],
        )

    @case(Forall, Exists)
    def binder(self, node: Forall | Exists, context: _FormatContext) -> tuple[object, ...]:
        name = self.printer.binder_name(len(context.scope))
        sort = f":{self.printer.name(node.sort)}" if node.sort else ""
        body_context = _FormatContext(0, (*context.scope, (name, node.sort)))
        return _wrapped(
            5 < context.prec,
            [f"{node.symbol}{self.printer.name(name)}{sort}. ", Visit(node.body, body_context)],
        )


def _format_node(node: Term | Formula, printer: _Printer, parent_prec: int = 0) -> str:
    """Render surface notation iteratively with immutable binder context."""
    printer.free = node.free_vars()
    return _NotationEmitter(printer).render(node, _FormatContext(parent_prec))


def _format_name(name: str) -> str:
    if name.isidentifier() or name.isdecimal() or name in _INFIX_PRECEDENCE:
        return name
    escaped = name.replace("\\", "\\\\").replace("`", "\\`")
    return f"`{escaped}`"


__all__ = [
    "ParseError",
    "parse_term",
    "parse_formula",
    "format_term",
    "format_formula",
]

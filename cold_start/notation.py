"""Human notation for the object language.

This module is an untrusted surface convenience. It parses and prints math-ish
text, but only the existing syntax nodes and checker decide what is well-formed
or proved.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import NoReturn

from .syntax import (
    Bottom,
    BVar,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Not,
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
_SINGLE = set("()[],.:=+-*/#") | {"∀", "∃", "→", "⇒", "¬", "⊥", "≠", "≤", "≥"}
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


class _Parser:
    def __init__(self, text: str, constants: frozenset[str]) -> None:
        self.tokens = _tokenize(text)
        self.i = 0
        self.constants = constants
        self.bound: dict[str, list[str]] = {}

    def parse_formula(self) -> Formula:
        return self._parse_implication()

    def parse_term(self, min_prec: int = 0) -> Term:
        left = self._parse_term_atom()
        while self.peek().text in _INFIX_PRECEDENCE:
            op = self.peek().text
            prec = _INFIX_PRECEDENCE[op]
            if prec < min_prec:
                break
            self.advance()
            right = self.parse_term(prec + 1)
            left = Fun(op, (left, right))
        return left

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

    def _parse_implication(self) -> Formula:
        left = self._parse_unary_formula()
        if self.peek().text in _IMPLIES:
            self.advance()
            return Implies(left, self._parse_implication())
        return left

    def _parse_unary_formula(self) -> Formula:
        tok = self.peek()
        if tok.text in _NOT:
            self.advance()
            return Not(self._parse_unary_formula())
        if tok.text in _FORALL:
            return self._parse_quantifier(forall)
        if tok.text in _EXISTS:
            return self._parse_quantifier(exists)
        return self._parse_formula_atom()

    def _parse_quantifier(self, ctor) -> Formula:
        self.advance()
        specs: list[tuple[str, str]] = []
        while True:
            name = self.expect_name()
            sort = ""
            if self.accept(":"):
                sort = self.expect_name()
            specs.append((name, sort))
            if self.accept(","):
                continue
            if self.peek().text == ".":
                break
        self.expect(".")
        for name, sort in specs:
            self.bound.setdefault(name, []).append(sort)
        try:
            body = self._parse_implication()
        finally:
            for name, _sort in reversed(specs):
                self.bound[name].pop()
                if not self.bound[name]:
                    del self.bound[name]
        for name, sort in reversed(specs):
            body = ctor(name, sort, body)
        return body

    def _parse_formula_atom(self) -> Formula:
        if self.peek().text == Bottom.symbol:
            self.advance()
            return Bottom()
        grouped = self._try_grouped_formula()
        if grouped is not None:
            return grouped
        left = self.parse_term()
        if self.accept(Eq.symbol):
            return Eq(left, self.parse_term())
        if self.peek().text in _NEQ:
            self.advance()
            return Not(Eq(left, self.parse_term()))
        self.error("expected formula")

    def _try_grouped_formula(self) -> Formula | None:
        if self.peek().text != "(":
            return None
        start = self.i
        try:
            self.advance()
            inner = self._parse_implication()
            self.expect(")")
        except ParseError:
            self.i = start
            return None
        if self.peek().text in {Eq.symbol, *_NEQ}:
            self.i = start
            return None
        return inner

    def _parse_term_atom(self) -> Term:
        tok = self.peek()
        if self.accept("("):
            inner = self.parse_term()
            self.expect(")")
            return inner
        if tok.kind == "NAME" or (tok.text in _INFIX_PRECEDENCE and self.peek_next().text == "("):
            name = self.advance().text
            if self.accept("("):
                args: list[Term] = []
                if not self.accept(")"):
                    while True:
                        args.append(self.parse_term())
                        if self.accept(")"):
                            break
                        self.expect(",")
                return Fun(name, tuple(args))
            if name.isdecimal() or name in self.constants:
                return Fun(name, ())
            sort = ""
            if self.accept(":"):
                sort = self.expect_name()
            bound_sort = self.bound_sort(name)
            if bound_sort is not None:
                if sort and sort != bound_sort:
                    self.error(
                        f"bound variable {name!r} has sort {bound_sort!r}, not {sort!r}"
                    )
                return Var(name, bound_sort)
            return Var(name, sort)
        self.error(f"expected term, got {tok.text!r}")

    def bound_sort(self, name: str) -> str | None:
        sorts = self.bound.get(name)
        if not sorts:
            return None
        return sorts[-1]


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
    scope: list[tuple[str, str]] = field(default_factory=list)  # (name, sort) of enclosing binders
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


def _format_node(node: Term | Formula, printer: _Printer, parent_prec: int = 0) -> str:
    """Render `node` to surface text, ITERATIVELY and in O(tree size).

    A pre-order walk emits string fragments left-to-right into `out`, joined once at
    the end -- so the result is built in O(total length), never by re-wrapping a
    growing accumulator (which would be O(n^2) in characters copied). The work stack
    holds three kinds of item: `("emit", node, prec)` to expand a node, `("lit", s)`
    to append a literal, and `("pop",)` to close a binder's scope after its body.
    Parenthesisation is decided top-down from `prec`, so each node emits its own
    brackets; bound variables read their binder's name from the scope stack."""
    printer.free = node.free_vars()  # computed once: binder names avoid these
    out: list[str] = []
    stack: list = [("emit", node, parent_prec)]
    while stack:
        item = stack.pop()
        tag = item[0]
        if tag == "lit":
            out.append(item[1])
        elif tag == "pop":
            printer.scope.pop()
        else:  # ("emit", node, prec)
            _emit(item[1], printer, item[2], out, stack)
    return "".join(out)


def _push(stack: list, pieces: list) -> None:
    """Push `pieces` (a forward-order list) so they pop left-to-right."""
    stack.extend(reversed(pieces))


def _emit(node: Term | Formula, printer: _Printer, prec: int, out: list, stack: list) -> None:
    if type(node) is Var:  # free variable: render with its sort (bound occurrences are BVar)
        name = printer.name(node.name)
        out.append(f"{name}:{printer.name(node.sort)}" if node.sort else name)
        return
    if type(node) is BVar:  # bound occurrence: its binder's name, from the scope stack
        if not 0 <= node.index < len(printer.scope):
            raise ValueError("cannot format a dangling bound variable outside a binder")
        out.append(printer.name(printer.scope[-1 - node.index][0]))
        return
    if type(node) is Bottom:
        out.append(node.symbol)
        return
    if type(node) is Fun:
        _emit_fun(node, printer, prec, out, stack)
        return
    if type(node) is Eq:
        wrap = 40 < prec
        pieces: list = [("lit", "(")] if wrap else []
        pieces += [("emit", node.lhs, 0), ("lit", f" {node.symbol} "), ("emit", node.rhs, 0)]
        if wrap:
            pieces.append(("lit", ")"))
        _push(stack, pieces)
        return
    if type(node) is Implies:
        if type(node.con) is Bottom:  # Not(A) == Implies(A, Bottom): render as ¬A
            wrap = 35 < prec
            pieces = [("lit", "(")] if wrap else []
            pieces += [("lit", "¬"), ("emit", node.ant, 35)]
            if wrap:
                pieces.append(("lit", ")"))
            _push(stack, pieces)
            return
        wrap = 10 < prec
        pieces = [("lit", "(")] if wrap else []
        pieces += [("emit", node.ant, 11), ("lit", f" {node.symbol} "), ("emit", node.con, 10)]
        if wrap:
            pieces.append(("lit", ")"))
        _push(stack, pieces)
        return
    if type(node) is Forall or type(node) is Exists:
        name = printer.binder_name(len(printer.scope))  # O(1): avoids `free` + enclosing names
        printer.scope.append((name, node.sort))
        wrap = 5 < prec
        sort = f":{printer.name(node.sort)}" if node.sort else ""
        pieces = [("lit", "(")] if wrap else []
        # the body keeps its BVars (no instantiate); `pop` closes the scope after it
        pieces += [("lit", f"{node.symbol}{printer.name(name)}{sort}. "), ("emit", node.body, 0)]
        pieces.append(("pop",))
        if wrap:
            pieces.append(("lit", ")"))
        _push(stack, pieces)
        return
    raise TypeError(f"cannot format {type(node).__name__}")


def _emit_fun(node: Fun, printer: _Printer, prec: int, out: list, stack: list) -> None:
    infix = _INFIX_PRECEDENCE.get(node.name)
    if infix is not None and len(node.args) == 2:
        wrap = infix < prec
        pieces: list = [("lit", "(")] if wrap else []
        pieces += [
            ("emit", node.args[0], infix),
            ("lit", f" {node.name} "),
            ("emit", node.args[1], infix + 1),  # left-assoc: right binds tighter
        ]
        if wrap:
            pieces.append(("lit", ")"))
        _push(stack, pieces)
        return
    name = printer.name(node.name)
    if not node.args and (node.name in printer.constants or node.name.isdecimal()):
        out.append(name)  # a bare constant or numeral
        return
    pieces = [("lit", name), ("lit", "(")]
    for k, arg in enumerate(node.args):
        if k:
            pieces.append(("lit", ", "))
        pieces.append(("emit", arg, 0))
    pieces.append(("lit", ")"))
    _push(stack, pieces)


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

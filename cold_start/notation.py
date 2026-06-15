"""Human notation for the object language.

This module is an untrusted surface convenience. It parses and prints math-ish
text, but only the existing syntax nodes and checker decide what is well-formed
or proved.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import ClassVar, NoReturn

from .syntax import (
    Bottom,
    Eq,
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
    return term.format(_Printer(constants))


def format_formula(formula: Formula, *, constants: frozenset[str] = _DEFAULT_CONSTANTS) -> str:
    """Render a formula in notation accepted by :func:`parse_formula`."""
    return formula.format(_Printer(constants))


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


# Pretty-printing is a polymorphic `node.format(ctx, parent_prec)` method on each
# syntax node: structural precedence is intrinsic to the operator, so it belongs on
# the node. The notation-specific *lexical* concerns the core syntax must not own --
# name quoting, the infix-symbol table, the constant set, fresh-name choice, the
# bound-name stack -- are carried here, in this printer context threaded as `ctx`.


@dataclass(slots=True)
class _Printer:
    """The lexical side of formatting, handed to each node's `format` method.

    `constants` are the symbols printed bare (e.g. ``0``, ``e``); `bound` maps an
    open binder's surface name to its sort (so a bound variable hides its sort);
    `used` tracks names in play so a binder can choose a fresh one. `infix` and the
    name-quoting / fresh-name helpers are the rest of the surface notation."""

    constants: frozenset[str]
    bound: dict[str, str] = field(default_factory=dict)
    used: set[str] = field(default_factory=set)
    infix: ClassVar[dict[str, int]] = _INFIX_PRECEDENCE

    def name(self, s: str) -> str:
        return _format_name(s)

    def fresh(self, avoid: set[str] | frozenset[str]) -> str:
        return _fresh_name(avoid)


def _fresh_name(avoid: set[str] | frozenset[str]) -> str:
    for name in _NAME_CANDIDATES:
        if name not in avoid:
            return name
    i = 0
    while True:
        name = f"x{i}"
        if name not in avoid:
            return name
        i += 1


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

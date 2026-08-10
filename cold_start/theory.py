"""Validated signatures and theories consumed by the trusted checker."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import TypeAlias, cast

from .sequent import Sequent
from .syntax import Formula, Term, validate

FunctionRank: TypeAlias = tuple[str, tuple[str, ...], str]
RelationRank: TypeAlias = tuple[str, tuple[str, ...]]
_FunctionLookup: TypeAlias = dict[str, tuple[tuple[str, ...], str]]
_RelationLookup: TypeAlias = dict[str, tuple[str, ...]]
_FunctionView: TypeAlias = Mapping[str, tuple[tuple[str, ...], str]]
_RelationView: TypeAlias = Mapping[str, tuple[str, ...]]


def _empty_function_view() -> _FunctionView:
    return MappingProxyType({})


def _empty_relation_view() -> _RelationView:
    return MappingProxyType({})


def _require_name(value: object, label: str) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{label} must be a nonempty genuine str")
    return value


@dataclass(frozen=True, slots=True)
class Signature:
    """A closed many-sorted function and relation vocabulary."""

    sorts: frozenset[str]
    ranks: tuple[FunctionRank, ...]
    relations: tuple[RelationRank, ...] = ()
    _by_name: _FunctionView = field(
        default_factory=_empty_function_view,
        init=False,
        compare=False,
        repr=False,
    )
    _relations_by_name: _RelationView = field(
        default_factory=_empty_relation_view,
        init=False,
        compare=False,
        repr=False,
    )

    def __post_init__(self) -> None:
        functions, relations = self._validated_lookups()
        object.__setattr__(self, "_by_name", MappingProxyType(functions))
        object.__setattr__(self, "_relations_by_name", MappingProxyType(relations))

    def _validated_lookups(self) -> tuple[_FunctionLookup, _RelationLookup]:
        if type(self.sorts) is not frozenset:
            raise TypeError("Signature.sorts must be a frozenset")
        for sort in self.sorts:
            if type(sort) is not str:
                raise TypeError("signature sort must be a genuine str")
        if type(self.ranks) is not tuple:
            raise TypeError("Signature.ranks must be a tuple")
        if type(self.relations) is not tuple:
            raise TypeError("Signature.relations must be a tuple")

        functions: _FunctionLookup = {}
        for rank in self.ranks:
            if type(rank) is not tuple or len(rank) != 3:
                raise TypeError("each function rank must be a (name, args, result) tuple")
            name, args, result = rank
            name = _require_name(name, "function symbol")
            if name in functions:
                raise ValueError(f"duplicate function symbol {name!r}")
            if type(args) is not tuple:
                raise TypeError(f"function {name!r} argument sorts must be a tuple")
            for sort in (*args, result):
                if type(sort) is not str or sort not in self.sorts:
                    raise ValueError(f"function {name!r} mentions undeclared sort {sort!r}")
            functions[name] = (args, result)

        relations: _RelationLookup = {}
        for rank in self.relations:
            if type(rank) is not tuple or len(rank) != 2:
                raise TypeError("each relation rank must be a (name, args) tuple")
            name, args = rank
            name = _require_name(name, "relation symbol")
            if name in relations:
                raise ValueError(f"duplicate relation symbol {name!r}")
            if type(args) is not tuple:
                raise TypeError(f"relation {name!r} argument sorts must be a tuple")
            for sort in args:
                if type(sort) is not str or sort not in self.sorts:
                    raise ValueError(f"relation {name!r} mentions undeclared sort {sort!r}")
            relations[name] = args
        return functions, relations

    def validate(self) -> None:
        functions, relations = self._validated_lookups()
        raw_functions: object = self._by_name
        if type(raw_functions) is not MappingProxyType:
            raise TypeError("Signature function lookup is not canonical")
        if dict(cast(_FunctionView, raw_functions)) != functions:
            raise TypeError("Signature function lookup is not canonical")
        raw_relations: object = self._relations_by_name
        if type(raw_relations) is not MappingProxyType:
            raise TypeError("Signature relation lookup is not canonical")
        if dict(cast(_RelationView, raw_relations)) != relations:
            raise TypeError("Signature relation lookup is not canonical")

    def rank(self, name: str) -> tuple[tuple[str, ...], str] | None:
        raw_functions: object = self._by_name
        if type(raw_functions) is not MappingProxyType:
            raise TypeError("Signature function lookup is not canonical")
        return cast(_FunctionView, raw_functions).get(name)

    def relation(self, name: str) -> tuple[str, ...] | None:
        raw_relations: object = self._relations_by_name
        if type(raw_relations) is not MappingProxyType:
            raise TypeError("Signature relation lookup is not canonical")
        return cast(_RelationView, raw_relations).get(name)

    def extend(self, ranks: tuple[FunctionRank, ...]) -> Signature:
        """This vocabulary plus more function symbols, sorts and relations kept.

        Conservative extension is how PEANO, SQUARE_ARITHMETIC and
        ROBINSON_PEANO_F are built on top of their bases. Rebuilding the
        `Signature` by hand at each site silently dropped `relations` whenever a
        caller forgot to forward it, so the operation belongs here."""
        return Signature(
            sorts=self.sorts,
            ranks=self.ranks + ranks,
            relations=self.relations,
        )


@dataclass(frozen=True, slots=True)
class Theory:
    """A validated axiom set with an optional closed signature and induction."""

    axioms: frozenset[Formula]
    zero: Term | None = None
    succ: str | None = None
    signature: Signature | None = None

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.axioms) is not frozenset:
            raise TypeError("Theory.axioms must be a frozenset")
        for raw_axiom in cast(frozenset[object], self.axioms):
            validate(raw_axiom)
            if not isinstance(raw_axiom, Formula):
                raise TypeError(f"Theory axiom is not a formula: {raw_axiom!r}")

        if (self.zero is None) != (self.succ is None):
            raise ValueError("theory zero and successor must be declared together")
        if self.zero is not None:
            raw_zero = cast(object, self.zero)
            validate(raw_zero)
            if not isinstance(raw_zero, Term):
                raise TypeError(f"Theory.zero is not a term: {raw_zero!r}")
            successor = _require_name(self.succ, "Theory.succ")
        else:
            successor = None

        if self.signature is not None:
            if type(self.signature) is not Signature:
                raise TypeError("Theory.signature must be an exact Signature or None")
            self.signature.validate()
            for axiom in self.axioms:
                Sequent(frozenset(), axiom).sort_check(self.signature)
            if self.zero is not None:
                induction_sort = self.zero.sort_of(self.signature)
                successor_rank = self.signature.rank(cast(str, successor))
                if successor_rank != ((induction_sort,), induction_sort):
                    raise ValueError(
                        f"induction successor {successor!r} must have rank "
                        f"({induction_sort!r},) -> {induction_sort!r}"
                    )

    def accepts(self, formula: Formula) -> bool:
        return formula in self.axioms

    def induction_sort(self) -> str:
        if self.zero is None:
            raise ValueError("theory defines no induction principle")
        if self.signature is None:
            return ""
        return self.zero.sort_of(self.signature)


def validate_theory(value: object) -> Theory:
    """Return one revalidated exact theory, or fail before checker use."""
    if type(value) is not Theory:
        raise TypeError(f"not a theory: {value!r}")
    value.validate()
    return value


__all__ = ["FunctionRank", "RelationRank", "Signature", "Theory", "validate_theory"]

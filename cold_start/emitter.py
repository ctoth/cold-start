"""Exact-dispatch, iterative text emission for external representations.

Concrete emitters declare handlers with :func:`case`. Class creation builds one
immutable exact-type table and, when ``covers=...`` is supplied, rejects missing,
duplicate, or unexpected cases. Handlers return strings and :class:`Visit` work
items; the shared driver expands them iteratively and joins the output once.

This is deliberately an adapter mechanism, not an object-language visitor:
syntax and proof nodes do not know about emitters, and dispatch never follows a
subclass MRO.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, ClassVar, Generic, NoReturn, TypeVar, cast

_Value = TypeVar("_Value")
_Context = TypeVar("_Context")
_Handler = TypeVar("_Handler", bound=Callable[..., object])
_CaseHandler = Callable[..., tuple[object, ...]]
_CASE_TYPES = "__cold_start_emitter_case_types__"


@dataclass(frozen=True, slots=True)
class Visit(Generic[_Value, _Context]):
    """Request that an emitter expand ``value`` under ``context``."""

    value: _Value
    context: _Context


@dataclass(frozen=True, slots=True)
class EmissionLimits:
    """Deterministic limits for one iterative external-text emission."""

    max_output_bytes: int
    max_expansions: int

    def __post_init__(self) -> None:
        for name, value in (
            ("max_output_bytes", self.max_output_bytes),
            ("max_expansions", self.max_expansions),
        ):
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive exact int")


class EmissionLimitError(ValueError):
    """An external representation exceeded local deterministic policy."""


def case(*types: type[object]) -> Callable[[_Handler], _Handler]:
    """Mark an emitter method as the exact handler for ``types``.

    The method is returned unchanged. Registration happens once when the owning
    emitter class is created; there is no global or runtime-mutable registry.
    """
    if not types:
        raise TypeError("an emitter case must name at least one exact type")
    if len(set(types)) != len(types):
        raise TypeError("an emitter case cannot name the same exact type twice")

    def decorate(handler: _Handler) -> _Handler:
        if hasattr(handler, _CASE_TYPES):
            raise TypeError(f"emitter handler {handler.__name__} already has case metadata")
        setattr(handler, _CASE_TYPES, types)
        return handler

    return decorate


class Emitter(Generic[_Value, _Context]):
    """Base for closed-family external text emitters."""

    __slots__ = ()
    _case_table: ClassVar[MappingProxyType[type[object], _CaseHandler]] = MappingProxyType(
        {}
    )

    def __init_subclass__(
        cls,
        *,
        covers: Iterable[type[object]] | None = None,
        **kwargs: object,
    ) -> None:
        super().__init_subclass__(**kwargs)
        table: dict[type[object], _CaseHandler] = {}

        for base in cls.__bases__:
            for handled, handler in getattr(base, "_case_table", {}).items():
                if handled in table:
                    raise TypeError(f"duplicate emitter case for {handled.__name__}")
                table[handled] = handler

        for member in cls.__dict__.values():
            handled_types = getattr(member, _CASE_TYPES, ())
            for handled in handled_types:
                if handled in table:
                    raise TypeError(f"duplicate emitter case for {handled.__name__}")
                table[handled] = cast(_CaseHandler, member)

        if covers is not None:
            expected = frozenset(covers)
            actual = frozenset(table)
            missing = expected - actual
            unexpected = actual - expected
            if missing:
                names = ", ".join(sorted(kind.__name__ for kind in missing))
                raise TypeError(f"missing emitter cases: {names}")
            if unexpected:
                names = ", ".join(sorted(kind.__name__ for kind in unexpected))
                raise TypeError(f"unexpected emitter cases: {names}")

        cls._case_table = MappingProxyType(table)

    def render(
        self,
        value: _Value,
        context: _Context,
        *,
        limits: EmissionLimits | None = None,
    ) -> str:
        """Render ``value`` iteratively, without using the Python call stack."""
        output: list[str] = []
        output_bytes = 0
        expansions = 0
        stack: list[object] = [Visit(value, context)]
        while stack:
            piece = stack.pop()
            if type(piece) is str:
                output_bytes += len(piece.encode("utf-8"))
                if limits is not None and output_bytes > limits.max_output_bytes:
                    self.limit_error("bytes", limits.max_output_bytes)
                output.append(piece)
            elif type(piece) is Visit:
                expansions += 1
                if limits is not None and expansions > limits.max_expansions:
                    self.limit_error("expansions", limits.max_expansions)
                visit = cast(Visit[Any, Any], piece)
                expanded = self.dispatch(
                    cast(_Value, visit.value), cast(_Context, visit.context)
                )
                stack.extend(reversed(expanded))
            else:
                raise TypeError(f"invalid emitter piece: {type(piece).__name__}")
        return "".join(output)

    def limit_error(self, kind: str, limit: int) -> NoReturn:
        """Raise the adapter's deterministic emission-limit error."""
        raise EmissionLimitError(f"emission {kind} limit exceeded ({limit})")

    def dispatch(self, value: _Value, context: _Context) -> tuple[object, ...]:
        """Expand one exact canonical value into forward-order pieces."""
        handler = self._case_table.get(type(value))
        if handler is None:
            return self.unsupported(value, context)
        pieces = handler(self, value, context)
        if type(pieces) is not tuple:
            raise TypeError(
                f"emitter case for {type(value).__name__} must return a tuple of pieces"
            )
        return pieces

    def unsupported(self, value: object, context: object) -> tuple[object, ...]:
        """Reject a value with no exact handler; adapters may customize the error."""
        raise TypeError(f"no exact emitter case for {type(value).__name__}")


__all__ = [
    "EmissionLimitError",
    "EmissionLimits",
    "Emitter",
    "Visit",
    "case",
]

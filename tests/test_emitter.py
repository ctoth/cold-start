"""Exact-dispatch, iterative external-emitter contracts."""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from cold_start.emitter import Emitter, Visit, case


class _Leaf:
    pass


class _Other:
    pass


def test_cases_build_one_exact_dispatch_table():
    class Example(Emitter[object, str], covers={_Leaf, _Other}):
        @case(_Leaf)
        def leaf(self, value: _Leaf, context: str):
            return (context,)

        @case(_Other)
        def other(self, value: _Other, context: str):
            return ("other:", context)

    emitter = Example()
    assert emitter.render(_Leaf(), "leaf") == "leaf"
    assert emitter.render(_Other(), "value") == "other:value"


def test_case_decorator_does_not_wrap_the_handler():
    def handler(self, value, context):
        return (context,)

    assert case(_Leaf)(handler) is handler


def test_class_creation_rejects_missing_duplicate_and_unexpected_cases():
    with pytest.raises(TypeError, match="missing.*_Other"):

        class Missing(Emitter[object, None], covers={_Leaf, _Other}):
            @case(_Leaf)
            def leaf(self, value, context):
                return ("leaf",)

    with pytest.raises(TypeError, match="duplicate.*_Leaf"):

        class Duplicate(Emitter[object, None], covers={_Leaf}):
            @case(_Leaf)
            def first(self, value, context):
                return ("first",)

            @case(_Leaf)
            def second(self, value, context):
                return ("second",)

    with pytest.raises(TypeError, match="unexpected.*_Other"):

        class Unexpected(Emitter[object, None], covers={_Leaf}):
            @case(_Leaf)
            def leaf(self, value, context):
                return ("leaf",)

            @case(_Other)
            def other(self, value, context):
                return ("other",)


def test_dispatch_is_exact_and_rejects_subclasses():
    class LeafChild(_Leaf):
        pass

    class Example(Emitter[object, None], covers={_Leaf}):
        @case(_Leaf)
        def leaf(self, value, context):
            return ("leaf",)

    with pytest.raises(TypeError, match="no exact emitter case.*LeafChild"):
        Example().render(LeafChild(), None)


def test_invalid_piece_is_rejected_instead_of_silently_stringified():
    class Example(Emitter[object, None], covers={_Leaf}):
        @case(_Leaf)
        def leaf(self, value, context):
            return (object(),)

    with pytest.raises(TypeError, match="invalid emitter piece"):
        Example().render(_Leaf(), None)


@dataclass(frozen=True, slots=True)
class _Chain:
    child: _Chain | None = None


def test_rendering_is_iterative_far_past_the_recursion_limit():
    class ChainEmitter(Emitter[_Chain, None], covers={_Chain}):
        @case(_Chain)
        def chain(self, value: _Chain, context: None):
            if value.child is None:
                return ("x",)
            return ("(", Visit(value.child, None), ")")

    value = _Chain()
    for _ in range(5_000):
        value = _Chain(value)

    assert ChainEmitter().render(value, None) == "(" * 5_000 + "x" + ")" * 5_000

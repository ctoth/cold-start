"""Exact boundary contracts exposed by trusted-base mutation testing."""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

import pytest

from cold_start.syntax import (
    BVar,
    Fun,
    Rel,
    Var,
    children,
    map_children,
    node_fields,
    validate,
)
from cold_start.theory import Signature


@dataclass(frozen=True)
class _DataclassClassSentinel:
    value: int = 0


def test_node_helpers_reject_dataclass_classes_independently() -> None:
    with pytest.raises(TypeError, match="not a node"):
        node_fields(_DataclassClassSentinel)
    with pytest.raises(TypeError, match="not a node"):
        children(_DataclassClassSentinel)
    with pytest.raises(TypeError, match="not a node"):
        map_children(_DataclassClassSentinel, lambda child: child)


def test_structural_equality_distinguishes_each_tuple_difference() -> None:
    variable = Var("x")
    assert Fun("f", (variable,)) != Fun("f", (variable, variable))

    list_args = object.__new__(Fun)
    object.__setattr__(list_args, "name", "f")
    object.__setattr__(list_args, "args", [variable])
    assert Fun("f", (variable,)) != list_args

    left_scalar = object.__new__(Fun)
    object.__setattr__(left_scalar, "name", "f")
    object.__setattr__(left_scalar, "args", ("left",))
    right_scalar = object.__new__(Fun)
    object.__setattr__(right_scalar, "name", "f")
    object.__setattr__(right_scalar, "args", ("right",))
    assert left_scalar != right_scalar


def test_de_bruijn_boundaries_are_exact() -> None:
    signature = Signature(sorts=frozenset({"N"}), ranks=())
    with pytest.raises(ValueError, match="dangling bound variable"):
        BVar(1).sort_of(signature, ("N",))
    with pytest.raises(TypeError, match="dangling bound variable"):
        validate(BVar(1), depth=1)
    with pytest.raises(TypeError, match="dangling bound variable"):
        validate(BVar(cast(int, "0")), depth=1)

    body = Fun("pair", (BVar(0), BVar(1)))
    assert body.instantiate(Var("x"), 0) == Fun("pair", (Var("x"), BVar(0)))


def test_relation_repr_uses_infix_only_for_binary_divisibility() -> None:
    left, right = Var("x"), Var("y")
    assert repr(Rel("|", (left, right))) == "x | y"
    assert repr(Rel("R", (left, right))) == "R(x, y)"
    assert repr(Rel("|", (left,))) == "|(x)"

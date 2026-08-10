"""A single model evaluator shared by every model-soundness test.

A `Model` is an interpretation of the function symbols plus (optionally) explicit
finite carriers per sort, needed only to decide quantifiers. `evaluate` is one
uniform fold: free variables come from `env` (name -> element), bound variables
from the de Bruijn stack `denv`, function symbols from `model.interp`, and ∀/∃
enumerate the carrier. Test files build their own models and sample assignments;
they all share this evaluator.

Alongside it live the two other helpers every such test needs: `assert_theorem`,
the trusted-checker side of the same honesty principle (a recipe must re-derive
its exact sequent, hypothesis-free), and `compose_t2`, the one non-commutative
carrier operation the monoid and sorted-action models share.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, field
from typing import Protocol

from cold_start.checker import check
from cold_start.syntax import Bottom, BVar, Eq, Exists, Forall, Fun, Implies, Rel, Var


class ModelLike(Protocol):
    """Any object with an interpretation of the function symbols. Carriers (for
    quantifiers) are looked up reflectively, so a model needs them only if its
    formulas contain quantifiers."""

    interp: dict


@dataclass
class Model:
    name: str
    interp: dict  # function-symbol name -> python callable
    carriers: dict = field(default_factory=dict)  # sort -> explicit element tuple (for ∀/∃)


def _carrier(model: ModelLike, sort: str):
    carriers = getattr(model, "carriers", None)
    if carriers:
        return carriers[sort]
    carrier = getattr(model, "carrier", None)  # single-sorted models expose one
    if carrier is None:
        raise TypeError(f"model {model!r} has no carrier to enumerate sort {sort!r}")
    return carrier


def evaluate(node: object, model: ModelLike, env: dict, denv: tuple = ()):
    if type(node) is Var:
        return env[node.name]
    if type(node) is BVar:
        return denv[node.index]  # 0 is the innermost binder
    if type(node) is Fun:
        return model.interp[node.name](*(evaluate(a, model, env, denv) for a in node.args))
    if type(node) is Eq:
        return evaluate(node.lhs, model, env, denv) == evaluate(node.rhs, model, env, denv)
    if type(node) is Rel:
        return model.interp[node.name](*(evaluate(a, model, env, denv) for a in node.args))
    if type(node) is Implies:
        return (not evaluate(node.ant, model, env, denv)) or evaluate(node.con, model, env, denv)
    if type(node) is Bottom:
        return False
    if type(node) is Forall:
        return all(evaluate(node.body, model, env, (e, *denv)) for e in _carrier(model, node.sort))
    if type(node) is Exists:
        return any(evaluate(node.body, model, env, (e, *denv)) for e in _carrier(model, node.sort))
    raise TypeError(f"cannot evaluate {type(node).__name__}")


def assert_theorem(pf, expected, theory) -> None:
    """The recipe re-derives exactly `expected`, hypothesis-free, in `theory`."""
    seq = check(pf, theory)
    assert not seq.hyps
    assert seq.concl == expected


def env_of(model, data, names: Sequence[str]) -> dict:
    """Sample one assignment of `names` from a single-carrier model's strategy."""
    return {name: data.draw(model.carrier) for name in names}


def compose_t2(g, f):
    """Transformations of {0,1} as tuples (h(0), h(1)); (g o f)(i) = g(f(i))."""
    return (g[f[0]], g[f[1]])

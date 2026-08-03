"""Tactics: the UNTRUSTED prover half of the De Bruijn split.

Nothing in this module is trusted, and nothing in the trusted core imports it.
It emits `proof.Pf` terms -- inert recipes -- and `checker.check` is the only
authority that decides whether they are proofs. That asymmetry is the whole
point of the architecture: this file may be arbitrarily clever, heuristic, or
outright buggy, and the worst it can produce is a proof term that `check`
rejects. So it is written for convenience (plain functions, local conditionals),
not for the polymorphism discipline the trusted core lives under.

The layer is a small equational engine:

    match(pattern, target)         first-order matching, pattern Vars are holes
    Rule                           a directed equation + the Pf that justifies it
    rewrite_step(term, rules)      rewrite the leftmost-outermost redex
    normalize(term, rules)         rewrite to a fixpoint, Trans-chained
    prove_eq(goal, rules)          normalize both sides, join with Trans/Sym
    by_induction(var, pred, rules) base + step by prove_eq, closed by Induct
"""

from __future__ import annotations

from dataclasses import fields, is_dataclass

from .syntax import Node, Var


class TacticError(Exception):
    """A tactic could not build a proof term. Distinct from the checker's
    rejection: this means we never even produced a candidate."""


def _is_node(v: object) -> bool:
    return is_dataclass(v) and not isinstance(v, type)


# ---------------------------------------------------------------------------
# First-order matching
# ---------------------------------------------------------------------------


def match(pattern: Node, target: Node, vars: frozenset[str] | None = None) -> dict | None:
    """Match `pattern` against `target`, returning `{name: Term}` or None.

    A `Var` whose name is in `vars` is a hole and binds to whatever term sits at
    that position; every other node (including a `Var` outside `vars`) must
    match literally. `vars` defaults to all of the pattern's free variables --
    pass `frozenset()` for a ground pattern, which is how an induction
    hypothesis is used (its variable is a fixed eigenvariable, not a hole).

    Works on terms and formulas alike: the walk is generic over dataclass
    fields, so `Eq`/`Implies`/binders match structurally without special cases.
    Iterative, like everything else here."""
    if vars is None:
        vars = pattern.free_vars()
    sigma: dict = {}
    stack: list = [(pattern, target)]
    while stack:
        p, t = stack.pop()
        if type(p) is Var and p.name in vars:
            bound = sigma.get(p.name)
            if bound is None:
                sigma[p.name] = t
            elif bound != t:
                return None  # non-linear pattern, two different witnesses
            continue
        if type(p) is not type(t):
            return None
        for f in fields(p):
            vp, vt = getattr(p, f.name), getattr(t, f.name)
            if _is_node(vp):
                stack.append((vp, vt))
            elif isinstance(vp, tuple):
                if not isinstance(vt, tuple) or len(vp) != len(vt):
                    return None
                for a, b in zip(vp, vt, strict=True):
                    if _is_node(a):
                        stack.append((a, b))
                    elif a != b:
                        return None
            elif vp != vt:
                return None
    return sigma


__all__ = ["TacticError", "match"]

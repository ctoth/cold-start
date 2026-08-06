"""Julia Robinson's multiplication definition over ``(S, |)``.

This is a literal expansion of Theorem 1.2, formula (2), from the rendered pages
101-102 of Robinson's 1949 paper.  Her coprimality and least-common-multiple
abbreviations are expanded into first-order formulas, including existential
witnesses where the paper uses lcm expressions as terms.  Consequently
``robinson_product(a, b, c)`` contains successor and divisibility but no primitive
addition or multiplication symbol.

Every constructor takes an optional ``via`` builder for the divisibility atom.
The default is the atomic relation ``|`` -- Robinson's own signature.  Passing
:func:`cold_start.divisibility.peano_divides` instead produces the SAME formula
with each atom interpreted in PEANO (``a|b := exists k, a*k=b``), which is the
shape the composed totality/uniqueness obligations take on the PEANO shore.
De Bruijn binders make the composition hygienic: abstraction reaches under the
interpretation's own existential without capture.

The constructors make claims; they do not add axioms or extend the trusted proof
checker.
"""

from __future__ import annotations

from collections.abc import Callable

from .prop import And, Iff, Or
from .syntax import Eq, Formula, Implies, Rel, Term, Var, exists, forall
from .vocabulary import S

Divides = Callable[[Term, Term], Formula]


def divides(divisor: Term, dividend: Term) -> Rel:
    """The atomic relation ``divisor | dividend``."""
    return Rel("|", (divisor, dividend))


def _fresh(stem: str, *nodes: Term | Formula) -> str:
    used = {name for node in nodes for name in node.free_vars()}
    if stem not in used:
        return stem
    index = 0
    while f"{stem}{index}" in used:
        index += 1
    return f"{stem}{index}"


def coprime(a: Term, b: Term, via: Divides = divides) -> Formula:
    """Robinson's ``a perpendicular b`` using divisibility alone.

    Every common divisor of ``a`` and ``b`` divides every positive integer; on
    the positive integers, that says the only common divisor is the unit 1.
    """
    divisor_name = _fresh("d", a, b)
    divisor = Var(divisor_name)
    arbitrary_name = _fresh("y", a, b, divisor)
    arbitrary = Var(arbitrary_name)
    body = Implies(
        And(via(divisor, a), via(divisor, b)),
        forall(arbitrary_name, "", via(divisor, arbitrary)),
    )
    return forall(divisor_name, "", body)


def lcm(a: Term, b: Term, c: Term, via: Divides = divides) -> Formula:
    """The graph ``c = lcm(a,b)`` using divisibility alone."""
    multiple_name = _fresh("x", a, b, c)
    multiple = Var(multiple_name)
    return forall(
        multiple_name,
        "",
        Iff(
            And(via(a, multiple), via(b, multiple)),
            via(c, multiple),
        ),
    )


def unit_case(a: Term, b: Term, c: Term, via: Divides = divides) -> Formula:
    """Formula (2)'s first disjunct, true exactly when ``a=b=c=1``."""
    arbitrary_name = _fresh("x", a, b, c)
    arbitrary = Var(arbitrary_name)
    return forall(
        arbitrary_name,
        "",
        And(via(a, arbitrary), via(b, arbitrary), via(c, arbitrary)),
    )


def _lcm_successor_multiple(modulus: Term, a: Term, x: Term, via: Divides) -> Formula:
    lcm_name = _fresh("l", modulus, a, x)
    value = Var(lcm_name)
    return exists(
        lcm_name,
        "",
        And(lcm(a, x, value, via), via(modulus, S(value))),
    )


def _successor_is_nested_lcm(u: Term, c: Term, x: Term, y: Term, via: Divides) -> Formula:
    xy_name = _fresh("l", u, c, x, y)
    xy = Var(xy_name)
    cxy_name = _fresh("v", u, c, x, y, xy)
    cxy = Var(cxy_name)
    return exists(
        xy_name,
        "",
        And(
            lcm(x, y, xy, via),
            exists(
                cxy_name,
                "",
                And(lcm(c, xy, cxy, via), Eq(S(u), cxy)),
            ),
        ),
    )


def robinson_product(a: Term, b: Term, c: Term, via: Divides = divides) -> Formula:
    """Formula (2): Robinson's ``a*b=c`` graph in successor and divisibility.

    The unit disjunct handles ``a=b=c=1``.  The other disjunct is Robinson's
    Chinese-remainder characterization, with every coprimality/lcm abbreviation
    expanded hygienically.
    """
    x_name = _fresh("x", a, b, c)
    x = Var(x_name)
    y_name = _fresh("y", a, b, c, x)
    y = Var(y_name)
    modulus_name = _fresh("m", a, b, c, x, y)
    modulus = Var(modulus_name)
    u_name = _fresh("u", a, b, c, x, y, modulus)
    u = Var(u_name)

    hypothesis = And(
        coprime(a, x, via),
        coprime(b, y, via),
        coprime(c, x, via),
        coprime(c, y, via),
        coprime(x, y, via),
        _lcm_successor_multiple(modulus, a, x, via),
        _lcm_successor_multiple(modulus, b, y, via),
    )
    conclusion = exists(
        u_name,
        "",
        And(
            via(modulus, u),
            _successor_is_nested_lcm(u, c, x, y, via),
        ),
    )
    general_case = forall(
        x_name,
        "",
        forall(
            y_name,
            "",
            forall(modulus_name, "", Implies(hypothesis, conclusion)),
        ),
    )
    return Or(unit_case(a, b, c, via), general_case)

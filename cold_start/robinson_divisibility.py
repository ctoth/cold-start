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
from .tactics import fresh_name
from .vocabulary import S

Divides = Callable[[Term, Term], Formula]
Domain = Callable[[Term], Formula]


def divides(divisor: Term, dividend: Term) -> Rel:
    """The atomic relation ``divisor | dividend``."""
    return Rel("|", (divisor, dividend))


def _forall_in(name: str, body: Formula, domain: Domain | None) -> Formula:
    if domain is not None:
        body = Implies(domain(Var(name)), body)
    return forall(name, "", body)


def _exists_in(name: str, body: Formula, domain: Domain | None) -> Formula:
    if domain is not None:
        body = And(domain(Var(name)), body)
    return exists(name, "", body)


def coprime(
    a: Term,
    b: Term,
    via: Divides = divides,
    *,
    domain: Domain | None = None,
) -> Formula:
    """Robinson's ``a perpendicular b`` using divisibility alone.

    Every common divisor of ``a`` and ``b`` divides every positive integer; on
    the positive integers, that says the only common divisor is the unit 1.
    """
    divisor_name = fresh_name("d", a, b)
    divisor = Var(divisor_name)
    arbitrary_name = fresh_name("y", a, b, divisor)
    arbitrary = Var(arbitrary_name)
    body = Implies(
        And(via(divisor, a), via(divisor, b)),
        _forall_in(arbitrary_name, via(divisor, arbitrary), domain),
    )
    return _forall_in(divisor_name, body, domain)


def lcm(
    a: Term,
    b: Term,
    c: Term,
    via: Divides = divides,
    *,
    domain: Domain | None = None,
) -> Formula:
    """The graph ``c = lcm(a,b)`` using divisibility alone."""
    multiple_name = fresh_name("x", a, b, c)
    multiple = Var(multiple_name)
    return _forall_in(
        multiple_name,
        Iff(
            And(via(a, multiple), via(b, multiple)),
            via(c, multiple),
        ),
        domain,
    )


def unit_case(
    a: Term,
    b: Term,
    c: Term,
    via: Divides = divides,
    *,
    domain: Domain | None = None,
) -> Formula:
    """Formula (2)'s first disjunct, true exactly when ``a=b=c=1``."""
    arbitrary_name = fresh_name("x", a, b, c)
    arbitrary = Var(arbitrary_name)
    return _forall_in(
        arbitrary_name,
        And(via(a, arbitrary), via(b, arbitrary), via(c, arbitrary)),
        domain,
    )


def _lcm_successor_multiple(
    modulus: Term,
    a: Term,
    x: Term,
    via: Divides,
    domain: Domain | None,
) -> Formula:
    lcm_name = fresh_name("l", modulus, a, x)
    value = Var(lcm_name)
    return _exists_in(
        lcm_name,
        And(lcm(a, x, value, via, domain=domain), via(modulus, S(value))),
        domain,
    )


def _successor_is_nested_lcm(
    u: Term,
    c: Term,
    x: Term,
    y: Term,
    via: Divides,
    domain: Domain | None,
) -> Formula:
    xy_name = fresh_name("l", u, c, x, y)
    xy = Var(xy_name)
    cxy_name = fresh_name("v", u, c, x, y, xy)
    cxy = Var(cxy_name)
    return _exists_in(
        xy_name,
        And(
            lcm(x, y, xy, via, domain=domain),
            _exists_in(
                cxy_name,
                And(lcm(c, xy, cxy, via, domain=domain), Eq(S(u), cxy)),
                domain,
            ),
        ),
        domain,
    )


def robinson_product(
    a: Term,
    b: Term,
    c: Term,
    via: Divides = divides,
    *,
    domain: Domain | None = None,
) -> Formula:
    """Formula (2): Robinson's ``a*b=c`` graph in successor and divisibility.

    The unit disjunct handles ``a=b=c=1``.  The other disjunct is Robinson's
    Chinese-remainder characterization, with every coprimality/lcm abbreviation
    expanded hygienically.
    """
    x_name = fresh_name("x", a, b, c)
    x = Var(x_name)
    y_name = fresh_name("y", a, b, c, x)
    y = Var(y_name)
    modulus_name = fresh_name("m", a, b, c, x, y)
    modulus = Var(modulus_name)
    u_name = fresh_name("u", a, b, c, x, y, modulus)
    u = Var(u_name)

    hypothesis = And(
        coprime(a, x, via, domain=domain),
        coprime(b, y, via, domain=domain),
        coprime(c, x, via, domain=domain),
        coprime(c, y, via, domain=domain),
        coprime(x, y, via, domain=domain),
        _lcm_successor_multiple(modulus, a, x, via, domain),
        _lcm_successor_multiple(modulus, b, y, via, domain),
    )
    conclusion = _exists_in(
        u_name,
        And(
            via(modulus, u),
            _successor_is_nested_lcm(u, c, x, y, via, domain),
        ),
        domain,
    )
    general_case = _forall_in(
        x_name,
        _forall_in(
            y_name,
            _forall_in(modulus_name, Implies(hypothesis, conclusion), domain),
            domain,
        ),
        domain,
    )
    return Or(unit_case(a, b, c, via, domain=domain), general_case)

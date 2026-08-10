"""Deterministic bounded Groebner ideal-membership search over F2.

The search is untrusted and proves nothing. Every basis element carries a vector
of cofactors in the original generators. A zero target remainder is returned
only with that vector; the caller may then replay it through ordinary equality
proofs. Budget exhaustion and a completed nonzero remainder are distinct values.

The monomial order is graded lexicographic over the exact structural ordering
of the problem's atoms. F2 is deliberate: every nonzero leading coefficient is
one, so reduction requires no coefficient division.
"""

from __future__ import annotations

from dataclasses import dataclass

from .proof import Pf
from .ring_nf import (
    AlgebraContext,
    EquationProof,
    Monomial,
    Polynomial,
    elaborate_ideal_membership,
    monomial_sort_key,
    multiply_monomials,
    normalize,
)
from .syntax import Eq, Term


@dataclass(frozen=True, slots=True)
class GroebnerLimits:
    max_steps: int
    max_degree: int
    max_monomials: int
    max_basis_size: int
    max_cofactor_monomials: int

    def __post_init__(self) -> None:
        for name in (
            "max_steps",
            "max_degree",
            "max_monomials",
            "max_basis_size",
            "max_cofactor_monomials",
        ):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive exact int")


DEFAULT_GROEBNER_LIMITS = GroebnerLimits(
    max_steps=100_000,
    max_degree=32,
    max_monomials=20_000,
    max_basis_size=256,
    max_cofactor_monomials=100_000,
)


@dataclass(frozen=True, slots=True)
class GroebnerStats:
    steps: int
    critical_pairs: int
    max_degree: int
    max_monomials: int
    basis_size: int
    max_cofactor_monomials: int


@dataclass(frozen=True, slots=True)
class MembershipWitness:
    cofactors: tuple[Polynomial, ...]
    stats: GroebnerStats


@dataclass(frozen=True, slots=True)
class CertifiedMembership:
    witness: MembershipWitness
    proof: Pf


@dataclass(frozen=True, slots=True)
class NotMember:
    remainder: Polynomial
    stats: GroebnerStats


@dataclass(frozen=True, slots=True)
class SearchExhausted:
    reason: str
    stats: GroebnerStats


SearchResult = MembershipWitness | NotMember | SearchExhausted
ProverResult = CertifiedMembership | NotMember | SearchExhausted


@dataclass(frozen=True, slots=True)
class _BasisElement:
    polynomial: Polynomial
    cofactors: tuple[Polynomial, ...]


class _BudgetExhausted(Exception):
    pass


@dataclass(slots=True)
class _Tracker:
    limits: GroebnerLimits
    steps: int = 0
    critical_pairs: int = 0
    max_degree: int = 0
    max_monomials: int = 0
    basis_size: int = 0
    max_cofactor_monomials: int = 0

    def consume(self) -> None:
        self.steps += 1
        if self.steps > self.limits.max_steps:
            raise _BudgetExhausted("Groebner steps limit exceeded")

    def observe_polynomial(self, polynomial: Polynomial) -> None:
        monomial_count = len(polynomial.terms)
        self.max_monomials = max(self.max_monomials, monomial_count)
        if monomial_count > self.limits.max_monomials:
            raise _BudgetExhausted("Groebner monomials limit exceeded")
        degree = max((_degree(monomial) for monomial, _ in polynomial.terms), default=0)
        self.max_degree = max(self.max_degree, degree)
        if degree > self.limits.max_degree:
            raise _BudgetExhausted("Groebner degree limit exceeded")

    def observe_basis(self, basis: list[_BasisElement]) -> None:
        self.basis_size = max(self.basis_size, len(basis))
        if len(basis) > self.limits.max_basis_size:
            raise _BudgetExhausted("Groebner basis-size limit exceeded")

    def observe_cofactors(self, cofactors: tuple[Polynomial, ...]) -> None:
        size = sum(len(cofactor.terms) for cofactor in cofactors)
        self.max_cofactor_monomials = max(self.max_cofactor_monomials, size)
        if size > self.limits.max_cofactor_monomials:
            raise _BudgetExhausted("Groebner cofactor-size limit exceeded")
        for cofactor in cofactors:
            self.observe_polynomial(cofactor)

    def snapshot(self) -> GroebnerStats:
        return GroebnerStats(
            steps=self.steps,
            critical_pairs=self.critical_pairs,
            max_degree=self.max_degree,
            max_monomials=self.max_monomials,
            basis_size=self.basis_size,
            max_cofactor_monomials=self.max_cofactor_monomials,
        )


@dataclass(frozen=True, slots=True)
class _MonomialOrder:
    atoms: tuple[Term, ...]

    def key(self, monomial: Monomial) -> tuple[int, tuple[int, ...]]:
        powers = dict(monomial)
        return (_degree(monomial), tuple(powers.get(atom, 0) for atom in self.atoms))


def _degree(monomial: Monomial) -> int:
    return sum(exponent for _atom, exponent in monomial)


def _canonical(monomials: set[Monomial]) -> Polynomial:
    return Polynomial(
        tuple((monomial, 1) for monomial in sorted(monomials, key=monomial_sort_key))
    )


def _zero() -> Polynomial:
    return Polynomial(())


def _one_monomial(monomial: Monomial) -> Polynomial:
    return Polynomial(((monomial, 1),))


def _add(left: Polynomial, right: Polynomial) -> Polynomial:
    monomials = {monomial for monomial, _ in left.terms}
    monomials.symmetric_difference_update(monomial for monomial, _ in right.terms)
    return _canonical(monomials)


def _scale(polynomial: Polynomial, monomial: Monomial) -> Polynomial:
    return _canonical(
        {multiply_monomials(source, monomial) for source, _ in polynomial.terms}
    )


def _divides(divisor: Monomial, dividend: Monomial) -> bool:
    available = dict(dividend)
    return all(available.get(atom, 0) >= exponent for atom, exponent in divisor)


def _quotient(dividend: Monomial, divisor: Monomial) -> Monomial:
    divisor_powers = dict(divisor)
    return tuple(
        (atom, exponent - divisor_powers.get(atom, 0))
        for atom, exponent in dividend
        if exponent - divisor_powers.get(atom, 0) > 0
    )


def _lcm(left: Monomial, right: Monomial) -> Monomial:
    powers = dict(left)
    for atom, exponent in right:
        powers[atom] = max(powers.get(atom, 0), exponent)
    return tuple(sorted(powers.items(), key=lambda item: monomial_sort_key(((item[0], 1),))))


def _leading(polynomial: Polynomial, order: _MonomialOrder) -> Monomial:
    if not polynomial.terms:
        raise ValueError("zero polynomial has no leading monomial")
    return max((monomial for monomial, _ in polynomial.terms), key=order.key)


def _problem_order(polynomials: tuple[Polynomial, ...]) -> _MonomialOrder:
    atoms = {
        atom
        for polynomial in polynomials
        for monomial, _coefficient in polynomial.terms
        for atom, _exponent in monomial
    }
    return _MonomialOrder(
        tuple(sorted(atoms, key=lambda atom: monomial_sort_key(((atom, 1),))))
    )


def _divide(
    polynomial: Polynomial,
    basis: list[_BasisElement],
    order: _MonomialOrder,
    tracker: _Tracker,
) -> tuple[Polynomial, tuple[Polynomial, ...]]:
    work = polynomial
    remainder = _zero()
    quotients = [_zero() for _ in basis]
    while work.terms:
        tracker.consume()
        leading = _leading(work, order)
        divisor_index = next(
            (
                index
                for index, element in enumerate(basis)
                if _divides(_leading(element.polynomial, order), leading)
            ),
            None,
        )
        if divisor_index is None:
            term = _one_monomial(leading)
            remainder = _add(remainder, term)
            work = _add(work, term)
        else:
            divisor = _leading(basis[divisor_index].polynomial, order)
            multiplier = _quotient(leading, divisor)
            quotients[divisor_index] = _add(
                quotients[divisor_index], _one_monomial(multiplier)
            )
            work = _add(work, _scale(basis[divisor_index].polynomial, multiplier))
        tracker.observe_polynomial(work)
        tracker.observe_polynomial(remainder)
    return remainder, tuple(quotients)


def _vector_add(
    left: tuple[Polynomial, ...], right: tuple[Polynomial, ...]
) -> tuple[Polynomial, ...]:
    return tuple(_add(a, b) for a, b in zip(left, right, strict=True))


def _vector_scale(
    vector: tuple[Polynomial, ...], monomial: Monomial
) -> tuple[Polynomial, ...]:
    return tuple(_scale(polynomial, monomial) for polynomial in vector)


def _apply_quotients(
    initial: tuple[Polynomial, ...],
    quotients: tuple[Polynomial, ...],
    basis: list[_BasisElement],
) -> tuple[Polynomial, ...]:
    result = initial
    for quotient, element in zip(quotients, basis, strict=True):
        for monomial, _coefficient in quotient.terms:
            result = _vector_add(result, _vector_scale(element.cofactors, monomial))
    return result


def _equation_polynomial(equation: Eq, context: AlgebraContext) -> Polynomial:
    left = normalize(equation.lhs, context).polynomial
    right = normalize(equation.rhs, context).polynomial
    return _add(left, right)


def _search(
    target: Polynomial,
    generators: tuple[Polynomial, ...],
    limits: GroebnerLimits,
) -> SearchResult:
    tracker = _Tracker(limits)
    try:
        order = _problem_order((target, *generators))
        basis: list[_BasisElement] = []
        width = len(generators)
        for index, generator in enumerate(generators):
            tracker.observe_polynomial(generator)
            if not generator.terms:
                continue
            cofactors = tuple(
                _one_monomial(()) if slot == index else _zero() for slot in range(width)
            )
            tracker.observe_cofactors(cofactors)
            basis.append(_BasisElement(generator, cofactors))
            tracker.observe_basis(basis)

        pairs = [(left, right) for right in range(len(basis)) for left in range(right)]
        while pairs:
            left_index, right_index = pairs.pop(0)
            tracker.consume()
            tracker.critical_pairs += 1
            left = basis[left_index]
            right = basis[right_index]
            left_lead = _leading(left.polynomial, order)
            right_lead = _leading(right.polynomial, order)
            common = _lcm(left_lead, right_lead)
            left_multiplier = _quotient(common, left_lead)
            right_multiplier = _quotient(common, right_lead)
            s_polynomial = _add(
                _scale(left.polynomial, left_multiplier),
                _scale(right.polynomial, right_multiplier),
            )
            s_cofactors = _vector_add(
                _vector_scale(left.cofactors, left_multiplier),
                _vector_scale(right.cofactors, right_multiplier),
            )
            tracker.observe_polynomial(s_polynomial)
            remainder, quotients = _divide(s_polynomial, basis, order, tracker)
            if remainder.terms:
                remainder_cofactors = _apply_quotients(s_cofactors, quotients, basis)
                tracker.observe_cofactors(remainder_cofactors)
                new_index = len(basis)
                basis.append(_BasisElement(remainder, remainder_cofactors))
                tracker.observe_basis(basis)
                pairs.extend((index, new_index) for index in range(new_index))
                pairs.sort()

        tracker.observe_polynomial(target)
        remainder, quotients = _divide(target, basis, order, tracker)
        if remainder.terms:
            return NotMember(remainder, tracker.snapshot())
        zero_vector = tuple(_zero() for _ in generators)
        cofactors = _apply_quotients(zero_vector, quotients, basis)
        tracker.observe_cofactors(cofactors)
        return MembershipWitness(cofactors, tracker.snapshot())
    except _BudgetExhausted as exc:
        return SearchExhausted(str(exc), tracker.snapshot())


def search_ideal_membership(
    goal: object,
    generators: tuple[Eq, ...],
    context: AlgebraContext,
    *,
    limits: GroebnerLimits = DEFAULT_GROEBNER_LIMITS,
) -> SearchResult:
    """Search for cofactors proving one F2 equation from generator equations."""
    if type(goal) is not Eq:
        raise TypeError("ideal-membership goal must be an exact Eq")
    if type(generators) is not tuple or any(type(item) is not Eq for item in generators):
        raise TypeError("ideal generators must be a tuple of exact Eq values")
    target = _equation_polynomial(goal, context)
    source_polynomials = tuple(
        _equation_polynomial(generator, context) for generator in generators
    )
    return _search(target, source_polynomials, limits)


def prove_ideal_membership(
    goal: object,
    sources: tuple[EquationProof, ...],
    context: AlgebraContext,
    *,
    limits: GroebnerLimits = DEFAULT_GROEBNER_LIMITS,
) -> ProverResult:
    """Search, then elaborate a carried cofactor witness into an ordinary proof."""
    if type(sources) is not tuple:
        raise TypeError("ideal proof sources must be a tuple")
    equations = tuple(source[0] for source in sources)
    result = search_ideal_membership(goal, equations, context, limits=limits)
    if not isinstance(result, MembershipWitness):
        return result
    proof = elaborate_ideal_membership(goal, sources, result.cofactors, context)
    return CertifiedMembership(result, proof)


__all__ = [
    "DEFAULT_GROEBNER_LIMITS",
    "CertifiedMembership",
    "GroebnerLimits",
    "GroebnerStats",
    "MembershipWitness",
    "NotMember",
    "ProverResult",
    "SearchExhausted",
    "SearchResult",
    "prove_ideal_membership",
    "search_ideal_membership",
]

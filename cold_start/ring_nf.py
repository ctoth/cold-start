"""Sparse proof-producing commutative polynomial normalization.

This module is an untrusted prover. Its sparse polynomials plan a derivation;
they never cross the proof boundary and the checker never evaluates them. Each
fold step emits an ordinary equality proof using only the canonical proof
constructors and context-supplied proved recipes.

The initial coefficient implementation is characteristic two. The IR and
context boundary are deliberately coefficient-aware so later phases can add
natural and integer coefficients without creating another normalizer.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, TypeAlias, cast

from .proof import Cong, Pf, Refl, Sym, Trans
from .syntax import Eq, Fun, Term, Var
from .tactics import Rule, TacticError, prove_eq

CoefficientDomain: TypeAlias = Literal["mod2"]
AtomKey: TypeAlias = Term
Monomial: TypeAlias = tuple[tuple[AtomKey, int], ...]
PolynomialTerm: TypeAlias = tuple[Monomial, int]
EquationProof: TypeAlias = tuple[Eq, Pf]
AtomSortKey: TypeAlias = tuple[str, str, str]
MonomialSortKey: TypeAlias = tuple[tuple[AtomSortKey, int], ...]


class RingNormalizationError(TacticError):
    """A term is outside the context or two polynomials are unequal."""


@dataclass(frozen=True, slots=True)
class Polynomial:
    """A canonical sparse polynomial: sorted monomials, nonzero coefficients."""

    terms: tuple[PolynomialTerm, ...]


@dataclass(frozen=True, slots=True)
class AlgebraContext:
    """Untrusted algebra symbols and proved recipes for one normalizer policy."""

    zero: str
    one: str
    add: str
    mul: str
    neg: str | None
    coefficient_domain: CoefficientDomain
    atoms: frozenset[Term]
    merge_rules: tuple[Rule, ...]
    rewrite_budget: int

    def __post_init__(self) -> None:
        names = (self.zero, self.one, self.add, self.mul)
        if any(type(name) is not str or not name for name in names):
            raise ValueError("algebra symbols must be nonempty exact strings")
        if len(set(names)) != len(names):
            raise ValueError("zero, one, addition, and multiplication must be distinct")
        if self.neg is not None and (type(self.neg) is not str or not self.neg):
            raise ValueError("negation must be absent or a nonempty exact string")
        if self.coefficient_domain != "mod2":
            raise ValueError("only the mod2 coefficient domain is implemented")
        if type(self.atoms) is not frozenset:
            raise TypeError("AlgebraContext.atoms must be a frozenset")
        for atom in self.atoms:
            if type(atom) is not Fun or atom.args:
                raise ValueError("declared generators must be exact nullary Fun terms")
            if atom.name in {self.zero, self.one, self.add, self.mul, self.neg}:
                raise ValueError(f"generator collides with algebra symbol {atom.name!r}")
        if type(self.merge_rules) is not tuple:
            raise TypeError("AlgebraContext.merge_rules must be a tuple")
        if type(self.rewrite_budget) is not int or self.rewrite_budget <= 0:
            raise ValueError("rewrite_budget must be a positive exact int")

    @property
    def zero_term(self) -> Term:
        return Fun(self.zero, ())

    @property
    def one_term(self) -> Term:
        return Fun(self.one, ())


@dataclass(frozen=True, slots=True)
class Normalization:
    """Sparse result, canonical quoted term, and ordinary proof of equality."""

    polynomial: Polynomial
    term: Term
    proof: Pf


def _atom_sort_key(atom: Term) -> AtomSortKey:
    if type(atom) is Var:
        return ("var", atom.sort, atom.name)
    if type(atom) is Fun and not atom.args:
        return ("generator", "", atom.name)
    raise RingNormalizationError(f"unsupported polynomial atom: {atom!r}")


def monomial_sort_key(monomial: Monomial) -> MonomialSortKey:
    """Stable structural order used for canonical sparse storage and quoting."""
    return tuple((_atom_sort_key(atom), exponent) for atom, exponent in monomial)


def _polynomial(raw: dict[Monomial, int]) -> Polynomial:
    terms = tuple(
        (monomial, coefficient & 1)
        for monomial, coefficient in sorted(
            raw.items(), key=lambda item: monomial_sort_key(item[0])
        )
        if coefficient & 1
    )
    return Polynomial(terms)


def _raw(poly: Polynomial) -> dict[Monomial, int]:
    return dict(poly.terms)


def _constant_one() -> Polynomial:
    return Polynomial((((), 1),))


def _atom(atom: Term) -> Polynomial:
    return Polynomial(((((atom, 1),), 1),))


def _add(left: Polynomial, right: Polynomial) -> Polynomial:
    out = _raw(left)
    for monomial, coefficient in right.terms:
        out[monomial] = out.get(monomial, 0) ^ coefficient
    return _polynomial(out)


def _multiply_monomials(left: Monomial, right: Monomial) -> Monomial:
    powers: dict[Term, int] = {}
    for atom, exponent in (*left, *right):
        powers[atom] = powers.get(atom, 0) + exponent
    return tuple(sorted(powers.items(), key=lambda item: _atom_sort_key(item[0])))


def _mul(left: Polynomial, right: Polynomial) -> Polynomial:
    out: dict[Monomial, int] = {}
    for left_monomial, left_coefficient in left.terms:
        for right_monomial, right_coefficient in right.terms:
            monomial = _multiply_monomials(left_monomial, right_monomial)
            coefficient = left_coefficient & right_coefficient
            out[monomial] = out.get(monomial, 0) ^ coefficient
    return _polynomial(out)


def _right_associated(symbol: str, values: list[Term], identity: Term) -> Term:
    if not values:
        return identity
    result = values[-1]
    for value in reversed(values[:-1]):
        result = Fun(symbol, (value, result))
    return result


def quote(polynomial: Polynomial, context: AlgebraContext) -> Term:
    """Quote one sparse polynomial in the context's fixed right-associated form."""
    monomial_terms: list[Term] = []
    for monomial, coefficient in polynomial.terms:
        if coefficient != 1:
            raise RingNormalizationError("mod2 polynomial has a non-bit coefficient")
        factors = [atom for atom, exponent in monomial for _ in range(exponent)]
        monomial_terms.append(
            _right_associated(context.mul, factors, context.one_term)
        )
    return _right_associated(context.add, monomial_terms, context.zero_term)


def _node_children(term: object, context: AlgebraContext) -> tuple[Term, ...]:
    if type(term) is Var:
        return ()
    if type(term) is not Fun:
        raise RingNormalizationError(
            f"unsupported polynomial term type: {type(term).__name__}"
        )
    if term.name in {context.add, context.mul}:
        if len(term.args) != 2:
            raise RingNormalizationError(
                f"unsupported arity for {term.name!r}: {len(term.args)}"
            )
        return term.args
    if not term.args and (
        term.name in {context.zero, context.one} or term in context.atoms
    ):
        return ()
    raise RingNormalizationError(f"unsupported function in polynomial term: {term.name!r}")


def _postorder(term: object, context: AlgebraContext) -> tuple[Term, ...]:
    unseen, active, complete = 0, 1, 2
    colors: dict[int, int] = {}
    order: list[Term] = []
    stack: list[tuple[object, bool]] = [(term, False)]
    while stack:
        candidate, leaving = stack.pop()
        children = _node_children(candidate, context)
        if type(candidate) not in {Var, Fun}:
            raise RingNormalizationError(
                f"unsupported polynomial term type: {type(candidate).__name__}"
            )
        node = cast(Term, candidate)
        identity = id(node)
        color = colors.get(identity, unseen)
        if leaving:
            if color != active:
                raise RingNormalizationError("invalid polynomial traversal state")
            colors[identity] = complete
            order.append(node)
            continue
        if color == complete:
            continue
        if color == active:
            raise RingNormalizationError("unsupported cyclic polynomial term")
        colors[identity] = active
        stack.append((node, True))
        stack.extend((child, False) for child in reversed(children))
    return tuple(order)


def _merge(
    original: Term,
    symbol: str,
    left: Normalization,
    right: Normalization,
    polynomial: Polynomial,
    context: AlgebraContext,
) -> Normalization:
    canonical_source = Fun(symbol, (left.term, right.term))
    canonical_target = quote(polynomial, context)
    descend = Cong(symbol, (left.proof, right.proof))
    if canonical_source == canonical_target:
        proof = descend
    else:
        merge = prove_eq(
            Eq(canonical_source, canonical_target),
            context.merge_rules,
            context.rewrite_budget,
        )
        proof = Trans(descend, merge)
    return Normalization(polynomial, canonical_target, proof)


def normalize(term: object, context: AlgebraContext) -> Normalization:
    """Reify and prove one supported term equal to its sparse canonical quote."""
    results: dict[int, Normalization] = {}
    for node in _postorder(term, context):
        if type(node) is Var or node in context.atoms:
            results[id(node)] = Normalization(_atom(node), node, Refl(node))
            continue
        if type(node) is not Fun:
            raise AssertionError("postorder admitted a non-term")
        if node.name == context.zero:
            results[id(node)] = Normalization(Polynomial(()), node, Refl(node))
        elif node.name == context.one:
            results[id(node)] = Normalization(_constant_one(), node, Refl(node))
        elif node.name == context.add:
            left, right = (results[id(child)] for child in node.args)
            results[id(node)] = _merge(
                node,
                context.add,
                left,
                right,
                _add(left.polynomial, right.polynomial),
                context,
            )
        elif node.name == context.mul:
            left, right = (results[id(child)] for child in node.args)
            results[id(node)] = _merge(
                node,
                context.mul,
                left,
                right,
                _mul(left.polynomial, right.polynomial),
                context,
            )
        else:
            raise AssertionError("postorder admitted an unsupported function")
    return results[id(term)]


def ring_eq(goal: object, context: AlgebraContext) -> Pf:
    """Prove an equality when both sides reify to the same sparse polynomial."""
    if type(goal) is not Eq:
        raise RingNormalizationError("ring_eq needs an exact Eq goal")
    left = normalize(goal.lhs, context)
    right = normalize(goal.rhs, context)
    if left.polynomial != right.polynomial:
        raise RingNormalizationError("equality sides reify to different polynomials")
    return Trans(left.proof, Sym(right.proof))


def _require_equation_proof(candidate: object) -> EquationProof:
    if type(candidate) is not tuple:
        raise TypeError("each source must be an (Eq, Pf) tuple")
    items = cast("tuple[object, ...]", candidate)
    if len(items) != 2:
        raise TypeError("each source must be an (Eq, Pf) tuple")
    equation, proof = items
    if type(equation) is not Eq or not isinstance(proof, Pf):
        raise TypeError("each source must contain an exact Eq and a Pf")
    return equation, proof


def elaborate_ideal_membership(
    goal: object,
    sources: tuple[EquationProof, ...],
    cofactors: tuple[Polynomial, ...],
    context: AlgebraContext,
) -> Pf:
    """Replay an F2 ideal-membership cofactor vector as an ordinary proof.

    Each nonzero cofactor scales its source equation by ``Cong('*', ...)``.
    The scaled equations are summed, ``ring_eq`` proves the witness cross-sum,
    and a second characteristic-two normalization cancels the shared suffix.
    Wrong cofactors fail while proving the cross-sum and return no candidate.
    """
    if type(goal) is not Eq:
        raise RingNormalizationError("ideal-membership elaboration needs an exact Eq goal")
    if type(sources) is not tuple or type(cofactors) is not tuple:
        raise TypeError("sources and cofactors must be tuples")
    if len(sources) != len(cofactors):
        raise RingNormalizationError("cofactor count does not match source count")

    scaled: list[EquationProof] = []
    for source, cofactor in zip(sources, cofactors, strict=True):
        equation, proof = _require_equation_proof(source)
        if not cofactor.terms:
            continue
        coefficient = quote(cofactor, context)
        scaled.append(
            (
                Eq(
                    Fun(context.mul, (equation.lhs, coefficient)),
                    Fun(context.mul, (equation.rhs, coefficient)),
                ),
                Cong(context.mul, (proof, Refl(coefficient))),
            )
        )

    if not scaled:
        return ring_eq(goal, context)

    first_equation, combined = scaled[0]
    left_sum, right_sum = first_equation.lhs, first_equation.rhs
    for equation, proof in scaled[1:]:
        combined = Cong(context.add, (combined, proof))
        left_sum = Fun(context.add, (left_sum, equation.lhs))
        right_sum = Fun(context.add, (right_sum, equation.rhs))

    on_sum = Cong(context.add, (Refl(goal.lhs), combined))
    shuffle = ring_eq(
        Eq(
            Fun(context.add, (goal.lhs, right_sum)),
            Fun(context.add, (goal.rhs, left_sum)),
        ),
        context,
    )
    with_suffix = Trans(on_sum, shuffle)
    doubled = Cong(context.add, (with_suffix, Refl(left_sum)))
    left_doubled = Fun(
        context.add,
        (Fun(context.add, (goal.lhs, left_sum)), left_sum),
    )
    right_doubled = Fun(
        context.add,
        (Fun(context.add, (goal.rhs, left_sum)), left_sum),
    )
    cancel_left = ring_eq(Eq(left_doubled, goal.lhs), context)
    cancel_right = ring_eq(Eq(right_doubled, goal.rhs), context)
    return Trans(Sym(cancel_left), Trans(doubled, cancel_right))


__all__ = [
    "AlgebraContext",
    "AtomKey",
    "CoefficientDomain",
    "EquationProof",
    "Monomial",
    "Normalization",
    "Polynomial",
    "RingNormalizationError",
    "elaborate_ideal_membership",
    "monomial_sort_key",
    "normalize",
    "quote",
    "ring_eq",
]

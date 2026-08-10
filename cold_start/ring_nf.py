"""Sparse proof-producing commutative polynomial normalization.

This module is an untrusted prover. Its sparse polynomials plan a derivation;
they never cross the proof boundary and the checker never evaluates them. Each
fold step emits an ordinary equality proof using only the canonical proof
constructors and context-supplied proved recipes.

The coefficient policy is explicit: natural semirings, integer rings, and
characteristic-two rings share the polynomial owner but not cancellation or
sign assumptions. The IR never crosses the proof boundary.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, TypeAlias, cast

from .proof import MP, Cong, Pf, Refl, Sym, Trans
from .syntax import Eq, Fun, Term, Var
from .tactics import DEFAULT_BUDGET, Rule, TacticError, prove_eq, simultaneous_inst

CoefficientDomain: TypeAlias = Literal["natural", "integer", "mod2"]
AtomKey: TypeAlias = Term
Monomial: TypeAlias = tuple[tuple[AtomKey, int], ...]
PolynomialTerm: TypeAlias = tuple[Monomial, int]
EquationProof: TypeAlias = tuple[Eq, Pf]
CombinationSource: TypeAlias = tuple[Eq, Pf, Term | None]
AtomSortKey: TypeAlias = tuple[str, str, str]
MonomialSortKey: TypeAlias = tuple[tuple[AtomSortKey, int], ...]


class RingNormalizationError(TacticError):
    """A term is outside the context or two polynomials are unequal."""


def _validate_cancellation(value: object) -> None:
    if value is not None and not isinstance(value, Pf):
        raise TypeError("right_cancellation must be absent or a Pf")


def _validate_proof(value: object, name: str) -> None:
    if not isinstance(value, Pf):
        raise TypeError(f"{name} must be a Pf")


@dataclass(frozen=True, slots=True)
class Polynomial:
    """A canonical sparse polynomial: sorted monomials, nonzero coefficients."""

    terms: tuple[PolynomialTerm, ...]


@dataclass(frozen=True, slots=True)
class AlgebraContext:
    """Untrusted algebra symbols and proved recipes for one normalizer policy."""

    zero: Term
    one: Term
    add: str
    mul: str
    neg: str | None
    successor: str | None
    coefficient_domain: CoefficientDomain
    atoms: frozenset[Term]
    merge_rules: tuple[Rule, ...]
    right_cancellation: Pf | None
    rewrite_budget: int

    def __post_init__(self) -> None:
        if type(self.zero) not in {Var, Fun} or type(self.one) not in {Var, Fun}:
            raise TypeError("zero and one must be exact terms")
        if self.zero == self.one or self.zero.free_vars() or self.one.free_vars():
            raise ValueError("zero and one must be distinct closed terms")
        names = (self.add, self.mul)
        if any(type(name) is not str or not name for name in names):
            raise ValueError("algebra operation symbols must be nonempty exact strings")
        optional_names = (self.neg, self.successor)
        if any(name is not None and (type(name) is not str or not name) for name in optional_names):
            raise ValueError("optional algebra symbols must be nonempty exact strings")
        present_names = (*names, *(name for name in optional_names if name is not None))
        if len(set(present_names)) != len(present_names):
            raise ValueError("algebra operation symbols must be distinct")
        if self.coefficient_domain not in {"natural", "integer", "mod2"}:
            raise ValueError("unsupported coefficient domain")
        if self.coefficient_domain == "integer" and self.neg is None:
            raise ValueError("integer coefficients require negation")
        if self.coefficient_domain != "integer" and self.neg is not None:
            raise ValueError("negation is reserved for integer coefficients")
        if self.coefficient_domain == "mod2" and self.right_cancellation is not None:
            raise ValueError("mod2 coefficients cannot carry natural cancellation")
        if self.coefficient_domain != "natural" and self.successor is not None:
            raise ValueError("successor is reserved for natural coefficients")
        if self.coefficient_domain != "mod2" and self.right_cancellation is None:
            raise ValueError("natural and integer contexts require right cancellation")
        if type(self.atoms) is not frozenset:
            raise TypeError("AlgebraContext.atoms must be a frozenset")
        for atom in self.atoms:
            if type(atom) is not Fun or atom.args:
                raise ValueError("declared generators must be exact nullary Fun terms")
            if atom in {self.zero, self.one} or atom.name in present_names:
                raise ValueError(f"generator collides with algebra symbol {atom.name!r}")
        if type(self.merge_rules) is not tuple:
            raise TypeError("AlgebraContext.merge_rules must be a tuple")
        _validate_cancellation(self.right_cancellation)
        if type(self.rewrite_budget) is not int or self.rewrite_budget <= 0:
            raise ValueError("rewrite_budget must be a positive exact int")


@dataclass(frozen=True, slots=True)
class RewriteCombinationContext:
    """Explicit rewrite policy for non-polynomial combination goals."""

    add: str
    mul: str
    rules: tuple[Rule, ...]
    right_cancellation: Pf
    budget: int = DEFAULT_BUDGET

    def __post_init__(self) -> None:
        if type(self.add) is not str or not self.add:
            raise ValueError("addition symbol must be a nonempty exact string")
        if type(self.mul) is not str or not self.mul:
            raise ValueError("multiplication symbol must be a nonempty exact string")
        if self.add == self.mul:
            raise ValueError("addition and multiplication symbols must be distinct")
        if type(self.rules) is not tuple:
            raise TypeError("rewrite rules must be a tuple")
        _validate_proof(self.right_cancellation, "right_cancellation")
        if type(self.budget) is not int or self.budget <= 0:
            raise ValueError("rewrite budget must be a positive exact int")


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


def _canonical_coefficient(coefficient: int, domain: CoefficientDomain) -> int:
    match domain:
        case "natural":
            if coefficient < 0:
                raise RingNormalizationError("natural coefficient became negative")
            return coefficient
        case "integer":
            return coefficient
        case "mod2":
            return coefficient & 1


def _polynomial(raw: dict[Monomial, int], domain: CoefficientDomain) -> Polynomial:
    terms = tuple(
        (monomial, canonical)
        for monomial, coefficient in sorted(
            raw.items(), key=lambda item: monomial_sort_key(item[0])
        )
        if (canonical := _canonical_coefficient(coefficient, domain)) != 0
    )
    return Polynomial(terms)


def _raw(poly: Polynomial) -> dict[Monomial, int]:
    return dict(poly.terms)


def _constant_one() -> Polynomial:
    return Polynomial((((), 1),))


def _atom(atom: Term) -> Polynomial:
    return Polynomial(((((atom, 1),), 1),))


def _add(left: Polynomial, right: Polynomial, domain: CoefficientDomain) -> Polynomial:
    out = _raw(left)
    for monomial, coefficient in right.terms:
        out[monomial] = out.get(monomial, 0) + coefficient
    return _polynomial(out, domain)


def _multiply_monomials(left: Monomial, right: Monomial) -> Monomial:
    powers: dict[Term, int] = {}
    for atom, exponent in (*left, *right):
        powers[atom] = powers.get(atom, 0) + exponent
    return tuple(sorted(powers.items(), key=lambda item: _atom_sort_key(item[0])))


def _mul(left: Polynomial, right: Polynomial, domain: CoefficientDomain) -> Polynomial:
    out: dict[Monomial, int] = {}
    for left_monomial, left_coefficient in left.terms:
        for right_monomial, right_coefficient in right.terms:
            monomial = _multiply_monomials(left_monomial, right_monomial)
            coefficient = left_coefficient * right_coefficient
            out[monomial] = out.get(monomial, 0) + coefficient
    return _polynomial(out, domain)


def _negate(polynomial: Polynomial, domain: CoefficientDomain) -> Polynomial:
    if domain != "integer":
        raise RingNormalizationError("negation requires integer coefficients")
    return _polynomial(
        {monomial: -coefficient for monomial, coefficient in polynomial.terms},
        domain,
    )


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
        if (
            coefficient == 0
            or _canonical_coefficient(coefficient, context.coefficient_domain)
            != coefficient
        ):
            raise RingNormalizationError(
                "polynomial contains a noncanonical coefficient"
            )
        factors = [atom for atom, exponent in monomial for _ in range(exponent)]
        term = _right_associated(context.mul, factors, context.one)
        if coefficient < 0:
            if context.neg is None:
                raise RingNormalizationError("negative coefficient requires negation")
            term = Fun(context.neg, (term,))
        monomial_terms.extend(term for _ in range(abs(coefficient)))
    return _right_associated(context.add, monomial_terms, context.zero)


def _node_children(term: object, context: AlgebraContext) -> tuple[Term, ...]:
    if type(term) is Var:
        return ()
    if type(term) is not Fun:
        raise RingNormalizationError(f"unsupported polynomial term type: {type(term).__name__}")
    if term == context.zero or term == context.one or term in context.atoms:
        return ()
    if term.name in {context.add, context.mul}:
        if len(term.args) != 2:
            raise RingNormalizationError(f"unsupported arity for {term.name!r}: {len(term.args)}")
        return term.args
    if context.neg is not None and term.name == context.neg:
        if len(term.args) != 1:
            raise RingNormalizationError(f"unsupported arity for {term.name!r}: {len(term.args)}")
        return term.args
    if context.successor is not None and term.name == context.successor:
        if len(term.args) != 1:
            raise RingNormalizationError(f"unsupported arity for {term.name!r}: {len(term.args)}")
        return term.args
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


def _merge_unary(
    original: Fun,
    child: Normalization,
    polynomial: Polynomial,
    context: AlgebraContext,
) -> Normalization:
    canonical_source = Fun(original.name, (child.term,))
    canonical_target = quote(polynomial, context)
    descend = Cong(original.name, (child.proof,))
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
        if node == context.zero:
            results[id(node)] = Normalization(Polynomial(()), node, Refl(node))
        elif node == context.one:
            results[id(node)] = Normalization(_constant_one(), node, Refl(node))
        elif node.name == context.add:
            left, right = (results[id(child)] for child in node.args)
            results[id(node)] = _merge(
                node,
                context.add,
                left,
                right,
                _add(
                    left.polynomial,
                    right.polynomial,
                    context.coefficient_domain,
                ),
                context,
            )
        elif node.name == context.mul:
            left, right = (results[id(child)] for child in node.args)
            results[id(node)] = _merge(
                node,
                context.mul,
                left,
                right,
                _mul(
                    left.polynomial,
                    right.polynomial,
                    context.coefficient_domain,
                ),
                context,
            )
        elif context.neg is not None and node.name == context.neg:
            child = results[id(node.args[0])]
            results[id(node)] = _merge_unary(
                node,
                child,
                _negate(child.polynomial, context.coefficient_domain),
                context,
            )
        elif context.successor is not None and node.name == context.successor:
            child = results[id(node.args[0])]
            results[id(node)] = _merge_unary(
                node,
                child,
                _add(
                    child.polynomial,
                    _constant_one(),
                    context.coefficient_domain,
                ),
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


def _require_combination_source(candidate: object) -> CombinationSource:
    if type(candidate) is not tuple:
        raise TypeError("each source must be an (Eq, Pf, coefficient) tuple")
    items = cast("tuple[object, ...]", candidate)
    if len(items) != 3:
        raise TypeError("each source must be an (Eq, Pf, coefficient) tuple")
    equation, proof, coefficient = items
    if type(equation) is not Eq or not isinstance(proof, Pf):
        raise TypeError("each source must contain an exact Eq and a Pf")
    if coefficient is not None and type(coefficient) not in {Var, Fun}:
        raise TypeError("a combination coefficient must be absent or an exact Term")
    return equation, proof, cast(Term | None, coefficient)


def instantiate_right_cancellation(
    theorem: Pf,
    lhs: Term,
    rhs: Term,
    suffix: Term,
) -> Pf:
    """Capture-safe ``x + z = y + z -> x = y`` instantiation."""
    return simultaneous_inst(theorem, {"x": lhs, "y": rhs, "z": suffix})


def _combine_sources(
    sources: tuple[CombinationSource, ...],
    add: str,
    mul: str,
) -> tuple[Term, Term, Pf]:
    """Scale and sum one nonempty, explicitly typed source tuple."""
    scaled: list[EquationProof] = []
    for candidate in sources:
        equation, proof, coefficient = _require_combination_source(candidate)
        if coefficient is not None:
            equation = Eq(
                Fun(mul, (equation.lhs, coefficient)),
                Fun(mul, (equation.rhs, coefficient)),
            )
            proof = Cong(mul, (proof, Refl(coefficient)))
        scaled.append((equation, proof))

    (first_equation, combined), *rest = scaled
    left_sum, right_sum = first_equation.lhs, first_equation.rhs
    for equation, proof in rest:
        combined = Cong(add, (combined, proof))
        left_sum = Fun(add, (left_sum, equation.lhs))
        right_sum = Fun(add, (right_sum, equation.rhs))
    return left_sum, right_sum, combined


def _shuffle_goal(goal: Eq, left_sum: Term, right_sum: Term, add: str) -> Eq:
    return Eq(
        Fun(add, (goal.lhs, right_sum)),
        Fun(add, (goal.rhs, left_sum)),
    )


def _finish_combination(
    goal: Eq,
    left_sum: Term,
    combined: Pf,
    shuffle: Pf,
    add: str,
    right_cancellation: Pf,
) -> Pf:
    on_sum = Cong(add, (Refl(goal.lhs), combined))
    return MP(
        instantiate_right_cancellation(
            right_cancellation,
            goal.lhs,
            goal.rhs,
            left_sum,
        ),
        Trans(on_sum, shuffle),
    )


def elaborate_combination(
    goal: object,
    sources: tuple[CombinationSource, ...],
    context: AlgebraContext | RewriteCombinationContext,
) -> Pf:
    """Prove an equality from a checked, optionally scaled equation sum."""
    if type(goal) is not Eq:
        raise RingNormalizationError("combination elaboration needs an exact Eq goal")
    if type(sources) is not tuple:
        raise TypeError("combination sources must be a tuple")
    exact_goal = goal
    if type(context) is RewriteCombinationContext:
        return _elaborate_rewrite_combination(
            exact_goal,
            sources,
            context,
        )
    if type(context) is not AlgebraContext:
        raise TypeError("combination context must be an exact supported context")
    algebra_context = context
    if not sources:
        return ring_eq(exact_goal, algebra_context)
    cancellation = algebra_context.right_cancellation
    if cancellation is None:
        raise RingNormalizationError("coefficient context has no right-cancellation recipe")

    left_sum, right_sum, combined = _combine_sources(
        sources,
        algebra_context.add,
        algebra_context.mul,
    )
    shuffle = ring_eq(
        _shuffle_goal(exact_goal, left_sum, right_sum, algebra_context.add),
        algebra_context,
    )
    return _finish_combination(
        exact_goal,
        left_sum,
        combined,
        shuffle,
        algebra_context.add,
        cancellation,
    )


def _elaborate_rewrite_combination(
    goal: Eq,
    sources: tuple[CombinationSource, ...],
    context: RewriteCombinationContext,
) -> Pf:
    """Handle recurrences outside the polynomial atom language.

    Primitive squaring still needs its own recursion axioms before its terms are
    polynomial. This keeps the shared scaled-sum/cancellation operation here
    without admitting ``sq(...)`` as an opaque polynomial atom.
    """
    if not sources:
        return prove_eq(goal, context.rules, context.budget)
    left_sum, right_sum, combined = _combine_sources(
        sources,
        context.add,
        context.mul,
    )
    shuffle = prove_eq(
        _shuffle_goal(goal, left_sum, right_sum, context.add),
        context.rules,
        context.budget,
    )
    return _finish_combination(
        goal,
        left_sum,
        combined,
        shuffle,
        context.add,
        context.right_cancellation,
    )


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
    if context.coefficient_domain != "mod2":
        raise RingNormalizationError("ideal-membership elaboration requires mod2")

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
    "CombinationSource",
    "CoefficientDomain",
    "EquationProof",
    "Monomial",
    "Normalization",
    "Polynomial",
    "RewriteCombinationContext",
    "RingNormalizationError",
    "elaborate_combination",
    "elaborate_ideal_membership",
    "monomial_sort_key",
    "normalize",
    "quote",
    "ring_eq",
]

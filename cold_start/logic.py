"""Conservative classical-connective sugar over implication and absurdity.

These constructors add no syntax nodes and no inference rules.  They merely use
the existing classical core (``Implies``/``Bottom`` and the checker's RAA rule) in
the standard encodings, keeping the trusted language small while making larger
first-order definitions legible.
"""

from __future__ import annotations

from .syntax import Formula, Implies, Not


def And(first: Formula, *rest: Formula) -> Formula:  # noqa: N802 - connective
    """Classical conjunction, right-associated for three or more operands."""
    operands = (first, *rest)
    result = operands[-1]
    for formula in reversed(operands[:-1]):
        result = Not(Implies(formula, Not(result)))
    return result


def Or(first: Formula, *rest: Formula) -> Formula:  # noqa: N802 - connective
    """Classical disjunction, right-associated for three or more operands."""
    operands = (first, *rest)
    result = operands[-1]
    for formula in reversed(operands[:-1]):
        result = Implies(Not(formula), result)
    return result


def Iff(left: Formula, right: Formula) -> Formula:  # noqa: N802 - connective
    """Biconditional as the conjunction of its two implications."""
    return And(Implies(left, right), Implies(right, left))

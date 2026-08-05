"""B1: multiplication interpreted in addition arithmetic with squaring."""

from __future__ import annotations

from .checker import Theory
from .interp import GraphSymbol, Interpretation
from .squaring import SQUARE_ARITHMETIC, square_product
from .squaring_proofs import square_product_total, square_product_unique

PRODUCT_FROM_SQUARE = GraphSymbol(
    "*",
    2,
    lambda args, result: square_product(args[0], args[1], result),
)

BARE_MULTIPLICATION_FROM_SQUARE = Theory(axioms=frozenset())


def squaring_interpretation() -> Interpretation:
    """The subtraction-free polarization graph, with both debts paid."""
    return Interpretation(
        name="multiplication-into-addition-and-square",
        source=BARE_MULTIPLICATION_FROM_SQUARE,
        target=SQUARE_ARITHMETIC,
        symbols=(PRODUCT_FROM_SQUARE,),
        payments=(
            ("totality:*", square_product_total()),
            ("uniqueness:*", square_product_unique()),
        ),
    )


__all__ = [
    "BARE_MULTIPLICATION_FROM_SQUARE",
    "PRODUCT_FROM_SQUARE",
    "square_product",
    "squaring_interpretation",
]

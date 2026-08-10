"""B1: multiplication interpreted in addition arithmetic with squaring."""

from __future__ import annotations

from .algebra import BARE_MULTIPLICATION
from .interp import GraphSymbol, Interpretation, ObligationKey
from .squaring import SQUARE_ARITHMETIC, square_product
from .squaring_proofs import square_product_total, square_product_unique

PRODUCT_FROM_SQUARE = GraphSymbol(
    "*",
    2,
    lambda args, result: square_product(args[0], args[1], result),
)

def squaring_interpretation() -> Interpretation:
    """The subtraction-free polarization graph, with both debts paid."""
    return Interpretation(
        name="multiplication-into-addition-and-square",
        source=BARE_MULTIPLICATION,
        target=SQUARE_ARITHMETIC,
        symbols=(PRODUCT_FROM_SQUARE,),
        payments=(
            (ObligationKey.totality("*"), square_product_total()),
            (ObligationKey.uniqueness("*"), square_product_unique()),
        ),
    )


__all__ = [
    "PRODUCT_FROM_SQUARE",
    "squaring_interpretation",
]

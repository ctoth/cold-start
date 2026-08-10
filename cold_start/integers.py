"""Abelian-group integers interpreted through Grothendieck pairs."""

from __future__ import annotations

from . import integer_pairs as pairs
from .algebra import AB_GROUP, ADD_ASSOC, ADD_COMM, ADD_NEG, ADD_ZERO
from .interp import ObligationKey
from .presburger import PRESBURGER
from .quotient import QuotientInterpretation, vec
from .vocabulary import ZERO, add


def integers_interpretation() -> QuotientInterpretation:
    """The abelian group of integers into Presburger, dimension two, all paid."""
    first, second = vec("x!0", 2), vec("x!1", 2)
    return QuotientInterpretation(
        name="integers-into-presburger-pairs",
        source=AB_GROUP,
        target=PRESBURGER,
        dim=2,
        equiv=pairs.int_eq,
        symbols=(
            pairs.ZERO_AS_DIAGONAL,
            pairs.ADD_COMPONENTWISE,
            pairs.NEG_AS_SWAP,
        ),
        payments=(
            (ObligationKey.equivalence("refl"), pairs.pay_equivalence_refl()),
            (ObligationKey.equivalence("sym"), pairs.pay_equivalence_sym()),
            (ObligationKey.equivalence("trans"), pairs.pay_equivalence_trans()),
            (
                ObligationKey.totality("0"),
                pairs.pay_totality(pairs.ZERO_AS_DIAGONAL, (ZERO, ZERO)),
            ),
            (
                ObligationKey.respect("0"),
                pairs.pay_respect(pairs.ZERO_AS_DIAGONAL, pairs.orient_zero),
            ),
            (
                ObligationKey.totality("+"),
                pairs.pay_totality(
                    pairs.ADD_COMPONENTWISE,
                    (add(first[0], second[0]), add(first[1], second[1])),
                ),
            ),
            (
                ObligationKey.respect("+"),
                pairs.pay_respect(pairs.ADD_COMPONENTWISE, pairs.orient_add),
            ),
            (
                ObligationKey.totality("neg"),
                pairs.pay_totality(pairs.NEG_AS_SWAP, (first[1], first[0])),
            ),
            (
                ObligationKey.respect("neg"),
                pairs.pay_respect(pairs.NEG_AS_SWAP, pairs.orient_neg),
            ),
            (ObligationKey.axiom(ADD_ZERO), pairs.pay_add_zero()),
            (ObligationKey.axiom(ADD_COMM), pairs.pay_add_comm()),
            (ObligationKey.axiom(ADD_ASSOC), pairs.pay_add_assoc()),
            (ObligationKey.axiom(ADD_NEG), pairs.pay_add_neg()),
        ),
    )


__all__ = ["integers_interpretation"]

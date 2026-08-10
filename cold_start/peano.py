"""Peano arithmetic: Presburger extended with multiplication.

PEANO adds one function symbol, `*`, and its two recursion axioms to
`cold_start.presburger.PRESBURGER` -- and nothing else. The induction rule,
zero, and successor are inherited unchanged. This is the line where number
theory stops being decidable: the addition fragment is complete (Presburger),
but once multiplication and induction coexist, Goedel's incompleteness applies.

A `Theory` is data (a frozen dataclass of axioms + induction structure), so
"Peano extends Presburger" is a value built with `dataclasses.replace`, not a
subclass -- the checker never dispatches on a theory's Python type.
"""

from __future__ import annotations

from dataclasses import replace

from . import vocabulary as _v
from .presburger import PRESBURGER, PRESBURGER_SIG
from .syntax import Eq, Formula, Var

# --- multiplication axioms (recursion on the second argument) -------------

MUL_ZERO_F: Formula = Eq(_v.mul(Var("x"), _v.ZERO), _v.ZERO)  # x * 0 = 0
MUL_SUCC_F: Formula = Eq(  # x * S y = (x * y) + x
    _v.mul(Var("x"), _v.S(Var("y"))),
    _v.add(_v.mul(Var("x"), Var("y")), Var("x")),
)


# Peano = Presburger + {the two multiplication axioms}. Same zero, successor, and
# induction rule; the only change is two more axioms and the `*` symbol they use.
PEANO_SIG = PRESBURGER_SIG.extend((("*", ("", ""), ""),))
PEANO = replace(
    PRESBURGER,
    axioms=PRESBURGER.axioms | {MUL_ZERO_F, MUL_SUCC_F},
    signature=PEANO_SIG,
)

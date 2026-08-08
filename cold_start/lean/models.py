"""Lean-side semantic models for cashing conditional exports out.

A registration is deliberately exact and closed: it names one concrete
``Theory`` object, interprets every function symbol in that theory, pays every
axiom, and supplies induction when the theory admits the ``Induct`` rule.
Structurally equal theories do not inherit registrations by accident.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..peano import MUL_SUCC_F, MUL_ZERO_F, PEANO
from ..presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    PRESBURGER,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
)
from ..squaring import SQUARE_ARITHMETIC, SQUARE_SUCC_F, SQUARE_ZERO_F
from ..syntax import Formula, Fun, children
from ..theory import Theory


def _theory_symbols(theory: Theory) -> dict[str, int]:
    roots: list[object] = [*theory.axioms]
    if theory.zero is not None:
        roots.append(theory.zero)
    symbols: dict[str, int] = {}
    seen: set[int] = set()
    stack = list(roots)
    while stack:
        node = stack.pop()
        identity = id(node)
        if identity in seen:
            continue
        seen.add(identity)
        if type(node) is Fun:
            arity = len(node.args)
            previous = symbols.setdefault(node.name, arity)
            if previous != arity:
                raise ValueError(f"theory symbol {node.name!r} has inconsistent arity")
        stack.extend(children(node))
    if theory.succ is not None:
        previous = symbols.setdefault(theory.succ, 1)
        if previous != 1:
            raise ValueError(f"induction successor {theory.succ!r} is not unary")
    return symbols


@dataclass(frozen=True, slots=True)
class LeanModel:
    """A complete Lean witness that one exact cold-start theory has a model."""

    name: str
    theory: Theory
    carrier: str
    symbols: tuple[tuple[str, str], ...]
    axiom_proofs: tuple[tuple[Formula, str], ...]
    induction_proof: str | None

    def __post_init__(self) -> None:
        if type(self.theory) is not Theory:
            raise TypeError(f"not an exact Theory: {self.theory!r}")
        if type(self.name) is not str or not self.name:
            raise ValueError("model name must be a nonempty string")
        if type(self.carrier) is not str or not self.carrier:
            raise ValueError("model carrier must be a nonempty Lean expression")

        symbol_names = [name for name, _lean in self.symbols]
        if len(symbol_names) != len(set(symbol_names)):
            raise ValueError("duplicate model symbol")
        expected_symbols = set(_theory_symbols(self.theory))
        if set(symbol_names) != expected_symbols:
            raise ValueError(
                "model symbols do not exactly cover theory symbols: "
                f"expected {sorted(expected_symbols)!r}, got {sorted(symbol_names)!r}"
            )

        paid_axioms = [formula for formula, _proof in self.axiom_proofs]
        if len(paid_axioms) != len(set(paid_axioms)):
            raise ValueError("duplicate model axiom proof")
        if set(paid_axioms) != set(self.theory.axioms):
            raise ValueError("axiom proofs do not exactly cover the theory axioms")

        has_induction = self.theory.zero is not None and self.theory.succ is not None
        if has_induction != (self.induction_proof is not None):
            raise ValueError("model induction proof does not match the theory")

    def symbol_map(self) -> dict[str, str]:
        return dict(self.symbols)

    def axiom_map(self) -> dict[Formula, str]:
        return dict(self.axiom_proofs)


_NAT_SYMBOLS = (
    ("0", "Nat.zero"),
    ("S", "Nat.succ"),
    ("+", "Nat.add"),
)
_NAT_PRESBURGER_AXIOMS = (
    (ADD_ZERO_F, "fun x => rfl"),
    (ADD_SUCC_F, "fun x y => rfl"),
    (SUCC_NEQ_ZERO, "fun x h => Nat.noConfusion h"),
    (SUCC_INJ, "fun x y h => Nat.noConfusion h (fun h' => h')"),
)
_NAT_INDUCTION = "fun P h0 hs n => Nat.rec (motive := P) h0 hs n"

NAT_PRESBURGER = LeanModel(
    name="nat-presburger",
    theory=PRESBURGER,
    carrier="Nat",
    symbols=_NAT_SYMBOLS,
    axiom_proofs=_NAT_PRESBURGER_AXIOMS,
    induction_proof=_NAT_INDUCTION,
)

NAT_PEANO = LeanModel(
    name="nat-peano",
    theory=PEANO,
    carrier="Nat",
    symbols=(*_NAT_SYMBOLS, ("*", "Nat.mul")),
    axiom_proofs=(
        *_NAT_PRESBURGER_AXIOMS,
        (MUL_ZERO_F, "fun x => rfl"),
        (MUL_SUCC_F, "fun x y => rfl"),
    ),
    induction_proof=_NAT_INDUCTION,
)

NAT_SQUARE = LeanModel(
    name="nat-addition-and-square",
    theory=SQUARE_ARITHMETIC,
    carrier="Nat",
    symbols=(*_NAT_SYMBOLS, ("sq", "(fun n => Nat.mul n n)")),
    axiom_proofs=(
        *_NAT_PRESBURGER_AXIOMS,
        (SQUARE_ZERO_F, "rfl"),
        (
            SQUARE_SUCC_F,
            """fun x => Eq.trans (Nat.succ_mul x (Nat.succ x))
  (Eq.trans
    (congrArg (fun t => Nat.add t (Nat.succ x)) (Nat.mul_succ x x))
    (Nat.add_assoc (Nat.mul x x) x (Nat.succ x)))""",
        ),
    ),
    induction_proof=_NAT_INDUCTION,
)

REGISTERED_MODELS = (NAT_PRESBURGER, NAT_PEANO, NAT_SQUARE)


def model_for(theory: object) -> LeanModel | None:
    """Return the model registered for this exact theory object, if any."""
    return next((model for model in REGISTERED_MODELS if model.theory is theory), None)


__all__ = [
    "LeanModel",
    "NAT_PEANO",
    "NAT_PRESBURGER",
    "NAT_SQUARE",
    "REGISTERED_MODELS",
    "model_for",
]

"""One evaluator for every model. The five test-file evaluators (eval_*/interp_*
/ev_*) were the same tree-walk with a per-model interpretation table; this folds
them into a single `evaluate(node, model, env, denv)`."""

from __future__ import annotations

from semantics import Model, evaluate

from cold_start.syntax import Eq, Fun, Var, exists, forall


def test_evaluate_terms_formulas_and_quantifiers():
    # Z/3 with zero `z`, successor `s`, addition `+`; carrier {0,1,2} for ∀/∃.
    m = Model(
        "Z/3",
        interp={"z": lambda: 0, "s": lambda x: (x + 1) % 3, "+": lambda a, b: (a + b) % 3},
        carriers={"": (0, 1, 2)},
    )
    z = Fun("z", ())
    assert evaluate(Fun("s", (z,)), m, {}) == 1  # term: s(z) = 1
    assert evaluate(Eq(Fun("+", (z, z)), z), m, {})  # 0 + 0 = 0
    assert evaluate(forall("x", "", Eq(Var("x"), Var("x"))), m, {})  # ∀x. x = x
    assert not evaluate(forall("x", "", Eq(Var("x"), z)), m, {})  # ∀x. x = 0 (false)
    assert evaluate(exists("x", "", Eq(Var("x"), Fun("s", (z,)))), m, {})  # ∃x. x = 1
    # free variable comes from env; bound variable from the de Bruijn stack
    assert evaluate(Var("a"), m, {"a": 2}) == 2

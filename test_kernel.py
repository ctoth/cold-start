"""Tests. Run standalone (`python test_kernel.py`) or under pytest.

These are the non-visual proof that the kernel is sound-by-construction and
that the first real theorem actually goes through.
"""

from __future__ import annotations

import kernel as k
from kernel import Eq, Implies, Var
from peano import ADD_SUCC, ADD_ZERO, S, ZERO, add, numeral
from proofs import left_identity_of_addition


# --- the trust boundary holds --------------------------------------------


def test_theorem_cannot_be_forged():
    """Constructing a Theorem outside the kernel must fail."""
    try:
        k.Theorem(frozenset(), Eq(ZERO, S(ZERO)))
    except PermissionError:
        return
    raise AssertionError("forged a Theorem without the kernel token!")


# --- individual inference rules ------------------------------------------


def test_refl():
    assert refl_concl(k.refl(Var("a"))) == Eq(Var("a"), Var("a"))


def test_sym_and_trans():
    ab = k.axiom(Eq(Var("a"), Var("b")))
    bc = k.axiom(Eq(Var("b"), Var("c")))
    assert k.sym(ab).concl == Eq(Var("b"), Var("a"))
    assert k.trans(ab, bc).concl == Eq(Var("a"), Var("c"))


def test_trans_rejects_mismatch():
    ab = k.axiom(Eq(Var("a"), Var("b")))
    cd = k.axiom(Eq(Var("c"), Var("d")))
    try:
        k.trans(ab, cd)
    except ValueError:
        return
    raise AssertionError("trans accepted a broken chain")


def test_cong():
    eq = k.axiom(Eq(Var("a"), Var("b")))
    assert k.cong("S", [eq]).concl == Eq(S(Var("a")), S(Var("b")))


def test_mp_and_discharge():
    a = Eq(Var("a"), Var("a"))
    b = Eq(Var("b"), Var("b"))
    imp = k.axiom(Implies(a, b))
    fact = k.axiom(a)
    assert k.mp(imp, fact).concl == b

    # assume a, conclude b via imp, then discharge a -> (a -> b) with no hyps
    assumed = k.assume(a)
    derived = k.mp(imp, assumed)
    assert a in derived.hyps
    discharged = k.implies_intro(a, derived)
    assert discharged.hyps == frozenset()
    assert discharged.concl == Implies(a, b)


def test_mp_rejects_wrong_antecedent():
    a = Eq(Var("a"), Var("a"))
    b = Eq(Var("b"), Var("b"))
    imp = k.axiom(Implies(a, b))
    wrong = k.axiom(b)
    try:
        k.mp(imp, wrong)
    except ValueError:
        return
    raise AssertionError("mp accepted the wrong antecedent")


def test_instantiate_guards_hypotheses():
    # x is free in the hypothesis, so instantiating it must be refused
    thm = k.assume(Eq(Var("x"), Var("x")))
    try:
        k.instantiate(thm, "x", ZERO)
    except ValueError:
        return
    raise AssertionError("instantiate clobbered a variable bound by a hypothesis")


# --- computing with the addition axioms ----------------------------------


def test_addition_computes():
    """2 + 1 = 3 should be derivable purely from the recursion axioms."""
    # 2 + S(0) = S(2 + 0)        (ADD_SUCC at x:=2, y:=0)
    two, zero = numeral(2), ZERO
    succ_step = k.instantiate(k.instantiate(ADD_SUCC, "x", two), "y", zero)
    # 2 + 0 = 2                  (ADD_ZERO at x:=2)
    base = k.instantiate(ADD_ZERO, "x", two)
    # S(2 + 0) = S(2)
    cong = k.cong("S", [base])
    # 2 + S(0) = S(2)  i.e.  2 + 1 = 3
    result = k.trans(succ_step, cong)
    assert result.concl == Eq(add(two, numeral(1)), numeral(3))
    assert result.hyps == frozenset()


# --- the headline theorem ------------------------------------------------


def test_left_identity_of_addition():
    thm = left_identity_of_addition()
    n = Var("n")
    assert thm.concl == Eq(add(ZERO, n), n)  #  0 + n = n
    assert thm.hyps == frozenset()  # proved outright, no leftover assumptions


# --- tiny helper ----------------------------------------------------------


def refl_concl(thm: k.Theorem) -> object:
    return thm.concl


def _main() -> int:
    tests = [v for name, v in sorted(globals().items()) if name.startswith("test_")]
    failures = 0
    for t in tests:
        try:
            t()
            print(f"PASS  {t.__name__}")
        except Exception as exc:  # noqa: BLE001 -- test harness
            failures += 1
            print(f"FAIL  {t.__name__}: {exc!r}")
    print(f"\n{len(tests) - failures}/{len(tests)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(_main())

"""The test suite. Every claim the checker makes about itself lives here as a
regression test -- especially the soundness attacks, so a reopened hole fails
loudly. Run under pytest, or standalone: ``python test_checker.py``.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys

import proof as P
from checker import Sequent, check, validate_proof
from peano import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    PEANO,
    ZERO,
    S,
    add,
    induction,
    is_induction_instance,
)
from proof import from_json, to_json
from proofs import left_identity_proof
from syntax import Eq, Formula, Fun, Implies, Term, Var, validate_term

HERE = os.path.dirname(os.path.abspath(__file__))


# --- the headline theorem -------------------------------------------------


def test_left_identity_of_addition():
    seq = check(left_identity_proof(), PEANO)
    n = Var("n")
    assert seq.concl == Eq(add(ZERO, n), n)  # 0 + n = n
    assert seq.hyps == frozenset()  # proved outright, no leftover assumptions


def test_addition_computes():
    """2 + 1 = 3 from the recursion axioms alone."""
    two = S(S(ZERO))
    # 2 + S(0) = S(2 + 0)
    unfold = P.Inst(P.Inst(P.Axiom(ADD_SUCC_F), "x", two), "y", ZERO)
    # 2 + 0 = 2  ->  S(2 + 0) = S(2)
    base = P.Inst(P.Axiom(ADD_ZERO_F), "x", two)
    proof = P.Trans(unfold, P.Cong("S", (base,)))
    seq = check(proof, PEANO)
    assert seq.concl == Eq(add(two, S(ZERO)), S(S(S(ZERO))))  # 2 + 1 = 3
    assert seq.hyps == frozenset()


# --- SOUNDNESS ATTACKS (regression sentinels) -----------------------------


class _EvilTerm(Term):
    """A Term subclass whose __eq__ lies -- the classic way to make `==` derive
    a falsehood. Must be rejected as non-canonical."""

    __slots__ = ()

    def __eq__(self, other):
        return True

    def __hash__(self):
        return 0


class _EvilStr(str):
    """A str subclass that lies on ==; could poison Var/Fun name comparison."""

    def __eq__(self, other):
        return True

    def __hash__(self):
        return 0


class _EvilFormula(Formula):
    """A Formula subclass that hashes into a target's bucket and claims equality
    to it -- the way to make frozenset subtraction in ImpIntro discharge a
    hypothesis that was never proved. Must be rejected as non-canonical."""

    __slots__ = ("target",)

    def __init__(self, target):
        self.target = target

    def __eq__(self, other):
        return True

    def __hash__(self):
        return hash(self.target)


def test_lying_formula_cannot_discharge_unproved_hypothesis():
    # Genuinely depend on h, then try to discharge a DIFFERENT (malicious)
    # formula that compares/hashes equal to h, which would strip h from the
    # hypotheses and yield `|- evil -> h` with no real assumptions.
    h = Eq(add(ZERO, Var("n")), Var("n"))
    evil = _EvilFormula(h)
    # Sanity: the threat is real -- evil genuinely strips h from a hyp set, so
    # this sentinel guards the actual discharge mechanism, not a vacuous reject.
    assert frozenset({h}) - {evil} == frozenset()
    attack = P.ImpIntro(evil, P.Assume(h))  # would remove h via hyps - {evil}
    try:
        check(attack, PEANO)
    except TypeError:
        return
    raise AssertionError("lying formula discharged an unproved hypothesis")


def test_lying_formula_in_assume_rejected():
    h = Eq(ZERO, ZERO)
    try:
        check(P.Assume(_EvilFormula(h)), PEANO)
    except TypeError:
        return
    raise AssertionError("lying formula accepted as a hypothesis")


def test_lying_term_cannot_derive_falsehood():
    # Trans(Refl(S0), Trans(Refl(Evil), Refl(0)))  once derived  S(0) = 0.
    attack = P.Trans(P.Refl(S(ZERO)), P.Trans(P.Refl(_EvilTerm()), P.Refl(ZERO)))
    try:
        check(attack, PEANO)
    except TypeError:
        return
    raise AssertionError("lying Term __eq__ derived a falsehood")


def test_lying_str_name_rejected():
    attack = P.Refl(Fun("S", (Var(_EvilStr("x")),)))
    try:
        check(attack, PEANO)
    except TypeError:
        return
    raise AssertionError("lying str name was accepted")


def test_validate_term_rejects_foreign_subclass():
    try:
        validate_term(_EvilTerm())
    except TypeError:
        return
    raise AssertionError("validate_term accepted a Term subclass")


def test_non_proof_is_rejected():
    for junk in (42, "nope", None, Eq(ZERO, ZERO)):
        try:
            check(junk, PEANO)
        except TypeError:
            continue
        raise AssertionError(f"check accepted a non-proof: {junk!r}")


def test_sequent_is_not_authority():
    """A Sequent is plain data -- you can build a false one freely. Authority is
    check() returning it, never the object's existence."""
    bogus = Sequent(frozenset(), Eq(ZERO, S(ZERO)))  # |- 0 = 1, fabricated
    assert bogus.concl == Eq(ZERO, S(ZERO))
    # ...but no proof term derives it from PEANO:
    try:
        check(P.Axiom(Eq(ZERO, S(ZERO))), PEANO)
    except ValueError:
        return
    raise AssertionError("checker accepted 0 = 1 as an axiom")


# --- per-rule side conditions ---------------------------------------------


def test_unknown_axiom_rejected():
    try:
        check(P.Axiom(Eq(ZERO, S(ZERO))), PEANO)
    except ValueError:
        return
    raise AssertionError("non-axiom accepted")


def test_mp_antecedent_mismatch_rejected():
    a, b = Eq(Var("a"), Var("a")), Eq(Var("b"), Var("b"))
    imp = P.ImpIntro(a, P.Assume(b))  # b |- a -> b   (derivable, no axiom needed)
    wrong = P.Refl(Var("c"))  # |- c = c, which is not `a`
    try:
        check(P.MP(imp, wrong), PEANO)
    except ValueError:
        return
    raise AssertionError("mp accepted a mismatched antecedent")


def test_trans_middle_mismatch_rejected():
    bad = P.Trans(P.Refl(ZERO), P.Refl(S(ZERO)))  # 0=0 then 1=1: 0 != 1
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("trans accepted a broken chain")


def test_instantiate_guards_hypotheses():
    # assume x = x, then try to instantiate x -- x is free in the hypothesis
    bad = P.Inst(P.Assume(Eq(Var("x"), Var("x"))), "x", ZERO)
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("instantiate clobbered a hypothesis variable")


def test_implies_intro_discharges():
    p = Eq(add(ZERO, Var("n")), Var("n"))
    seq = check(P.ImpIntro(p, P.Assume(p)), PEANO)  # |- p -> p
    assert seq.concl == Implies(p, p)
    assert seq.hyps == frozenset()


# --- the induction schema recognizer --------------------------------------


def test_induction_recognizer_accepts_genuine_instance():
    n = Var("n")
    pred = Eq(add(ZERO, n), n)
    pred0 = Eq(add(ZERO, ZERO), ZERO)
    predS = Eq(add(ZERO, S(n)), S(n))
    schema = Implies(pred0, Implies(Implies(pred, predS), pred))
    assert is_induction_instance(schema)


def test_induction_recognizer_rejects_bogus():
    assert not is_induction_instance(Eq(ZERO, S(ZERO)))
    assert not is_induction_instance(Implies(Eq(ZERO, ZERO), Eq(ZERO, S(ZERO))))


def test_induction_builder_roundtrips_through_checker():
    n = Var("n")
    pred = Eq(add(ZERO, n), n)
    base = P.Inst(P.Axiom(ADD_ZERO_F), "x", ZERO)
    ih = P.Assume(pred)
    unfold = P.Inst(P.Inst(P.Axiom(ADD_SUCC_F), "x", ZERO), "y", n)
    step = P.ImpIntro(pred, P.Trans(unfold, P.Cong("S", (ih,))))
    seq = check(induction("n", pred, base, step), PEANO)
    assert seq.concl == pred and seq.hyps == frozenset()


# --- serialization & cross-process verification ---------------------------


def test_serialization_roundtrips():
    pf = left_identity_proof()
    again = from_json(to_json(pf))
    assert again == pf  # structural equality survives JSON
    assert check(again, PEANO).concl == check(pf, PEANO).concl


def test_validate_proof_runs_on_wellformed():
    validate_proof(left_identity_proof())  # must not raise


def _run_verify(stdin_text: str):
    return subprocess.run(
        [sys.executable, "verify.py"],
        input=stdin_text,
        capture_output=True,
        text=True,
        cwd=HERE,
    )


def test_cross_process_verifies_valid_proof():
    """The De Bruijn payoff: a fresh process trusting only checker.py + the
    theory re-derives the proof from inert JSON."""
    proof_json = to_json(left_identity_proof())
    result = _run_verify(proof_json)
    assert result.returncode == 0, result.stderr
    assert "VERIFIED" in result.stdout
    assert "+(0, n) = n" in result.stdout


def test_cross_process_rejects_forged_axiom():
    forged = json.dumps(
        {"k": "Axiom", "formula": {
            "k": "Eq",
            "lhs": {"k": "Fun", "name": "0", "args": []},
            "rhs": {"k": "Fun", "name": "S", "args": [{"k": "Fun", "name": "0", "args": []}]},
        }}
    )  # claims |- 0 = 1
    result = _run_verify(forged)
    assert result.returncode == 1
    assert "REJECTED" in result.stderr


# --- standalone runner ----------------------------------------------------


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

"""The test suite. Every claim the checker makes about itself lives here as a
regression test -- especially the soundness attacks, so a reopened hole fails
loudly. Run under pytest, or standalone: ``python test_checker.py``.
"""

from __future__ import annotations

import os
import subprocess
import sys

import cold_start.proof as P
from cold_start.checker import check, validate_proof
from cold_start.codec import decode_proof, encode_proof
from cold_start.peano import PEANO
from cold_start.presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    ZERO,
    S,
    add,
)
from cold_start.presburger_proofs import left_identity_proof
from cold_start.robinson_proofs import robinson_add_proof
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Formula, Fun, Implies, Term, Var, validate

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(HERE)  # `cold_start` package lives at the repo root, not in tests/


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


def test_term_args_snapshotted_against_caller_mutation():
    # The aliasing attack: build a term from a mutable list, use it, then mutate
    # the list. A term that aliased the list would change retroactively.
    args: list[Term] = [Var("x")]
    term = Fun("S", args)  # pyright: ignore[reportArgumentType]  -- a list is the attack
    proof = P.Refl(term)
    before = check(proof, PEANO).concl
    args[0] = Fun("0", ())  # mutate the caller's list AFTER proving
    after = check(proof, PEANO).concl
    expected = Eq(Fun("S", (Var("x"),)), Fun("S", (Var("x"),)))
    assert term.args == (Var("x"),)  # snapshotted at construction, not aliased
    assert before == after == expected  # the proof did not change under us


def test_forged_fun_with_mutable_args_rejected():
    # Bypass __post_init__ via object.__new__ to smuggle in a live list, and
    # confirm the checker's validation is an independent backstop.
    bad = object.__new__(Fun)
    object.__setattr__(bad, "name", "f")
    object.__setattr__(bad, "args", [Var("x")])  # mutable, never snapshotted
    try:
        check(P.Refl(bad), PEANO)
    except TypeError:
        return
    raise AssertionError("checker accepted a Fun carrying a mutable list")


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


def test_validate_rejects_foreign_subclass():
    try:
        validate(_EvilTerm())
    except TypeError:
        return
    raise AssertionError("validate accepted a Term subclass")


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


def test_induction_schema_not_exploitable_to_derive_falsehood():
    """The induction principle must not let us derive 0 = 1. With induction
    encoded as a free-variable axiom `P[0] -> ((P -> P[Sx]) -> P)`, taking
    P(n) := n=0 and instantiating x:=1 yields a *false* axiom instance whose
    step (1=0)->(2=0) is provable, extracting |- 1=0. This must be rejected."""
    x = Var("x")
    pred = Eq(x, ZERO)
    one, two = S(ZERO), S(S(ZERO))
    schema = Implies(Eq(ZERO, ZERO), Implies(Implies(pred, Eq(S(x), ZERO)), pred))
    inst = P.Inst(P.Axiom(schema), "x", one)  # (0=0) -> (((1=0)->(2=0)) -> (1=0))
    # prove the (closed) step (1=0)->(2=0):  from 1=0, cong S gives 2=1, trans 2=0
    assume1 = P.Assume(Eq(one, ZERO))
    step_proof = P.ImpIntro(Eq(one, ZERO), P.Trans(P.Cong("S", (assume1,)), assume1))
    exploit = P.MP(P.MP(inst, P.Refl(ZERO)), step_proof)
    try:
        seq = check(exploit, PEANO)
    except (ValueError, TypeError):
        return  # rejected -- sound
    assert seq.concl != Eq(one, ZERO), f"SOUNDNESS BUG: derived {seq}"
    assert two  # keep the binding referenced


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


# --- the induction rule ----------------------------------------------------


def _left_identity_base_and_step():
    """Genuine base/step proofs for  0 + n = n  by induction on n."""
    n = Var("n")
    pred = Eq(add(ZERO, n), n)
    base = P.Inst(P.Axiom(ADD_ZERO_F), "x", ZERO)  # 0 + 0 = 0
    ih = P.Assume(pred)
    unfold = P.Inst(P.Inst(P.Axiom(ADD_SUCC_F), "x", ZERO), "y", n)
    step = P.ImpIntro(pred, P.Trans(unfold, P.Cong("S", (ih,))))
    return pred, base, step


def test_induction_rule_proves_left_identity():
    pred, base, step = _left_identity_base_and_step()
    seq = check(P.Induct("n", pred, base, step), PEANO)
    assert seq.concl == pred and seq.hyps == frozenset()


def test_induction_rejects_wrong_base():
    pred, _base, step = _left_identity_base_and_step()
    wrong_base = P.Refl(ZERO)  # proves 0=0, not pred[n:=0] which is 0+0=0
    try:
        check(P.Induct("n", pred, wrong_base, step), PEANO)
    except ValueError:
        return
    raise AssertionError("induction accepted a base that doesn't prove pred[0]")


def test_induction_rejects_wrong_step():
    pred, base, _step = _left_identity_base_and_step()
    wrong_step = P.Refl(ZERO)  # not an implication of the right shape
    try:
        check(P.Induct("n", pred, base, wrong_step), PEANO)
    except ValueError:
        return
    raise AssertionError("induction accepted a malformed step")


def test_induction_rejects_var_free_in_hypothesis():
    # base/step that leave the induction variable free in an undischarged
    # hypothesis must be refused -- that is the side condition that keeps the
    # step universally quantified and blocks the 1=0 exploit.
    n = Var("n")
    pred = Eq(add(ZERO, n), n)
    leaky_base = P.Assume(Eq(n, n))  # hypothesis n=n keeps n free, undischarged
    _, _, step = _left_identity_base_and_step()
    try:
        check(P.Induct("n", pred, leaky_base, step), PEANO)
    except ValueError:
        return
    raise AssertionError("induction allowed its variable free in a hypothesis")


# --- serialization & cross-process verification ---------------------------


def test_serialization_roundtrips():
    pf = left_identity_proof()
    again = decode_proof(encode_proof(pf))
    assert again == pf  # structural equality survives serialization
    assert check(again, PEANO).concl == check(pf, PEANO).concl


def test_validate_proof_runs_on_wellformed():
    validate_proof(left_identity_proof())  # must not raise


def _run_verify(stdin_bytes: bytes, *args: str):
    return subprocess.run(
        [sys.executable, "-m", "cold_start.verify", *args],
        input=stdin_bytes,
        capture_output=True,
        cwd=REPO_ROOT,
    )


def test_cross_process_verifies_valid_proof():
    """The De Bruijn payoff: a fresh process trusting only checker.py + the
    theory re-derives the proof from inert bytes."""
    proof_bytes = encode_proof(left_identity_proof())
    result = _run_verify(proof_bytes)
    assert result.returncode == 0, result.stderr
    out = result.stdout.decode()
    assert "VERIFIED" in out
    assert "+(0, n) = n" in out


def test_cross_process_verifies_under_presburger():
    # `0 + n = n` cites only the addition axioms, so it checks under the
    # addition-only fragment too -- if the verifier knows that theory exists.
    result = _run_verify(encode_proof(left_identity_proof()), "--theory", "presburger")
    assert result.returncode == 0, result.stderr
    assert "VERIFIED [presburger]" in result.stdout.decode()


def test_cross_process_verifies_file_with_explicit_theory(tmp_path):
    proof_path = tmp_path / "left-identity.hmb"
    proof_path.write_bytes(encode_proof(left_identity_proof()))

    result = _run_verify(b"", str(proof_path), "--theory", "presburger")

    assert result.returncode == 0, result.stderr
    assert "VERIFIED [presburger]" in result.stdout.decode()


def test_cross_process_verifies_under_robinson():
    # The (1, S, ·) theory with `+` eliminated: a fresh process re-derives
    # 2 + 3 = 5 from Robinson's own axioms, as a bridge with no `+` symbol.
    proof_bytes = encode_proof(robinson_add_proof(2, 3))
    result = _run_verify(proof_bytes, "--theory", "robinson")
    assert result.returncode == 0, result.stderr
    assert "VERIFIED [robinson]" in result.stdout.decode()


def test_cross_process_rejects_unknown_theory():
    result = _run_verify(encode_proof(left_identity_proof()), "--theory", "nonesuch")
    assert result.returncode == 2
    assert "unknown theory" in result.stderr.decode()


def test_cross_process_rejects_missing_theory_value():
    result = _run_verify(b"", "--theory")
    assert result.returncode == 2
    assert "error:" in result.stderr.decode()


def test_cross_process_rejects_duplicate_paths():
    result = _run_verify(b"", "first.hmb", "second.hmb")
    assert result.returncode == 2
    assert "error:" in result.stderr.decode()


def test_cross_process_reports_a_missing_file(tmp_path):
    result = _run_verify(b"", str(tmp_path / "missing.hmb"))
    assert result.returncode == 2
    assert "cannot read" in result.stderr.decode()


def test_cross_process_reports_an_unreadable_path(tmp_path):
    result = _run_verify(b"", str(tmp_path))
    assert result.returncode == 2
    assert "cannot read" in result.stderr.decode()


def test_cross_process_rejects_malformed_bytes():
    result = _run_verify(b"not a Hamblin stream")
    assert result.returncode == 1
    assert "REJECTED" in result.stderr.decode()


def test_cross_process_rejects_forged_axiom():
    # An adversary emits a well-formed proof term that simply claims a false axiom
    # (0 = S(0), i.e. 0 = 1). The checker re-derives and rejects: not an axiom.
    forged = encode_proof(P.Axiom(Eq(Fun("0", ()), Fun("S", (Fun("0", ()),)))))
    result = _run_verify(forged)
    assert result.returncode == 1
    assert "REJECTED" in result.stderr.decode()


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

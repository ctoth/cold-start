"""Canonical arithmetic vocabulary ownership and declared Robinson language."""

from cold_start.robinson import ONE, ROBINSON_SIG
from cold_start.syntax import Fun
from cold_start.vocabulary import ONE as CANONICAL_ONE


def test_robinson_uses_a_primitive_one_not_hidden_zero() -> None:
    assert ONE is CANONICAL_ONE
    assert ONE == Fun("1", ())
    assert ROBINSON_SIG.rank("1") == ((), "")
    assert ROBINSON_SIG.rank("0") is None

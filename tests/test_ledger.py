"""The bridge ledger: every interpretation artifact, measured in one place.

The campaign metric -- how small is the bridge, what toll was paid, what
debts stay open -- must be one command, not an archaeology of per-module
`__main__` blocks. The ledger enumerates every registered artifact, verifies
each through the trusted checker, and renders one honest table."""

from __future__ import annotations

from cold_start.interp import BridgeReport
from cold_start.ledger import ARTIFACTS, format_ledger, ledger


def test_ledger_covers_every_artifact():
    reports = ledger()
    assert len(reports) == len(ARTIFACTS)
    names = [r.name for r in reports]
    assert len(set(names)) == len(names)
    assert "presburger-into-skolem-powers-of-two" in names
    assert "robinson-1949-s2-into-peano-positives" in names
    assert all(isinstance(r, BridgeReport) for r in reports)


def test_ledger_orders_paid_before_open():
    """Fully paid bridges list first; conjectures with open debts follow."""
    reports = ledger()
    seen_open = False
    for report in reports:
        if not report.complete:
            seen_open = True
        else:
            assert not seen_open, f"{report.name} is complete but sorts after an open bridge"


def test_format_ledger_is_one_honest_table():
    reports = ledger()
    text = format_ledger(reports)
    for report in reports:
        assert report.name in text
    assert "bridge" in text
    assert "toll" in text
    assert "open" in text
    assert "totality:+" in text  # the Skolem debt is visible, not hidden
    line_count = len(text.strip().splitlines())
    assert line_count >= len(reports) + 1  # a header plus one row each

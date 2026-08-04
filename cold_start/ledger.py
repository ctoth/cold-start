"""The bridge ledger: every interpretation artifact, measured in one command.

    uv run python -m cold_start.ledger

The campaign's question -- how far did each bridge reach, how small is it,
what toll was paid, what debts remain -- deserves a single answer surface.
Each registered artifact is rebuilt and driven through `interp.verify`, so
the numbers printed here are re-derived by the trusted checker on every run,
never quoted from documentation. Fully paid bridges sort first; a bridge
with open obligations is a conjecture with a ledger, and its debts are the
most important column.

Untrusted, like every prover module: this file only totals what `check`
accepts.
"""

from __future__ import annotations

from collections.abc import Callable

from .bridges import robinson_interpretation, robinson_into_peano
from .divisibility_bridges import (
    divisibility_into_peano,
    robinson_product_interpretation,
)
from .integers import integers_interpretation
from .interp import BridgeReport, Interpretation, verify
from .quotient import QuotientInterpretation
from .quotient import verify as verify_quotient
from .skolem import skolem_interpretation

Artifact = Interpretation | QuotientInterpretation

ARTIFACTS: tuple[Callable[[], Artifact], ...] = (
    robinson_interpretation,
    robinson_into_peano,
    divisibility_into_peano,
    robinson_product_interpretation,
    skolem_interpretation,
    integers_interpretation,
)
"""Every interpretation artifact the repository has landed."""


def _verify(artifact: Artifact) -> BridgeReport:
    if isinstance(artifact, QuotientInterpretation):
        return verify_quotient(artifact)
    return verify(artifact)


def ledger() -> tuple[BridgeReport, ...]:
    """Verify every artifact; complete bridges first, then by name."""
    reports = [_verify(build()) for build in ARTIFACTS]
    reports.sort(key=lambda r: (not r.complete, r.name))
    return tuple(reports)


def format_ledger(reports: tuple[BridgeReport, ...]) -> str:
    """One aligned table: name, bridge size, toll, paid count, open debts."""
    rows = [("artifact", "bridge", "toll", "paid", "open")]
    for r in reports:
        rows.append(
            (
                r.name,
                str(r.bridge_size),
                str(r.total_toll),
                f"{sum(s.paid for s in r.statuses)}/{len(r.statuses)}",
                ", ".join(r.open_labels()) or "-",
            )
        )
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    lines = ["  ".join(cell.ljust(width) for cell, width in zip(rows[0], widths, strict=True))]
    for row in rows[1:]:
        lines.append("  ".join(cell.ljust(width) for cell, width in zip(row, widths, strict=True)))
    return "\n".join(lines)


if __name__ == "__main__":
    print(format_ledger(ledger()))


__all__ = ["ARTIFACTS", "format_ledger", "ledger"]

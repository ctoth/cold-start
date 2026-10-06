"""Deterministic trusted work accounting for one checker invocation.

A counter is named once, in `CumulativeName` or `MaximumName`. `WorkLimits`
holds its `max_<name>` ceiling and `WorkUsage` its final value; everything else
here is derived from those names.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from typing import Literal, cast, get_args


class WorkLimitError(ValueError):
    """One named deterministic checker-work ceiling was exceeded."""


CumulativeName = Literal[
    "proof_nodes",
    "proof_edges",
    "syntax_nodes",
    "syntax_edges",
    "hypothesis_elements",
    "syntax_visits",
    "syntax_rebuilds",
    "sort_steps",
    "sequent_steps",
    "string_bytes",
]
MaximumName = Literal[
    "single_term_nodes",
    "single_formula_nodes",
    "derived_hypotheses",
    "derived_sequent_nodes",
]


@dataclass(frozen=True, slots=True)
class WorkLimits:
    max_proof_nodes: int
    max_proof_edges: int
    max_syntax_nodes: int
    max_syntax_edges: int
    max_hypothesis_elements: int
    max_syntax_visits: int
    max_syntax_rebuilds: int
    max_sort_steps: int
    max_sequent_steps: int
    max_string_bytes: int
    max_single_term_nodes: int
    max_single_formula_nodes: int
    max_derived_hypotheses: int
    max_derived_sequent_nodes: int

    def __post_init__(self) -> None:
        for name, value in _ceilings(self).items():
            if type(value) is not int or value <= 0:
                raise ValueError(f"max_{name} must be a positive exact int")


def _ceilings(limits: WorkLimits) -> dict[str, int]:
    """Each counter's ceiling, keyed by the counter's own name."""
    return {
        field.name.removeprefix("max_"): cast(int, getattr(limits, field.name))
        for field in fields(limits)
    }


DEFAULT_WORK_LIMITS = WorkLimits(
    max_proof_nodes=1_000_000,
    max_proof_edges=4_000_000,
    max_syntax_nodes=2_000_000,
    max_syntax_edges=8_000_000,
    max_hypothesis_elements=20_000_000,
    max_syntax_visits=100_000_000,
    max_syntax_rebuilds=20_000_000,
    max_sort_steps=100_000_000,
    max_sequent_steps=100_000_000,
    max_string_bytes=1_000_000,
    max_single_term_nodes=2_000_000,
    max_single_formula_nodes=4_000_000,
    max_derived_hypotheses=100_000,
    max_derived_sequent_nodes=10_000_000,
)


@dataclass(frozen=True, slots=True)
class WorkUsage:
    proof_nodes: int
    proof_edges: int
    syntax_nodes: int
    syntax_edges: int
    hypothesis_elements: int
    syntax_visits: int
    syntax_rebuilds: int
    sort_steps: int
    sequent_steps: int
    string_bytes: int
    single_term_nodes: int
    single_formula_nodes: int
    derived_hypotheses: int
    derived_sequent_nodes: int


class WorkMeter:
    """Mutable per-call meter; no identities or counters survive a check."""

    __slots__ = (
        "_ceilings",
        "_free_var_sorts",
        "_peaks",
        "_syntax_identities",
        "_syntax_sizes",
        "_term_sorts",
        "_totals",
    )

    def __init__(self, limits: WorkLimits = DEFAULT_WORK_LIMITS) -> None:
        if type(limits) is not WorkLimits:
            raise TypeError("work limits must be exact WorkLimits")
        self._ceilings = _ceilings(limits)
        self._totals: dict[str, int] = dict.fromkeys(get_args(CumulativeName), 0)
        self._peaks: dict[str, int] = dict.fromkeys(get_args(MaximumName), 0)
        self._syntax_identities: set[int] = set()
        self._syntax_sizes: dict[int, int] = {}
        self._term_sorts: dict[tuple[int, int, tuple[str, ...]], str] = {}
        self._free_var_sorts: dict[int, frozenset[tuple[str, str]]] = {}

    def _within(self, name: str, value: int) -> int:
        limit = self._ceilings[name]
        if value > limit:
            raise WorkLimitError(
                f"work limit exceeded: {name} would be {value} (limit {limit})"
            )
        return value

    def consume(self, name: CumulativeName, amount: int = 1) -> None:
        if type(amount) is not int or amount < 0:
            raise TypeError("work amount must be a nonnegative exact int")
        self._totals[name] = self._within(name, self._totals[name] + amount)

    def observe(self, name: MaximumName, value: int) -> None:
        if type(value) is not int or value < 0:
            raise TypeError("work maximum must be a nonnegative exact int")
        self._peaks[name] = max(self._peaks[name], self._within(name, value))

    def input_syntax(self, identity: int, edge_count: int) -> bool:
        if identity in self._syntax_identities:
            return False
        self.consume("syntax_nodes")
        self.consume("syntax_edges", edge_count)
        self._syntax_identities.add(identity)
        return True

    def inspect_string(self, value: str) -> None:
        if type(value) is not str:
            raise TypeError("metered string must be an exact str")
        limit = self._ceilings["string_bytes"]
        if len(value) > limit - self._totals["string_bytes"]:
            raise WorkLimitError(
                "work limit exceeded: string_bytes minimum character count "
                f"would exceed limit {limit}"
            )
        self.consume("string_bytes", len(value.encode("utf-8")))

    def syntax_size(self, identity: int) -> int | None:
        """Return a size already derived during this invocation, if any."""
        return self._syntax_sizes.get(identity)

    def remember_syntax_size(self, identity: int, size: int) -> None:
        """Cache one immutable canonical syntax size for this invocation."""
        if type(size) is not int or size <= 0:
            raise TypeError("syntax size must be a positive exact int")
        previous = self._syntax_sizes.setdefault(identity, size)
        if previous != size:
            raise RuntimeError("syntax identity changed size during one check")

    def term_sort(
        self,
        signature_identity: int,
        term_identity: int,
        scope: tuple[str, ...],
    ) -> str | None:
        """Return one sort already checked under this signature and scope."""
        return self._term_sorts.get((signature_identity, term_identity, scope))

    def remember_term_sort(
        self,
        signature_identity: int,
        term_identity: int,
        scope: tuple[str, ...],
        sort: str,
    ) -> None:
        """Cache a checked immutable term sort for this invocation."""
        if type(sort) is not str:
            raise TypeError("term sort must be an exact str")
        key = (signature_identity, term_identity, scope)
        previous = self._term_sorts.setdefault(key, sort)
        if previous != sort:
            raise RuntimeError("term identity changed sort during one check")

    def free_var_sorts(
        self,
        identity: int,
    ) -> frozenset[tuple[str, str]] | None:
        """Return free variable/sort pairs already derived for one syntax node."""
        return self._free_var_sorts.get(identity)

    def remember_free_var_sorts(
        self,
        identity: int,
        pairs: frozenset[tuple[str, str]],
    ) -> None:
        """Cache immutable free-variable data for this invocation."""
        if type(pairs) is not frozenset:
            raise TypeError("free variable sorts must be an exact frozenset")
        previous = self._free_var_sorts.setdefault(identity, pairs)
        if previous != pairs:
            raise RuntimeError("syntax identity changed free variables during one check")

    def snapshot(self) -> WorkUsage:
        return WorkUsage(**self._totals, **self._peaks)


def require_lowered_work_limits(
    limits: WorkLimits,
    ceiling: WorkLimits = DEFAULT_WORK_LIMITS,
) -> WorkLimits:
    """Accept an exact limit set only when no repository ceiling is raised."""
    if type(limits) is not WorkLimits or type(ceiling) is not WorkLimits:
        raise TypeError("work limits and ceiling must be exact WorkLimits")
    maxima = _ceilings(ceiling)
    if any(value > maxima[name] for name, value in _ceilings(limits).items()):
        raise ValueError("verifier work limits may only lower repository ceilings")
    return limits


__all__ = [
    "DEFAULT_WORK_LIMITS",
    "CumulativeName",
    "MaximumName",
    "WorkLimitError",
    "WorkLimits",
    "WorkMeter",
    "WorkUsage",
    "require_lowered_work_limits",
]

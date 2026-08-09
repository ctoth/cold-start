"""Deterministic trusted work accounting for one checker invocation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal


class WorkLimitError(ValueError):
    """One named deterministic checker-work ceiling was exceeded."""


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
        values = (
            ("max_proof_nodes", self.max_proof_nodes),
            ("max_proof_edges", self.max_proof_edges),
            ("max_syntax_nodes", self.max_syntax_nodes),
            ("max_syntax_edges", self.max_syntax_edges),
            ("max_hypothesis_elements", self.max_hypothesis_elements),
            ("max_syntax_visits", self.max_syntax_visits),
            ("max_syntax_rebuilds", self.max_syntax_rebuilds),
            ("max_sort_steps", self.max_sort_steps),
            ("max_sequent_steps", self.max_sequent_steps),
            ("max_string_bytes", self.max_string_bytes),
            ("max_single_term_nodes", self.max_single_term_nodes),
            ("max_single_formula_nodes", self.max_single_formula_nodes),
            ("max_derived_hypotheses", self.max_derived_hypotheses),
            ("max_derived_sequent_nodes", self.max_derived_sequent_nodes),
        )
        for name, value in values:
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive exact int")


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


class WorkMeter:
    """Mutable per-call meter; no identities or counters survive a check."""

    __slots__ = (
        "_free_var_sorts",
        "_syntax_identities",
        "_syntax_sizes",
        "_term_sorts",
        "derived_hypotheses",
        "derived_sequent_nodes",
        "hypothesis_elements",
        "limits",
        "proof_edges",
        "proof_nodes",
        "sequent_steps",
        "single_formula_nodes",
        "single_term_nodes",
        "sort_steps",
        "string_bytes",
        "syntax_edges",
        "syntax_nodes",
        "syntax_rebuilds",
        "syntax_visits",
    )

    def __init__(self, limits: WorkLimits = DEFAULT_WORK_LIMITS) -> None:
        if type(limits) is not WorkLimits:
            raise TypeError("work limits must be exact WorkLimits")
        self.limits = limits
        self.proof_nodes = 0
        self.proof_edges = 0
        self.syntax_nodes = 0
        self.syntax_edges = 0
        self.hypothesis_elements = 0
        self.syntax_visits = 0
        self.syntax_rebuilds = 0
        self.sort_steps = 0
        self.sequent_steps = 0
        self.string_bytes = 0
        self.single_term_nodes = 0
        self.single_formula_nodes = 0
        self.derived_hypotheses = 0
        self.derived_sequent_nodes = 0
        self._syntax_identities: set[int] = set()
        self._syntax_sizes: dict[int, int] = {}
        self._term_sorts: dict[tuple[int, int, tuple[str, ...]], str] = {}
        self._free_var_sorts: dict[int, frozenset[tuple[str, str]]] = {}

    @staticmethod
    def _next(name: str, current: int, amount: int, limit: int) -> int:
        value = current + amount
        if value > limit:
            raise WorkLimitError(
                f"work limit exceeded: {name} would be {value} (limit {limit})"
            )
        return value

    def consume(self, name: CumulativeName, amount: int = 1) -> None:
        if type(amount) is not int or amount < 0:
            raise TypeError("work amount must be a nonnegative exact int")
        match name:
            case "proof_nodes":
                self.proof_nodes = self._next(
                    name, self.proof_nodes, amount, self.limits.max_proof_nodes
                )
            case "proof_edges":
                self.proof_edges = self._next(
                    name, self.proof_edges, amount, self.limits.max_proof_edges
                )
            case "syntax_nodes":
                self.syntax_nodes = self._next(
                    name, self.syntax_nodes, amount, self.limits.max_syntax_nodes
                )
            case "syntax_edges":
                self.syntax_edges = self._next(
                    name, self.syntax_edges, amount, self.limits.max_syntax_edges
                )
            case "hypothesis_elements":
                self.hypothesis_elements = self._next(
                    name,
                    self.hypothesis_elements,
                    amount,
                    self.limits.max_hypothesis_elements,
                )
            case "syntax_visits":
                self.syntax_visits = self._next(
                    name, self.syntax_visits, amount, self.limits.max_syntax_visits
                )
            case "syntax_rebuilds":
                self.syntax_rebuilds = self._next(
                    name,
                    self.syntax_rebuilds,
                    amount,
                    self.limits.max_syntax_rebuilds,
                )
            case "sort_steps":
                self.sort_steps = self._next(
                    name, self.sort_steps, amount, self.limits.max_sort_steps
                )
            case "sequent_steps":
                self.sequent_steps = self._next(
                    name, self.sequent_steps, amount, self.limits.max_sequent_steps
                )
            case "string_bytes":
                self.string_bytes = self._next(
                    name, self.string_bytes, amount, self.limits.max_string_bytes
                )

    @staticmethod
    def _maximum(name: str, current: int, value: int, limit: int) -> int:
        if value > limit:
            raise WorkLimitError(
                f"work limit exceeded: {name} would be {value} (limit {limit})"
            )
        return max(current, value)

    def observe(self, name: MaximumName, value: int) -> None:
        if type(value) is not int or value < 0:
            raise TypeError("work maximum must be a nonnegative exact int")
        match name:
            case "single_term_nodes":
                self.single_term_nodes = self._maximum(
                    name,
                    self.single_term_nodes,
                    value,
                    self.limits.max_single_term_nodes,
                )
            case "single_formula_nodes":
                self.single_formula_nodes = self._maximum(
                    name,
                    self.single_formula_nodes,
                    value,
                    self.limits.max_single_formula_nodes,
                )
            case "derived_hypotheses":
                self.derived_hypotheses = self._maximum(
                    name,
                    self.derived_hypotheses,
                    value,
                    self.limits.max_derived_hypotheses,
                )
            case "derived_sequent_nodes":
                self.derived_sequent_nodes = self._maximum(
                    name,
                    self.derived_sequent_nodes,
                    value,
                    self.limits.max_derived_sequent_nodes,
                )

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
        remaining = self.limits.max_string_bytes - self.string_bytes
        if len(value) > remaining:
            raise WorkLimitError(
                "work limit exceeded: string_bytes minimum character count "
                f"would exceed limit {self.limits.max_string_bytes}"
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
        return WorkUsage(
            proof_nodes=self.proof_nodes,
            proof_edges=self.proof_edges,
            syntax_nodes=self.syntax_nodes,
            syntax_edges=self.syntax_edges,
            hypothesis_elements=self.hypothesis_elements,
            syntax_visits=self.syntax_visits,
            syntax_rebuilds=self.syntax_rebuilds,
            sort_steps=self.sort_steps,
            sequent_steps=self.sequent_steps,
            string_bytes=self.string_bytes,
            single_term_nodes=self.single_term_nodes,
            single_formula_nodes=self.single_formula_nodes,
            derived_hypotheses=self.derived_hypotheses,
            derived_sequent_nodes=self.derived_sequent_nodes,
        )


def require_lowered_work_limits(
    limits: WorkLimits,
    ceiling: WorkLimits = DEFAULT_WORK_LIMITS,
) -> WorkLimits:
    """Accept an exact limit set only when no repository ceiling is raised."""
    if type(limits) is not WorkLimits or type(ceiling) is not WorkLimits:
        raise TypeError("work limits and ceiling must be exact WorkLimits")
    comparisons = (
        (limits.max_proof_nodes, ceiling.max_proof_nodes),
        (limits.max_proof_edges, ceiling.max_proof_edges),
        (limits.max_syntax_nodes, ceiling.max_syntax_nodes),
        (limits.max_syntax_edges, ceiling.max_syntax_edges),
        (limits.max_hypothesis_elements, ceiling.max_hypothesis_elements),
        (limits.max_syntax_visits, ceiling.max_syntax_visits),
        (limits.max_syntax_rebuilds, ceiling.max_syntax_rebuilds),
        (limits.max_sort_steps, ceiling.max_sort_steps),
        (limits.max_sequent_steps, ceiling.max_sequent_steps),
        (limits.max_string_bytes, ceiling.max_string_bytes),
        (limits.max_single_term_nodes, ceiling.max_single_term_nodes),
        (limits.max_single_formula_nodes, ceiling.max_single_formula_nodes),
        (limits.max_derived_hypotheses, ceiling.max_derived_hypotheses),
        (limits.max_derived_sequent_nodes, ceiling.max_derived_sequent_nodes),
    )
    if any(value > maximum for value, maximum in comparisons):
        raise ValueError("verifier work limits may only lower repository ceilings")
    return limits


__all__ = [
    "DEFAULT_WORK_LIMITS",
    "WorkLimitError",
    "WorkLimits",
    "WorkMeter",
    "WorkUsage",
    "require_lowered_work_limits",
]

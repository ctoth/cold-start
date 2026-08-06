"""Semantic coverage accounting for the generated Lean corpus."""

from __future__ import annotations

from dataclasses import dataclass

from ..proof import CANONICAL_PROOF_TYPES, Induct
from ..syntax import Exists, Forall, Rel, children
from .corpus import OFFICIAL_THEORIES, CorpusEntry, corpus_entries

REQUIRED_FEATURES = frozenset(
    {
        "induction",
        "universal-quantification",
        "existential-quantification",
        "relations",
        "ordinary-interpretation",
        "quotient-interpretation",
        "proof-family:presburger",
        "proof-family:peano",
        "proof-family:robinson",
        "proof-family:squaring",
        "proof-family:divisibility",
        "proof-family:robinson-divisibility",
        "proof-family:parity",
        "proof-family:order",
        "proof-family:integer-pairs",
        "proof-family:skolem",
    }
)


def _tree(*roots: object) -> tuple[object, ...]:
    nodes: list[object] = []
    stack = list(roots)
    while stack:
        node = stack.pop()
        nodes.append(node)
        stack.extend(children(node))
    return tuple(nodes)


@dataclass(frozen=True, slots=True)
class CoverageReport:
    """Observed and missing proof-language, feature, and theory coverage."""

    proof_rules: frozenset[str]
    features: frozenset[str]
    theories: frozenset[str]
    missing_proof_rules: frozenset[str]
    missing_features: frozenset[str]
    missing_theories: frozenset[str]

    @property
    def complete(self) -> bool:
        return not (self.missing_proof_rules or self.missing_features or self.missing_theories)


def corpus_coverage(entries: list[CorpusEntry] | None = None) -> CoverageReport:
    """Measure the corpus by semantics rather than public-function counting."""
    selected = corpus_entries() if entries is None else entries
    rules: set[str] = set()
    features = {feature for entry in selected for feature in entry.features}
    represented = {id(entry.theory) for entry in selected}

    for entry in selected:
        nodes = _tree(entry.proof, *entry.theory.axioms)
        rules.update(
            type(node).__name__ for node in nodes if type(node) in CANONICAL_PROOF_TYPES
        )
        if any(type(node) is Induct for node in nodes):
            features.add("induction")
        if any(type(node) is Forall for node in nodes):
            features.add("universal-quantification")
        if any(type(node) is Exists for node in nodes):
            features.add("existential-quantification")
        if any(type(node) is Rel for node in nodes):
            features.add("relations")

    expected_rules = frozenset(rule.__name__ for rule in CANONICAL_PROOF_TYPES)
    theory_names = frozenset(
        name for name, theory in OFFICIAL_THEORIES if id(theory) in represented
    )
    expected_theories = frozenset(name for name, _theory in OFFICIAL_THEORIES)
    observed_rules = frozenset(rules)
    observed_features = frozenset(features)
    return CoverageReport(
        proof_rules=observed_rules,
        features=observed_features,
        theories=theory_names,
        missing_proof_rules=expected_rules - observed_rules,
        missing_features=REQUIRED_FEATURES - observed_features,
        missing_theories=expected_theories - theory_names,
    )


def format_coverage(report: CoverageReport) -> str:
    """Render one explicit, stable semantic coverage summary."""
    status = "complete" if report.complete else "incomplete"
    return (
        f"Lean coverage {status}: {len(report.proof_rules)} proof rules; "
        f"{len(report.features)} feature families; {len(report.theories)} official theories"
    )


__all__ = [
    "REQUIRED_FEATURES",
    "CoverageReport",
    "corpus_coverage",
    "format_coverage",
]

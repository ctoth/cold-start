"""Semantic coverage accounting for the generated Lean corpus."""

from __future__ import annotations

from dataclasses import dataclass

from ..proof import CANONICAL_PROOF_TYPES, Axiom, Induct
from ..syntax import Exists, Forall, Rel, children
from .corpus import EXCLUDED_THEORIES, OFFICIAL_THEORIES, CorpusEntry, corpus_entries

# What a feature label is worth depends on where it comes from, so the two
# kinds are kept apart and reported apart.
#
# DERIVED features are read off the exported material itself -- the proof term
# and the axioms it is stated over -- so the corpus cannot claim one it does not
# have. ASSERTED features are hand-written labels saying which proof family an
# entry came from; nothing checks them, and the report says so rather than
# letting them pass as measurements.
DERIVED_FEATURES = frozenset(
    {
        "induction",
        "universal-quantification",
        "existential-quantification",
        "relations",
    }
)

ASSERTED_FEATURES = frozenset(
    {
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
        "proof-family:algebra",
        "proof-family:group-ring",
        "proof-family:cubic-ring",
        "proof-family:differential-ring",
    }
)

REQUIRED_FEATURES = DERIVED_FEATURES | ASSERTED_FEATURES


def _tree(*roots: object) -> tuple[object, ...]:
    nodes: list[object] = []
    seen: set[int] = set()
    stack = list(roots)
    while stack:
        node = stack.pop()
        identity = id(node)
        if identity in seen:
            continue
        seen.add(identity)
        nodes.append(node)
        stack.extend(children(node))
    return tuple(nodes)


def cites_its_theory(entry: CorpusEntry) -> bool:
    """Whether `entry` is a REAL theorem of its theory rather than a tautology.

    A proof that cites no axiom and uses no induction principle holds in the
    empty theory, so it says nothing about the theory it is filed under -- which
    is precisely what a filler `Refl(Var("x"))` was. Theory coverage is measured
    with this, so padding cannot certify a theory again."""
    return any(type(node) in (Axiom, Induct) for node in _tree(entry.proof))


@dataclass(frozen=True, slots=True)
class CoverageReport:
    """Observed and missing proof-language, feature, and theory coverage."""

    proof_rules: frozenset[str]
    derived_features: frozenset[str]
    asserted_features: frozenset[str]
    theories: frozenset[str]
    missing_proof_rules: frozenset[str]
    missing_features: frozenset[str]
    missing_theories: frozenset[str]
    excluded_theories: tuple[tuple[str, str], ...]

    @property
    def features(self) -> frozenset[str]:
        return self.derived_features | self.asserted_features

    @property
    def complete(self) -> bool:
        return not (self.missing_proof_rules or self.missing_features or self.missing_theories)


def corpus_coverage(entries: list[CorpusEntry] | None = None) -> CoverageReport:
    """Measure the corpus by semantics rather than public-function counting."""
    selected = corpus_entries() if entries is None else entries
    rules: set[str] = set()
    derived: set[str] = set()
    asserted: set[str] = set()
    covered: set[int] = set()

    for entry in selected:
        stray = entry.features - ASSERTED_FEATURES
        if stray:
            raise ValueError(
                f"{entry.name} asserts {sorted(stray)}; a derived feature is measured, "
                "never claimed, and an unknown one is not a feature family"
            )
        asserted.update(entry.features)
        if cites_its_theory(entry):
            covered.add(id(entry.theory))
        # The exported theorem carries its theory's whole axiom set as
        # hypotheses, so the axioms are part of what Lean reads and count here.
        nodes = _tree(entry.proof, *entry.theory.axioms)
        rules.update(type(node).__name__ for node in nodes if type(node) in CANONICAL_PROOF_TYPES)
        if any(type(node) is Induct for node in nodes):
            derived.add("induction")
        if any(type(node) is Forall for node in nodes):
            derived.add("universal-quantification")
        if any(type(node) is Exists for node in nodes):
            derived.add("existential-quantification")
        if any(type(node) is Rel for node in nodes):
            derived.add("relations")

    expected_rules = frozenset(rule.__name__ for rule in CANONICAL_PROOF_TYPES)
    theory_names = frozenset(name for name, theory in OFFICIAL_THEORIES if id(theory) in covered)
    expected_theories = frozenset(name for name, _theory in OFFICIAL_THEORIES)
    observed_rules = frozenset(rules)
    observed_features = frozenset(derived | asserted)
    return CoverageReport(
        proof_rules=observed_rules,
        derived_features=frozenset(derived),
        asserted_features=frozenset(asserted),
        theories=theory_names,
        missing_proof_rules=expected_rules - observed_rules,
        missing_features=REQUIRED_FEATURES - observed_features,
        missing_theories=expected_theories - theory_names,
        excluded_theories=tuple((name, reason) for name, _theory, reason in EXCLUDED_THEORIES),
    )


def format_coverage(report: CoverageReport) -> str:
    """Render one explicit, stable semantic coverage summary.

    Counts alone cannot be acted on, so every gap is named: what is missing, and
    what is excluded on purpose and why."""
    status = "complete" if report.complete else "INCOMPLETE"
    lines = [
        f"Lean coverage {status}: {len(report.proof_rules)} proof rules; "
        f"{len(report.derived_features)} derived and {len(report.asserted_features)} "
        f"asserted (unchecked) feature families; "
        f"{len(report.theories)}/{len(report.theories) + len(report.missing_theories)} "
        f"official theories",
    ]
    for label, missing in (
        ("missing proof rules", report.missing_proof_rules),
        ("missing feature families", report.missing_features),
        ("missing theories", report.missing_theories),
    ):
        if missing:
            lines.append(f"  {label}: {', '.join(sorted(missing))}")
    for name, reason in report.excluded_theories:
        lines.append(f"  excluded by design -- {name}: {reason}")
    return "\n".join(lines)


__all__ = [
    "ASSERTED_FEATURES",
    "DERIVED_FEATURES",
    "REQUIRED_FEATURES",
    "CoverageReport",
    "cites_its_theory",
    "corpus_coverage",
    "format_coverage",
]

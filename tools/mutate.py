"""Mutation testing for the trusted core, isolated in a disposable worktree.

The source argument is always a tracked, repository-relative path. The tool
creates a detached temporary Git worktree, mutates the corresponding file there,
runs the focused tests there, removes the worktree, and leaves the caller's
checkout untouched even if a mutant or test run fails.

The named ``logical`` and ``portable`` campaigns have separate source and test
slices. Pass one or more repository-relative paths for a focused run inside the
selected campaign.

Usage:  uv run python tools/mutate.py --campaign logical [source ...]
"""

from __future__ import annotations

import argparse
import ast
import copy
import os
import subprocess
import sys
import tempfile
from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parent.parent
CampaignName = Literal["logical", "portable"]


@dataclass(frozen=True, slots=True)
class MutationCampaign:
    sources: tuple[Path, ...]
    tests: tuple[str, ...]


MUTATION_CAMPAIGNS = MappingProxyType(
    {
        "logical": MutationCampaign(
            sources=(
                Path("cold_start/checker.py"),
                Path("cold_start/proof.py"),
                Path("cold_start/sequent.py"),
                Path("cold_start/syntax.py"),
                Path("cold_start/theory.py"),
            ),
            tests=(
                "tests/test_checker.py",
                "tests/test_kernel_boundaries.py",
                "tests/test_theory.py",
                "tests/test_quantifiers.py",
                "tests/test_quant_soundness.py",
                "tests/test_logic.py",
                "tests/test_sorts.py",
                "tests/test_relations.py",
                "tests/test_properties.py",
                "tests/test_rings.py",
            ),
        ),
        "portable": MutationCampaign(
            sources=(
                Path("cold_start/certificate.py"),
                Path("cold_start/codec.py"),
                Path("cold_start/verify.py"),
            ),
            tests=(
                "tests/test_certificate.py",
                "tests/test_codec.py",
            ),
        ),
    }
)

CMP_SWAP: dict[type[ast.cmpop], type[ast.cmpop]] = {
    ast.Is: ast.IsNot,
    ast.IsNot: ast.Is,
    ast.Eq: ast.NotEq,
    ast.NotEq: ast.Eq,
    ast.Lt: ast.LtE,
    ast.LtE: ast.Lt,
    ast.Gt: ast.GtE,
    ast.GtE: ast.Gt,
    ast.In: ast.NotIn,
    ast.NotIn: ast.In,
}
BOOL_SWAP: dict[type[ast.boolop], type[ast.boolop]] = {ast.And: ast.Or, ast.Or: ast.And}


def resolve_source(repo_root: Path, requested: str) -> Path:
    """Return a safe tracked source path relative to ``repo_root``.

    Absolute paths, traversal outside the repository, directories, missing files,
    and untracked files are rejected before a disposable worktree is created.
    """
    raw = Path(requested)
    if raw.is_absolute():
        raise ValueError("mutation source must be a repository-relative path")

    root = repo_root.resolve()
    resolved = (root / raw).resolve()
    try:
        relative = resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError("mutation source must stay within the repository") from exc

    if not resolved.is_file():
        raise ValueError(f"mutation source is not a file: {relative}")

    tracked = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--error-unmatch", "--", relative.as_posix()],
        capture_output=True,
        text=True,
        check=False,
    )
    if tracked.returncode != 0:
        raise ValueError(f"mutation source is not tracked: {relative}")
    return relative


def resolve_campaign_sources(
    repo_root: Path,
    campaign: CampaignName,
    requested: list[str],
) -> tuple[Path, ...]:
    """Resolve an explicit focused campaign or the complete trusted base."""
    declared = MUTATION_CAMPAIGNS[campaign].sources
    sources = (
        tuple(resolve_source(repo_root, source) for source in requested)
        if requested
        else declared
    )
    if len(sources) != len(set(sources)):
        raise ValueError("duplicate mutation source")
    outside = tuple(source for source in sources if source not in declared)
    if outside:
        raise ValueError(f"source is outside the {campaign} campaign: {outside[0]}")
    return sources


@contextmanager
def disposable_worktree(repo_root: Path) -> Generator[Path, None, None]:
    """Yield a verified detached worktree owned by this invocation."""
    root = repo_root.resolve()
    temp_parent = Path(tempfile.gettempdir()).resolve()
    temp_root = Path(tempfile.mkdtemp(prefix="cold-start-mutate-", dir=temp_parent)).resolve()
    if temp_root.parent != temp_parent or not temp_root.name.startswith("cold-start-mutate-"):
        raise RuntimeError(f"unexpected mutation workspace: {temp_root}")

    worktree = temp_root / "worktree"
    added = False
    try:
        created = subprocess.run(
            ["git", "-C", str(root), "worktree", "add", "--detach", str(worktree), "HEAD"],
            capture_output=True,
            text=True,
            check=False,
        )
        if created.returncode != 0:
            raise RuntimeError(f"could not create mutation worktree: {created.stderr.strip()}")
        added = True

        reported = subprocess.run(
            ["git", "-C", str(worktree), "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        if Path(reported).resolve() != worktree.resolve():
            raise RuntimeError(f"Git reported an unexpected mutation worktree: {reported}")

        print(f"mutation worktree: {worktree}")
        yield worktree
    finally:
        if added:
            removed = subprocess.run(
                ["git", "-C", str(root), "worktree", "remove", "--force", str(worktree)],
                capture_output=True,
                text=True,
                check=False,
            )
            if removed.returncode != 0:
                raise RuntimeError(
                    f"could not remove mutation worktree {worktree}: {removed.stderr.strip()}"
                )
        if worktree.exists():
            raise RuntimeError(f"mutation worktree still exists after removal: {worktree}")
        temp_root.rmdir()


def _build(tree: ast.AST, target: int) -> tuple[ast.AST, str, int]:
    """Return ``(mutated_tree, description, total_sites)`` for one mutation."""
    counter = [0]
    desc: list[str] = []

    class T(ast.NodeTransformer):
        def visit_Compare(self, node: ast.Compare) -> ast.AST:
            self.generic_visit(node)
            for i, op in enumerate(node.ops):
                replacement = CMP_SWAP.get(type(op))
                if replacement is not None:
                    if counter[0] == target:
                        old = type(op).__name__
                        node.ops[i] = replacement()
                        desc.append(f"line {node.lineno}: {old} -> {type(node.ops[i]).__name__}")
                    counter[0] += 1
            return node

        def visit_BoolOp(self, node: ast.BoolOp) -> ast.AST:
            self.generic_visit(node)
            replacement = BOOL_SWAP.get(type(node.op))
            if replacement is not None:
                if counter[0] == target:
                    old = type(node.op).__name__
                    node.op = replacement()
                    desc.append(f"line {node.lineno}: {old} -> {type(node.op).__name__}")
                counter[0] += 1
            return node

        def visit_UnaryOp(self, node: ast.UnaryOp) -> ast.AST:
            self.generic_visit(node)
            if isinstance(node.op, ast.Not):
                if counter[0] == target:
                    desc.append(f"line {node.lineno}: drop `not`")
                    counter[0] += 1
                    return node.operand
                counter[0] += 1
            return node

    new = T().visit(copy.deepcopy(tree))
    ast.fix_missing_locations(new)
    return new, (desc[0] if desc else ""), counter[0]


def _test_command(campaign: CampaignName) -> list[str]:
    return [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "-x",
        "-k",
        "not deep and not iterative",
        *MUTATION_CAMPAIGNS[campaign].tests,
    ]


def run_mutations(repo_root: Path, relative: Path, campaign: CampaignName) -> int:
    with disposable_worktree(repo_root) as workspace:
        target = workspace / relative
        original = target.read_text(encoding="utf-8")
        tree = ast.parse(original)
        _, _, total = _build(tree, -1)
        print(f"{total} mutation sites in {relative}\n")
        survivors: list[str] = []
        try:
            for k in range(total):
                mutant, desc, _ = _build(tree, k)
                target.write_text(ast.unparse(mutant), encoding="utf-8")
                try:
                    result = subprocess.run(
                        _test_command(campaign),
                        cwd=workspace,
                        capture_output=True,
                        check=False,
                        env={**os.environ, "HYPOTHESIS_PROFILE": "fast"},
                        timeout=60,
                    )
                except subprocess.TimeoutExpired:
                    print(f"  killed    {desc} (test timeout)")
                else:
                    if result.returncode == 0:
                        survivors.append(desc)
                        print(f"  SURVIVED  {desc}")
                    else:
                        print(f"  killed    {desc}")
        finally:
            target.write_text(original, encoding="utf-8")

        print(f"\n{len(survivors)}/{total} survived")
        for description in survivors:
            print("  SURVIVOR:", description)
        return 1 if survivors else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--campaign",
        choices=tuple(MUTATION_CAMPAIGNS),
        required=True,
    )
    parser.add_argument("sources", nargs="*")
    args = parser.parse_args(argv)
    campaign = args.campaign
    try:
        sources = resolve_campaign_sources(REPO_ROOT, campaign, args.sources)
    except ValueError as exc:
        parser.error(str(exc))
    failed = False
    for source in sources:
        failed = bool(run_mutations(REPO_ROOT, source, campaign)) or failed
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())

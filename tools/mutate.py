"""Mutation testing for the trusted core, isolated in a disposable worktree.

The source argument is always a tracked, repository-relative path. The tool
creates a detached temporary Git worktree, mutates the corresponding file there,
runs the focused tests there, removes the worktree, and leaves the caller's
checkout untouched even if a mutant or test run fails.

With no arguments the complete declared trusted base is mutated.  Pass one or
more repository-relative paths for a focused kernel campaign.

Usage:  uv run python tools/mutate.py [cold_start/checker.py ...]
"""

from __future__ import annotations

import argparse
import ast
import copy
import os
import subprocess
import sys
import tempfile
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
TRUSTED_SOURCES = (
    Path("cold_start/checker.py"),
    Path("cold_start/proof.py"),
    Path("cold_start/sequent.py"),
    Path("cold_start/syntax.py"),
    Path("cold_start/theory.py"),
)

CMP_SWAP = {
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
BOOL_SWAP = {ast.And: ast.Or, ast.Or: ast.And}


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


def resolve_campaign_sources(repo_root: Path, requested: list[str]) -> tuple[Path, ...]:
    """Resolve an explicit focused campaign or the complete trusted base."""
    sources = (
        tuple(resolve_source(repo_root, source) for source in requested)
        if requested
        else TRUSTED_SOURCES
    )
    if len(sources) != len(set(sources)):
        raise ValueError("duplicate mutation source")
    return sources


@contextmanager
def disposable_worktree(repo_root: Path) -> Iterator[Path]:
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


def _build(tree: ast.AST, target: int):
    """Return ``(mutated_tree, description, total_sites)`` for one mutation."""
    counter = [0]
    desc: list[str] = []

    class T(ast.NodeTransformer):
        def visit_Compare(self, node):
            self.generic_visit(node)
            for i, op in enumerate(node.ops):
                if type(op) in CMP_SWAP:
                    if counter[0] == target:
                        old = type(op).__name__
                        node.ops[i] = CMP_SWAP[type(op)]()
                        desc.append(f"line {node.lineno}: {old} -> {type(node.ops[i]).__name__}")
                    counter[0] += 1
            return node

        def visit_BoolOp(self, node):
            self.generic_visit(node)
            if type(node.op) in BOOL_SWAP:
                if counter[0] == target:
                    old = type(node.op).__name__
                    node.op = BOOL_SWAP[type(node.op)]()
                    desc.append(f"line {node.lineno}: {old} -> {type(node.op).__name__}")
                counter[0] += 1
            return node

        def visit_UnaryOp(self, node):
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


def _test_command() -> list[str]:
    return [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "-x",
        "-k",
        "not deep and not iterative",
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
    ]


def run_mutations(repo_root: Path, relative: Path) -> int:
    with disposable_worktree(repo_root) as workspace:
        target = workspace / relative
        original = target.read_text(encoding="utf-8")
        tree = ast.parse(original)
        _, _, total = _build(tree, -1)
        print(f"{total} mutation sites in {relative}\n")
        survivors = []
        try:
            for k in range(total):
                mutant, desc, _ = _build(tree, k)
                target.write_text(ast.unparse(mutant), encoding="utf-8")
                try:
                    result = subprocess.run(
                        _test_command(),
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
    parser.add_argument("sources", nargs="*")
    args = parser.parse_args(argv)
    try:
        sources = resolve_campaign_sources(REPO_ROOT, args.sources)
    except ValueError as exc:
        parser.error(str(exc))
    failed = False
    for source in sources:
        failed = bool(run_mutations(REPO_ROOT, source)) or failed
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())

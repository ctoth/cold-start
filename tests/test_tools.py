"""Operational safety contracts for repository-owned tools."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from tools import mutate

REPO_ROOT = Path(__file__).resolve().parent.parent


def test_mutation_source_must_be_a_safe_repository_relative_file(tmp_path: Path):
    assert mutate.resolve_source(REPO_ROOT, "cold_start/checker.py") == Path(
        "cold_start/checker.py"
    )

    for unsafe in (
        REPO_ROOT / "cold_start" / "checker.py",
        Path("..") / "outside.py",
        Path("cold_start"),
        Path("missing.py"),
        tmp_path / "outside.py",
    ):
        with pytest.raises(ValueError):
            mutate.resolve_source(REPO_ROOT, str(unsafe))


def test_mutation_cli_rejects_an_absolute_target(tmp_path: Path):
    target = tmp_path / "outside.py"
    target.write_text("value = 1\n", encoding="utf-8")
    before = target.read_bytes()

    result = subprocess.run(
        [sys.executable, "tools/mutate.py", str(target)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 2
    assert "repository-relative" in result.stderr
    assert target.read_bytes() == before


def test_full_gate_prints_the_pytest_summary_and_names_basic_pyright_mode():
    gate = (REPO_ROOT / "tools" / "gate.ps1").read_text(encoding="utf-8")

    assert "@('uv', 'run', 'pytest')" in gate
    assert "@('uv', 'run', 'pytest', '-q')" not in gate
    assert "pyright (basic)" in gate


def test_ci_uses_the_lockfile_supported_python_and_the_owned_local_gate():
    workflow = (REPO_ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")

    assert 'python-version: "3.11"' in workflow
    assert "uv sync --locked --dev" in workflow
    assert "pwsh -File tools/gate.ps1" in workflow
    assert "uv run pytest" not in workflow
    assert "uv run ruff" not in workflow
    assert "uv run pyright" not in workflow


def test_ci_checks_the_generated_corpus_and_compiles_it_with_pinned_lean4():
    workflow = (REPO_ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    toolchain = (REPO_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()

    assert toolchain.startswith("leanprover/lean4:v4.")
    assert "uv run python -m cold_start.lean" in workflow
    assert "git diff --exit-code -- lean_export/ColdStart.lean" in workflow
    assert "lean lean_export/ColdStart.lean" in workflow


def test_type_checking_mode_is_named_consistently():
    gate = (REPO_ROOT / "tools" / "gate.ps1").read_text(encoding="utf-8")
    config = (REPO_ROOT / "pyrightconfig.json").read_text(encoding="utf-8")

    assert '"typeCheckingMode": "basic"' in config
    assert "pyright (basic)" in gate
    assert "strict" not in gate.lower()


def test_durable_docs_name_current_architecture_owners():
    readme = (REPO_ROOT / "README.md").read_text(encoding="utf-8")
    architecture = (REPO_ROOT / "ARCHITECTURE.md").read_text(encoding="utf-8")
    working_rules = (REPO_ROOT / "cold_start" / "CLAUDE.md").read_text(encoding="utf-8")
    durable = "\n".join((readme, architecture, working_rules))

    for stale in (
        "cold_start/lean.py",
        "cold_start/proofs.py",
        "`proofs.robinson_add_proof",
        "to_bytes/from_bytes",
        "dependency-free",
    ):
        assert stale not in durable

    for current in (
        "cold_start/codec.py",
        "cold_start/presburger_proofs.py",
        "cold_start/peano_proofs.py",
        "cold_start/lean/models.py",
        "cold_start/lean/corpus.py",
    ):
        assert current in readme
    assert "`Rel`" in architecture


def test_superseded_chronological_docs_are_deleted():
    for relative in (
        "NOTES.md",
        "notes-cold-start.md",
        "notes-formula2.md",
        "workstreams/notation-formatter-deletion-first.md",
    ):
        assert not (REPO_ROOT / relative).exists()

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

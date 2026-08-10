"""Operational safety contracts for repository-owned tools."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest

from tools import mutate

REPO_ROOT = Path(__file__).resolve().parent.parent
CI_WORKFLOW = REPO_ROOT / ".github" / "workflows" / "ci.yml"
TEST_PATH_PATTERN = re.compile(r"tests/test_[A-Za-z0-9_]+\.py")
EXPECTED_TRUSTED_SOURCES = (
    Path("cold_start/checker.py"),
    Path("cold_start/proof.py"),
    Path("cold_start/sequent.py"),
    Path("cold_start/syntax.py"),
    Path("cold_start/theory.py"),
    Path("cold_start/work.py"),
)
EXPECTED_PORTABLE_SOURCES = (
    Path("cold_start/certificate.py"),
    Path("cold_start/codec.py"),
    Path("cold_start/verify.py"),
)


def test_ci_runs_every_test_module_on_disk():
    """CI hand-lists its test slices, so an added module can silently never run."""
    workflow = CI_WORKFLOW.read_text(encoding="utf-8")
    named = set(TEST_PATH_PATTERN.findall(workflow))
    on_disk = {
        path.relative_to(REPO_ROOT).as_posix()
        for path in (REPO_ROOT / "tests").glob("test_*.py")
    }

    assert not (on_disk - named), (
        f"test modules missing from ci.yml: {sorted(on_disk - named)}"
    )
    assert not (named - on_disk), (
        f"ci.yml names test modules that do not exist: {sorted(named - on_disk)}"
    )


def test_mutation_campaigns_equal_the_declared_source_boundaries():
    assert mutate.MUTATION_CAMPAIGNS["logical"].sources == EXPECTED_TRUSTED_SOURCES
    assert mutate.MUTATION_CAMPAIGNS["portable"].sources == EXPECTED_PORTABLE_SOURCES
    assert (
        mutate.resolve_campaign_sources(REPO_ROOT, "logical", [])
        == EXPECTED_TRUSTED_SOURCES
    )
    assert (
        mutate.resolve_campaign_sources(REPO_ROOT, "portable", [])
        == EXPECTED_PORTABLE_SOURCES
    )


def test_mutation_campaign_rejects_duplicate_sources():
    with pytest.raises(ValueError, match="duplicate mutation source"):
        mutate.resolve_campaign_sources(
            REPO_ROOT,
            "logical",
            ["cold_start/checker.py", "cold_start/checker.py"],
        )


def test_mutation_campaign_rejects_a_source_from_the_other_boundary():
    with pytest.raises(ValueError, match="outside the portable campaign"):
        mutate.resolve_campaign_sources(
            REPO_ROOT,
            "portable",
            ["cold_start/checker.py"],
        )


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
        [sys.executable, "tools/mutate.py", "--campaign", "logical", str(target)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 2
    assert "repository-relative" in result.stderr
    assert target.read_bytes() == before

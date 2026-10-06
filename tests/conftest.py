"""Shared pytest configuration for the cold-start suite.

`cold_start` is importable because pyproject sets `pythonpath = ["."]`; this dir
goes on sys.path automatically (no __init__.py), so test modules may import each
other (e.g. test_logic reuses test_model's evaluator).
"""

from __future__ import annotations

import os

from hypothesis import HealthCheck, settings

# A trimmed profile for fast/iterative runs; full otherwise.
settings.register_profile("default", deadline=None)
settings.register_profile(
    "fast",
    max_examples=25,
    deadline=None,
    suppress_health_check=list(HealthCheck),
)
# Mutation testing draws the same examples on every run, from no saved database:
# a mutant killed only by a lucky random example would flip verdict between runs.
settings.register_profile(
    "mutation",
    max_examples=25,
    deadline=None,
    suppress_health_check=list(HealthCheck),
    derandomize=True,
    database=None,
)
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "default"))

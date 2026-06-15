"""Shared pytest configuration for the cold-start suite.

`cold_start` is importable because pyproject sets `pythonpath = ["."]`; this dir
goes on sys.path automatically (no __init__.py), so test modules may import each
other (e.g. test_logic reuses test_model's evaluator).
"""

from __future__ import annotations

import os

from hypothesis import HealthCheck, settings

# A trimmed profile for fast/iterative runs and mutation testing; full otherwise.
settings.register_profile("default", deadline=None)
settings.register_profile(
    "fast",
    max_examples=25,
    deadline=None,
    suppress_health_check=list(HealthCheck),
)
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "default"))

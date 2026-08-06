"""Generate the checked-in Lean corpus."""

from __future__ import annotations

import argparse
from pathlib import Path

from .corpus import CORPUS_PATH, write_corpus
from .coverage import corpus_coverage, format_coverage


def main(argv: list[str] | None = None) -> None:
    """Generate a Lean corpus at an explicit path or the repository default."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", type=Path, default=CORPUS_PATH)
    args = parser.parse_args(argv)
    print(f"wrote {write_corpus(args.output)}")
    print(format_coverage(corpus_coverage()))


if __name__ == "__main__":
    main()

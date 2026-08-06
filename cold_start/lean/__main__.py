"""Generate the checked-in Lean corpus."""

from .corpus import write_corpus
from .coverage import corpus_coverage, format_coverage


def main() -> None:
    print(f"wrote {write_corpus()}")
    print(format_coverage(corpus_coverage()))


if __name__ == "__main__":
    main()

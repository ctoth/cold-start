"""Generate the checked-in Lean corpus."""

from .corpus import write_corpus


def main() -> None:
    print(f"wrote {write_corpus()}")


if __name__ == "__main__":
    main()

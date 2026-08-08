"""Independent proof verifier.

Reads a binary proof term (from a file argument or stdin), checks it against a
named theory, and prints the resulting sequent. Exit code 0 on a valid proof,
1 on rejection. This is the De Bruijn criterion made concrete: a proof produced
anywhere -- by a buggy prover, an adversary, another machine -- is trusted only
to the extent this small program re-derives it.

The wire form is hamblin's recursion-free postfix bytes, not JSON: a proof nested
arbitrarily deep (or a hostile, deeply nested blob) decodes -- or is cleanly
REJECTED -- without a `RecursionError` at the front door. hamblin reports a
malformed stream as `HamblinError`, a `ValueError`, so the existing rejection path
already covers it.

Usage:
    python verify.py proof.hmb
    cat proof.hmb | python verify.py
    python verify.py proof.hmb --theory peano

The theories are `peano`, `presburger` (the addition-only fragment),
`robinson` (the (1, S, ·) basis with `+` eliminated) and `diffring2` (the
differential char-2 ring the Jacobian certificate lives in). A proof is checked
against exactly the one theory named, so citing an axiom from another is a
rejection.
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Mapping
from pathlib import Path
from types import MappingProxyType

from .checker import check
from .codec import decode_proof
from .diffring2 import DIFF_RING_2
from .groupring2 import GROUP_RING_P2
from .peano import PEANO
from .presburger import PRESBURGER
from .robinson import ROBINSON_PEANO
from .theory import Theory

THEORIES: Mapping[str, Theory] = MappingProxyType(
    {
        "peano": PEANO,
        "presburger": PRESBURGER,
        "robinson": ROBINSON_PEANO,
        "diffring2": DIFF_RING_2,
        "groupring2": GROUP_RING_P2,
    }
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="cold-start-verify",
        description="Decode and independently check one Hamblin proof term.",
    )
    parser.add_argument("path", nargs="?", help="proof file; omit to read standard input")
    parser.add_argument("--theory", default="peano", help="peano, presburger, or robinson")
    return parser


def _read_input(path: str | None) -> bytes | None:
    try:
        if path is None:
            return sys.stdin.buffer.read()
        with Path(path).open("rb") as source:
            return source.read()
    except OSError as exc:
        label = "standard input" if path is None else repr(path)
        print(f"error: cannot read {label}: {exc}", file=sys.stderr)
        return None


def main(argv: list[str]) -> int:
    args = _parser().parse_args(argv)

    theory = THEORIES.get(args.theory)
    if theory is None:
        print(f"unknown theory: {args.theory!r} (have: {', '.join(THEORIES)})", file=sys.stderr)
        return 2

    data = _read_input(args.path)
    if data is None:
        return 2

    try:
        pf = decode_proof(data)
        sequent = check(pf, theory)
    except (ValueError, TypeError) as exc:
        print(f"REJECTED: {exc}", file=sys.stderr)
        return 1

    print(f"VERIFIED [{args.theory}]: {sequent}")
    return 0


def cli() -> None:
    """Console-script adapter using the process argument vector."""
    raise SystemExit(main(sys.argv[1:]))


if __name__ == "__main__":
    cli()

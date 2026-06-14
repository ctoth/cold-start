"""Independent proof verifier.

Reads a JSON proof term (from a file argument or stdin), checks it against a
named theory, and prints the resulting sequent. Exit code 0 on a valid proof,
1 on rejection. This is the De Bruijn criterion made concrete: a proof produced
anywhere -- by a buggy prover, an adversary, another machine -- is trusted only
to the extent this small program re-derives it.

Usage:
    python verify.py proof.json
    cat proof.json | python verify.py
    python verify.py proof.json --theory peano
"""

from __future__ import annotations

import sys

from checker import check
from proof import from_json

THEORIES = {}


def _load_theories() -> None:
    from peano import PEANO

    THEORIES["peano"] = PEANO


def main(argv: list[str]) -> int:
    _load_theories()
    path = None
    theory_name = "peano"
    i = 0
    while i < len(argv):
        if argv[i] == "--theory":
            theory_name = argv[i + 1]
            i += 2
        else:
            path = argv[i]
            i += 1

    theory = THEORIES.get(theory_name)
    if theory is None:
        print(f"unknown theory: {theory_name!r} (have: {', '.join(THEORIES)})", file=sys.stderr)
        return 2

    text = open(path, encoding="utf-8").read() if path else sys.stdin.read()

    try:
        pf = from_json(text)
        sequent = check(pf, theory)
    except (ValueError, TypeError) as exc:
        print(f"REJECTED: {exc}", file=sys.stderr)
        return 1

    print(f"VERIFIED [{theory_name}]: {sequent}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

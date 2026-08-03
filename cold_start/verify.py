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

The theories are `peano`, `presburger` (the addition-only fragment) and
`robinson` (the (1, S, ·) basis with `+` eliminated). A proof is checked against
exactly the one theory named, so citing an axiom from another is a rejection.
"""

from __future__ import annotations

import sys

from .checker import check
from .proof import from_bytes

THEORIES = {}


def _load_theories() -> None:
    from .peano import PEANO
    from .presburger import PRESBURGER
    from .robinson import ROBINSON_PEANO

    THEORIES["peano"] = PEANO
    THEORIES["presburger"] = PRESBURGER
    THEORIES["robinson"] = ROBINSON_PEANO


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

    data = open(path, "rb").read() if path else sys.stdin.buffer.read()

    try:
        pf = from_bytes(data)
        sequent = check(pf, theory)
    except (ValueError, TypeError) as exc:
        print(f"REJECTED: {exc}", file=sys.stderr)
        return 1

    print(f"VERIFIED [{theory_name}]: {sequent}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

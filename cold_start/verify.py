"""Independent verifier for portable, embedded-theory certificates.

The artifact names its theory and carries that theory's semantic fingerprint and
claimed sequent. The verifier resolves only its closed registry, checks the
fingerprint, re-derives the proof with the ordinary checker, and compares the
exact claim. The command accepts a file path or standard input; there is no
external theory selector or raw-proof fallback.
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Mapping
from pathlib import Path
from types import MappingProxyType

from .certificate import Certificate
from .checker import check
from .codec import decode_certificate, theory_fingerprint
from .diffring2 import DIFF_RING_2
from .groupring2 import GROUP_RING_P2
from .peano import PEANO
from .presburger import PRESBURGER
from .robinson import ROBINSON_PEANO
from .sequent import Sequent
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


def verify_certificate(
    certificate: Certificate,
    theories: Mapping[str, Theory] = THEORIES,
) -> Sequent:
    """Resolve, fingerprint, check, and claim-match one inert certificate."""
    if type(certificate) is not Certificate:
        raise TypeError("expected an exact Certificate")
    theory = theories.get(certificate.theory_key)
    if theory is None:
        raise ValueError(f"unknown embedded theory: {certificate.theory_key!r}")
    if theory_fingerprint(theory) != certificate.theory_fingerprint:
        raise ValueError("embedded theory fingerprint mismatch")
    derived = check(certificate.proof, theory)
    if derived != certificate.claim:
        raise ValueError("certificate claim mismatch")
    return derived


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="cold-start-verify",
        description="Decode and independently check one portable certificate.",
    )
    parser.add_argument("path", nargs="?", help="certificate file; omit for stdin")
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
    data = _read_input(args.path)
    if data is None:
        return 2

    try:
        certificate = decode_certificate(data)
        sequent = verify_certificate(certificate)
    except (ValueError, TypeError) as exc:
        print(f"REJECTED: {exc}", file=sys.stderr)
        return 1

    print(f"VERIFIED [{certificate.theory_key}]: {sequent}")
    return 0


def cli() -> None:
    """Console-script adapter using the process argument vector."""
    raise SystemExit(main(sys.argv[1:]))


if __name__ == "__main__":
    cli()


__all__ = ["THEORIES", "main", "verify_certificate"]

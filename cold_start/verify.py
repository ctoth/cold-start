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
from .checker import CheckResult, check_claim_with_usage
from .codec import (
    DEFAULT_CERTIFICATE_LIMITS,
    CertificateLimits,
    decode_certificate,
    require_lowered_certificate_limits,
    theory_fingerprint,
)
from .diffring2 import DIFF_RING_2
from .groupring2 import GROUP_RING_P2
from .peano import PEANO
from .presburger import PRESBURGER
from .robinson import ROBINSON_PEANO
from .sequent import Sequent
from .theory import Theory
from .work import (
    DEFAULT_WORK_LIMITS,
    WorkLimits,
    require_lowered_work_limits,
)

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
    *,
    work_limits: WorkLimits = DEFAULT_WORK_LIMITS,
) -> Sequent:
    """Resolve, fingerprint, check, and claim-match one inert certificate."""
    return verify_certificate_with_usage(
        certificate,
        theories,
        work_limits=work_limits,
    ).sequent


def verify_certificate_with_usage(
    certificate: Certificate,
    theories: Mapping[str, Theory] = THEORIES,
    *,
    work_limits: WorkLimits = DEFAULT_WORK_LIMITS,
) -> CheckResult:
    """Verify one certificate and retain its deterministic checker accounting."""
    if type(certificate) is not Certificate:
        raise TypeError("expected an exact Certificate")
    theory = theories.get(certificate.theory_key)
    if theory is None:
        raise ValueError(f"unknown embedded theory: {certificate.theory_key!r}")
    if theory_fingerprint(theory) != certificate.theory_fingerprint:
        raise ValueError("embedded theory fingerprint mismatch")
    limits = require_lowered_work_limits(work_limits)
    return check_claim_with_usage(
        certificate.proof,
        theory,
        certificate.claim,
        limits=limits,
    )


def verify_bytes(
    data: bytes,
    *,
    certificate_limits: CertificateLimits = DEFAULT_CERTIFICATE_LIMITS,
    work_limits: WorkLimits = DEFAULT_WORK_LIMITS,
) -> tuple[Certificate, Sequent]:
    """Decode and verify bytes under repository-ceiling-or-lower limits."""
    certificate, result = verify_bytes_with_usage(
        data,
        certificate_limits=certificate_limits,
        work_limits=work_limits,
    )
    return certificate, result.sequent


def verify_bytes_with_usage(
    data: bytes,
    *,
    certificate_limits: CertificateLimits = DEFAULT_CERTIFICATE_LIMITS,
    work_limits: WorkLimits = DEFAULT_WORK_LIMITS,
) -> tuple[Certificate, CheckResult]:
    """Decode and verify bytes while retaining deterministic work usage."""
    io_limits = require_lowered_certificate_limits(certificate_limits)
    checker_limits = require_lowered_work_limits(work_limits)
    certificate = decode_certificate(data, limits=io_limits)
    return certificate, verify_certificate_with_usage(
        certificate,
        work_limits=checker_limits,
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="cold-start-verify",
        description="Decode and independently check one portable certificate.",
    )
    parser.add_argument(
        "--report-work",
        action="store_true",
        help="print deterministic artifact usage and repository ceilings",
    )
    parser.add_argument("path", nargs="?", help="certificate file; omit for stdin")
    return parser


def _read_input(path: str | None, max_bytes: int) -> bytes | None:
    try:
        if path is None:
            data = sys.stdin.buffer.read(max_bytes + 1)
        else:
            with Path(path).open("rb") as source:
                data = source.read(max_bytes + 1)
    except OSError as exc:
        label = "standard input" if path is None else repr(path)
        print(f"error: cannot read {label}: {exc}", file=sys.stderr)
        return None
    if len(data) > max_bytes:
        raise ValueError("certificate input bytes limit exceeded")
    return data


def main(argv: list[str]) -> int:
    args = _parser().parse_args(argv)
    try:
        data = _read_input(args.path, DEFAULT_CERTIFICATE_LIMITS.max_input_bytes)
        if data is None:
            return 2
        certificate, result = verify_bytes_with_usage(data)
    except (ValueError, TypeError) as exc:
        print(f"REJECTED: {exc}", file=sys.stderr)
        return 1

    print(f"VERIFIED [{certificate.theory_key}]: {result.sequent}")
    if args.report_work:
        print(
            f"WORK certificate_bytes={len(data)} usage={result.usage} "
            f"work_limits={DEFAULT_WORK_LIMITS} "
            f"certificate_limits={DEFAULT_CERTIFICATE_LIMITS}"
        )
    return 0


def cli() -> None:
    """Console-script adapter using the process argument vector."""
    raise SystemExit(main(sys.argv[1:]))


if __name__ == "__main__":
    cli()


__all__ = [
    "THEORIES",
    "main",
    "verify_bytes",
    "verify_bytes_with_usage",
    "verify_certificate",
    "verify_certificate_with_usage",
]

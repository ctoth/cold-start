"""Inert data carried by the portable certificate wire.

Holding a :class:`Certificate` proves nothing. Authority remains in the ordinary
checker after the verifier resolves and fingerprints the embedded theory key.
"""

from __future__ import annotations

from dataclasses import dataclass

from .proof import Pf
from .sequent import Sequent


@dataclass(frozen=True, slots=True)
class Certificate:
    theory_key: str
    theory_fingerprint: bytes
    claim: Sequent
    proof: Pf


__all__ = ["Certificate"]

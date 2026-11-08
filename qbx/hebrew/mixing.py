"""
Hebrew-augmented invariant hashing.

The mixing function takes canonical bytes and augments them with a
deterministic "Hebrew mix" derived from a provided label (e.g., a Hebrew
word, a category name, a functor name). This provides an additional
collision-resistance layer that is *structural* (tied to the gematria
functor) rather than free-text.

Mixing rule:
    mixed = SHA3-256( canonical_bytes || 0x00 || gematria_bytes(label) || 0x00 || nonce )

The result is a hex digest.
"""

from __future__ import annotations

import os
import uuid
from typing import Optional

from qbx.core.hashing import pq_hash
from qbx.hebrew.gematria import gematria_bytes


class HebrewMixer:
    """
    Deterministic Hebrew-augmented hash mixing.

    The mixer is disabled if QBX_HEBREW_MIX_ENABLED=false.
    """

    def __init__(self, enabled: Optional[bool] = None, default_label: str = ""):
        if enabled is None:
            enabled = os.getenv("QBX_HEBREW_MIX_ENABLED", "true").lower() == "true"
        self.enabled = enabled
        self.default_label = default_label

    def mix(
        self,
        canonical_bytes: bytes,
        label: Optional[str] = None,
        nonce: Optional[bytes] = None,
    ) -> str:
        """
        Return the Hebrew-mixed hash of canonical_bytes.

        If mixing is disabled, returns the plain PQ hash.
        """
        if not self.enabled or not (label or self.default_label):
            return pq_hash(canonical_bytes)

        used_label = label if label is not None else self.default_label
        used_nonce = nonce if nonce is not None else uuid.uuid4().bytes

        g_bytes = gematria_bytes(used_label)
        payload = (
            canonical_bytes
            + b"\x00"
            + g_bytes
            + b"\x00"
            + used_nonce
        )
        return pq_hash(payload)

    def mix_with_gematria_value(
        self,
        canonical_bytes: bytes,
        gematria: int,
        nonce: Optional[bytes] = None,
    ) -> str:
        """Mix with an explicit gematria value (skip string lookup)."""
        if not self.enabled:
            return pq_hash(canonical_bytes)
        used_nonce = nonce if nonce is not None else uuid.uuid4().bytes
        g_bytes = gematria.to_bytes(8, "big", signed=False)
        payload = canonical_bytes + b"\x00" + g_bytes + b"\x00" + used_nonce
        return pq_hash(payload)

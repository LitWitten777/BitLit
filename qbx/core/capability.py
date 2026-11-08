"""Signed capability tokens with a revocation list (decision Q-001, option 2).

A capability token is a self-contained, signed blob::

    qbxcap1.<claims>.<signature>

* ``claims`` is the base64url (unpadded) encoding of the canonical JSON of a
  claims object (see :class:`CapabilityClaims`).
* ``signature`` is the base64url (unpadded) signature produced by a signer
  from :mod:`qbx.core.signing` over ``pq_hash("qbxcap1." + claims)`` — i.e. over
  the hash of everything before the final dot, so the version prefix is
  authenticated too.  (Only ``signing.py`` may use the cryptography library;
  this module works with any signer exposing ``sign(payload_hash) ->
  SignedBlob`` and ``key_id``, and any verifier exposing ``verify(SignedBlob)
  -> bool`` — ``StubSigner`` / ``HybridSigner`` today.)

A token is **valid** for a scope at time ``t`` iff

1. it parses, and its version prefix is ``qbxcap1``;
2. its ``key_id`` names a trusted verifier and the signature verifies;
3. ``not_before <= t < expires_at`` (both are integer UNIX seconds);
4. the requested scope is one of the token's scopes (``"*"`` grants all);
5. its ``token_id`` is not on the revocation list.

Revocation is what option 2 adds over plain JWTs: a :class:`RevocationList`
holds revoked ``token_id`` values, and the database mirror lives in migration
``018_capability_revocation.sql``.  Signature verification happens here, in
Python; PostgreSQL only stores tokens and revocations.

Phase 4 plans to move tokens on-chain (option 3); the claims format is chosen
so that a token can later be anchored by its ``token_id`` without change.
"""

from __future__ import annotations

import base64
import json
import secrets
import time
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Iterable, Mapping, Optional, Protocol, Tuple

from qbx.core.canonical import canonical_json
from qbx.core.exceptions import CapabilityRequiredError
from qbx.core.hashing import pq_hash
from qbx.core.signing import SignedBlob


class Signer(Protocol):
    key_id: str

    def sign(self, payload_hash: str) -> SignedBlob: ...


class Verifier(Protocol):
    def verify(self, blob: SignedBlob) -> bool: ...

TOKEN_VERSION = "qbxcap1"
WILDCARD_SCOPE = "*"


class InvalidCapabilityError(CapabilityRequiredError):
    """A capability token was presented but is not valid; ``reason`` says why."""

    def __init__(self, reason: str, message: Optional[str] = None):
        self.reason = reason
        super().__init__(message or f"invalid capability token: {reason}")


def _b64e(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _b64d(text: str) -> bytes:
    pad = "=" * (-len(text) % 4)
    return base64.urlsafe_b64decode(text + pad)


@dataclass(frozen=True)
class CapabilityClaims:
    token_id: str
    subject: str
    scopes: Tuple[str, ...]
    issued_at: int
    not_before: int
    expires_at: int
    key_id: str

    def to_dict(self) -> dict:
        return {
            "token_id": self.token_id,
            "subject": self.subject,
            "scopes": list(self.scopes),
            "issued_at": self.issued_at,
            "not_before": self.not_before,
            "expires_at": self.expires_at,
            "key_id": self.key_id,
        }

    @classmethod
    def from_dict(cls, d: Mapping) -> "CapabilityClaims":
        try:
            scopes = d["scopes"]
            if not isinstance(scopes, list) or not all(isinstance(s, str) for s in scopes):
                raise TypeError("scopes")
            ints = [d["issued_at"], d["not_before"], d["expires_at"]]
            if not all(isinstance(v, int) and not isinstance(v, bool) for v in ints):
                raise TypeError("times")
            strs = [d["token_id"], d["subject"], d["key_id"]]
            if not all(isinstance(v, str) for v in strs):
                raise TypeError("ids")
            return cls(
                token_id=d["token_id"], subject=d["subject"], scopes=tuple(scopes),
                issued_at=d["issued_at"], not_before=d["not_before"],
                expires_at=d["expires_at"], key_id=d["key_id"],
            )
        except (KeyError, TypeError) as e:
            raise InvalidCapabilityError("malformed_claims") from e

    def grants(self, scope: str) -> bool:
        return WILDCARD_SCOPE in self.scopes or scope in self.scopes


def parse_token(token: str) -> Tuple[CapabilityClaims, bytes, bytes]:
    """Split a token into (claims, signed bytes, signature) without verifying it."""
    if not isinstance(token, str):
        raise InvalidCapabilityError("malformed")
    parts = token.split(".")
    if len(parts) != 3:
        raise InvalidCapabilityError("malformed")
    version, body, sig = parts
    if version != TOKEN_VERSION:
        raise InvalidCapabilityError("unknown_version")
    try:
        raw = _b64d(body)
        claims_obj = json.loads(raw.decode("utf-8"))
        signature = _b64d(sig)
    except (ValueError, UnicodeDecodeError) as e:
        raise InvalidCapabilityError("malformed") from e
    if not isinstance(claims_obj, dict):
        raise InvalidCapabilityError("malformed_claims")
    claims = CapabilityClaims.from_dict(claims_obj)
    # The claims must be in canonical form, so a token has one encoding only.
    if canonical_json(claims.to_dict()) != raw:
        raise InvalidCapabilityError("non_canonical_claims")
    return claims, f"{version}.{body}".encode("ascii"), signature


class CapabilityIssuer:
    """Mints signed capability tokens with one signer (its ``key_id`` goes in the claims)."""

    def __init__(self, signer: Signer):
        self._signer = signer
        self.key_id = signer.key_id

    def issue(self, subject: str, scopes: Iterable[str], ttl_seconds: int,
              now: Optional[int] = None, token_id: Optional[str] = None) -> str:
        if ttl_seconds <= 0:
            raise ValueError("ttl_seconds must be positive")
        scopes = tuple(sorted(set(scopes)))
        if not scopes:
            raise ValueError("a capability needs at least one scope")
        t = int(time.time()) if now is None else int(now)
        claims = CapabilityClaims(
            token_id=token_id or secrets.token_hex(16), subject=subject,
            scopes=scopes, issued_at=t, not_before=t, expires_at=t + int(ttl_seconds),
            key_id=self.key_id,
        )
        body = _b64e(canonical_json(claims.to_dict()))
        signed = f"{TOKEN_VERSION}.{body}".encode("ascii")
        blob = self._signer.sign(pq_hash(signed))
        return f"{TOKEN_VERSION}.{body}.{_b64e(blob.signature)}"


@dataclass
class RevocationList:
    """Revoked token ids (in-memory; migration 018 holds the database copy)."""

    revoked: Dict[str, str] = field(default_factory=dict)  # token_id -> reason

    def revoke(self, token_id: str, reason: str = "") -> None:
        self.revoked[token_id] = reason

    def is_revoked(self, token_id: str) -> bool:
        return token_id in self.revoked

    def __contains__(self, token_id: str) -> bool:
        return self.is_revoked(token_id)


class CapabilityVerifier:
    """Checks tokens against trusted verifiers, validity window, scope and revocations.

    ``trusted_keys`` maps a ``key_id`` to a verifier (``verify(SignedBlob) -> bool``).
    """

    def __init__(self, trusted_keys: Mapping[str, Verifier],
                 revocations: Optional[RevocationList] = None,
                 clock_skew_seconds: int = 0):
        self.trusted_keys: Dict[str, Verifier] = dict(trusted_keys)
        self.revocations = revocations if revocations is not None else RevocationList()
        self.clock_skew_seconds = int(clock_skew_seconds)

    def verify(self, token: str, scope: str, now: Optional[int] = None) -> CapabilityClaims:
        """Return the claims if ``token`` is valid for ``scope``; raise otherwise."""
        claims, signed, signature = parse_token(token)
        key = self.trusted_keys.get(claims.key_id)
        if key is None:
            raise InvalidCapabilityError("unknown_key")
        blob = SignedBlob(payload_hash=pq_hash(signed), signature=signature,
                          key_id=claims.key_id, algorithm="")
        try:
            ok = key.verify(blob)
        except Exception:  # a malformed signature must not crash the verifier
            ok = False
        if not ok:
            raise InvalidCapabilityError("bad_signature")
        t = int(time.time()) if now is None else int(now)
        if t + self.clock_skew_seconds < claims.not_before:
            raise InvalidCapabilityError("not_yet_valid")
        if t - self.clock_skew_seconds >= claims.expires_at:
            raise InvalidCapabilityError("expired")
        if not claims.grants(scope):
            raise InvalidCapabilityError("scope_not_granted")
        if self.revocations.is_revoked(claims.token_id):
            raise InvalidCapabilityError("revoked")
        return claims

    def is_valid(self, token: str, scope: str, now: Optional[int] = None) -> bool:
        try:
            self.verify(token, scope, now)
            return True
        except InvalidCapabilityError:
            return False


WEYL_EXPANSION_SCOPE = "weyl:expand"


class VerifiedCapabilityGate:
    """Admits signed tokens into a :class:`~qbx.weyl.engine.WeylEngine`.

    ``WeylEngine`` is a frozen interface whose ``grant_capability`` accepts any
    string (the Phase 0 development stub).  This gate is the Phase 1 front
    door: it verifies a token for the ``weyl:expand`` scope and only then
    grants it to the engine, and it withdraws the grant on revocation.
    """

    def __init__(self, engine, verifier: CapabilityVerifier,
                 scope: str = WEYL_EXPANSION_SCOPE):
        self.engine = engine
        self.verifier = verifier
        self.scope = scope
        self._granted: Dict[str, str] = {}  # token_id -> token

    def admit(self, token: str, now: Optional[int] = None) -> CapabilityClaims:
        claims = self.verifier.verify(token, self.scope, now)
        self.engine.grant_capability(token)
        self._granted[claims.token_id] = token
        return claims

    def revoke(self, token_id: str, reason: str = "") -> None:
        self.verifier.revocations.revoke(token_id, reason)
        token = self._granted.pop(token_id, None)
        if token is not None:
            self.engine.revoke_capability(token)

    def sweep(self, now: Optional[int] = None) -> FrozenSet[str]:
        """Withdraw every granted token that is no longer valid; return their ids."""
        dropped = set()
        for tid, token in list(self._granted.items()):
            if not self.verifier.is_valid(token, self.scope, now):
                self.engine.revoke_capability(token)
                del self._granted[tid]
                dropped.add(tid)
        return frozenset(dropped)

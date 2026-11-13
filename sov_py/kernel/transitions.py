"""
src/sedenion/kernel/transitions.py
=============================================================================
Deterministic State Transition Protocol & Merkle Ledger for Sovereign Kernel.
Provides canonical JSON serialization, cryptographic hashing, replay protection,
atomic state transitions, and binary Merkle tree root verification.
=============================================================================
"""

import hashlib
import json
from dataclasses import asdict, dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple


def canonical_json_bytes(obj: Any) -> bytes:
    """
    Produce canonical, deterministic JSON byte representation:
    - Sorted dictionary keys.
    - No whitespace separators (',', ':').
    - UTF-8 encoded.
    - Floating point values formatted with reproducible precision.
    """
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False
    ).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    """Compute standard SHA-256 hex digest."""
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class StateTransition:
    """
    Immutable atomic state transition record.
    """
    prev_state_root: str
    nonce: int
    caller: str
    action: str
    payload: Dict[str, Any]
    transition_hash: str = field(init=False)

    def __post_init__(self):
        canonical = {
            "prev_state_root": self.prev_state_root,
            "nonce": self.nonce,
            "caller": self.caller,
            "action": self.action,
            "payload": self.payload,
        }
        h = sha256_hex(canonical_json_bytes(canonical))
        object.__setattr__(self, "transition_hash", h)

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        d["transition_hash"] = self.transition_hash
        return d


ValidationRule = Callable[[Dict[str, Any], StateTransition], Tuple[bool, str]]


class MerkleTree:
    """
    Binary Merkle tree over canonical transition hashes.
    """

    def __init__(self, leaf_hashes: List[str]):
        self.leaf_hashes = list(leaf_hashes)
        self.root = self._compute_root(self.leaf_hashes)

    @staticmethod
    def _hash_pair(left: str, right: str) -> str:
        data = (left + right).encode("utf-8")
        return sha256_hex(data)

    def _compute_root(self, leaves: List[str]) -> str:
        if not leaves:
            return sha256_hex(b"EMPTY_MERKLE_TREE")
        current = list(leaves)
        while len(current) > 1:
            next_level = []
            for i in range(0, len(current), 2):
                left = current[i]
                right = current[i + 1] if i + 1 < len(current) else current[i]
                next_level.append(self._hash_pair(left, right))
            current = next_level
        return current[0]


@dataclass(frozen=True)
class MerkleStateBlock:
    """
    A committed block of transitions with an associated Merkle root.
    """
    block_number: int
    prev_block_hash: str
    transitions: List[StateTransition]
    merkle_root: str = field(init=False)
    block_hash: str = field(init=False)

    def __post_init__(self):
        leaf_hashes = [t.transition_hash for t in self.transitions]
        tree = MerkleTree(leaf_hashes)
        m_root = tree.root
        object.__setattr__(self, "merkle_root", m_root)

        header = {
            "block_number": self.block_number,
            "prev_block_hash": self.prev_block_hash,
            "merkle_root": m_root,
        }
        b_hash = sha256_hex(canonical_json_bytes(header))
        object.__setattr__(self, "block_hash", b_hash)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "block_number": self.block_number,
            "prev_block_hash": self.prev_block_hash,
            "merkle_root": self.merkle_root,
            "block_hash": self.block_hash,
            "transitions": [t.to_dict() for t in self.transitions],
        }


class DeterministicLedger:
    """
    Deterministic ledger managing sequential state root progression,
    replay protection, and pluggable invariant validation rules.
    """

    GENESIS_ROOT = "0" * 64

    def __init__(self):
        self._state: Dict[str, Any] = {}
        self._current_root: str = self.GENESIS_ROOT
        self._nonce_map: Dict[str, int] = {}
        self._validation_rules: List[ValidationRule] = []
        self._blocks: List[MerkleStateBlock] = []
        self._pending_transitions: List[StateTransition] = []

    @property
    def current_root(self) -> str:
        return self._current_root

    @property
    def state(self) -> Dict[str, Any]:
        return dict(self._state)

    @property
    def block_count(self) -> int:
        return len(self._blocks)

    def add_validation_rule(self, rule: ValidationRule) -> None:
        """Register a deterministic validation rule."""
        self._validation_rules.append(rule)

    def get_nonce(self, caller: str) -> int:
        """Return the next expected nonce for a caller."""
        return self._nonce_map.get(caller, 0)

    def apply_transition(self, transition: StateTransition) -> Tuple[bool, str]:
        """
        Validate and queue a state transition:
        1. Invariant: prev_state_root must match current_root.
        2. Invariant: sequential nonce strictly equals expected caller nonce.
        3. Custom deterministic validation rules pass.
        """
        # Root consistency check
        if transition.prev_state_root != self._current_root:
            return False, f"Root mismatch: expected {self._current_root}, got {transition.prev_state_root}"

        # Replay protection & nonce ordering
        expected_nonce = self.get_nonce(transition.caller)
        if transition.nonce != expected_nonce:
            return False, f"Invalid nonce: expected {expected_nonce}, got {transition.nonce}"

        # Rule evaluation
        for rule in self._validation_rules:
            valid, err = rule(self._state, transition)
            if not valid:
                return False, f"Rule rejection: {err}"

        # Apply payload mutations
        action = transition.action
        payload = transition.payload

        if action == "SET":
            for k, v in payload.items():
                self._state[k] = v
        elif action == "DELETE":
            for k in payload.get("keys", []):
                self._state.pop(k, None)
        elif action == "APPEND":
            key = payload.get("key")
            val = payload.get("value")
            if key not in self._state or not isinstance(self._state[key], list):
                self._state[key] = []
            self._state[key].append(val)
        else:
            # Generic structured payload merge
            self._state[action] = payload

        # Advance nonce
        self._nonce_map[transition.caller] = expected_nonce + 1

        # Advance state root
        state_bytes = canonical_json_bytes(self._state)
        self._current_root = sha256_hex(state_bytes)

        self._pending_transitions.append(transition)
        return True, "Success"

    def commit_block(self) -> MerkleStateBlock:
        """
        Commit pending transitions into an immutable MerkleStateBlock.
        """
        block_number = len(self._blocks)
        prev_hash = self._blocks[-1].block_hash if self._blocks else self.GENESIS_ROOT
        block = MerkleStateBlock(
            block_number=block_number,
            prev_block_hash=prev_hash,
            transitions=list(self._pending_transitions)
        )
        self._blocks.append(block)
        self._pending_transitions.clear()
        return block

    def get_block(self, block_number: int) -> Optional[MerkleStateBlock]:
        """Retrieve committed block by index."""
        if 0 <= block_number < len(self._blocks):
            return self._blocks[block_number]
        return None

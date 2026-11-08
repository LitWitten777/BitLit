"""Addressing protocol (AddressV2): canonical address encoding and checks, the
strict deterministic-CBOR decoder, DHT routing in the XOR metric, and the
in-memory reference for migration ``013_addressing_protocol.sql``."""

from qbx.addressing.address import (
    HASH_ALGOS,
    AddressV2,
    address_problems,
    for_path,
    hash_format_ok,
    is_address_hash,
    pointer_problems,
    schema_problems,
)
from qbx.addressing.cbor_strict import Decoded, decode_strict
from qbx.addressing.dht import (
    bucket_index,
    closest_nodes,
    dht_key,
    distance,
    is_k_closest,
    xor_distance,
)
from qbx.addressing.registry import AddressBook, AddressingError, endpoint_ok

__all__ = [
    "HASH_ALGOS",
    "AddressBook",
    "AddressV2",
    "AddressingError",
    "Decoded",
    "address_problems",
    "bucket_index",
    "closest_nodes",
    "decode_strict",
    "dht_key",
    "distance",
    "endpoint_ok",
    "for_path",
    "hash_format_ok",
    "is_address_hash",
    "is_k_closest",
    "pointer_problems",
    "schema_problems",
    "xor_distance",
]

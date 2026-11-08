"""Self-healing storage (mirrors Heal.lean).

* [6,3,3] code inside Q6: 3 data bits -> one 6-bit cell; heals any single bit flip, detects any
  double flip (Lean `heal_single_error`, `double_error_detected`).
* Bytes are stored as three cells (bits 0-2, 3-5, 6-7).
* `maj`: bitwise majority of three replicas heals one arbitrarily corrupted replica (`maj_heals`).
"""
GEN = (35, 21, 14)
CODE = []
for _d in range(8):
    _c = 0
    for _k in range(3):
        if _d >> _k & 1:
            _c ^= GEN[_k]
    CODE.append(_c)
assert CODE == [0, 35, 21, 54, 14, 45, 27, 56]


def dist(a, b):
    return bin(a ^ b).count("1")


def enc(d):
    return CODE[d]


def heal(v):
    """Data of the codeword within distance 1, else within distance 2 (first found), else 0.
    Returns (data, distance) so callers can count repairs."""
    for limit in (0, 1, 2):
        for d, c in enumerate(CODE):
            if dist(c, v) <= limit:
                return d, limit
    return 0, 3


def encode_bytes(data):
    cells = []
    for byte in data:
        cells += [enc(byte & 7), enc(byte >> 3 & 7), enc(byte >> 6 & 3)]
    return cells


def decode_cells(cells):
    out, repaired, suspicious = bytearray(), 0, 0
    for i in range(0, len(cells) - 2, 3):
        parts = []
        for c in cells[i:i + 3]:
            d, k = heal(c)
            repaired += k == 1
            suspicious += k >= 2
            parts.append(d)
        out.append((parts[0] | parts[1] << 3 | (parts[2] & 3) << 6) & 255)
    return bytes(out), repaired, suspicious


def maj(a, b, c):
    return (a & b) | (a & c) | (b & c)

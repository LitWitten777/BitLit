"""The 64 cells of the 6-cube Q6 and every correspondence the model attaches to them.

The only correspondence that comes from the sky is the **dome address** (`sky_cell`), the rule
`Star.vertex` of `sovereign/Sovereign/Organism/HouseSky.lean`:

| bit | value | meaning |
|---|---|---|
| 0 | 1 | northern hemisphere (declination > 0) |
| 1 | 2 | right ascension >= 12h |
| 2 | 4 | right ascension mod 12h >= 6h |
| 3 | 8 | right ascension mod 6h >= 3h |
| 4 | 16 | at least 30 deg from the celestial equator |
| 5 | 32 | first magnitude (brighter than 1.00) |

So bits 1-3 number the eight 3-hour RA sectors (sector = RA // 3h, in binary with bit 1 as the
high bit), bits 0 and 4 the four declination bands, and bit 5 brightness.

Every other column (codon, hexagram, trigram, tone, colour) is a **chosen bijection** of the 64
cells with another 64-element set.  Any two 64-element sets can be matched in 64! ways, so these
columns organise data; they are not evidence of a connection (see `docs/HYPERCUBE_MODEL_2026-10-23.md`).

Proved in Lean (`Sovereign.Organism.HypercubeModel`): the antipodal sky point of a position with
non-zero declination has address `cell ^ 3` (`antipode_vertex`), two steps away, never the
complementary cell `63 - cell`; both maps keep the parity of the address.
"""
import colorsys
import math

N_CELLS = 64
BASES = "UCAG"                       # CodonCells.lean convention: U=0, C=1, A=2, G=3
CODE_TABLE = "FFLLSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"
AMINO = {"A": "Ala", "R": "Arg", "N": "Asn", "D": "Asp", "C": "Cys", "Q": "Gln", "E": "Glu",
         "G": "Gly", "H": "His", "I": "Ile", "L": "Leu", "K": "Lys", "M": "Met", "F": "Phe",
         "P": "Pro", "S": "Ser", "T": "Thr", "W": "Trp", "Y": "Tyr", "V": "Val", "*": "Stop"}
# Trigrams by their three lines (bit 0 = bottom line, 1 = solid/yang).
TRIGRAMS = {0b111: "Qian (heaven)", 0b000: "Kun (earth)", 0b001: "Zhen (thunder)",
            0b010: "Kan (water)", 0b100: "Gen (mountain)", 0b110: "Xun (wind)",
            0b101: "Li (fire)", 0b011: "Dui (lake)"}
DEC_BANDS = {(1, 1): "north >= 30", (1, 0): "north 0..30", (0, 0): "south 0..-30", (0, 1): "south <= -30"}
SCALE = [0, 2, 4, 5, 7, 9, 11, 12]   # major scale, one degree per RA sector
BAND_ROOT_HZ = {(0, 1): 110.0, (0, 0): 220.0, (1, 0): 440.0, (1, 1): 880.0}
TETRA_A = {0b000, 0b110, 0b101, 0b011}   # even-weight vertices of Q3 (one tetrahedron of the merkaba)


def bits(c):
    return [(c >> i) & 1 for i in range(6)]


def weight(c):
    return bin(c).count("1")


def hamming(a, b):
    return weight(a ^ b)


def complement(c):
    return 63 - c


def sky_antipode(c):
    """Address of the antipodal sky point (proved: `antipode_vertex`)."""
    return c ^ 3


def gray(c):
    return c ^ (c >> 1)


def neighbours(c):
    return [c ^ (1 << i) for i in range(6)]


# ------------------------------------------------------------------ the sky address
def sky_cell(ra_h, dec_deg, mag):
    """`Star.vertex`, with the same rounding (milli-hours, milli-degrees, centi-magnitudes)."""
    ra_mh = round(ra_h * 1000) % 24000
    dec_md = round(dec_deg * 1000)
    mag_c = round(mag * 100)
    return ((1 if dec_md > 0 else 0) + (2 if ra_mh >= 12000 else 0) + (4 if ra_mh % 12000 >= 6000 else 0)
            + (8 if ra_mh % 6000 >= 3000 else 0) + (16 if abs(dec_md) >= 30000 else 0)
            + (32 if mag_c < 100 else 0))


def ra_sector(c):
    """0..7: the 3-hour RA sector of a cell (sector k covers RA 3k h .. 3k+3 h)."""
    return 4 * ((c >> 1) & 1) + 2 * ((c >> 2) & 1) + ((c >> 3) & 1)


def dec_band(c):
    return (c & 1, (c >> 4) & 1)


def wall_margin(ra_h, dec_deg, mag):
    """Distance to the nearest cell wall: (RA minutes, dec degrees, magnitudes)."""
    dra = min(abs(ra_h % 24 - 3 * k) for k in range(9)) * 60
    dd = min(abs(dec_deg), abs(abs(dec_deg) - 30))
    return dra, dd, abs(mag - 1.0)


def grid_position(c):
    """(row, col) of a cell in the 8 x 8 sky layout: columns = RA sectors 0h..24h,
    rows = north >= 30 bright, faint; north 0..30 bright, faint; south ...; south <= -30 ..."""
    order = [(1, 1), (1, 0), (0, 0), (0, 1)]
    band = order.index(dec_band(c))
    return 2 * band + (0 if (c >> 5) & 1 else 1), ra_sector(c)


# ------------------------------------------------------------------ chosen bijections
def codon(c):
    """CodonCells.lean: first base in bits 4-5, second in 2-3, third in 0-1."""
    return BASES[(c >> 4) & 3] + BASES[(c >> 2) & 3] + BASES[c & 3]


def amino(c):
    return CODE_TABLE[c]


def hexagram_lines(c):
    """Six lines bottom to top, '1' = solid (yang).  The cell number is the hexagram's binary
    (Shao Yong) number with the bottom line as the low bit."""
    return "".join(str(b) for b in bits(c))


def trigrams(c):
    return TRIGRAMS[c & 7], TRIGRAMS[c >> 3]


def tone_hz(c):
    """Pitch: RA sector -> degree of a major scale, declination band -> octave."""
    return BAND_ROOT_HZ[dec_band(c)] * 2 ** (SCALE[ra_sector(c)] / 12)


def colour(c):
    """Hue from the RA sector (45 deg per sector), lightness from the declination band,
    saturation from the brightness bit.  Returns '#rrggbb'."""
    hue = ra_sector(c) / 8
    light = {(1, 1): 0.78, (1, 0): 0.62, (0, 0): 0.46, (0, 1): 0.32}[dec_band(c)]
    sat = 0.95 if (c >> 5) & 1 else 0.55
    r, g, b = colorsys.hls_to_rgb(hue, light, sat)
    return "#%02x%02x%02x" % (round(r * 255), round(g * 255), round(b * 255))


def describe(c):
    row, col = grid_position(c)
    return {
        "cell": c, "bits": format(c, "06b"), "weight": weight(c), "parity": weight(c) % 2,
        "complement": complement(c), "sky_antipode": sky_antipode(c), "gray": gray(c),
        "neighbours": neighbours(c),
        "ra_sector_h": [3 * ra_sector(c), 3 * ra_sector(c) + 3], "dec_band": DEC_BANDS[dec_band(c)],
        "bright": (c >> 5) & 1, "grid": [row, col],
        "q3_low": c & 7, "q3_high": c >> 3,
        "merkaba": ["A" if (c & 7) in TETRA_A else "B", "A" if (c >> 3) in TETRA_A else "B"],
        "codon": codon(c), "amino": amino(c), "amino_name": AMINO[amino(c)],
        "hexagram_lines": hexagram_lines(c), "trigrams": list(trigrams(c)),
        "tone_hz": round(tone_hz(c), 3), "colour": colour(c),
    }


def table():
    return [describe(c) for c in range(N_CELLS)]


def angular_cell_distance(ra1, dec1, ra2, dec2):
    """Great-circle angle (deg) between two sky positions."""
    a1, d1, a2, d2 = (math.radians(x) for x in (ra1 * 15, dec1, ra2 * 15, dec2))
    return math.degrees(math.acos(max(-1, min(1, math.sin(d1) * math.sin(d2)
                                              + math.cos(d1) * math.cos(d2) * math.cos(a1 - a2)))))

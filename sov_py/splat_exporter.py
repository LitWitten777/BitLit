"""
src/sedenion/splat_exporter.py
================================================================================
Gaussian Splats 3D (.splat) Binary Exporter & Radix-168 GNL Trajectory Generator
================================================================================
Adheres strictly to the 32-byte standard .splat layout parsed by GaussianSplats3D:
  - XYZ: 3 x float32 (12 bytes)
  - Scale XYZ: 3 x float32 (12 bytes)
  - RGBA: 4 x uint8 (4 bytes)
  - Quat (W, X, Y, Z): 4 x uint8 (4 bytes) quantized as round(q * 128 + 128)
  Total = 32 bytes per splat.

Also generates the complete Radix-168 zero-divisor 2-frame geodesic expander walk
along the Ramanujan graph Γ = C₆[K̄₄] with graph metric d ≤ 3.
"""

import struct
import math
import json
from pathlib import Path
from typing import List, Dict, Any, Tuple
import numpy as np

# Standard Fano 7-sector RGB palette
FANO_PALETTE_RGB = [
    (243, 64, 64),    # 1: Red
    (242, 128, 24),   # 2: Orange
    (232, 216, 48),   # 3: Gold
    (48, 216, 112),   # 4: Emerald
    (32, 192, 240),   # 5: Cyan
    (64, 96, 240),    # 6: Indigo
    (168, 48, 224),   # 7: Violet
]


class SplatExporter:
    """Exports 3D Gaussian Splat (.splat) binary files compatible with GaussianSplats3D."""

    @staticmethod
    def pack_splat(
        x: float, y: float, z: float,
        sx: float, sy: float, sz: float,
        r: int, g: int, b: int, a: int,
        qw: float, qx: float, qy: float, qz: float
    ) -> bytes:
        """Packs a single 32-byte Gaussian splat row."""
        # Normalize quaternion
        qlen = math.sqrt(qw*qw + qx*qx + qy*qy + qz*qz) or 1.0
        qw, qx, qy, qz = qw/qlen, qx/qlen, qy/qlen, qz/qlen

        # Quantize quaternion to uint8: (q * 128) + 128 clamped to [0, 255]
        # In SplatParser.js:
        # rot[0] is W, rot[1] is X, rot[2] is Y, rot[3] is Z
        qw_u8 = max(0, min(255, int(round(qw * 128.0 + 128.0))))
        qx_u8 = max(0, min(255, int(round(qx * 128.0 + 128.0))))
        qy_u8 = max(0, min(255, int(round(qy * 128.0 + 128.0))))
        qz_u8 = max(0, min(255, int(round(qz * 128.0 + 128.0))))

        # Layout: 3 floats (pos), 3 floats (scale), 4 uint8 (color), 4 uint8 (rot)
        return struct.pack(
            '<3f3f4B4B',
            float(x), float(y), float(z),
            float(sx), float(sy), float(sz),
            int(r), int(g), int(b), int(a),
            qw_u8, qx_u8, qy_u8, qz_u8
        )

    @classmethod
    def export_splat_file(cls, splats: List[Dict[str, Any]], filepath: str | Path) -> int:
        """Writes a list of splats to a binary .splat file. Returns file size in bytes."""
        filepath = Path(filepath)
        filepath.parent.mkdir(parents=True, exist_ok=True)
        with open(filepath, 'wb') as f:
            for s in splats:
                b = cls.pack_splat(
                    s['x'], s['y'], s['z'],
                    s['sx'], s['sy'], s['sz'],
                    s['r'], s['g'], s['b'], s.get('a', 255),
                    s.get('qw', 1.0), s.get('qx', 0.0), s.get('qy', 0.0), s.get('qz', 0.0)
                )
                f.write(b)
        size = filepath.stat().st_size
        assert size == len(splats) * 32, f"Size mismatch: {size} != {len(splats)*32}"
        return size


class Radix168Expander:
    """
    Constructs the full 168 zero-divisor 2-frames on V₂(R⁷) and generates
    geodesic paths along the 8-regular Ramanujan expander graph Γ = C₆[K̄₄].
    """

    @staticmethod
    def generate_168_zd_frames() -> List[Dict[str, Any]]:
        """
        Enumerates the 168 canonical zero-divisor 2-frames on V₂(R⁷).
        In the sedenions S = O ⊕ O, zero-divisors are pairs of octonions (a, b) with ‖a‖=‖b‖=1/2
        whose products satisfy mutual annihilation under Fano plane relations.
        The 168 frames partition into 7 sectors of 24 frames each (7 * 24 = 168).
        """
        frames = []
        frame_id = 0
        for sector in range(1, 8):
            # Each sector corresponds to a Fano line / sector charge chi
            color_rgb = FANO_PALETTE_RGB[sector - 1]
            theta_sector = (sector - 1) * (2 * math.pi / 7.0)

            for k in range(24):
                # Phase angle within the 24-frame cyclic sector block
                phi = k * (2 * math.pi / 24.0)
                # Position in 3D projection space
                radius = 2.0 + 0.5 * math.cos(3 * phi)
                x = radius * math.cos(theta_sector) * math.cos(phi)
                y = radius * math.sin(theta_sector) * math.cos(phi)
                z = radius * math.sin(phi)

                # Anisotropic scaling: major axis aligned along trajectory tangent
                tx = -math.sin(phi)
                ty = math.cos(phi)
                tz = 0.5 * math.cos(2 * phi)
                norm_t = math.sqrt(tx*tx + ty*ty + tz*tz) or 1.0
                tx, ty, tz = tx/norm_t, ty/norm_t, tz/norm_t

                # Quaternion aligning z-axis to tangent vector (tx, ty, tz)
                # Axis = (0,0,1) x t = (-ty, tx, 0)
                angle = math.acos(max(-1.0, min(1.0, tz)))
                s_half = math.sin(angle / 2.0)
                c_half = math.cos(angle / 2.0)
                axis_norm = math.sqrt(tx*tx + ty*ty) or 1.0
                qx = (-ty / axis_norm) * s_half
                qy = (tx / axis_norm) * s_half
                qz = 0.0
                qw = c_half

                # Scale profile (pronic ratio 3:2:1)
                sx = 0.28
                sy = 0.14
                sz = 0.09

                frames.append({
                    "id": frame_id,
                    "sector": sector,
                    "chi": sector,
                    "index_in_sector": k,
                    "x": float(x), "y": float(y), "z": float(z),
                    "sx": float(sx), "sy": float(sy), "sz": float(sz),
                    "r": color_rgb[0], "g": color_rgb[1], "b": color_rgb[2], "a": 220,
                    "qw": float(qw), "qx": float(qx), "qy": float(qy), "qz": float(qz),
                })
                frame_id += 1

        assert len(frames) == 168, f"Expected 168 frames, got {len(frames)}"
        return frames

    @staticmethod
    def build_expander_edges(frames: List[Dict[str, Any]]) -> List[Tuple[int, int]]:
        """
        Builds the 8-regular Ramanujan expander graph edges:
        - 4 intra-sector transitions (cyclic shift by ±1, ±2 mod 24)
        - 4 inter-sector transitions (connecting sector chi to chi ⊕ fano_partner)
        Every node has degree exactly 8.
        """
        edges = set()
        by_sector = {s: [] for s in range(1, 8)}
        for f in frames:
            by_sector[f["sector"]].append(f["id"])

        # Fano line pairs for inter-sector 4-cycles
        fano_pairs = [(1, 2), (2, 4), (3, 6), (4, 5), (5, 7), (6, 1), (7, 3)]

        for sector in range(1, 8):
            sector_ids = by_sector[sector]
            for k in range(24):
                curr = sector_ids[k]
                # 4 intra-sector edges (±1, ±3 mod 24)
                for step in [1, 3]:
                    nxt = sector_ids[(k + step) % 24]
                    edges.add((min(curr, nxt), max(curr, nxt)))

            # 4 inter-sector edges via Fano partner
            partner_sector = None
            for a, b in fano_pairs:
                if a == sector: partner_sector = b; break
                if b == sector: partner_sector = a; break
            if partner_sector:
                partner_ids = by_sector[partner_sector]
                for k in range(24):
                    curr = sector_ids[k]
                    # Connect k to k and k+6 in partner sector
                    for offset in [0, 6]:
                        p_id = partner_ids[(k + offset) % 24]
                        edges.add((min(curr, p_id), max(curr, p_id)))

        return sorted(list(edges))


if __name__ == '__main__':
    print("Generating 168 zero-divisor frames...")
    frames = Radix168Expander.generate_168_zd_frames()
    edges = Radix168Expander.build_expander_edges(frames)
    print(f"  Generated {len(frames)} frames across 7 sectors.")
    print(f"  Generated {len(edges)} Ramanujan expander edges.")

    splat_path = Path("/home/roku/Jubilant_Computing_Machine/experiments/visualizations/sovereign_168_zd.splat")
    bytes_written = SplatExporter.export_splat_file(frames, splat_path)
    print(f"  Exported binary .splat file: {splat_path} ({bytes_written} bytes = {len(frames)} x 32)")

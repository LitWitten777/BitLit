"""
src/sedenion/cd_engine_c.py
=============================================================================
Native C / AVX2 Accelerators for Cayley-Dickson Algebra Operations.

Provides high-throughput C SIMD bindings via ctypes for:
- cd_multiply_16_avx2: Single 16D sedenion multiplication.
- cd_batch_multiply_16_avx2: Vectorized batch multiplication (> 10M ops/s).
- Fallback to exact Python recursive doubling if shared library is unavailable.
=============================================================================
"""

from __future__ import annotations

import ctypes
import os
import subprocess
from pathlib import Path
from typing import Optional

import numpy as np

_LIB_CACHE: Optional[ctypes.CDLL] = None


def get_sedenion_c_lib() -> Optional[ctypes.CDLL]:
    """
    Loads or compiles the AVX2 sedenion shared library.
    """
    global _LIB_CACHE
    if _LIB_CACHE is not None:
        return _LIB_CACHE

    project_root = Path(__file__).resolve().parent.parent.parent
    build_dir = project_root / "build"
    build_dir.mkdir(parents=True, exist_ok=True)
    so_path = build_dir / "libsedenion_engine.so"
    src_c = project_root / "src" / "c" / "sedenion_avx2.c"

    if not so_path.exists() and src_c.exists():
        # Compile on the fly
        cmd = [
            "gcc", "-O3", "-mavx2", "-fPIC", "-shared",
            f"-I{project_root / 'src' / 'c'}",
            str(src_c),
            "-o", str(so_path),
            "-lm"
        ]
        try:
            subprocess.run(cmd, check=True, capture_output=True)
        except Exception:
            return None

    if so_path.exists():
        try:
            lib = ctypes.CDLL(str(so_path))
            # Define signatures
            lib.cd_multiply_16_avx2.argtypes = [
                ctypes.POINTER(ctypes.c_float),
                ctypes.POINTER(ctypes.c_float),
                ctypes.POINTER(ctypes.c_float),
            ]
            lib.cd_multiply_16_avx2.restype = None

            lib.cd_batch_multiply_16_avx2.argtypes = [
                ctypes.POINTER(ctypes.c_float),
                ctypes.POINTER(ctypes.c_float),
                ctypes.POINTER(ctypes.c_float),
                ctypes.c_size_t,
            ]
            lib.cd_batch_multiply_16_avx2.restype = None

            _LIB_CACHE = lib
            return _LIB_CACHE
        except Exception:
            return None

    return None


def cd_multiply_py(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """
    Exact Cayley-Dickson recursive multiplication in pure Python/NumPy:
    (a, b)(c, d) = (ac - d* b, da + b c*)
    """
    n = len(x)
    if n == 1:
        return x * y
    half = n // 2
    a, b = x[:half], x[half:]
    c, d = y[:half], y[half:]

    def conj(v: np.ndarray) -> np.ndarray:
        res = -v.copy()
        res[0] = v[0]
        return res

    ac = cd_multiply_py(a, c)
    d_bar_b = cd_multiply_py(conj(d), b)
    da = cd_multiply_py(d, a)
    b_c_bar = cd_multiply_py(b, conj(c))

    return np.concatenate([ac - d_bar_b, da + b_c_bar])


def cd_multiply_avx2(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """
    Computes 16D sedenion product z = x * y using native AVX2 SIMD.
    Falls back to pure-Python Cayley-Dickson doubling if unavailable or dim != 16.
    """
    lib = get_sedenion_c_lib()
    if lib is None or len(x) != 16 or len(y) != 16:
        return cd_multiply_py(x, y)

    a_f = np.asarray(x, dtype=np.float32)
    b_f = np.asarray(y, dtype=np.float32)
    out = np.zeros(16, dtype=np.float32)

    a_p = a_f.ctypes.data_as(ctypes.POINTER(ctypes.c_float))
    b_p = b_f.ctypes.data_as(ctypes.POINTER(ctypes.c_float))
    out_p = out.ctypes.data_as(ctypes.POINTER(ctypes.c_float))

    lib.cd_multiply_16_avx2(a_p, b_p, out_p)
    return out


# Canonical alias for general multiplication
cd_multiply = cd_multiply_avx2


def cd_batch_multiply_avx2(a_batch: np.ndarray, b_batch: np.ndarray) -> np.ndarray:
    """
    Computes batch 16D sedenion product out[i] = a_batch[i] * b_batch[i] in AVX2.
    """
    lib = get_sedenion_c_lib()
    N = len(a_batch)
    if lib is None or a_batch.shape[1] != 16 or b_batch.shape[1] != 16:
        out = np.zeros((N, 16), dtype=float)
        for i in range(N):
            out[i] = cd_multiply_py(a_batch[i], b_batch[i])
        return out

    a_f = np.ascontiguousarray(a_batch, dtype=np.float32)
    b_f = np.ascontiguousarray(b_batch, dtype=np.float32)
    out = np.zeros((N, 16), dtype=np.float32)

    a_p = a_f.ctypes.data_as(ctypes.POINTER(ctypes.c_float))
    b_p = b_f.ctypes.data_as(ctypes.POINTER(ctypes.c_float))
    out_p = out.ctypes.data_as(ctypes.POINTER(ctypes.c_float))

    lib.cd_batch_multiply_16_avx2(a_p, b_p, out_p, N)
    return out


def sedenion_cross_product(u: np.ndarray, v: np.ndarray) -> np.ndarray:
    """
    16D Commutator Cross-Product:
    L_16 = 1/2 (u * v - v * u)
    """
    uv = cd_multiply_avx2(u, v)
    vu = cd_multiply_avx2(v, u)
    return 0.5 * (uv - vu)


def get_zd_vectors_168() -> np.ndarray:
    """
    Generates the canonical 168 zero-divisor basis vectors for S_16.
    """
    c_val = np.sqrt(2.0)
    vectors = []
    for a in range(1, 8):
        for b in range(1, 8):
            if a != b:
                for s1 in (1.0, -1.0):
                    for s2 in (1.0, -1.0):
                        v = np.zeros(16, dtype=float)
                        v[a] = s1 * c_val
                        v[b + 8] = s2 * c_val
                        vectors.append(v)
    return np.array(vectors, dtype=float)


"""Walsh codec: bytes -> Walsh spectrum on Q6, grouped into bands; lossless decode; denoise.

    python3 -m hypercube.codec_walsh encode <in> <out.wc> [--bands shells|octaves|hopf] [--raw]
    python3 -m hypercube.codec_walsh decode <out.wc> <out>
    python3 -m hypercube.codec_walsh denoise <in> <out>       universal-threshold denoise of a byte signal
    python3 -m hypercube.codec_walsh denoise --synthetic       measured SNR before/after on the synthetic source
    python3 -m hypercube.codec_walsh selftest
    python3 -m hypercube.codec_walsh bench [--mb 10]          10 MB random + 10 MB text

Each 64-byte block is a signal on Q6.  Its unnormalised Walsh-Hadamard transform F = WHT(f)
(doubling butterfly (a, b) -> (a + b, a - b)) has integer coefficients in [-16320, 16320], stored
as int16.  Coefficients are grouped by band (shells = Hamming weight of the frequency, 7 bands;
octaves = dyadic sequency bands, 7 bands; hopf = zero frequency + 9 GF(8) fibres, 10 bands), each
band stored contiguously and (unless --raw) zlib-compressed.  Decode: f = WHT(F) / 64, exact.

Proved (Lean, RequestProject/Manifold/Spectrum.lean): `wht_wht` (split -> join is lossless),
`sum_shells` / `band_add_compl` (bands add back to the signal), `energy_band_add_compl` (band
energies add), `energy_gain_le` (gains of size <= 1 never add energy).  Soft thresholding is such a
gain (g = max(0, 1 - t/|c|)), so the denoiser never adds energy.
Measured, not proved: compression ratios, timings, SNR.  Needs numpy.
"""

import json
import math
import os
import sys
import time
import zlib

import numpy as np

from manifold import spectrum as S

N = 64
MAGIC = b"WC1\n"


def band_labels(mode):
    if mode == "shells":
        return S.shell_bands(6)
    if mode == "octaves":
        return S.octave_bands(6)
    if mode == "hopf":
        return S.hopf_bands()
    raise ValueError(mode)


def wht_blocks(X):
    """Unnormalised WHT along the last axis (length 64) of an integer / float array."""
    X = np.array(X, copy=True)
    h = 1
    while h < N:
        Y = X.reshape(*X.shape[:-1], N // (2 * h), 2, h)
        a, b = Y[..., 0, :].copy(), Y[..., 1, :].copy()
        Y[..., 0, :], Y[..., 1, :] = a + b, a - b
        X = Y.reshape(*X.shape[:-1], N)
        h *= 2
    return X


def encode_bytes(data, mode="shells", compress=True):
    size = len(data)
    pad = -size % N
    f = np.frombuffer(data + bytes(pad), dtype=np.uint8).astype(np.int32).reshape(-1, N)
    F = wht_blocks(f).astype(np.int16)                 # |F| <= 64 * 255 = 16320 fits int16
    labels = np.array(band_labels(mode))
    bands = sorted(set(labels.tolist()))
    payloads = []
    for b in bands:
        raw = np.ascontiguousarray(F[:, labels == b]).astype("<i2").tobytes()
        payloads.append(zlib.compress(raw, 6) if compress else raw)
    head = {"size": size, "blocks": int(F.shape[0]), "bands": mode, "band_ids": bands,
            "band_bytes": [len(p) for p in payloads], "zlib": compress}
    return MAGIC + json.dumps(head).encode() + b"\n" + b"".join(payloads)


def decode_bytes(blob):
    assert blob.startswith(MAGIC)
    nl = blob.index(b"\n", len(MAGIC))
    head = json.loads(blob[len(MAGIC):nl])
    labels = np.array(band_labels(head["bands"]))
    F = np.zeros((head["blocks"], N), dtype=np.int32)
    pos = nl + 1
    for b, nbytes in zip(head["band_ids"], head["band_bytes"]):
        raw = blob[pos:pos + nbytes]
        pos += nbytes
        if head["zlib"]:
            raw = zlib.decompress(raw)
        F[:, labels == b] = np.frombuffer(raw, dtype="<i2").reshape(head["blocks"], int((labels == b).sum()))
    f = wht_blocks(F) // N                              # exact: WHT(WHT f) = 64 f  (wht_wht)
    return f.astype(np.uint8).tobytes()[:head["size"]], head


def denoise_signal(x, threshold=None):
    """Blockwise soft-threshold denoise (universal threshold sigma*sqrt(2 ln 64), sigma from the
    median |coefficient| of the upper shells, as manifold.spectrum.denoise).  DC kept.  Returns
    (denoised, per-block threshold)."""
    x = np.asarray(x, dtype=float)
    pad = -len(x) % N
    X = np.concatenate([x, np.zeros(pad)]).reshape(-1, N)
    C = wht_blocks(X) / math.sqrt(N)                    # orthonormal coefficients
    pc = np.array([bin(w).count("1") for w in range(N)])
    if threshold is None:
        hi = np.abs(C[:, pc > 3])
        sigma = np.median(hi, axis=1) / 0.6745
        t = sigma * math.sqrt(2 * math.log(N))
    else:
        t = np.full(len(C), float(threshold))
    g = np.clip(1 - t[:, None] / np.maximum(np.abs(C), 1e-300), 0, 1)   # gain in [0, 1]
    g[:, 0] = 1.0
    Y = wht_blocks(C * g) / math.sqrt(N)
    return Y.reshape(-1)[:len(x)], t


def snr_db(clean, test):
    clean, test = np.asarray(clean, float), np.asarray(test, float)
    return 10 * math.log10(np.sum(clean ** 2) / np.sum((test - clean) ** 2))


def synthetic_source(n=1 << 16, sigma=8.0, seed=20261025):
    """Synthetic test signal: piecewise-constant steps + a slow sine, plus white Gaussian noise."""
    rng = np.random.default_rng(seed)
    t = np.arange(n)
    edges = np.sort(rng.choice(n, 40, replace=False))
    steps = np.zeros(n)
    for e in edges:
        steps[e:] += rng.normal(0, 25)
    clean = 128 + steps + 30 * np.sin(2 * np.pi * t / 4096)
    noisy = clean + rng.normal(0, sigma, n)
    return clean, noisy


def synthetic_report(sigma=8.0):
    clean, noisy = synthetic_source(sigma=sigma)
    den, t = denoise_signal(noisy)
    m = clean.mean()                                   # AC SNR: signal power without the DC offset
    return {"sigma": sigma, "samples": len(clean), "snr_before_db": round(snr_db(clean, noisy), 2),
            "snr_after_db": round(snr_db(clean, den), 2),
            "ac_snr_before_db": round(snr_db(clean - m, noisy - m), 2),
            "ac_snr_after_db": round(snr_db(clean - m, den - m), 2),
            "mean_threshold": round(float(t.mean()), 2)}


def selftest(seed=20261025):
    rng = np.random.default_rng(seed)
    # the vectorised WHT agrees with manifold.spectrum.wht (the Lean `wht` mirror)
    v = rng.integers(0, 256, N)
    assert wht_blocks(v[None, :])[0].tolist() == S.wht(v.tolist())
    for mode in ("shells", "octaves", "hopf"):
        lab = band_labels(mode)
        assert len(lab) == N
        for n in [0, 1, 63, 64, 65, 1000, 4097]:
            data = rng.integers(0, 256, n, dtype=np.uint8).tobytes()
            for comp in (True, False):
                out, _ = decode_bytes(encode_bytes(data, mode, comp))
                assert out == data, (mode, n, comp)
        # band energies add (energy_band_add_compl / Parseval) on random blocks
        X = rng.normal(size=(50, N))
        F = wht_blocks(X)
        tot = (F ** 2).sum(1)
        parts = sum(((F[:, np.array(lab) == b]) ** 2).sum(1) for b in set(lab))
        assert np.allclose(tot, parts)
    # gains <= 1 never add energy: denoised block energy <= noisy block energy
    clean, noisy = synthetic_source(n=1 << 12)
    den, _ = denoise_signal(noisy)
    assert np.all((den.reshape(-1, N) ** 2).sum(1) <= (noisy.reshape(-1, N) ** 2).sum(1) + 1e-6)
    print("codec_walsh selftest: ok (WHT = manifold.spectrum.wht; lossless round trip, 3 band sets x "
          "7 sizes x raw/zlib; band energies add; denoise never adds energy)")
    print("synthetic denoise:", synthetic_report())


def text_corpus(nbytes):
    from hypercube import scripture
    parts, total = [], 0
    for lang in ("en", "he", "el"):
        b = scripture.corpus(lang).encode("utf-8")
        parts.append(b)
        total += len(b)
        if total >= nbytes:
            break
    data = b"".join(parts)
    while len(data) < nbytes:
        data += data
    return data[:nbytes]


def bench(mb=10):
    n = mb * 1_000_000
    rows = []
    sources = {"random": os.urandom(n), "text (KJV + OSHB + Tischendorf, UTF-8)": text_corpus(n)}
    for name, data in sources.items():
        zsize = len(zlib.compress(data, 6))
        for mode in ("shells", "octaves", "hopf"):
            for comp in (False, True):
                t0 = time.perf_counter()
                blob = encode_bytes(data, mode, comp)
                t1 = time.perf_counter()
                out, _ = decode_bytes(blob)
                t2 = time.perf_counter()
                assert out == data
                rows.append((name, mode, "zlib" if comp else "raw", len(data), len(blob),
                             len(blob) / len(data), zsize / len(data), t1 - t0, t2 - t1))
    lines = [f"Walsh codec benchmark ({mb} MB per source); size ratio = encoded / original",
             f"{'source':40s} {'bands':8s} {'store':5s} {'ratio':>7s} {'zlib(orig)':>10s} "
             f"{'enc s':>6s} {'dec s':>6s}"]
    for r in rows:
        lines.append(f"{r[0]:40s} {r[1]:8s} {r[2]:5s} {r[5]:7.3f} {r[6]:10.3f} {r[7]:6.2f} {r[8]:6.2f}")
    rep = synthetic_report()
    lines.append(f"denoise, synthetic source (steps + sine + N(0, {rep['sigma']}^2), "
                 f"{rep['samples']} samples): SNR {rep['snr_before_db']} dB -> {rep['snr_after_db']} dB; "
                 f"AC SNR (DC removed) {rep['ac_snr_before_db']} dB -> {rep['ac_snr_after_db']} dB")
    return "\n".join(lines)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m hypercube.codec_walsh")
    sub = ap.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("encode"); e.add_argument("inp"); e.add_argument("out")
    e.add_argument("--bands", default="shells", choices=["shells", "octaves", "hopf"])
    e.add_argument("--raw", action="store_true")
    d = sub.add_parser("decode"); d.add_argument("inp"); d.add_argument("out")
    n = sub.add_parser("denoise"); n.add_argument("inp", nargs="?"); n.add_argument("out", nargs="?")
    n.add_argument("--synthetic", action="store_true")
    sub.add_parser("selftest")
    b = sub.add_parser("bench"); b.add_argument("--mb", type=int, default=10)
    a = ap.parse_args(argv)
    if a.cmd == "encode":
        data = open(a.inp, "rb").read()
        blob = encode_bytes(data, a.bands, not a.raw)
        open(a.out, "wb").write(blob)
        print(f"{len(data)} bytes -> {len(blob)} bytes ({a.bands}, {'raw' if a.raw else 'zlib'}); "
              f"ratio {len(blob) / max(1, len(data)):.3f}")
    elif a.cmd == "decode":
        out, head = decode_bytes(open(a.inp, "rb").read())
        open(a.out, "wb").write(out)
        print(f"decoded {head['size']} bytes ({head['bands']})")
    elif a.cmd == "denoise":
        print("synthetic source:", synthetic_report())
        if not a.synthetic:
            x = np.frombuffer(open(a.inp, "rb").read(), dtype=np.uint8).astype(float)
            y, t = denoise_signal(x)
            open(a.out, "wb").write(np.clip(np.rint(y), 0, 255).astype(np.uint8).tobytes())
            print(f"{a.inp}: {len(x)} samples, mean threshold {t.mean():.2f}, energy kept "
                  f"{np.sum(y ** 2) / max(1e-12, np.sum(x ** 2)):.4f} (no clean reference: SNR not measurable)")
    elif a.cmd == "bench":
        print(bench(a.mb))
    else:
        selftest()


if __name__ == "__main__":
    main(sys.argv[1:])

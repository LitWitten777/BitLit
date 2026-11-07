"""Where the model's raw data lives, and how it is unpacked.

The large inputs stay committed in compressed form under `sources/` (they pass `.gitignore`
because `.lzma` is not an ignored extension).  On first use they are unpacked into `.cache/`
(git-ignored), and their MD5 is checked against the value recorded here, so a run is always
tied to known bytes.

| archive | contents used |
|---|---|
| `sources/ephemeris.tar.lzma` | Swiss Ephemeris `sepl*.se1` (planets) and `semo*.se1` (Moon), JPL DE441-based, JD 186997.5 - 2597651 (about 4200 BC - AD 2400); `de421.bsp` (1899-2053) |
| `sources/bible.tar.lzma` | KJV with Strong's numbers (`kjv_strongs.json`), OSHB Hebrew (`OSHB-v.2.2/`), Tischendorf Greek |
| `sources/hyg_v44.tar.lzma` | HYG v4.4 star catalogue (`hyg_v44.csv`) |
"""
import hashlib
import lzma
import os
import tarfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.path.join(ROOT, ".cache")
SCRIPTS = os.path.join(ROOT, "scripts")

ARCHIVES = {
    "ephemeris": ("sources/ephemeris.tar.lzma", "3a553d743d32a5a38a658948bd20710d", "ephe"),
    "bible": ("sources/bible.tar.lzma", "04f6f342db31e37269f5a99e1ef922a5", "bible"),
    "hyg": ("sources/hyg_v44.tar.lzma", "adc695e60b50d5d9ddc8b1369f463891", None),
}


def md5(path):
    h = hashlib.md5()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def ensure(name, verify=True):
    """Unpack archive `name` into `.cache/` if needed and return the cache directory."""
    rel, digest, marker = ARCHIVES[name]
    stamp = os.path.join(CACHE, f".{name}.ok")
    if os.path.exists(stamp):
        return CACHE
    src = os.path.join(ROOT, rel)
    if not os.path.exists(src):
        raise FileNotFoundError(f"{rel} is missing; it is the committed source of the {name} data")
    if verify and md5(src) != digest:
        raise ValueError(f"{rel}: MD5 differs from the recorded {digest}")
    os.makedirs(CACHE, exist_ok=True)
    with lzma.open(src, format=lzma.FORMAT_ALONE) as raw, tarfile.open(fileobj=raw, mode="r|") as tf:
        tf.extractall(CACHE, filter="data")
    with open(stamp, "w") as f:
        f.write(digest + "\n")
    return CACHE


def ephe_dir():
    ensure("ephemeris")
    return os.path.join(CACHE, "ephe")


def bible_dir():
    ensure("bible")
    return os.path.join(CACHE, "bible")


def hyg_csv():
    ensure("hyg")
    for dirpath, _, files in os.walk(CACHE):
        for f in files:
            if f.startswith("hyg") and f.endswith(".csv"):
                return os.path.join(dirpath, f)
    raise FileNotFoundError("hyg_v44.csv not found after unpacking")


def fetch_all():
    return {name: ensure(name) for name in ARCHIVES}

"""Ingest any data and split it into channels ("colours").

Everything becomes a list of integers.  The rules, in order:

  * a path to an existing file: its bytes (then decoded as below if it is text);
  * bytes that decode as UTF-8 text: treated as text;
  * text: if it parses as JSON, numbers are collected from it in document order
    (strings inside it are treated as text); if every non-empty line is a
    comma/tab/space separated row of numbers, it is treated as a numeric table;
    otherwise it is treated as text;
  * WAV audio (RIFF/WAVE bytes): one channel per audio channel (ch0, ch1, ...),
    decoded with the standard-library `wave` module;
  * a list / tuple of numbers: numeric;
  * anything else: its `repr`, as text.

Channels produced:
  text     bytes   (UTF-8 bytes)
           code    (Unicode code points)
           written (position of each tabulated letter in its alphabet, 1-based;
                    0 for other characters)
           spoken  (sound-feature blade of each tabulated letter; 0 otherwise)
           value   (letter value: gematria / isopsephy / Latin ordinal)
  numeric  samples (numbers quantised to integers: integers unchanged, other
                    numbers multiplied by 2**16 and rounded; the scale is recorded)
           and, for tables, one channel per column (col0, col1, ...)
  binary   bytes

Quantisation is the only lossy step and is recorded, so a stored record states
exactly what was transformed.
"""

import io
import json
import os
import wave

from . import alphabets

SCALE_BITS = 16


def _quantise(xs):
    if all(isinstance(x, int) and not isinstance(x, bool) for x in xs):
        return [int(x) for x in xs], 0
    return [int(round(float(x) * (1 << SCALE_BITS))) for x in xs], SCALE_BITS


def _numbers_in_json(obj, nums, texts):
    if isinstance(obj, bool):
        nums.append(int(obj))
    elif isinstance(obj, (int, float)):
        nums.append(obj)
    elif isinstance(obj, str):
        texts.append(obj)
    elif isinstance(obj, dict):
        for k in obj:
            _numbers_in_json(obj[k], nums, texts)
    elif isinstance(obj, (list, tuple)):
        for v in obj:
            _numbers_in_json(v, nums, texts)


def _parse_table(text):
    rows = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        cells = [c for c in line.replace(",", " ").replace("\t", " ").split(" ") if c]
        try:
            rows.append([float(c) if any(ch in c for ch in ".eE") else int(c) for c in cells])
        except ValueError:
            return None
    return rows or None


def text_channels(text):
    written, spoken, value = [], [], []
    for ch in text:
        l = alphabets.letter_of(ch)
        written.append(0 if l is None else l.index + 1)
        spoken.append(0 if l is None else l.sound)
        value.append(0 if l is None else l.value)
    return {
        "bytes": list(text.encode("utf-8")),
        "code": [ord(c) for c in text],
        "written": written,
        "spoken": spoken,
        "value": value,
    }


def _wav(data):
    with wave.open(io.BytesIO(data)) as w:
        nch, width, nframes = w.getnchannels(), w.getsampwidth(), w.getnframes()
        frames = w.readframes(nframes)
    chans = {"ch%d" % c: [] for c in range(nch)}
    step = nch * width
    for f in range(nframes):
        for c in range(nch):
            b = frames[f * step + c * width: f * step + (c + 1) * width]
            v = int.from_bytes(b, "little", signed=(width > 1))
            if width == 1:
                v -= 128
            chans["ch%d" % c].append(v)
    return {"kind": "audio", "channels": chans, "scale_bits": 0, "text": None}


def ingest(obj):
    """Return {"kind", "channels": {name: [int]}, "scale_bits", "text"}."""
    if isinstance(obj, str) and len(obj) < 4096 and "\n" not in obj and os.path.isfile(obj):
        with open(obj, "rb") as fh:
            obj = fh.read()
    if isinstance(obj, (bytes, bytearray)) and obj[:4] == b"RIFF" and obj[8:12] == b"WAVE":
        return _wav(bytes(obj))
    if isinstance(obj, (bytes, bytearray)):
        try:
            obj = bytes(obj).decode("utf-8")
        except UnicodeDecodeError:
            return {"kind": "binary", "channels": {"bytes": list(obj)}, "scale_bits": 0,
                    "text": None}
    if isinstance(obj, (list, tuple)) and all(
            isinstance(x, (int, float)) and not isinstance(x, bool) for x in obj):
        q, s = _quantise(list(obj))
        return {"kind": "numeric", "channels": {"samples": q}, "scale_bits": s, "text": None}
    if not isinstance(obj, str):
        obj = repr(obj)
    text = obj
    stripped = text.strip()
    if stripped[:1] in "[{":
        try:
            data = json.loads(stripped)
        except ValueError:
            data = None
        if data is not None:
            nums, texts = [], []
            _numbers_in_json(data, nums, texts)
            chans = {}
            s = 0
            if nums:
                chans["samples"], s = _quantise(nums)
            joined = " ".join(texts)
            if joined:
                chans.update(text_channels(joined))
            return {"kind": "json", "channels": chans, "scale_bits": s,
                    "text": joined or None}
    rows = _parse_table(text)
    if rows is not None and any(len(r) > 0 for r in rows):
        flat = [x for r in rows for x in r]
        q, s = _quantise(flat)
        chans = {"samples": q}
        width = max(len(r) for r in rows)
        if width > 1 and all(len(r) == width for r in rows):
            for c in range(width):
                chans["col%d" % c] = _quantise([r[c] for r in rows])[0]
        return {"kind": "numeric", "channels": chans, "scale_bits": s, "text": None}
    return {"kind": "text", "channels": text_channels(text), "scale_bits": 0, "text": text}

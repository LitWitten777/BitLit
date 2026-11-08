"""Output sets: everything the engine computes for one input, written to one folder.

    python -m qbx_engine outset "בראשית ברא אלהים" --out out/genesis [--frames 60]

writes

  index.md            what is in the folder, with the check results
  record.json         the full engine record (channels, multivectors, torus, colours)
  letters.json/.csv   one detail card per letter (`letters.card`)
  session.json        the timed session after the scheduled frames (clock, torus,
                      braid, merkaba, current letters, checks)
  braids.json         the words as two bundles of braids: side by side and braided
                      through each other (`braidbraid.interact`)
  checks.json         every re-derived Lean statement, by module
  torus.svg           the torus grid (heat map) at the final offset
  standing.svg        the standing wave over one period (strip of frames)
  braid.svg           the braid traced by reading the words
  merkaba.svg         the merkaba in its final orientation with the control legend
  standing.wav        the standing wave as sound (8 kHz, 16-bit mono)
  fidelity.json       which fields are exact, digitised, reference data or convention,
                      with error bounds and torus-node collisions (`fidelity`)

Each file is plain JSON / CSV / SVG / WAV, readable without this package.
"""

import csv
import json
import os
import struct
import wave

from . import beasts, braidbraid, braidlines, fidelity, harmonic, letters, merkaba, standing
from .controls import Session
from .engine import Engine


def _heat(v, lo, hi):
    x = 0.0 if hi == lo else (v - lo) / (hi - lo)
    r = int(255 * min(1, max(0, 1.5 * x - 0.2)))
    g = int(255 * min(1, max(0, 1.5 - abs(3 * x - 1.5))))
    b = int(255 * min(1, max(0, 1.2 - 1.5 * x)))
    return "#%02x%02x%02x" % (r, g, b)


def grid_svg(grid, title, cell=14):
    N, M = len(grid), len(grid[0])
    flat = [v for row in grid for v in row]
    lo, hi = min(flat), max(flat)
    w, h = M * cell + 20, N * cell + 40
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" font-family="sans-serif">'
           % (w, h), '<rect width="100%" height="100%" fill="#0d1117"/>',
           '<text x="10" y="18" fill="#e6edf3" font-size="13">%s</text>' % title]
    for j in range(N):
        for k in range(M):
            out.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s"/>'
                       % (10 + k * cell, 28 + j * cell, cell - 1, cell - 1, _heat(grid[j][k], lo, hi)))
    out.append("</svg>")
    return "\n".join(out)


def strip_svg(frames, title, cell=3):
    N, M = len(frames[0]), len(frames[0][0])
    flat = [v for f in frames for row in f for v in row]
    lo, hi = min(flat), max(flat)
    per_row = 8
    rows = (len(frames) + per_row - 1) // per_row
    fw, fh = M * cell + 6, N * cell + 6
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" font-family="sans-serif">'
           % (per_row * fw + 20, rows * fh + 40), '<rect width="100%" height="100%" fill="#0d1117"/>',
           '<text x="10" y="18" fill="#e6edf3" font-size="13">%s</text>' % title]
    for i, f in enumerate(frames):
        ox, oy = 10 + (i % per_row) * fw, 28 + (i // per_row) * fh
        for j in range(N):
            for k in range(M):
                out.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s"/>'
                           % (ox + k * cell, oy + j * cell, cell, cell, _heat(f[j][k], lo, hi)))
    out.append("</svg>")
    return "\n".join(out)


def braid_svg(n, word, title, dx=26, dy=22):
    """Strand diagram: strands are vertical lines, sigma_i crosses strands i and i+1."""
    H = (len(word) + 1) * dy + 40
    W = (n + 1) * dx + 20
    cols = ["#e8a33d", "#3d7be8", "#7a8b3a", "#c9d6ea", "#d65db1", "#4ec9b0", "#f14c4c", "#b5cea8"]
    pos = list(range(n))  # pos[slot] = strand label
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" font-family="sans-serif">'
           % (W, H), '<rect width="100%" height="100%" fill="#0d1117"/>',
           '<text x="10" y="18" fill="#e6edf3" font-size="13">%s</text>' % title]
    y = 30
    for g in word:
        i = abs(g) - 1
        for s in range(n):
            if s not in (i, i + 1):
                x = 20 + s * dx
                out.append('<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="%s" stroke-width="3"/>'
                           % (x, y, x, y + dy, cols[pos[s] % len(cols)]))
        x1, x2 = 20 + i * dx, 20 + (i + 1) * dx
        under, over = ((x2, x1, pos[i + 1]), (x1, x2, pos[i])) if g > 0 else \
            ((x1, x2, pos[i]), (x2, x1, pos[i + 1]))
        out.append('<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="%s" stroke-width="3" '
                   'stroke-dasharray="4,5"/>' % (under[0], y, under[1], y + dy, cols[under[2] % len(cols)]))
        out.append('<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="#0d1117" stroke-width="7"/>'
                   % (over[0], y, over[1], y + dy))
        out.append('<line x1="%d" y1="%d" x2="%d" y2="%d" stroke="%s" stroke-width="3"/>'
                   % (over[0], y, over[1], y + dy, cols[over[2] % len(cols)]))
        pos[i], pos[i + 1] = pos[i + 1], pos[i]
        y += dy
    out.append("</svg>")
    return "\n".join(out)


def write_wav(path, samples, rate=8000):
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(b"".join(struct.pack("<h", int(max(-1, min(1, s)) * 32000)) for s in samples))


def all_checks(session=None):
    from . import clock as _clock
    out = {"beasts": beasts.checks(), "harmonic": harmonic.checks(), "merkaba": merkaba.checks(),
           "braid_with_braid": braidbraid.checks()}
    if session is not None:
        out["standing"] = standing.check(session.grid0, session.p, session.q, 3)
        out["clock"] = session.master_clock().check()
        out["session_run"] = session.checks()
    else:
        c = _clock.MasterClock().add("a", 4).add("b", 3).add("c", 10)
        out["clock"] = c.check()
    return out


def outset(src, out_dir, frames=None, N=16, M=25):
    os.makedirs(out_dir, exist_ok=True)
    text = src if isinstance(src, str) else None
    rec = Engine(torus=(N, M)).process(src)
    sess = Session(text if text else "QBX", N=N, M=M)
    if frames is None:
        frames = min(sess.master_clock().joint_period(), 120)
    sess.advance(frames)
    st = sess.state()
    files = {}

    def dump(name, obj):
        with open(os.path.join(out_dir, name), "w", encoding="utf-8") as fh:
            json.dump(obj, fh, ensure_ascii=False, indent=1, default=str)
        files[name] = True

    dump("record.json", rec)
    cards = letters.cards(text or "", N, M)
    dump("letters.json", cards)
    with open(os.path.join(out_dir, "letters.csv"), "w", newline="", encoding="utf-8") as fh:
        wr = csv.writer(fh)
        wr.writerow(["alphabet", "glyph", "name", "value", "ipa", "holes", "symmetry", "grade",
                     "dominant_beast", "frequency_hz", "pitch_class_cents", "torus_node"])
        for c in cards:
            wr.writerow([c["alphabet"], c["glyph"], c["name"], c["value"], c["ipa"],
                         c["written"]["holes"], c["written"]["symmetry"], c["spoken"]["grade"],
                         c["beasts"]["dominant"], c["harmonic"]["frequency_hz"],
                         c["harmonic"]["pitch_class_cents"],
                         "%d,%d" % tuple(c["harmonic"]["torus_node"])])
    files["letters.csv"] = True
    dump("session.json", st)
    t = sess.texts
    half = max(1, len(t) // 2)
    a, b = t[:half], t[half:] or t[:1]
    if len(a) == 1:
        a = a + [a[0][::-1]]
    if len(b) == 1:
        b = b + [b[0][::-1]]
    dump("braids.json", braidbraid.interact(a, b))
    checks = all_checks(sess)
    dump("checks.json", checks)
    fid = fidelity.report(text or "", N, M)
    dump("fidelity.json", fid)
    svgs = {
        "torus.svg": grid_svg(sess.torus_grid(), "torus %dx%d, channel %s, offset %s"
                              % (N, M, sess.channel, tuple(sess.offset))),
        "standing.svg": strip_svg(standing.frames(sess.grid0, sess.p, sess.q, 16)[0],
                                  "standing wave, direction (%d,%d), first 16 ticks of period %d"
                                  % (sess.p, sess.q, standing.period(N, M, sess.p, sess.q))),
        "braid.svg": braid_svg(sess.strands, sess.full_word[:80],
                               "braid of the reading (%d strands)" % sess.strands),
        "merkaba.svg": merkaba.svg(sess.merk, title="Merkaba after %d frames" % sess.frame),
    }
    for name, s in svgs.items():
        with open(os.path.join(out_dir, name), "w", encoding="utf-8") as fh:
            fh.write(s)
        files[name] = True
    write_wav(os.path.join(out_dir, "standing.wav"), standing.sonify(sess.grid0, sess.p, sess.q))
    files["standing.wav"] = True
    ok = all(v for group in checks.values() for v in group.values())
    lines = ["# Output set", "", "Input: `%s`" % (text if text else "(file/bytes)"), "",
             "Frames played: %d (joint period %d)" % (sess.frame, st["clock"]["joint_period"]), "",
             "All checks: **%s**" % ("OK" if ok else "FAILED"), "", "| file | |", "|---|---|"]
    for name in ["record.json", "letters.json", "letters.csv", "session.json", "braids.json",
                 "checks.json", "torus.svg", "standing.svg", "braid.svg", "merkaba.svg",
                 "standing.wav", "fidelity.json"]:
        lines.append("| `%s` | |" % name)
    lines += ["", "## Checks", ""]
    for g, d in checks.items():
        lines.append("- %s: %s" % (g, ", ".join("%s=%s" % (k, v) for k, v in d.items())))
    lines += ["", "## How closely this matches observation", "",
              "Every field is tiered in `fidelity.json` (see `QBX/Formal/Engine/Reality.lean`):",
              ""]
    for t, d in fidelity.TIERS.items():
        lines.append("- **%s**: %s" % (t, d))
    col = fid["torus"]["collisions_in_this_input"]
    lines += ["", "Torus %dx%d keeps values only modulo %d; values of this input sharing a node: %s"
              % (N, M, N * M, "; ".join("%s" % c["values"] for c in col) if col else "none")]
    with open(os.path.join(out_dir, "index.md"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    return {"dir": out_dir, "ok": ok, "files": sorted(files) + ["index.md"]}

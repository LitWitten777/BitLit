"""Command line: `python3 -m hypercube <command> ...` (run from the repository root).

  fetch                         unpack the committed archives into .cache/ (MD5-checked)
  state TIME [--place LAT,LON] [--shift DEG] [--eclipses]
                                the full state as JSON (TIME: 2026-10-23T12:00, '763-06-15 BC', or a JD; UT)
  eclipses FROM TO [--kind solar|lunar] [--place LAT,LON]
                                computed eclipse list (years or dates)
  encode TEXT [--style base64|codon|amino|cells|hexagram]
  decode CELLS [--style base64|codon|cells]
  profile TEXT                  script, gematria, braid walk, cells of a text
  deobfuscate TEXT [--depth N]  ranked decodings
  verse REF                     KJV text, sky placement rule inverse, letter profile of the original
  svg TIME [--place ..] [-o FILE]
  wav FROM TO STEP_DAYS [-o FILE]
  html FROM TO STEP_DAYS [-o FILE]
  gears                         the cycle table (Saros, inex, Metonic, ...) and how well each meshes
  wind TIME [--cycle saros] [--steps -3,3] [--kind solar|lunar]
                                step the real sky forward/backward by whole cycles from TIME
  lattice                       Q6 vs E8 vs E8+E8+E8 vs Leech: shells, roots, minimal vectors
  gauge [--n 6] [--sweeps N]    Z/2 lattice gauge theory on the cube (Monte Carlo scan)
  build [--ancient]             regenerate hypercube/data/*.json
  crossdomain [--no-sky]        stage 3: crystals, circuits, Cayley-Dickson cocycles, topology, sky braid
  crystal-svg [-o FILE]         the codon crystal graph as SVG
  hebrew DATE | --to-civil Y M D
                                Hebrew calendar date of a civil date (or the reverse; months from Nisan = 1)
  calibrate                     recompute the statements of the ten calibration documents
                                -> artifacts/hypercube/calibration_ledger.tsv
  patterns                      factorions (bases 2-12), nets of the n-cube (n <= 4), Curtis's MOG
  hopf                          the four finite Hopf fibrations of Q6 (GF(2), GF(4), GF(8), GF(64))
  music [--wav FILE] [--svg FILE]
                                music vortexes: octave vortex on the Hopf bundle, Tonnetz vortices,
                                scales, commas, octave classes of Z^6 and E8, Psalm 119 rendering
  selftest                      quick end-to-end checks
"""
import argparse
import json
import os
import sys

from . import av, build_data, codec, eclipses, scripture, state, store
from .timescale import jd_from_calendar, parse_time

OUTDIR = os.path.join(store.ROOT, "hypercube", "out")


def _place(s):
    if not s:
        return None
    lat, lon = s.split(",")
    return float(lat), float(lon)


def _when(s):
    try:
        return jd_from_calendar(int(s), 1, 1)
    except ValueError:
        return parse_time(s)


def _dump(obj):
    print(json.dumps(obj, ensure_ascii=False, indent=1))


def main(argv=None):
    ap = argparse.ArgumentParser(prog="hypercube", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("fetch")
    p = sub.add_parser("state")
    p.add_argument("time")
    p.add_argument("--place")
    p.add_argument("--shift", type=float, default=0.0)
    p.add_argument("--eclipses", action="store_true")
    p = sub.add_parser("eclipses")
    p.add_argument("start")
    p.add_argument("end")
    p.add_argument("--kind", choices=["solar", "lunar"])
    p.add_argument("--place")
    p = sub.add_parser("encode")
    p.add_argument("text", nargs="+")
    p.add_argument("--style", default="base64")
    p = sub.add_parser("decode")
    p.add_argument("cells", nargs="+")
    p.add_argument("--style", default="base64")
    p = sub.add_parser("profile")
    p.add_argument("text", nargs="+")
    p = sub.add_parser("deobfuscate")
    p.add_argument("text", nargs="+")
    p.add_argument("--depth", type=int, default=3)
    p.add_argument("--top", type=int, default=5)
    p = sub.add_parser("verse")
    p.add_argument("ref", nargs="+")
    p = sub.add_parser("svg")
    p.add_argument("time")
    p.add_argument("--place")
    p.add_argument("-o")
    for name in ("wav", "html"):
        p = sub.add_parser(name)
        p.add_argument("start")
        p.add_argument("end")
        p.add_argument("step", type=float)
        p.add_argument("-o")
    sub.add_parser("gears")
    p = sub.add_parser("wind")
    p.add_argument("time")
    p.add_argument("--cycle", default="saros")
    p.add_argument("--steps", default="-3,3")
    p.add_argument("--kind", choices=["solar", "lunar"])
    sub.add_parser("lattice")
    p = sub.add_parser("gauge")
    p.add_argument("--n", type=int, default=6)
    p.add_argument("--sweeps", type=int, default=3000)
    p = sub.add_parser("build")
    p.add_argument("--ancient", action="store_true")
    p = sub.add_parser("crossdomain")
    p.add_argument("--no-sky", action="store_true")
    p = sub.add_parser("crystal-svg")
    p.add_argument("-o", default=None)
    p = sub.add_parser("hebrew")
    p.add_argument("date", nargs="?")
    p.add_argument("--to-civil", nargs=3, type=int, metavar=("YEAR", "MONTH", "DAY"))
    sub.add_parser("calibrate")
    sub.add_parser("patterns")
    sub.add_parser("hopf")
    p = sub.add_parser("music")
    p.add_argument("--wav", default=None)
    p.add_argument("--svg", default=None)
    sub.add_parser("selftest")
    a = ap.parse_args(argv)

    if a.cmd == "fetch":
        _dump(store.fetch_all())
    elif a.cmd == "state":
        _dump(state.state(parse_time(a.time), _place(a.place), a.shift, with_eclipses=a.eclipses))
    elif a.cmd == "eclipses":
        kinds = (a.kind,) if a.kind else ("solar", "lunar")
        rows = eclipses.eclipses_between(_when(a.start), _when(a.end), kinds=kinds)
        pl = _place(a.place)
        for r in rows:
            line = f'{r["date"]}  {r["kind"]:5s} {r["type"]:9s} mag {r["magnitude"]:.3f}  saros {r["saros"]}'
            if pl:
                lc = eclipses.local_circumstances(r, *pl)
                line += (f'  | here: {lc["phase_seen"]} {lc["magnitude"]:.2f}, Sun alt {lc["sun_alt"]:.0f}'
                         if r["kind"] == "solar" else f'  | here: Moon alt {lc["moon_alt"]:.0f} at max')
            print(line)
    elif a.cmd == "encode":
        print(codec.render(codec.encode_text(" ".join(a.text)), a.style))
    elif a.cmd == "decode":
        print(codec.decode_text(codec.parse_rendered(" ".join(a.cells), a.style)))
    elif a.cmd == "profile":
        _dump(codec.letter_profile(" ".join(a.text)))
    elif a.cmd == "deobfuscate":
        for r in codec.deobfuscate(" ".join(a.text), depth=a.depth)[:a.top]:
            print(f'{r["score"]:7.3f} {r["lang"]} {" > ".join(r["chain"]) or "(as given)"}: {r["text"][:200]}')
    elif a.cmd == "verse":
        b, c, v = scripture.parse_ref(" ".join(a.ref))
        osis = {1: "Gen", 43: "John"}.get(b)
        out = {"ref": f"{scripture.BOOKS[b - 1]} {c}:{v}", "kjv": scripture.kjv_text(b, c, v),
               "chapter_index": scripture.continuous_index(b, c),
               "ra_arc_h_unshifted": [round((scripture.continuous_index(b, c) - 1) * 24 / 1189, 4),
                                      round(scripture.continuous_index(b, c) * 24 / 1189, 4)]}
        if osis:
            orig = scripture.original_verse(f"{osis}.{c}.{v}")
            out["original"] = orig
            out["profile"] = {k: v2 for k, v2 in codec.letter_profile(orig).items() if k not in ("cells", "base64")}
        _dump(out)
    elif a.cmd == "svg":
        s = state.state(parse_time(a.time), _place(a.place), with_eclipses=False)
        path = a.o or os.path.join(OUTDIR, "sky.svg")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        open(path, "w", encoding="utf-8").write(av.svg(s))
        print(path)
    elif a.cmd in ("wav", "html"):
        frames = state.series(parse_time(a.start), parse_time(a.end), a.step)
        path = a.o or os.path.join(OUTDIR, f"sky.{a.cmd}")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        if a.cmd == "wav":
            av.wav(frames, path)
        else:
            open(path, "w", encoding="utf-8").write(av.html(frames, f"{a.start} .. {a.end}, step {a.step} d"))
        print(path)
    elif a.cmd == "gears":
        from . import gears
        for r in gears.gear_table():
            print(r)
    elif a.cmd == "wind":
        from . import gears
        lo, hi = (int(x) for x in a.steps.split(","))
        for r in gears.wind(parse_time(a.time), a.cycle, range(lo, hi + 1), a.kind):
            print(r)
    elif a.cmd == "lattice":
        from . import lattice
        _dump(lattice.report())
    elif a.cmd == "gauge":
        from . import gauge
        for r in gauge.scan(a.n, sweeps=a.sweeps):
            print(r)
    elif a.cmd == "build":
        print("\n".join(build_data.build(a.ancient)))
    elif a.cmd == "crossdomain":
        from . import crossdomain
        _dump(crossdomain.report(with_sky=not a.no_sky))
    elif a.cmd == "crystal-svg":
        from . import crossdomain
        os.makedirs(OUTDIR, exist_ok=True)
        print(crossdomain.crystal_svg(a.o or os.path.join(OUTDIR, "codon_crystal.svg")))
    elif a.cmd == "hebrew":
        from . import hebcal
        if a.to_civil:
            print("%d-%02d-%02d" % hebcal.civil_from_hebrew(*a.to_civil))
        else:
            y, m, d = (int(x) for x in a.date.split("-")) if not a.date.startswith("-") else \
                (-int(a.date[1:].split("-")[0]), *map(int, a.date[1:].split("-")[1:]))
            print(hebcal.label(hebcal.hebrew_from_civil(y, m, d)))
    elif a.cmd == "calibrate":
        from . import calibrate
        calibrate.main()
    elif a.cmd == "patterns":
        from . import patterns
        _dump(patterns.report())
    elif a.cmd == "hopf":
        from . import hopf
        hopf.selfcheck()
        _dump(hopf.report())
    elif a.cmd == "music":
        from . import music
        music.selfcheck()
        if a.wav:
            print(music.render_wav(a.wav))
        if a.svg:
            print(music.render_svg(a.svg))
        if not (a.wav or a.svg):
            _dump(music.report())
    elif a.cmd == "selftest":
        from . import selftest
        sys.exit(selftest.run())


if __name__ == "__main__":
    main()

"""python3 -m manifold <command>

  selftest                      check the Python mirrors against the values proved in Lean
  demo [--ticks N]              scripted run: start, speed 6, speed 2 (auto-brake), stop
  run [--source S] [--bands B] [--speed V] [--ticks N] [--attack R]
                                non-interactive run, one status line per tick
  repl [--source S] [--bands B] interactive: start | stop | speed N | chip B.. | unchip B.. |
                                blow B G | status | spectrum | quit   (runs in the background)
  spectrum [--source S] [--bands B]   band energies of one block
  zd                            sedenion zero-divisor census and annihilator dimensions
  tower                         which laws hold at each Cayley-Dickson level
  gematria [--controls K]       gematria lab on the Torah -> artifacts/manifold/gematria_lab.txt

Sources S: synthetic (default), synthetic-repeat, text:<string>, file:<path>, torah.
Bands B:  shells (default, Hamming weight 0..6), hopf (GF(8) fibres), octaves (dyadic sequency).
"""
import os
import sys

from . import cd, controller, heal, spectrum
from .runtime import Manifold, source_from_spec


def _opt(args, name, default):
    if name in args:
        i = args.index(name)
        return args[i + 1]
    return default


def selftest():
    fails = 0

    def check(name, cond):
        nonlocal fails
        print(("ok   " if cond else "FAIL ") + name)
        fails += not cond

    # Control.lean `controller_trace`
    check("governor trace = Lean controller_trace",
          controller.run_script(controller.Governor(), controller.LEAN_TRACE_SCRIPT) == controller.LEAN_TRACE)
    g = controller.Governor(accel=3, brake=5, vmax=9)
    g.start(); g.set_speed(50)
    seen = [g.tick() for _ in range(10)]
    check("speed never exceeds vmax and reaches it", max(seen) <= 9 and seen[-1] == 9)
    g.set_speed(1)
    down = [g.tick() for _ in range(3)]
    check("auto-brake: monotone, no undershoot", down == [4, 1, 1])
    # CDTower.lean
    census = cd.zero_divisor_census(4)
    check("sedenion census 210/84/42/336 = Lean two_term_zero_divisor_count",
          (census["elements"], census["zero_divisors"], census["assessors"], census["ordered_pairs"]) == (210, 84, 42, 336))
    check("(e1+e10)(e5+e14) = 0 (Lean sedenion_zero_divisor)",
          not any(cd.mul(cd.two_term(4, 1, 10, 1), cd.two_term(4, 5, 14, 1))))
    check("basis table matches doubling recursion fsgn",
          all(cd.mul(cd.basis(4, i), cd.basis(4, j))[i ^ j] == cd.fsgn(4, i, j) for i in range(16) for j in range(16)))
    p3, p4 = cd.properties(3), cd.properties(4)
    check("octonions: alternative, norm-multiplicative; sedenions: neither",
          p3["alternative"] and p3["norm_multiplicative"] and not p4["alternative"] and not p4["norm_multiplicative"])
    check("doubling lifts zero divisors: annihilator of e1+e10 has dim 4 in S, 8 one level up",
          cd.annihilator_dim(cd.two_term(4, 1, 10, 1)) == 4 and cd.annihilator_dim(cd.two_term(5, 1, 10, 1)) == 8)
    # Spectrum.lean
    import random
    rnd = random.Random(0)
    f = [rnd.uniform(-1, 1) for _ in range(64)]
    check("wht(wht f) = 64 f (Lean wht_wht)", max(abs(a - 64 * b) for a, b in zip(spectrum.wht(spectrum.wht(f)), f)) < 1e-9)
    check("Parseval (Lean wht_parseval)", abs(spectrum.energy(spectrum.wht(f)) - 64 * spectrum.energy(f)) < 1e-9)
    for kind, bands in (("shells", spectrum.shell_bands(6)), ("hopf", spectrum.hopf_bands()),
                        ("octaves", spectrum.octave_bands(6))):
        comps = spectrum.split(f, bands)
        check(f"{kind}: components join back (Lean sum_shells / band_add_compl)",
              max(abs(a - b) for a, b in zip(spectrum.join(comps), f)) < 1e-9)
        check(f"{kind}: band energies add up (Lean energy_band_add_compl)",
              abs(sum(spectrum.energy(c) for c in comps.values()) - spectrum.energy(f)) < 1e-9)
    check("shell sizes 1,6,15,20,15,6,1", [spectrum.shell_bands(6).count(k) for k in range(7)] == [1, 6, 15, 20, 15, 6, 1])
    chipped = spectrum.chip(f, spectrum.shell_bands(6), {4, 5, 6})
    check("chipping never adds energy (Lean energy_gain_le)", spectrum.energy(chipped) <= spectrum.energy(f) + 1e-12)
    blown = spectrum.blowup(f, spectrum.shell_bands(6), {1: 2.0})
    check("blowing up never removes energy (Lean le_energy_gain)", spectrum.energy(blown) >= spectrum.energy(f) - 1e-12)
    D = spectrum.wht(spectrum.upsample_double(f))
    check("CD doubling (f, f) has spectrum (2F, 0) (Lean wht_double)", max(abs(v) for v in D[64:]) < 1e-9)
    # Heal.lean
    check("heal fixes every single flip (Lean heal_single_error)",
          all(heal.heal(heal.enc(d) ^ (1 << i))[0] == d for d in range(8) for i in range(6)))
    check("double flips never land on a codeword (Lean double_error_detected)",
          all((heal.enc(d) ^ (1 << i) ^ (1 << j)) not in heal.CODE for d in range(8) for i in range(6) for j in range(6) if i != j))
    data = os.urandom(200)
    cells = heal.encode_bytes(data)
    for k in range(0, len(cells), 2):
        cells[k] ^= 1 << (k % 6)
    out, rep, _ = heal.decode_cells(cells)
    check("byte store heals one flip per cell", out == data and rep == len(range(0, len(cells), 2)))
    check("majority vote heals a corrupted replica (Lean maj_heals)", heal.maj(12345, 12345, 999) == 12345)
    # runtime end to end
    m = Manifold(source_from_spec("synthetic"))
    m.start(); m.set_speed(4)
    for _ in range(30):
        m.tick()
    m.corrupt_replica(1, 77777)
    m.tick()
    check("runtime: processes blocks, repairs flips, heals a corrupted control replica",
          m.stats["blocks"] > 50 and m.stats["repaired"] > 0 and m.replicas_agree() and m.stats["replica_repairs"] >= 1)
    m.stop()
    for _ in range(10):
        m.tick()
    check("runtime: stop brakes to 0", m.gov.speed == 0)
    print(f"\n{fails} failure(s)")
    return fails


def demo(ticks=40):
    m = Manifold(source_from_spec("synthetic"))
    script = {0: ("start",), 1: ("speed", 6), 18: ("speed", 2), 30: ("stop",)}
    for t in range(ticks):
        if t in script:
            c = script[t]
            print(f"--> command {c}")
            {"start": lambda: m.start(), "stop": lambda: m.stop(),
             "speed": lambda: m.set_speed(c[1])}[c[0]]()
        m.tick()
        print(m.status())
    print("agents:", m.last_report.get("agents"))
    print("stats:", m.stats)


def run(args):
    m = Manifold(source_from_spec(_opt(args, "--source", "synthetic")), bands=_opt(args, "--bands", "shells"))
    if "--attack" in args and m.critic:
        m.critic.rate = float(_opt(args, "--attack", "0.5"))
    m.start()
    m.set_speed(int(_opt(args, "--speed", "5")))
    for _ in range(int(_opt(args, "--ticks", "30"))):
        m.tick()
        print(m.status())
    print("stats:", m.stats)


def repl(args):
    m = Manifold(source_from_spec(_opt(args, "--source", "synthetic")), bands=_opt(args, "--bands", "shells"),
                 tick_seconds=0.2)
    m.run_background()
    print("manifold running in the background (stopped).  Commands: start, stop, speed N, chip B.., "
          "unchip B.., blow B G, status, spectrum, quit")
    try:
        for line in sys.stdin:
            w = line.split()
            if not w:
                continue
            c = w[0]
            if c == "start":
                m.start()
            elif c == "stop":
                m.stop()
            elif c == "speed" and len(w) > 1:
                m.set_speed(int(w[1]))
            elif c == "chip":
                m.chip(*map(int, w[1:]))
            elif c == "unchip":
                m.unchip(*map(int, w[1:]))
            elif c == "blow" and len(w) > 2:
                m.blow(int(w[1]), float(w[2]))
            elif c == "spectrum":
                be = m.last_report.get("band_energy", {})
                print({k: round(v, 1) for k, v in be.items()})
            elif c in ("quit", "exit"):
                break
            print(m.status())
    finally:
        m.shutdown()


def show_spectrum(args):
    src = source_from_spec(_opt(args, "--source", "synthetic"))
    kind = _opt(args, "--bands", "shells")
    bands = {"shells": spectrum.shell_bands(6), "octaves": spectrum.octave_bands(6)}.get(kind) or spectrum.hopf_bands()
    raw, _ = src.next_block(64)
    x = [b - 128 for b in raw]
    be = spectrum.band_energy(x, bands)
    tot = sum(be.values()) or 1
    for b in sorted(be):
        print(f"band {b:2d}  {be[b] / tot:7.3%}  " + "#" * int(60 * be[b] / tot))


def zd():
    c = cd.zero_divisor_census(4)
    print(f"sedenions: {c['elements']} two-term elements, {c['zero_divisors']} zero divisors, "
          f"{c['assessors']} assessors, {c['ordered_pairs']} ordered annihilating pairs")
    print("annihilator dimension of e1+e10:", cd.annihilator_dim(cd.two_term(4, 1, 10, 1)), "(sedenions),",
          cd.annihilator_dim(cd.two_term(5, 1, 10, 1)), "(one doubling up)")
    c5 = cd.zero_divisor_census(5)
    print(f"level 5 (32-ions): {c5['elements']} two-term elements, {c5['zero_divisors']} zero divisors, "
          f"{c5['assessors']} index pairs")


def tower():
    for n in range(0, 6):
        print(n, 2 ** n, cd.properties(n, trials=60))


def gematria(args):
    from .gematria_lab import lab
    txt = lab(n_controls=int(_opt(args, "--controls", "20")))
    os.makedirs("artifacts/manifold", exist_ok=True)
    with open("artifacts/manifold/gematria_lab.txt", "w", encoding="utf-8") as f:
        f.write(txt + "\n")
    print(txt)


def main(argv):
    if not argv:
        print(__doc__)
        return 0
    cmd, args = argv[0], argv[1:]
    if cmd == "selftest":
        return 1 if selftest() else 0
    if cmd == "demo":
        demo(int(_opt(args, "--ticks", "40")))
    elif cmd == "run":
        run(args)
    elif cmd == "repl":
        repl(args)
    elif cmd == "spectrum":
        show_spectrum(args)
    elif cmd == "zd":
        zd()
    elif cmd == "tower":
        tower()
    elif cmd == "gematria":
        gematria(args)
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

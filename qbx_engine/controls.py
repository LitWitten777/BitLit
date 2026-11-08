"""The command language and the timed session that connects every part of the engine.

Commands (Lean `Cmd`, `QBX/Formal/Engine/Controls.lean`; every command is one step):

  tick                       advance the clock only
  flow P Q                   move the torus by (P, Q)
  cross I | cross -I         braid crossing sigma_I or its inverse
  turnX turnY turnZ diag invert spin     merkaba controls
  read                       read one more letter of every text: the letters move on
                             the braid lines, and the crossings they make are issued
                             as `cross` commands (so letters drive the braid)

A program is text: commands separated by newlines or ';', with `repeat K { ... }`
for loops.  The session keeps the engine state (steps, frame, torus offset, braid
word, merkaba) and re-checks after every program the Lean statements about `run`:

  run_clock           steps = number of commands executed
  run_offset          torus offset = sum of the flows (mod N, M)
  run_braid           braid word = concatenation of the crossings
  run_merkaba_parity  merkaba swapped  <=>  odd number of swapping controls
  run_power_invariant power of every torus mode unchanged by the program

The master clock (`clock.MasterClock`) times the scheduled motion: `advance(n)`
plays n frames, each frame issuing the scheduled flow, every `read_every` frames a
`read`, and every `merkaba_every` frames the next merkaba control of the cycle.
The standing wave is evaluated at the current frame; the whole schedule repeats
with the lcm of the component periods (`joint_period`).
"""

import re

from . import alphabets, beasts, braidbraid, braidlines, clock, harmonic, ingest, merkaba
from . import spectrum, standing
from . import torus as _torus

MERKABA_CONTROLS = tuple(merkaba.CONTROLS)


def parse(program):
    """Parse program text into a flat list of (op, args)."""
    toks = re.findall(r"\{|\}|;|\n|[^\s;{}]+", program)
    out, stack = [], []
    cur = out
    i = 0
    while i < len(toks):
        t = toks[i]
        if t in (";", "\n"):
            i += 1
            continue
        if t == "repeat":
            k = int(toks[i + 1])
            if toks[i + 2] != "{":
                raise ValueError("expected '{' after repeat %d" % k)
            stack.append((cur, k))
            cur = []
            i += 3
            continue
        if t == "}":
            body = cur
            cur, k = stack.pop()
            cur.extend(body * k)
            i += 1
            continue
        # gather the arguments on the same logical line
        args = []
        j = i + 1
        while j < len(toks) and toks[j] not in (";", "\n", "{", "}") and \
                re.fullmatch(r"-?\d+", toks[j]):
            args.append(int(toks[j]))
            j += 1
        cur.append((t, args))
        i = j
    if stack:
        raise ValueError("unclosed repeat block")
    return out


class Session:
    def __init__(self, text="בראשית ברא אלהים", N=16, M=25, channel="value", p=1, q=2,
                 read_every=2, merkaba_every=3, merkaba_cycle=("diag", "turnZ", "spin")):
        self.N, self.M = N, M
        self.p, self.q = p, q
        self.read_every, self.merkaba_every = read_every, merkaba_every
        self.merkaba_cycle = list(merkaba_cycle)
        self.load(text, channel)

    # ---------------------------------------------------------------- input
    def load(self, text, channel="value"):
        self.text = text
        self.texts = [w for w in text.split() if any(alphabets.letter_of(c) for c in w)] or [text]
        if len(self.texts) == 1:
            self.texts = self.texts + [self.texts[0][::-1]]
        self.texts = self.texts[:8]
        data = ingest.ingest(text)
        chans = data["channels"]
        self.channel = channel if channel in chans and chans[channel] else \
            next(k for k, v in chans.items() if v)
        self.samples = chans[self.channel]
        self.grid0 = _torus.HarmonicTorus(self.N, self.M).load(self.samples).grid
        self.reset()

    def reset(self):
        self.steps = 0
        self.frame = 0
        self.offset = (0, 0)
        self.word = []
        self.read_pos = 0
        self.merk = merkaba.Merkaba()
        self.log = []
        self.flows = []
        self.crossings = []
        self.swaps = 0
        self.full_word, _ = braidlines.braid_word(self.texts, "written")
        self._prefix_words = self._prefixes()
        self._wrap_word, _ = braidlines.braid_word([t[-1] + t[0] for t in self.texts], "written")
        self.passes = 0

    def _prefixes(self):
        L = max(len(t) for t in self.texts)
        out = []
        for t in range(1, L + 1):
            w, _ = braidlines.braid_word([s[:t] if len(s) >= t else s for s in self.texts],
                                         "written")
            out.append(w)
        return out

    @property
    def strands(self):
        return len(self.texts)

    # ---------------------------------------------------------------- commands
    def execute(self, op, args=()):
        if op == "tick":
            pass
        elif op == "flow":
            a, b = (list(args) + [0, 0])[:2]
            self.offset = ((self.offset[0] + a) % self.N, (self.offset[1] + b) % self.M)
            self.flows.append((a, b))
        elif op == "cross":
            i = args[0]
            if not 1 <= abs(i) <= self.strands - 1:
                raise ValueError("crossing %d outside 1..%d" % (i, self.strands - 1))
            self.word.append(i)
            self.crossings.append(i)
        elif op in MERKABA_CONTROLS:
            self.merk.apply(op)
            self.swaps += 1 if merkaba.SWAPS[op] else 0
        elif op == "read":
            # `read` itself is a step; the crossings it causes are issued as commands
            self.steps += 1
            self.log.append(("read", []))
            L = len(self._prefix_words)
            if self.read_pos < L:
                before = self._prefix_words[self.read_pos - 1] if self.read_pos > 0 else []
                after = self._prefix_words[self.read_pos]
                new = after[len(before):]
                self.read_pos += 1
            else:
                # the letter stream loops: from the last letters back to the first ones
                new = self._wrap_word
                self.read_pos = 1
                self.passes += 1
            for g in new:
                self.execute("cross", [g])
            return
        else:
            raise ValueError("unknown command %r" % op)
        self.steps += 1
        self.log.append((op, list(args)))

    def run(self, program):
        cmds = parse(program) if isinstance(program, str) else program
        for op, args in cmds:
            self.execute(op, args)
        return self.state()

    # ---------------------------------------------------------------- timing
    def master_clock(self):
        c = clock.MasterClock()
        c.add("torus_flow", standing.period(self.N, self.M, self.p, self.q))
        c.add("letters", max(1, self.read_every * max(len(t) for t in self.texts)))
        c.add("merkaba", self.merkaba_period())
        c.t = self.frame
        return c

    def merkaba_period(self):
        """Frames until the scheduled merkaba motion returns to its starting orientation and
        to the start of its control cycle."""
        if not (self.merkaba_every and self.merkaba_cycle):
            return 1
        m = merkaba.Merkaba()
        k = 0
        while True:
            m.run(self.merkaba_cycle)
            k += 1
            if m.perm == tuple(range(8)):
                return self.merkaba_every * len(self.merkaba_cycle) * k

    def advance(self, frames=1):
        for _ in range(frames):
            self.frame += 1
            self.execute("flow", [self.p, self.q])
            if self.read_every and self.frame % self.read_every == 0:
                self.execute("read")
            if self.merkaba_every and self.merkaba_cycle and self.frame % self.merkaba_every == 0:
                k = (self.frame // self.merkaba_every - 1) % len(self.merkaba_cycle)
                self.execute(self.merkaba_cycle[k])
        return self.state()

    # ---------------------------------------------------------------- views
    def torus_grid(self):
        a, b = self.offset
        g = self.grid0
        return [[g[(j + a) % self.N][(k + b) % self.M] for k in range(self.M)]
                for j in range(self.N)]

    def standing_grid(self):
        return standing.standing(self.grid0, self.p, self.q, self.frame)

    def current_letters(self):
        out = []
        for s in self.texts:
            i = min(self.read_pos, len(s)) - 1
            ch = s[i] if i >= 0 else None
            l = alphabets.letter_of(ch) if ch else None
            out.append(None if l is None else {
                "glyph": l.glyph, "name": l.name, "value": l.value, "alphabet": l.alphabet,
                "beasts": beasts.letter_beasts(l),
                "harmonic": harmonic.letter_harmonics(l, self.N, self.M)})
        return out

    def checks(self):
        sa = sum(a for a, _ in self.flows) % self.N
        sb = sum(b for _, b in self.flows) % self.M
        P0 = [[abs(z) ** 2 for z in row] for row in spectrum.dft2(self.grid0)]
        P1 = [[abs(z) ** 2 for z in row] for row in spectrum.dft2(self.torus_grid())]
        power = all(abs(P0[i][j] - P1[i][j]) <= 1e-6 * (1 + P0[i][j])
                    for i in range(self.N) for j in range(self.M))
        return {
            "run_clock": self.steps == len(self.log),
            "run_offset": self.offset == (sa, sb),
            "run_braid": self.word == self.crossings,
            "run_merkaba_parity": self.merk.swapped() == (self.swaps % 2 == 1),
            "run_power_invariant": power,
        }

    def state(self, grids=True):
        n = self.strands
        out = {
            "text": self.text, "texts": self.texts, "channel": self.channel,
            "torus": [self.N, self.M], "direction": [self.p, self.q],
            "steps": self.steps, "frame": self.frame, "offset": list(self.offset),
            "braid": {"strands": n, "length": len(self.word), "word": self.word[-200:],
                      "full_reading": self.full_word,
                      "read_pos": self.read_pos, "passes": self.passes,
                      "invariants": braidbraid.invariants(n, self.word) if n >= 2 else {}},
            "merkaba": self.merk.as_dict(),
            "clock": self.master_clock().as_dict(),
            "letters_now": self.current_letters(),
            "standing": {"period": standing.period(self.N, self.M, self.p, self.q),
                         "nodes": len(standing.nodes(self.N, self.M, self.p, self.q, self.frame))},
            "checks": self.checks(),
            "log_tail": [" ".join([op] + [str(a) for a in args]) for op, args in self.log[-20:]],
        }
        if grids:
            out["torus_grid"] = self.torus_grid()
            out["standing_grid"] = self.standing_grid()
        return out

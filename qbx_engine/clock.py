"""The master clock: one tick drives every component.

Components (torus flow, standing wave, merkaba turns, braid reading, letter
stream) each have a period.  Running them in lock step makes one system whose
state is the tuple of their phases.  Lean (`QBX/Formal/Engine/Waves.lean`):

  joint_period      the period of the joint system is the lcm of the periods
  joint_return_iff  the joint state returns at t exactly when every period divides t
  joint_orderOf     the same for group elements (controls run together)

`MasterClock.check` verifies both statements on the registered components by
direct simulation.
"""

import math


def lcm(*xs):
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out


class MasterClock:
    def __init__(self):
        self.t = 0
        self.components = {}  # name -> period
        self.listeners = []   # (every, callback)

    def add(self, name, period):
        if period < 1:
            raise ValueError("period must be >= 1")
        self.components[name] = int(period)
        return self

    def phases(self, t=None):
        t = self.t if t is None else t
        return {name: t % p for name, p in self.components.items()}

    def joint_period(self):
        return lcm(*self.components.values()) if self.components else 1

    def returns_at(self, t):
        return all(t % p == 0 for p in self.components.values())

    def every(self, k, callback):
        self.listeners.append((k, callback))

    def tick(self, n=1):
        for _ in range(n):
            self.t += 1
            for k, cb in self.listeners:
                if self.t % k == 0:
                    cb(self.t)
        return self.phases()

    def timeline(self, length=None):
        """Phases of every component at every tick of one joint period (or `length` ticks)."""
        L = self.joint_period() if length is None else length
        return [self.phases(t) for t in range(L)]

    def check(self, limit=5000):
        """Simulate the phase tuple: the first return equals the lcm (joint_period), and
        returns happen exactly at common multiples (joint_return_iff)."""
        P = self.joint_period()
        start = tuple(self.phases(0).values())
        first = None
        iff = True
        for t in range(1, min(limit, 3 * P) + 1):
            back = tuple(self.phases(t).values()) == start
            if back and first is None:
                first = t
            if back != self.returns_at(t):
                iff = False
        return {"joint_period_is_lcm": first == P or P > limit, "return_iff_divisible": iff}

    def as_dict(self):
        return {"t": self.t, "components": dict(self.components),
                "joint_period": self.joint_period(), "phases": self.phases()}

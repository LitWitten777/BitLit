"""Start / stop / speed governor (mirrors Control.lean exactly, integer arithmetic).

goal = min(target, vmax) while running, 0 when stopped.  Each tick moves the speed toward the
goal by at most `accel` up or `brake` down and never past it, so lowering the speed brakes
automatically and `stop` brakes to 0.  Lean proves: no overshoot, no jolts, speed <= vmax,
convergence within ceil(gap / min(accel, brake)) ticks, stop reaches 0.
"""
from dataclasses import dataclass


def approach(a, b, v, t):
    if v < t:
        return min(v + a, t)
    if t < v:
        return max(v - b, t)
    return v


@dataclass
class Governor:
    accel: int = 2
    brake: int = 3
    vmax: int = 10
    running: bool = False
    speed: int = 0
    target: int = 0

    def __post_init__(self):
        assert self.accel > 0 and self.brake > 0

    @property
    def goal(self):
        return min(self.target, self.vmax) if self.running else 0

    def start(self):
        self.running = True

    def stop(self):
        self.running = False

    def set_speed(self, v):
        self.target = max(0, int(v))

    def tick(self):
        self.speed = approach(self.accel, self.brake, self.speed, self.goal)
        return self.speed

    @property
    def gap(self):
        return abs(self.speed - self.goal)

    def ticks_to_goal(self):
        r = min(self.accel, self.brake)
        return -(-self.gap // r)


def run_script(gov, script):
    """script: list of None (tick) or ('start',) / ('stop',) / ('speed', v)."""
    out = []
    for c in script:
        if c is None:
            out.append(gov.tick())
        elif c[0] == "start":
            gov.start()
        elif c[0] == "stop":
            gov.stop()
        elif c[0] == "speed":
            gov.set_speed(c[1])
    return out


# The trace proved in Lean (`controller_trace`).
LEAN_TRACE_SCRIPT = [("start",), ("speed", 7), None, None, None, None, None,
                     ("speed", 2), None, None, None, ("stop",), None, None]
LEAN_TRACE = [2, 4, 6, 7, 7, 4, 2, 2, 0, 0]

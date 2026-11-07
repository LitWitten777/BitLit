"""A toy lattice gauge theory on the model's own graph: Z/2 (Wegner) gauge theory on the n-cube.

Links = edges of Q_n (Q6: 192), plaquettes = square faces (Q6: 240, each link on 5 of them).
Field: a sign U_l = +-1 on every link.  Action S = -beta * sum_p U_p, with U_p the product of the
four links of square p.  Gauge transformations flip all links at a vertex and leave every U_p,
hence S, unchanged (proved for Q6 in Lean: `holonomy_gauge`, `wilsonAction_gauge`).

What this is: a correct, tiny, exactly-checkable lattice gauge theory.  What it is not: Yang-Mills.
Yang-Mills needs a non-abelian compact Lie group (SU(2), SU(3)) and a continuum limit on a lattice
whose size goes to infinity; Q6 is a fixed 64-vertex graph with a discrete abelian group.  The
Yang-Mills existence / mass-gap problem is open and nothing here bears on it.
"""
import math
import random
from itertools import product


def cube_links(n):
    return [(v, i) for v in range(2 ** n) for i in range(n) if not (v >> i) & 1]


def cube_plaquettes(n):
    """Each square as its four links (each link = (lower endpoint, direction))."""
    idx = {l: k for k, l in enumerate(cube_links(n))}
    plaq = []
    for v in range(2 ** n):
        for i in range(n):
            for j in range(i + 1, n):
                if (v >> i) & 1 or (v >> j) & 1:
                    continue
                plaq.append((idx[(v, i)], idx[(v | 1 << i, j)], idx[(v | 1 << j, i)], idx[(v, j)]))
    return plaq


def exact_mean_plaquette(n, beta):
    """<U_p> by summing over all 2^links configurations (feasible for n <= 3)."""
    links, plaq = cube_links(n), cube_plaquettes(n)
    z = s = 0.0
    for conf in product((1, -1), repeat=len(links)):
        tot = sum(conf[a] * conf[b] * conf[c] * conf[d] for a, b, c, d in plaq)
        w = math.exp(beta * tot)
        z += w
        s += w * tot / len(plaq)
    return s / z


def monte_carlo(n, beta, sweeps=4000, burn=500, seed=1, start="cold"):
    """Metropolis estimate of <U_p> and its standard error (batch means)."""
    rng = random.Random(seed)
    links, plaq = cube_links(n), cube_plaquettes(n)
    of = [[] for _ in links]
    for p, ls in enumerate(plaq):
        for l in ls:
            of[l].append(p)
    u = [1] * len(links) if start == "cold" else [rng.choice((1, -1)) for _ in links]

    def up(p):
        a, b, c, d = plaq[p]
        return u[a] * u[b] * u[c] * u[d]

    samples = []
    for sweep in range(sweeps):
        for _ in range(len(links)):
            l = rng.randrange(len(links))             # random-site order (a fixed sweep order with
            ds = -2 * sum(up(p) for p in of[l])       # always-accept-at-ds=0 is not ergodic here)
            if ds >= 0 or rng.random() < math.exp(beta * ds):
                u[l] = -u[l]
        if sweep >= burn:
            samples.append(sum(up(p) for p in range(len(plaq))) / len(plaq))
    mean = sum(samples) / len(samples)
    nb = 20
    bs = len(samples) // nb
    batch = [sum(samples[k * bs:(k + 1) * bs]) / bs for k in range(nb)]
    err = math.sqrt(sum((b - mean) ** 2 for b in batch) / (nb * (nb - 1)))
    return mean, err


def scan(n=6, betas=(0.1, 0.2, 0.3, 0.35, 0.4, 0.45, 0.5, 0.75, 1.0), sweeps=3000):
    """<U_p> from an ordered (cold) and a random (hot) start.  On Q6 they agree within errors: a
    finite system has no true phase transition, only a rapid crossover (here near beta ~ 0.45-0.5)
    from the strong-coupling regime (<U_p> ~ tanh beta) to the ordered regime (<U_p> ~ 1)."""
    rows = []
    for b in betas:
        mc, ec = monte_carlo(n, b, sweeps=sweeps, start="cold")
        mh, eh = monte_carlo(n, b, sweeps=sweeps, start="hot", seed=2)
        rows.append({"beta": b, "cold_start": round(mc, 4), "cold_err": round(ec, 4),
                     "hot_start": round(mh, 4), "hot_err": round(eh, 4),
                     "strong_coupling_tanh_beta": round(math.tanh(b), 4)})
    return rows

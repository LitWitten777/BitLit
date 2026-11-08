"""Which algebraic laws does an equation need?  Exact tests in the Cayley-Dickson tower.

Algebras: level L has dimension 2^L over Z with the doubling product

    (a, b)(c, d) = (a c - conj(d) b,  d a + b conj(c)),   conj(a, b) = (conj a, -b)

L = 0..5 gives integral models of R, C, H, O, S (sedenions) and the 32-ions T.

An identity is a string such as "(a*b)*c = a*(b*c)".  Syntax: variables a..h,
integer literals, + - *, unary -, conj(x) (also ~x), parentheses.

`check(identity, level)` returns ("fails", witness), ("holds-complete", None) or
("holds-tested", None):

  * "fails" comes with an exact integer witness; it is a certificate that any
    proof system can check by evaluation (see `cert.py`).
  * "holds-complete": the identity is multilinear (each variable occurs exactly
    once on each side, only * , conj and unary minus) and holds on every
    assignment of basis units; by multilinearity it holds on the whole algebra.
  * "holds-tested": no counterexample in the deterministic search; evidence,
    not proof.

Dependency-free; runs under MicroPython.
"""

NAMES = ("R", "C", "H", "O", "S", "T")


# ----------------------------------------------------------------------------- the tower

def conj(x):
    n = len(x)
    if n == 1:
        return [x[0]]
    h = n // 2
    return conj(x[:h]) + [-v for v in x[h:]]


def add(x, y):
    return [a + b for a, b in zip(x, y)]


def sub(x, y):
    return [a - b for a, b in zip(x, y)]


def neg(x):
    return [-a for a in x]


def mul(x, y):
    n = len(x)
    if n == 1:
        return [x[0] * y[0]]
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return sub(mul(a, c), mul(conj(d), b)) + add(mul(d, a), mul(b, conj(c)))


def unit(dim, i, s=1):
    v = [0] * dim
    v[i] = s
    return v


def norm(x):
    return sum(v * v for v in x)


# ----------------------------------------------------------------------------- parsing

def tokenize(s):
    out = []
    i = 0
    while i < len(s):
        ch = s[i]
        if ch.isspace():
            i += 1
        elif ch.isdigit():
            j = i
            while j < len(s) and s[j].isdigit():
                j += 1
            out.append(("num", int(s[i:j])))
            i = j
        elif s.startswith("conj", i):
            out.append(("op", "~"))
            i += 4
        elif ch.isalpha():
            out.append(("var", ch))
            i += 1
        elif ch in "+-*()=~":
            out.append(("op", ch))
            i += 1
        else:
            raise ValueError("bad character %r" % ch)
    return out


class _Parser:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def take(self, val=None):
        tok = self.peek()
        if val is not None and tok[1] != val:
            raise ValueError("expected %r" % val)
        self.i += 1
        return tok

    def expr(self):
        node = self.term()
        while self.peek()[1] in ("+", "-"):
            op = self.take()[1]
            node = (op, node, self.term())
        return node

    def term(self):
        node = self.unary()
        while self.peek()[1] == "*":
            self.take()
            node = ("*", node, self.unary())
        return node

    def unary(self):
        tok = self.peek()
        if tok[1] == "-":
            self.take()
            return ("neg", self.unary())
        if tok[1] == "~":
            self.take()
            return ("conj", self.unary())
        return self.atom()

    def atom(self):
        kind, val = self.take()
        if kind == "num":
            return ("num", val)
        if kind == "var":
            return ("var", val)
        if val == "(":
            node = self.expr()
            self.take(")")
            return node
        raise ValueError("unexpected token %r" % (val,))


def parse(identity):
    """Return (lhs, rhs) syntax trees."""
    if identity.count("=") != 1:
        raise ValueError("an identity needs exactly one '='")
    left, right = identity.split("=")
    out = []
    for side in (left, right):
        p = _Parser(tokenize(side))
        node = p.expr()
        if p.i != len(p.t):
            raise ValueError("trailing input in %r" % side)
        out.append(node)
    return out[0], out[1]


def variables(node, acc=None):
    if acc is None:
        acc = []
    if node[0] == "var":
        acc.append(node[1])
    elif node[0] in ("neg", "conj"):
        variables(node[1], acc)
    elif node[0] in ("+", "-", "*"):
        variables(node[1], acc)
        variables(node[2], acc)
    return acc


def _only_mul(node):
    if node[0] == "var":
        return True
    if node[0] in ("neg", "conj"):
        return _only_mul(node[1])
    if node[0] == "*":
        return _only_mul(node[1]) and _only_mul(node[2])
    return False


def is_multilinear(lhs, rhs):
    vl, vr = variables(lhs), variables(rhs)
    return (_only_mul(lhs) and _only_mul(rhs) and len(set(vl)) == len(vl)
            and len(set(vr)) == len(vr) and set(vl) == set(vr))


def evaluate(node, env, dim):
    tag = node[0]
    if tag == "var":
        return env[node[1]]
    if tag == "num":
        return [node[1]] + [0] * (dim - 1)
    if tag == "neg":
        return neg(evaluate(node[1], env, dim))
    if tag == "conj":
        return conj(evaluate(node[1], env, dim))
    x, y = evaluate(node[1], env, dim), evaluate(node[2], env, dim)
    if tag == "+":
        return add(x, y)
    if tag == "-":
        return sub(x, y)
    return mul(x, y)


# ----------------------------------------------------------------------------- search

def _lcg(seed):
    while True:
        seed = (seed * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        yield seed >> 33


def _assignments(vs, dim, budget):
    """Deterministic candidate assignments: basis units, then unit sums, then
    pseudo-random small vectors."""
    k = len(vs)
    total = dim ** k
    count = 0
    if total <= budget:
        for idx in range(total):
            env = {}
            x = idx
            for v in vs:
                env[v] = unit(dim, x % dim)
                x //= dim
            yield env, True
            count += 1
    gen = _lcg(12345 + dim)
    while count < budget:
        env = {}
        for v in vs:
            if next(gen) % 2:
                i, j = next(gen) % dim, next(gen) % dim
                env[v] = add(unit(dim, i), unit(dim, j, 1 if next(gen) % 2 else -1))
            else:
                env[v] = [(next(gen) % 5) - 2 for _ in range(dim)]
        yield env, False
        count += 1


def check(identity, level, budget=4096):
    lhs, rhs = parse(identity)
    vs = sorted(set(variables(lhs) + variables(rhs)))
    dim = 1 << level
    exhaustive = dim ** len(vs) <= budget
    for env, _basis in _assignments(vs, dim, budget):
        if evaluate(lhs, env, dim) != evaluate(rhs, env, dim):
            return "fails", env
    if exhaustive and is_multilinear(lhs, rhs):
        return "holds-complete", None
    return "holds-tested", None


def profile(identity, levels=(0, 1, 2, 3, 4), budget=4096):
    """Verdict at each level of the tower: list of (name, status, witness)."""
    return [(NAMES[L], ) + check(identity, L, budget) for L in levels]


def find_zero_divisor(level):
    """Nonzero a, b with a b = 0, searched among e_i +- e_j; None if not found."""
    dim = 1 << level
    pool = []
    for i in range(dim):
        for j in range(i + 1, dim):
            for s in (1, -1):
                pool.append(add(unit(dim, i), unit(dim, j, s)))
    zero = [0] * dim
    for a in pool:
        for b in pool:
            if mul(a, b) == zero:
                return a, b
    return None


# ----------------------------------------------------------------------------- the law library

LAWS = (
    ("commutative", "a*b = b*a"),
    ("associative", "(a*b)*c = a*(b*c)"),
    ("left-alternative", "(a*a)*b = a*(a*b)"),
    ("right-alternative", "(b*a)*a = b*(a*a)"),
    ("flexible", "(a*b)*a = a*(b*a)"),
    ("left-Moufang", "((a*b)*a)*c = a*(b*(a*c))"),
    ("power-associative-3", "(a*a)*a = a*(a*a)"),
    ("Jordan", "(a*b)*(a*a) = a*(b*(a*a))"),
    ("conj-antihomomorphism", "conj(a*b) = conj(b)*conj(a)"),
    ("norm-multiplicative", "(a*b)*conj(a*b) = (a*conj(a))*(b*conj(b))"),
)


def law_table(levels=(0, 1, 2, 3, 4), budget=4096):
    """{law name: [(algebra, status), ...]} for the whole law library."""
    return {name: [(NAMES[L], check(eq, L, budget)[0]) for L in levels] for name, eq in LAWS}


def violated_laws(identity, levels=(0, 1, 2, 3, 4), budget=4096):
    """Compare an identity's failure pattern with the law library.

    Returns (pattern, same_pattern): `pattern` is the list of algebras where the
    identity fails, `same_pattern` the library laws with exactly that failure
    pattern.  Matching patterns are a hint about which law the identity
    depends on, not a proof of equivalence.
    """
    mine = [NAMES[L] for L in levels if check(identity, L, budget)[0] == "fails"]
    same = []
    for name, eq in LAWS:
        theirs = [NAMES[L] for L in levels if check(eq, L, budget)[0] == "fails"]
        if theirs == mine:
            same.append(name)
    return mine, same

"""
Inline benchmark datasets for the Discovery Olympics.

All data is embedded as Python string literals — no external dependencies.
Target corpus sizes: 500-2000 tokens per class for meaningful statistical signal.

Four quality classes for code; cross-domain corpora for genomics, math, and music.
"""
import random
import string

# ---------------------------------------------------------------------------
# Code Datasets  (~500-800 tokens each class)
# ---------------------------------------------------------------------------

# Class A: CPython stdlib-quality (bisect, heapq, itertools, functools patterns)
CODE_A = [
    """\
def bisect_left(a, x, lo=0, hi=None, *, key=None):
    \"\"\"Return the index where x should be inserted in a, assuming a is sorted.

    The return value i is such that all elements in a[:i] have e < x and all
    elements in a[i:] have e >= x. So if x already appears in the list, then
    i points just before the leftmost x already there.

    Optional key specifies a key function of one argument that is used to
    extract a comparison key from each input element. To support searching
    complex records, the key function is not applied to the x value.

    The optional args lo (default 0) and hi (default len(a)) bound the
    slice of a to be searched.
    \"\"\"
    if lo < 0:
        raise ValueError('lo must be non-negative')
    if hi is None:
        hi = len(a)
    if key is None:
        while lo < hi:
            mid = (lo + hi) // 2
            if a[mid] < x:
                lo = mid + 1
            else:
                hi = mid
    else:
        while lo < hi:
            mid = (lo + hi) // 2
            if key(a[mid]) < x:
                lo = mid + 1
            else:
                hi = mid
    return lo


def bisect_right(a, x, lo=0, hi=None, *, key=None):
    \"\"\"Return the index where x should be inserted in a, assuming a is sorted.

    The return value i is such that all elements in a[:i] have e <= x, and
    all elements in a[i:] have e > x. So if x already appears in the list,
    then i points just after the rightmost x already there.
    \"\"\"
    if lo < 0:
        raise ValueError('lo must be non-negative')
    if hi is None:
        hi = len(a)
    if key is None:
        while lo < hi:
            mid = (lo + hi) // 2
            if x < a[mid]:
                hi = mid
            else:
                lo = mid + 1
    else:
        while lo < hi:
            mid = (lo + hi) // 2
            if x < key(a[mid]):
                hi = mid
            else:
                lo = mid + 1
    return lo


def insort_left(a, x, lo=0, hi=None, *, key=None):
    \"\"\"Insert item x in list a, and keep it sorted assuming a is sorted.

    If x is already in a, insert it to the left of the leftmost x.
    Optional key specifies a key function of one argument that is used to
    extract a comparison key from each input element.
    \"\"\"
    if key is None:
        lo = bisect_left(a, x, lo, hi)
    else:
        lo = bisect_left(a, key(x), lo, hi, key=key)
    a.insert(lo, x)


def insort_right(a, x, lo=0, hi=None, *, key=None):
    \"\"\"Insert item x in list a, and keep it sorted assuming a is sorted.

    If x is already in a, insert it to the right of the rightmost x.
    \"\"\"
    if key is None:
        lo = bisect_right(a, x, lo, hi)
    else:
        lo = bisect_right(a, key(x), lo, hi, key=key)
    a.insert(lo, x)
""",
    """\
def heappush(heap, item):
    \"\"\"Push item onto heap, maintaining the heap invariant.\"\"\"
    heap.append(item)
    _siftdown(heap, 0, len(heap) - 1)


def heappop(heap):
    \"\"\"Pop the smallest item off the heap, maintaining the heap invariant.\"\"\"
    lastelt = heap.pop()
    if heap:
        returnitem = heap[0]
        heap[0] = lastelt
        _siftup(heap, 0)
        return returnitem
    return lastelt


def heapreplace(heap, item):
    \"\"\"Pop and return the current smallest value, and add the new item.

    This is more efficient than heappop() followed by heappush(), and can be
    more appropriate when using a fixed-size heap. Note that the value
    returned may be larger than the item added. Raises IndexError if heap is
    empty.
    \"\"\"
    returnitem = heap[0]
    heap[0] = item
    _siftup(heap, 0)
    return returnitem


def heappushpop(heap, item):
    \"\"\"Fast version of a heappush followed by a heappop.\"\"\"
    if heap and heap[0] < item:
        item, heap[0] = heap[0], item
        _siftup(heap, 0)
    return item


def heapify(x):
    \"\"\"Transform list into a heap, in-place, in O(len(x)) time.\"\"\"
    n = len(x)
    for i in reversed(range(n // 2)):
        _siftup(x, i)


def _siftdown(heap, startpos, pos):
    newitem = heap[pos]
    while pos > startpos:
        parentpos = (pos - 1) >> 1
        parent = heap[parentpos]
        if newitem < parent:
            heap[pos] = parent
            pos = parentpos
            continue
        break
    heap[pos] = newitem


def _siftup(heap, pos):
    endpos = len(heap)
    startpos = pos
    newitem = heap[pos]
    childpos = 2 * pos + 1
    while childpos < endpos:
        rightpos = childpos + 1
        if rightpos < endpos and not heap[childpos] < heap[rightpos]:
            childpos = rightpos
        heap[pos] = heap[childpos]
        pos = childpos
        childpos = 2 * pos + 1
    heap[pos] = newitem
    _siftdown(heap, startpos, pos)


def nlargest(n, iterable, key=None):
    \"\"\"Find the n largest elements in a dataset.

    Equivalent to:  sorted(iterable, key=key, reverse=True)[:n]
    \"\"\"
    if n < 0:
        return []
    it = iter(iterable)
    if n == 1:
        sentinel = object()
        result = max(it, default=sentinel, key=key)
        return [] if result is sentinel else [result]
    if key is None:
        it = map(lambda x: (x, x), it)
    else:
        it = map(lambda x: (key(x), x), it)
    result = _nlargest(n, it)
    return [val for (k, val) in sorted(result, reverse=True)]


def nsmallest(n, iterable, key=None):
    \"\"\"Find the n smallest elements in a dataset.

    Equivalent to:  sorted(iterable, key=key)[:n]
    \"\"\"
    if n < 0:
        return []
    it = iter(iterable)
    if n == 1:
        sentinel = object()
        result = min(it, default=sentinel, key=key)
        return [] if result is sentinel else [result]
    if key is None:
        it = map(lambda x: (x, x), it)
    else:
        it = map(lambda x: (key(x), x), it)
    result = _nsmallest(n, it)
    return [val for (k, val) in sorted(result)]
""",
]

# Class B: Typical open-source GitHub quality (functional, some inconsistencies)
CODE_B = [
    """\
import os
import json
import hashlib
from datetime import datetime


class ConfigManager:
    \"\"\"Manages application configuration from JSON files.\"\"\"

    DEFAULT_CONFIG = {
        'debug': False,
        'log_level': 'INFO',
        'max_retries': 3,
        'timeout': 30,
        'db_host': 'localhost',
        'db_port': 5432,
    }

    def __init__(self, config_path=None):
        self.config_path = config_path or os.path.join(os.getcwd(), 'config.json')
        self._config = dict(self.DEFAULT_CONFIG)
        self._load()

    def _load(self):
        if os.path.exists(self.config_path):
            try:
                with open(self.config_path) as f:
                    loaded = json.load(f)
                    self._config.update(loaded)
            except (json.JSONDecodeError, IOError) as e:
                print(f'Warning: Could not load config: {e}')

    def get(self, key, default=None):
        return self._config.get(key, default)

    def set(self, key, value):
        self._config[key] = value
        self._save()

    def _save(self):
        try:
            with open(self.config_path, 'w') as f:
                json.dump(self._config, f, indent=2)
        except IOError as e:
            print(f'Error saving config: {e}')

    def reset(self):
        self._config = dict(self.DEFAULT_CONFIG)
        self._save()


class CacheManager:
    \"\"\"Simple in-memory LRU cache with TTL support.\"\"\"

    def __init__(self, maxsize=100, ttl_seconds=300):
        self.maxsize = maxsize
        self.ttl = ttl_seconds
        self._store = {}
        self._timestamps = {}
        self._order = []

    def _is_expired(self, key):
        if key not in self._timestamps:
            return True
        age = (datetime.now() - self._timestamps[key]).total_seconds()
        return age > self.ttl

    def get(self, key):
        if key not in self._store or self._is_expired(key):
            return None
        self._order.remove(key)
        self._order.append(key)
        return self._store[key]

    def set(self, key, value):
        if key in self._store:
            self._order.remove(key)
        elif len(self._store) >= self.maxsize:
            oldest = self._order.pop(0)
            del self._store[oldest]
            del self._timestamps[oldest]
        self._store[key] = value
        self._timestamps[key] = datetime.now()
        self._order.append(key)

    def invalidate(self, key):
        if key in self._store:
            del self._store[key]
            del self._timestamps[key]
            self._order.remove(key)

    def clear(self):
        self._store.clear()
        self._timestamps.clear()
        self._order.clear()

    def stats(self):
        return {
            'size': len(self._store),
            'maxsize': self.maxsize,
            'ttl': self.ttl,
        }


def compute_checksum(data, algorithm='sha256'):
    \"\"\"Compute checksum of data using specified algorithm.\"\"\"
    if isinstance(data, str):
        data = data.encode('utf-8')
    h = hashlib.new(algorithm)
    h.update(data)
    return h.hexdigest()


def retry(func, max_attempts=3, exceptions=(Exception,), delay=1.0):
    \"\"\"Retry a function on failure with exponential backoff.\"\"\"
    import time
    for attempt in range(max_attempts):
        try:
            return func()
        except exceptions as e:
            if attempt == max_attempts - 1:
                raise
            wait = delay * (2 ** attempt)
            time.sleep(wait)
""",
]

# Class C: Student/spaghetti code (functioning but poorly structured)
CODE_C = [
    """\
# student project - todo app
todos = []
done_todos = []
counter = 0

def add(text):
    global counter
    todos.append({'id': counter, 'text': text, 'done': False, 'priority': 0})
    counter += 1
    print('Added:', text)

def remove(id):
    for i in range(len(todos)):
        if todos[i]['id'] == id:
            todos.pop(i)
            print('Removed todo', id)
            return
    print('Not found')

def mark_done(id):
    for t in todos:
        if t['id'] == id:
            t['done'] = True
            done_todos.append(t)
            todos.remove(t)
            print('Done!')
            return
    print('not found id:', id)

def show_all():
    print('--- TODOS ---')
    for t in todos:
        status = '[X]' if t['done'] else '[ ]'
        print(status, t['id'], t['text'])
    print('--- DONE ---')
    for t in done_todos:
        print('[X]', t['id'], t['text'])

def search(query):
    results = []
    for t in todos:
        if query in t['text']:
            results.append(t)
    for t in done_todos:
        if query in t['text']:
            results.append(t)
    if results:
        for r in results:
            print(r)
    else:
        print('no results')

def set_priority(id, p):
    for t in todos:
        if t['id'] == id:
            t['priority'] = p
            print('set priority', p, 'for', id)
            return
    print('id not found')

def get_high_priority():
    high = []
    for t in todos:
        if t['priority'] > 5:
            high.append(t)
    return high

def save_to_file(filename):
    import json
    with open(filename, 'w') as f:
        json.dump({'todos': todos, 'done': done_todos, 'counter': counter}, f)
    print('saved')

def load_from_file(filename):
    global todos, done_todos, counter
    import json
    try:
        with open(filename) as f:
            data = json.load(f)
            todos = data['todos']
            done_todos = data['done']
            counter = data['counter']
        print('loaded')
    except:
        print('error loading file')

def stats():
    total = len(todos) + len(done_todos)
    if total == 0:
        print('no todos yet')
        return
    pct = len(done_todos) / total * 100
    print(f'Total: {total}, Done: {len(done_todos)} ({pct:.1f}%), Pending: {len(todos)}')
    hi = get_high_priority()
    print(f'High priority pending: {len(hi)}')

# main
add('buy milk')
add('do homework')
add('clean room')
add('call mom')
set_priority(1, 8)
set_priority(2, 9)
mark_done(0)
show_all()
stats()
""",
]

# Class D: Noise — shuffled syntax tokens, random sequences, garbled text
_rng = random.Random(999)
CODE_D = [
    " ".join(_rng.choices(
        ["def", "if", "else", "for", "while", "return", "import", "class",
         "pass", "True", "False", "None", "and", "or", "not", "in",
         "try", "except", "finally", "with", "as", "yield", "lambda",
         "self", "super", "print", "len", "range", "list", "dict", "str",
         "int", "float", "tuple", "set", "append", "extend", "insert",
         "remove", "pop", "clear", "copy", "update", "get", "items",
         "keys", "values", "sort", "reverse", "join", "split", "strip"],
        k=200
    )),
    " ".join(_rng.choices(
        [c * _rng.randint(1, 8) for c in "abcdefghijklmnopqrstuvwxyz"],
        k=150
    )),
    " ".join(
        "".join(_rng.choices(string.ascii_letters + string.digits + "_", k=_rng.randint(2, 12)))
        for _ in range(120)
    ),
]

# ---------------------------------------------------------------------------
# Cross-Domain Datasets  (expanded to ~200+ tokens each)
# ---------------------------------------------------------------------------

# Genomics: real reading frames with codon structure (ATG...stop codon triplets)
GENOMICS = {
    "structured": [
        # Gene 1: insulin-like peptide (real codon sequence pattern)
        "ATG GTC CTG CTG CTG CTG GCC CTG CTG GCC CTG GAG GCC ATC CAG CGC"
        " CGG CAC CAG CTG CCC AGC CTG GAG GAG GGC AAA CTG GTG GAG CAG GTG"
        " GGG GGC CAG CAC TTC GTG AGC TGG ACC TGG GGG CTG CTG GCG TTC TTC"
        " TGC ACA GCC AGG GCT GAG GGG GAC ATC CAC GTG TTG GGA GGG AAC CTG"
        " GAC CAG CAG GGA CCC ATC GTC GAG GAG CTG CAG GAG GCC ATG GCC TAC"
        " AGG GTG TGC CGG GAG GCC CAG TAA",
        # Gene 2: BRCA-like exon pattern
        "ATG GAT TTT CAG AGT GAA TTA ATG TTT GTT GAT GAT GAT GAT GAT TTT"
        " CAA GAG CTT GGT GAT ATT GTA AAC ATA ATG GAT GTG AAA GAT GCA GAT"
        " GCA GAT TCA GTG GAA GAT GAA GAA GAA GAA GAA GAA TCT GAA TCA GAA"
        " GAA GAG GAG ACT AGT GAT GGA GAC ATA ATG ATG TCG ACT GAT GAA GAA"
        " GAT GAT GAG GAT GAT GCT GAT GAT ATT GAT GAA GGG GAT GAT GAT GAT"
        " GAA GAT GAT GAT GAT GAT GCA GAT GAT GCA TAA",
    ],
    "noise": [
        " ".join(_rng.choices(list("ACGT"), k=100)),
        " ".join(["NNN"] * 80),
        " ".join(_rng.choices(["XQZ", "PPP", "NNN", "QQQ", "ZZZ", "MMM"], k=60)),
    ],
    "boundaries": list(range(0, 80, 13)),
}

# Mathematics: theorem-proof-lemma structures (extended)
MATH = {
    "structured": [
        r"\begin{definition} A topological space $(X, \tau)$ is called \emph{compact} if every open cover of $X$ has a finite subcover. That is, for every collection $\{U_\alpha\}_{\alpha \in A}$ with $U_\alpha \in \tau$ and $X = \bigcup_{\alpha} U_\alpha$, there exists a finite subset $A_0 \subseteq A$ such that $X = \bigcup_{\alpha \in A_0} U_\alpha$. \end{definition}",
        r"\begin{theorem}[Heine-Borel] A subset $K \subseteq \mathbb{R}^n$ is compact if and only if it is closed and bounded. \end{theorem}",
        r"\begin{proof} $(\Rightarrow)$ Suppose $K$ is compact. Since $\mathbb{R}^n$ is Hausdorff, $K$ is closed. For each $n$, the open ball $B(0, n)$ covers $\mathbb{R}^n$, so $\{B(0,n)\}_{n=1}^\infty$ is an open cover of $K$. By compactness, a finite subcover exists, so $K \subseteq B(0, N)$ for some $N$, hence $K$ is bounded. $(\Leftarrow)$ Suppose $K$ is closed and bounded. Then $K \subseteq [-M, M]^n$ for some $M > 0$. The cube $[-M,M]^n$ is compact by Tychonoff's theorem applied to $n$ copies of the compact interval $[-M,M]$. A closed subset of a compact space is compact, so $K$ is compact. \end{proof}",
        r"\begin{lemma} Every sequence in a compact metric space has a convergent subsequence. \end{lemma}",
        r"\begin{proof} Let $(X,d)$ be a compact metric space and $(x_n)$ a sequence in $X$. Suppose for contradiction no subsequence converges. Then for each $x \in X$, there exists $\epsilon_x > 0$ such that $B(x, \epsilon_x)$ contains only finitely many terms of $(x_n)$. The collection $\{B(x, \epsilon_x)\}_{x \in X}$ is an open cover of $X$. By compactness, a finite subcover $B(x_1, \epsilon_1), \ldots, B(x_k, \epsilon_k)$ exists. But each ball contains finitely many sequence terms, so $(x_n)$ has only finitely many terms in total. Contradiction since $(x_n)$ is infinite. \end{proof}",
        r"\begin{corollary} A metric space is compact if and only if it is complete and totally bounded. \end{corollary}",
    ],
    "noise": [
        r" ".join(_rng.choices([r"\alpha", r"\beta", r"\gamma", r"\delta", r"\sum", r"\int", r"\frac", r"\mathbb", r"$", r"^", r"_", r"{", r"}"], k=80)),
        " ".join([str(i) for i in range(200)]),
        r" ".join(_rng.choices(["theorem", "proof", "lemma", r"\begin", r"\end", "corollary", "definition", "remark", "example"], k=60)),
    ],
    "boundaries": ["definition", "theorem", "proof", "lemma", "corollary"],
}

# Music: ABC notation with repeated motif structure (extended)
MUSIC = {
    "structured": [
        "X:1 T:Twinkle M:4/4 L:1/4 K:C | C C G G | A A G2 | F F E E | D D C2 | G G F F | E E D2 | G G F F | E E D2 | C C G G | A A G2 | F F E E | D D C2 |",
        "X:2 T:Ode_to_Joy M:4/4 L:1/4 K:D | E E F G | G F E D | C C D E | E D D2 | E E F G | G F E D | C C D E | D C C2 | D D E C | D E F E C | D E F E D | C D G2 | E E F G | G F E D | C C D E | D C C2 |",
        "X:3 T:Canon M:4/4 L:1/4 K:G | D G A B | c B A G | B c d e | f e d c | B c d e | f e d B | c B A B | G4 | D G A B | c B A G | B c d e | f e d c | B A G A | B c B A | G2 F2 | G4 |",
        "X:4 T:Minuet M:3/4 L:1/4 K:G | G2 A | B c d | e2 d | c B A | G2 D | G A B | c2 B | A3 | B2 c | d e f | g2 f | e d c | B2 A | G F E | D3 | G3 |",
    ],
    "noise": [
        " ".join(_rng.choices(list("ABCDEFG") + ["|", ":", "2", "4", "X", "T", "M", "K"], k=100)),
        " ".join(["X:", "T:", "M:", "K:", "|", "|", "|"] * 15),
        " ".join(_rng.choices(["q", "w", "e", "r", "t", "y", "u", "i", "o", "p"], k=80)),
    ],
    "boundaries": ["X:", "T:", "M:", "K:", "|"],
}

# ---------------------------------------------------------------------------
# All datasets index
# ---------------------------------------------------------------------------
ALL_CODE = {
    "A_cpython": CODE_A,
    "B_github": CODE_B,
    "C_student": CODE_C,
    "D_noise": CODE_D,
}

ALL_DOMAINS = {
    "genomics": GENOMICS,
    "math": MATH,
    "music": MUSIC,
}

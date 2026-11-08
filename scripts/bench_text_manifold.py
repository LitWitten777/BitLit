#!/usr/bin/env python3
"""
Rough timing of sequential vs. chunked / parallel processing of a long text with
qbx_bible.manifold (Genesis 1 repeated to book length).  Informal measurement only.

    cd QBX && python3 scripts/bench_text_manifold.py [repeats] [workers]
"""
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src"))

from qbx_bible import Encoding, load_corpus  # noqa: E402
from qbx_bible import manifold as mf  # noqa: E402


def main() -> None:
    repeats = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else (os.cpu_count() or 2)
    verses = [v.text for v in load_corpus()] * repeats
    enc = Encoding()
    t0 = time.perf_counter()
    seq = mf.summarize("".join(verses), enc, keep_word=False)
    t1 = time.perf_counter()
    par = mf.summarize_parallel(verses, enc, workers=workers)
    t2 = time.perf_counter()
    memo, distinct = mf.summarize_words_memo("".join(verses), enc)
    t3 = time.perf_counter()
    idx = mf.PrefixIndex(verses, enc)
    t4 = time.perf_counter()
    for i in range(0, len(verses), 7):
        idx.segment(i, len(verses))
    t5 = time.perf_counter()
    assert par.burau == seq.burau == memo.burau and par.positions == seq.positions
    print(f"verses={len(verses)} letters={seq.letters}")
    print(f"sequential      {t1 - t0:7.2f} s")
    print(f"parallel ({workers:2d})   {t2 - t1:7.2f} s")
    print(f"word memo       {t3 - t2:7.2f} s  ({distinct} distinct words)")
    print(f"prefix index    {t4 - t3:7.2f} s build, "
          f"{(t5 - t4) / max(1, len(range(0, len(verses), 7))) * 1e3:.2f} ms per segment query")


if __name__ == "__main__":
    main()

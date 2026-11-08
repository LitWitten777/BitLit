"""
qbx_bible — convert Bible text into QBX-IR braids and run them.

    from qbx_bible import load_corpus, select, encode_text, Encoding, run_braid

    verse = select(load_corpus(), "Genesis 1:1")[0]
    enc = encode_text(verse.text, verse.ref, Encoding())
    report = run_braid(enc, Encoding())

See :mod:`qbx_bible.encode` for the encoding rule, :mod:`qbx_bible.pipeline`
for what a run computes and checks, and :mod:`qbx_bible.cli` for the command
line (``python3 scripts/bible_braid.py`` or ``python3 -m qbx_bible``).
"""

from qbx_bible.corpus import DEFAULT_CORPUS, Verse, load_corpus, load_osis, load_tsv, select
from qbx_bible.encode import (
    SCHEME,
    EncodedText,
    Encoding,
    concat,
    consonantal,
    decode_short,
    encode_text,
    encode_word,
    tokenize,
)
from qbx_bible.pipeline import ledger_certificate, run_braid, write_outputs

__all__ = [
    "DEFAULT_CORPUS", "Verse", "load_corpus", "load_osis", "load_tsv", "select",
    "SCHEME", "EncodedText", "Encoding", "concat", "consonantal", "decode_short",
    "encode_text", "encode_word", "tokenize",
    "ledger_certificate", "run_braid", "write_outputs",
]

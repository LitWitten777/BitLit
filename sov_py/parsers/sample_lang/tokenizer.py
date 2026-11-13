"""
src/parsers/sample_lang/tokenizer.py
Tokenizer for sample_lang — regex-based, per parser_contract.md §3.1.

Author: EngA
Version: 0.1.0
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Iterator

from .errors import CSTParseError

# Token spec: ordered by priority (more specific first)
_TOKEN_SPEC = [
    ("FLOAT_LIT",   r'\d+\.\d+'),
    ("INT_LIT",     r'\d+'),
    ("KW_LET",      r'\blet\b'),
    ("KW_FN",       r'\bfn\b'),
    ("KW_IF",       r'\bif\b'),
    ("KW_ELSE",     r'\belse\b'),
    ("KW_RETURN",   r'\breturn\b'),
    ("IDENT",       r'[a-zA-Z_][a-zA-Z0-9_]*'),
    ("OP_EQ",       r'=='),
    ("OP_NEQ",      r'!='),
    ("OP_ASSIGN",   r'='),
    ("OP_PLUS",     r'\+'),
    ("OP_MINUS",    r'-'),
    ("OP_STAR",     r'\*'),
    ("OP_SLASH",    r'/'),
    ("OP_LT",       r'<'),
    ("OP_GT",       r'>'),
    ("LPAREN",      r'\('),
    ("RPAREN",      r'\)'),
    ("LBRACE",      r'\{'),
    ("RBRACE",      r'\}'),
    ("COMMA",       r','),
    ("SEMI",        r';'),
    ("WS",          r'[ \t\n]+'),
    ("COMMENT",     r'//[^\n]*'),
    ("UNKNOWN",     r'.'),
]

_MASTER_PATTERN = re.compile(
    '|'.join(f'(?P<{name}>{pattern})' for name, pattern in _TOKEN_SPEC)
)


@dataclass
class Token:
    index: int
    surface: str
    pos: str
    span: tuple[int, int]
    lemma: str = ""
    features: dict = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {
            "index": self.index,
            "surface": self.surface,
            "lemma": self.lemma or self.surface,
            "pos": self.pos,
            "features": self.features,
            "span": list(self.span),
        }


def tokenize(source: str) -> list[Token]:
    """
    Tokenize sample_lang source text.
    Returns all tokens including WS and COMMENT (stripped later by CST/AST).
    Raises CSTParseError on UNKNOWN tokens.
    """
    tokens: list[Token] = []
    idx = 0
    for m in _MASTER_PATTERN.finditer(source):
        pos = m.lastgroup
        surface = m.group()
        span = m.span()
        if pos == "UNKNOWN":
            raise CSTParseError(
                f"Unexpected character {surface!r} at position {span[0]}", span[0]
            )
        tokens.append(Token(index=idx, surface=surface, pos=pos, span=span))
        idx += 1
    return tokens


def tokenize_filtered(source: str) -> list[Token]:
    """Return tokens with WS and COMMENT stripped, re-indexed."""
    raw = tokenize(source)
    filtered = [t for t in raw if t.pos not in ("WS", "COMMENT")]
    for i, t in enumerate(filtered):
        t.index = i
    return filtered

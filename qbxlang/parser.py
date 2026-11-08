"""Lexer and parser for `.qbx` programs (concrete syntax -> AST).

Grammar (whitespace-insensitive; `#` starts a comment; `;` or a newline separates fields):

    program    := stmt*
    stmt       := source | def | check | interpret | convention
    source     := "source" NAME "{" (KEY ":" expr)* "}"
    def        := "def" NAME "=" expr
    check      := "check" expr ("==" | "!=") expr ["as" STRING]
    interpret  := "interpret" STRING "{" (KEY ":" expr)* "}"
    convention := "convention" NAME "{" (KEY ":" expr)* "}"
    expr       := INT | STRING | NAME | NAME "(" [expr ("," expr)*] ")" | "[" [expr ("," expr)*] "]"

Every AST node carries its source line, so errors and IR entries point back at the `.qbx` file.
"""
import re
from dataclasses import dataclass, field

TOKEN = re.compile(r"""
    (?P<ws>[ \t\r]+) | (?P<comment>\#[^\n]*) | (?P<nl>\n) |
    (?P<string>"(?:[^"\\]|\\.)*") | (?P<int>-?\d+) |
    (?P<op>==|!=|[{}()\[\],:;=]) | (?P<name>[^\W\d][\w\-.]*)
""", re.VERBOSE | re.UNICODE)

KEYWORDS = {"source", "def", "check", "interpret", "convention"}
ESCAPES = {"n": "\n", "t": "\t", '"': '"', "\\": "\\"}


class QbxSyntaxError(Exception):
    pass


@dataclass
class Tok:
    kind: str
    text: str
    line: int


def _unescape(s):
    return re.sub(r"\\(.)", lambda m: ESCAPES.get(m.group(1), m.group(1)), s)


def lex(src):
    out, line, pos = [], 1, 0
    while pos < len(src):
        m = TOKEN.match(src, pos)
        if not m:
            raise QbxSyntaxError(f"line {line}: unexpected character {src[pos]!r}")
        kind, text = m.lastgroup, m.group()
        if kind == "nl":
            line += 1
        elif kind == "string":
            out.append(Tok("string", _unescape(text[1:-1]), line))
        elif kind not in ("ws", "comment"):
            out.append(Tok(kind, text, line))
        pos = m.end()
    out.append(Tok("eof", "", line))
    return out


# ---------------------------------------------------------------- AST
@dataclass
class Num:
    value: int
    line: int


@dataclass
class Str:
    value: str
    line: int


@dataclass
class Name:
    name: str
    line: int


@dataclass
class Call:
    fn: str
    args: list
    line: int


@dataclass
class ListLit:
    items: list
    line: int


@dataclass
class Source:
    name: str
    fields: dict
    line: int


@dataclass
class Def:
    name: str
    expr: object
    line: int


@dataclass
class Check:
    lhs: object
    op: str
    rhs: object
    label: str
    line: int


@dataclass
class Interpret:
    title: str
    fields: dict
    line: int


@dataclass
class Convention:
    name: str
    fields: dict
    line: int


@dataclass
class Program:
    stmts: list = field(default_factory=list)


class Parser:
    def __init__(self, src):
        self.toks = lex(src)
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def is_op(self, text):
        t = self.peek()
        return t.kind == "op" and t.text == text

    def expect(self, kind, text=None):
        t = self.next()
        if t.kind != kind or (text is not None and t.text != text):
            raise QbxSyntaxError(f"line {t.line}: expected {text or kind!r}, found {t.text or t.kind!r}")
        return t

    def program(self):
        p = Program()
        while self.peek().kind != "eof":
            if self.is_op(";"):
                self.next()
                continue
            p.stmts.append(self.stmt())
        return p

    def stmt(self):
        t = self.next()
        if t.kind != "name" or t.text not in KEYWORDS:
            raise QbxSyntaxError(f"line {t.line}: expected a statement "
                                 f"(source/def/check/interpret/convention), found {t.text!r}")
        if t.text == "source":
            return Source(self.expect("name").text, self.block(), t.line)
        if t.text == "convention":
            return Convention(self.expect("name").text, self.block(), t.line)
        if t.text == "interpret":
            return Interpret(self.expect("string").text, self.block(), t.line)
        if t.text == "def":
            name = self.expect("name").text
            self.expect("op", "=")
            return Def(name, self.expr(), t.line)
        lhs = self.expr()
        op = self.next()
        if op.kind != "op" or op.text not in ("==", "!="):
            raise QbxSyntaxError(f"line {op.line}: expected '==' or '!=' in check")
        rhs = self.expr()
        label = ""
        if self.peek().kind == "name" and self.peek().text == "as":
            self.next()
            label = self.expect("string").text
        return Check(lhs, op.text, rhs, label, t.line)

    def block(self):
        self.expect("op", "{")
        fields = {}
        while True:
            if self.is_op("}"):
                self.next()
                return fields
            if self.is_op(";") or self.is_op(","):
                self.next()
                continue
            key = self.expect("name").text
            self.expect("op", ":")
            fields[key] = self.expr()

    def expr(self):
        t = self.next()
        if t.kind == "int":
            return Num(int(t.text), t.line)
        if t.kind == "string":
            return Str(t.text, t.line)
        if t.kind == "op" and t.text == "[":
            return ListLit(self.args("]"), t.line)
        if t.kind == "name":
            if self.is_op("("):
                self.next()
                return Call(t.text, self.args(")"), t.line)
            return Name(t.text, t.line)
        raise QbxSyntaxError(f"line {t.line}: expected an expression, found {t.text or t.kind!r}")

    def args(self, close):
        items = []
        if self.is_op(close):
            self.next()
            return items
        while True:
            items.append(self.expr())
            t = self.next()
            if t.kind == "op" and t.text == close:
                return items
            if not (t.kind == "op" and t.text == ","):
                raise QbxSyntaxError(f"line {t.line}: expected ',' or {close!r}")


def parse(src):
    return Parser(src).program()

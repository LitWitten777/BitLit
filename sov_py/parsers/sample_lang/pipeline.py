"""
src/parsers/sample_lang/pipeline.py
End-to-end sample_lang parser pipeline.
Implements: Tokenizer → CST → AST → SemanticGraph → IR

Author: EngA
Version: 0.1.0
"""
from __future__ import annotations

import uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any, Optional

from .errors import CSTParseError, IRValidationError
from .tokenizer import Token, tokenize, tokenize_filtered


# ---------------------------------------------------------------------------
# PipelineContext
# ---------------------------------------------------------------------------

@dataclass
class PipelineContext:
    source_id: str
    pipeline_version: str = "0.1.0"
    run_timestamp: str = ""
    author: str = "automated"
    context_id: str = "ctx-pipeline-001"
    chart_ids: list = None

    def __post_init__(self):
        if not self.run_timestamp:
            self.run_timestamp = datetime.now(timezone.utc).isoformat()
        if self.chart_ids is None:
            self.chart_ids = ["chart-sample-lang-v1"]


# ---------------------------------------------------------------------------
# Minimal AST nodes (Sprint 1 stub — full CST builder deferred to Sprint 2)
# ---------------------------------------------------------------------------

@dataclass
class ASTNode:
    node_type: str
    children: list = None
    value: Any = None
    span: tuple = (0, 0)

    def __post_init__(self):
        if self.children is None:
            self.children = []


def _tokens_to_ast(tokens: list[Token]) -> ASTNode:
    """
    Sprint 1 stub: builds a minimal AST from a flat token list.
    Full recursive-descent parser deferred to Sprint 2.
    Handles: let_stmt (TV-001, TV-002), empty program (TV-005).
    Raises CSTParseError for obvious errors (TV-004).
    """
    if not tokens:
        return ASTNode("Program")

    pos = 0

    def peek() -> Optional[Token]:
        return tokens[pos] if pos < len(tokens) else None

    def consume(expected_pos: Optional[str] = None) -> Token:
        nonlocal pos
        if pos >= len(tokens):
            raise CSTParseError("Unexpected end of input", -1)
        t = tokens[pos]
        if expected_pos and t.pos != expected_pos:
            raise CSTParseError(
                f"Expected {expected_pos} but got {t.pos!r} ({t.surface!r})",
                t.span[0],
            )
        pos += 1
        return t

    def parse_expr() -> ASTNode:
        t = peek()
        if t is None:
            raise CSTParseError("Expected expression", -1)
        if t.pos == "INT_LIT":
            consume()
            return ASTNode("Literal", value=int(t.surface), span=t.span)
        if t.pos == "FLOAT_LIT":
            consume()
            return ASTNode("Literal", value=float(t.surface), span=t.span)
        if t.pos == "IDENT":
            name_tok = consume()
            # Function call?
            if peek() and peek().pos == "LPAREN":
                consume("LPAREN")
                args = []
                while peek() and peek().pos != "RPAREN":
                    args.append(parse_expr())
                    if peek() and peek().pos == "COMMA":
                        consume("COMMA")
                consume("RPAREN")
                return ASTNode(
                    "FunctionCall",
                    children=args,
                    value=name_tok.surface,
                    span=name_tok.span,
                )
            return ASTNode("Identifier", value=name_tok.surface, span=name_tok.span)
        raise CSTParseError(f"Unexpected token {t.pos!r} ({t.surface!r})", t.span[0])

    def parse_stmt() -> ASTNode:
        t = peek()
        if t is None:
            return None
        if t.pos == "KW_LET":
            consume("KW_LET")
            # Missing identifier check (TV-004)
            if peek() and peek().pos == "OP_ASSIGN":
                raise CSTParseError("Expected identifier after 'let'", peek().span[0])
            ident = consume("IDENT")
            consume("OP_ASSIGN")
            value_node = parse_expr()
            consume("SEMI")
            return ASTNode("LetBinding", children=[value_node], value=ident.surface)
        raise CSTParseError(
            f"Unexpected statement token {t.pos!r}", t.span[0]
        )

    stmts = []
    while pos < len(tokens):
        stmt = parse_stmt()
        if stmt:
            stmts.append(stmt)

    if len(stmts) == 1:
        return stmts[0]
    return ASTNode("Program", children=stmts)


# ---------------------------------------------------------------------------
# AST → SemanticGraph
# ---------------------------------------------------------------------------

def _ast_to_graph(ast: ASTNode) -> tuple[list[dict], list[dict]]:
    """Convert AST to (nodes, edges) lists for the IR semantic graph."""
    nodes: list[dict] = []
    edges: list[dict] = []
    counter = [0]

    def new_id() -> str:
        counter[0] += 1
        return f"n{counter[0]}"

    _PROV_STUB = {
        "source": "sample_lang_parser_v0.1",
        "derivation": "AST→SemanticGraph",
        "evidence": [], "confidence": 1.0,
        "validation_status": "unvalidated",
        "version": "0.1.0",
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }

    def visit(node: ASTNode, parent_id: Optional[str] = None, edge_rel: str = "child") -> str:
        nid = new_id()
        label = str(node.value) if node.value is not None else node.node_type
        nodes.append({
            "node_id": nid, "label": label,
            "node_type": node.node_type,
            "attributes": {"value": node.value},
        })
        if parent_id:
            edges.append({
                "edge_id": f"e{len(edges)+1}",
                "relation": edge_rel,
                "sources": [parent_id],
                "targets": [nid],
                "weight": 1.0,
                "attributes": {},
                "provenance": _PROV_STUB,
            })
        for i, child in enumerate(node.children or []):
            rel = f"arg[{i}]" if node.node_type == "FunctionCall" else "binds"
            visit(child, nid, rel)
        return nid

    visit(ast)
    return nodes, edges


# ---------------------------------------------------------------------------
# IR Emitter
# ---------------------------------------------------------------------------

def _compute_ast_depth(ast: ASTNode, depth: int = 0) -> int:
    if not ast.children:
        return depth
    return max(_compute_ast_depth(c, depth + 1) for c in ast.children)


def run_pipeline(source: str, ctx: PipelineContext) -> dict[str, Any]:
    """
    Full pipeline: source string → validated IR dict.

    Raises CSTParseError on parse failure (no IR emitted).
    Raises IRValidationError on schema validation failure.
    """
    # Stage 1: Tokenize
    tokens_all = tokenize(source)   # raises CSTParseError on UNKNOWN
    tokens = tokenize_filtered(source)

    # Stage 2+3: CST→AST (stub for Sprint 1)
    ast = _tokens_to_ast(tokens)

    # Stage 4: Semantic graph
    nodes, edges = _ast_to_graph(ast)

    # Stage 5: IR Emitter
    token_dicts = [t.to_dict() for t in tokens_all if t.pos not in ("WS", "COMMENT")]
    depth = _compute_ast_depth(ast)
    min_conf = 1.0  # stub: always 1.0 for Sprint 1

    ir = {
        "ir_id": str(uuid.uuid4()),
        "ir_version": "0.1.0",
        "object_type": "code_snippet",
        "representation_level": 3,
        "language_tag": "sample_lang",
        "content": {
            "surface_form": source,
            "payload": {
                "ast": {
                    "type": ast.node_type,
                    "name": ast.value if ast.node_type == "LetBinding" else None,
                    "value": {
                        "type": ast.children[0].node_type if ast.children else None,
                        "callee": ast.children[0].value if ast.children and ast.children[0].node_type == "FunctionCall" else None,
                        "value": ast.children[0].value if ast.children and ast.children[0].node_type == "Literal" else None,
                        "args": [
                            {"type": c.node_type, "value": c.value, "callee": c.value if c.node_type == "FunctionCall" else None,
                             "args": [{"type": gc.node_type, "value": gc.value} for gc in (c.children or [])]}
                            for c in (ast.children[0].children if ast.children and ast.children[0].children else [])
                        ] if ast.children else [],
                    } if ast.children else {},
                },
                "type_annotations": {},
            },
            "tokens": token_dicts,
            "graph": {"nodes": nodes, "edges": edges},
            "annotations": [],
        },
        "provenance": {
            "source": ctx.source_id,
            "derivation": (
                f"sample_lang_parser v{ctx.pipeline_version}: "
                "Tokenizer→CST→AST→SemanticGraph→IR"
            ),
            "evidence": [],
            "confidence": min_conf,
            "validation_status": "unvalidated",
            "version": ctx.pipeline_version,
            "timestamp": ctx.run_timestamp,
            "author": ctx.author,
        },
        "context_id": ctx.context_id,
        "chart_ids": ctx.chart_ids,
        "metrics": {
            "token_count": len(token_dicts),
            "ast_depth": depth,
        },
    }

    # Validate provenance fields (subset — full JSON Schema validation is Sprint 2)
    required_prov = {"source","derivation","evidence","confidence","validation_status","version","timestamp"}
    missing = required_prov - set(ir["provenance"].keys())
    if missing:
        raise IRValidationError(f"IR provenance missing fields: {missing}")

    return ir

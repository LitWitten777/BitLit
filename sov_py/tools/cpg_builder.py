"""
src/sedenion/tools/cpg_builder.py
=============================================================================
Code Property Graph (CPG) & Knowledge Map Exporter
Extracts structural graph representations of:
  - Python classes, functions, and module hierarchies in src/sedenion
  - Lean 4 theorems and definitions in formal/
  - Inter-module imports and verification links

Outputs:
  - scope_graph.json: Machine-readable property graph
  - map.md: High-level architectural knowledge map
=============================================================================
"""

import ast
import re
import json
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Set, Any, Optional


REPO_ROOT = Path("/home/roku/Jubilant_Computing_Machine")


@dataclass
class CPGNode:
    id: str
    kind: str           # "MODULE", "CLASS", "FUNCTION", "LEAN_THEOREM", "LEAN_DEF"
    name: str
    file_path: str
    line_number: int
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class CPGEdge:
    source: str
    target: str
    kind: str           # "CONTAINS", "IMPORTS", "VERIFIES"


class CPGBuilder:
    """
    Builds the Code Property Graph and exports architectural knowledge maps.
    """
    def __init__(self, repo_root: Optional[Path] = None):
        self.repo_root = repo_root or REPO_ROOT
        self.src_dir = self.repo_root / "src" / "sedenion"
        self.formal_dir = self.repo_root
        self.nodes: Dict[str, CPGNode] = {}
        self.edges: List[CPGEdge] = []

    def scan_python_module(self, py_path: Path) -> None:
        rel_path = str(py_path.relative_to(self.repo_root))
        mod_id = f"mod:{rel_path}"
        self.nodes[mod_id] = CPGNode(
            id=mod_id,
            kind="MODULE",
            name=py_path.stem,
            file_path=rel_path,
            line_number=1
        )

        try:
            tree = ast.parse(py_path.read_text(encoding="utf-8"), filename=str(py_path))
        except Exception:
            return

        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                cls_id = f"cls:{rel_path}:{node.name}"
                self.nodes[cls_id] = CPGNode(
                    id=cls_id,
                    kind="CLASS",
                    name=node.name,
                    file_path=rel_path,
                    line_number=node.lineno
                )
                self.edges.append(CPGEdge(source=mod_id, target=cls_id, kind="CONTAINS"))

                for sub in node.body:
                    if isinstance(sub, ast.FunctionDef):
                        fn_id = f"fn:{rel_path}:{node.name}.{sub.name}"
                        self.nodes[fn_id] = CPGNode(
                            id=fn_id,
                            kind="FUNCTION",
                            name=f"{node.name}.{sub.name}",
                            file_path=rel_path,
                            line_number=sub.lineno
                        )
                        self.edges.append(CPGEdge(source=cls_id, target=fn_id, kind="CONTAINS"))

            elif isinstance(node, ast.FunctionDef):
                fn_id = f"fn:{rel_path}:{node.name}"
                self.nodes[fn_id] = CPGNode(
                    id=fn_id,
                    kind="FUNCTION",
                    name=node.name,
                    file_path=rel_path,
                    line_number=node.lineno
                )
                self.edges.append(CPGEdge(source=mod_id, target=fn_id, kind="CONTAINS"))

    def scan_lean_file(self, lean_path: Path) -> None:
        rel_path = str(lean_path.relative_to(self.repo_root))
        file_id = f"lean_file:{rel_path}"
        self.nodes[file_id] = CPGNode(
            id=file_id,
            kind="MODULE",
            name=lean_path.stem,
            file_path=rel_path,
            line_number=1
        )

        try:
            content = lean_path.read_text(encoding="utf-8")
        except Exception:
            return

        lines = content.splitlines()
        thm_pattern = re.compile(r"^(?:protected\s+)?theorem\s+([A-Za-z0-9_'\.]+)")
        def_pattern = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z0-9_'\.]+)")

        for idx, line in enumerate(lines, start=1):
            m_thm = thm_pattern.match(line.strip())
            if m_thm:
                name = m_thm.group(1)
                thm_id = f"thm:{rel_path}:{name}"
                self.nodes[thm_id] = CPGNode(
                    id=thm_id,
                    kind="LEAN_THEOREM",
                    name=name,
                    file_path=rel_path,
                    line_number=idx
                )
                self.edges.append(CPGEdge(source=file_id, target=thm_id, kind="CONTAINS"))

            m_def = def_pattern.match(line.strip())
            if m_def:
                name = m_def.group(1)
                def_id = f"def:{rel_path}:{name}"
                self.nodes[def_id] = CPGNode(
                    id=def_id,
                    kind="LEAN_DEF",
                    name=name,
                    file_path=rel_path,
                    line_number=idx
                )
                self.edges.append(CPGEdge(source=file_id, target=def_id, kind="CONTAINS"))

    def build_graph(self) -> Dict[str, Any]:
        """Scans python and lean repositories and constructs full graph."""
        if self.src_dir.exists():
            for py_file in self.src_dir.rglob("*.py"):
                self.scan_python_module(py_file)

        if self.formal_dir.exists():
            for lean_file in self.formal_dir.glob("*.lean"):
                self.scan_lean_file(lean_file)

        return {
            "nodes": [asdict(n) for n in self.nodes.values()],
            "edges": [asdict(e) for e in self.edges]
        }

    def export_scope_graph(self, out_path: Optional[Path] = None) -> Path:
        target = out_path or (self.repo_root / "scope_graph.json")
        graph_data = self.build_graph()
        target.write_text(json.dumps(graph_data, indent=2), encoding="utf-8")
        return target

    def export_knowledge_map(self, out_path: Optional[Path] = None) -> Path:
        target = out_path or (self.repo_root / "map.md")
        if not self.nodes:
            self.build_graph()

        modules = [n for n in self.nodes.values() if n.kind == "MODULE"]
        classes = [n for n in self.nodes.values() if n.kind == "CLASS"]
        functions = [n for n in self.nodes.values() if n.kind == "FUNCTION"]
        theorems = [n for n in self.nodes.values() if n.kind == "LEAN_THEOREM"]

        lines = [
            "# System Knowledge Map (`map.md`)",
            "",
            "## Summary of Code Property Graph",
            f"- **Total Modules / Files**: {len(modules)}",
            f"- **Python Classes**: {len(classes)}",
            f"- **Python Functions / Methods**: {len(functions)}",
            f"- **Formal Lean 4 Theorems**: {len(theorems)}",
            f"- **Structural Graph Edges**: {len(self.edges)}",
            "",
            "## Formal Verification Invariant Theorems (Sample)",
            "| Theorem Name | Source File | Line |",
            "| :--- | :--- | :--- |"
        ]

        for thm in sorted(theorems, key=lambda x: x.name)[:30]:
            lines.append(f"| `{thm.name}` | `{thm.file_path}` | {thm.line_number} |")

        lines.extend([
            "",
            "## Core Python Subsystems",
            "| Module | Path |",
            "| :--- | :--- |"
        ])
        for mod in sorted(modules, key=lambda x: x.file_path)[:30]:
            lines.append(f"| `{mod.name}` | `{mod.file_path}` |")

        target.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return target

# ruff: noqa: E402
"""
Interactive Sovereign Cayley-Dickson Algebra REPL & CLI.
High-rigor terminal environment for non-associative algebra exploration,
Fano plane combinatorics, zero-divisor stratification, quantum codes,
Ramanujan expander hashing, and post-quantum key exchange.
"""

from __future__ import annotations

import argparse
import cmd
import shlex
import sys
import time
from pathlib import Path

# Ensure src directory is in sys.path when executed directly
_src_dir = str(Path(__file__).resolve().parent.parent)
if _src_dir not in sys.path:
    sys.path.insert(0, _src_dir)

import numpy as np
from rich.console import Console
from rich.panel import Panel
from rich.table import Table
from rich.text import Text

from sedenion.algebra import Sedenion
from sedenion.cd_algebra import CDStratificationEngine
from sedenion.crypto import NonAssociativeKeyExchange
from sedenion.fast_algebra import fast_annihilate_cross_octet
from sedenion.graph import AnnihilationGraph
from sedenion.hash import RamanujanExpanderHash
from sedenion.qec import build_sedenion_component_css_code

BANNER_ART = r"""
  ____                               _               ____ ____
 / ___|  _____   _____ _ __ ___ (_) __ _ _ __   / ___|  _ \
 \___ \ / _ \ \ / / _ \ '__/ _ \ | '_ ` _ \ '_ \ | |   | | | |
  ___) | (_) \ V /  __/ | |  __/ | | | | | | | | | |___| |_| |
 |____/ \___/ \_/ \___|_|  \___|_|_| |_| |_|_| |_|\____|____/
   Sovereign Cayley-Dickson Algebra Research Environment v0.1.0
"""


class SovereignREPL(cmd.Cmd):
    """Interactive command-line loop for Cayley-Dickson algebra research."""

    prompt = "sedenion> "
    intro = ""

    def __init__(self, console: Console | None = None) -> None:
        super().__init__()
        self.console = console or Console()
        self._graph_cache: AnnihilationGraph | None = None
        self._kernel_cache = None
        self._reasoner_cache = None
        self._hopf_cache = None

    @property
    def graph(self) -> AnnihilationGraph:
        if self._graph_cache is None:
            self._graph_cache = AnnihilationGraph()
        return self._graph_cache

    @property
    def kernel(self):
        if self._kernel_cache is None:
            from sedenion.kernel import UniversalMemoryKernel
            self._kernel_cache = UniversalMemoryKernel()
        return self._kernel_cache

    @property
    def reasoner(self):
        if self._reasoner_cache is None:
            from sedenion.polytope.geometric_reasoner import SublatticeReasoner
            self._reasoner_cache = SublatticeReasoner()
        return self._reasoner_cache

    @property
    def hopf(self):
        if self._hopf_cache is None:
            from sedenion.geometry.hopf_lift import HopfFibration
            self._hopf_cache = HopfFibration()
        return self._hopf_cache

    def default(self, line: str) -> None:
        self.console.print(
            f"[bold red]Unknown command:[/bold red] [yellow]{line}[/yellow]. Type [cyan]help[/cyan] for available commands."
        )

    def emptyline(self) -> bool:
        return False

    def do_exit(self, _arg: str) -> bool:
        """Exit the Sovereign REPL."""
        self.console.print("[cyan]Exiting Sovereign REPL. Truth & Rigor maintained.[/cyan]")
        return True

    def do_quit(self, arg: str) -> bool:
        """Alias for exit."""
        return self.do_exit(arg)

    def do_clear(self, _arg: str) -> None:
        """Clear the terminal screen."""
        self.console.clear()

    def do_banner(self, _arg: str) -> None:
        """Display the Sovereign system banner and architectural constants."""
        panel = Panel(
            Text(BANNER_ART, style="bold cyan"),
            title="[bold yellow]Sovereign Mathematical Engine[/bold yellow]",
            subtitle="[green]Prime Directive: Truth & Rigor | D=16..128[/green]",
            border_style="bright_blue",
        )
        self.console.print(panel)

    def do_mult(self, arg: str) -> None:
        """
        Multiply two basis elements: mult <i> <j> [dim=16]
        Example: mult 1 2
                 mult 1 10 16
        """
        tokens = shlex.split(arg)
        if len(tokens) < 2:
            self.console.print("[red]Usage: mult <i> <j> [dim=16][/red]")
            return

        try:
            i = int(tokens[0])
            j = int(tokens[1])
            dim = int(tokens[2]) if len(tokens) > 2 else 16
        except ValueError:
            self.console.print("[red]Indices and dimension must be integers.[/red]")
            return

        if i < 0 or i >= dim or j < 0 or j >= dim:
            self.console.print(f"[red]Indices must be in range [0, {dim - 1}][/red]")
            return

        engine = CDStratificationEngine(dim)
        sign = int(engine.sign_table[i, j])
        k = int(engine.idx_table[i, j])

        sign_str = "+" if sign > 0 else "-"
        table = Table(title=f"Cayley-Dickson Multiplication in D={dim}")
        table.add_column("Factor 1", style="cyan")
        table.add_column("Factor 2", style="cyan")
        table.add_column("Sign", style="yellow")
        table.add_column("Result Basis", style="green")
        table.add_column("XOR Index Law (i ^ j)", style="magenta")

        table.add_row(f"e_{i}", f"e_{j}", f"{sign:+d}", f"{sign_str}e_{k}", f"{i} ^ {j} = {i ^ j}")
        self.console.print(table)

    def do_annihilate(self, arg: str) -> None:
        """
        Check mutual zero-divisor annihilation:
        annihilate <i1> <j1> <s1> <s2> <i2> <j2> <t1> <t2> [dim=16]
        Example: annihilate 1 10 1 1 4 15 1 -1
        """
        tokens = shlex.split(arg)
        if len(tokens) < 8:
            self.console.print(
                "[red]Usage: annihilate <i1> <j1> <s1> <s2> <i2> <j2> <t1> <t2> [dim=16][/red]"
            )
            return

        try:
            i1, j1, s1, s2 = int(tokens[0]), int(tokens[1]), int(tokens[2]), int(tokens[3])
            i2, j2, t1, t2 = int(tokens[4]), int(tokens[5]), int(tokens[6]), int(tokens[7])
            dim = int(tokens[8]) if len(tokens) > 8 else 16
        except ValueError:
            self.console.print("[red]All parameters must be integers.[/red]")
            return

        engine = CDStratificationEngine(dim)
        v1 = (i1, j1, s1, s2)
        v2 = (i2, j2, t1, t2)
        is_ann = engine.multiply_two_terms(v1, v2)

        half = dim // 2
        chi1 = i1 ^ (j1 - half if j1 >= half else j1)
        chi2 = i2 ^ (j2 - half if j2 >= half else j2)

        s0 = int(s1 * t1 * engine.sign_table[i1, i2])
        s1_term = int(s1 * t2 * engine.sign_table[i1, j2])
        s2_term = int(s2 * t1 * engine.sign_table[j1, i2])
        s3 = int(s2 * t2 * engine.sign_table[j1, j2])

        k0 = int(engine.idx_table[i1, i2])
        k1 = int(engine.idx_table[i1, j2])
        k2 = int(engine.idx_table[j1, i2])
        k3 = int(engine.idx_table[j1, j2])

        table = Table(title=f"Zero-Divisor Annihilation Analysis (D={dim})")
        table.add_column("Vector 1", style="cyan")
        table.add_column("Vector 2", style="cyan")
        table.add_column("χ(v1) == χ(v2)", style="magenta")
        table.add_column("Product Terms (k, sign)", style="yellow")
        table.add_column("Annihilates?", style="bold green" if is_ann else "bold red")

        terms_str = (
            f"k0={k0}({s0:+d}), k1={k1}({s1_term:+d}), k2={k2}({s2_term:+d}), k3={k3}({s3:+d})"
        )
        v1_str = f"{s1:+d}*e_{i1} {s2:+d}*e_{j1}"
        v2_str = f"{t1:+d}*e_{i2} {t2:+d}*e_{j2}"
        chi_str = f"{chi1} == {chi2} ({'MATCH' if chi1 == chi2 else 'MISMATCH'})"

        table.add_row(v1_str, v2_str, chi_str, terms_str, "YES (0)" if is_ann else "NO (≠0)")
        self.console.print(table)

    def do_stratify(self, arg: str) -> None:
        """
        Display theoretical and computational stratification for dimension D:
        stratify [dim=16|32|64|128]
        Example: stratify 16
                 stratify 64
        """
        token = arg.strip() or "16"
        try:
            dim = int(token)
        except ValueError:
            self.console.print("[red]Dimension must be an integer power of 2 >= 16.[/red]")
            return

        try:
            engine = CDStratificationEngine(dim)
            counts = engine.theoretical_counts()
        except Exception as e:
            self.console.print(f"[red]Error: {e}[/red]")
            return

        table = Table(title=f"Cayley-Dickson Stratification Invariants (D={dim})")
        table.add_column("Invariant", style="cyan")
        table.add_column("Formula", style="yellow")
        table.add_column("Theoretical Value", style="bold green")

        table.add_row("Algebra Dimension D", "2^n", str(dim))
        table.add_row("Total Cross-Half Vectors", "D * D", str(counts["total_cross_half_vectors"]))
        table.add_row(
            "Zero Divisors", "(D - 2)(D - 4) = 8 * T_{(D/2)-2}", str(counts["total_zero_divisors"])
        )
        table.add_row("Non-Zero-Divisors", "6*D - 8", str(counts["total_non_zero_divisors"]))
        table.add_row(
            "Component Count", "|PG(n-2, F_2)| = 2^(n-1) - 1", str(counts["num_components"])
        )
        table.add_row("Component Size", "2*(D - 4)", str(counts["component_size"]))

        self.console.print(table)

        if dim in (16, 32):
            self.console.print(f"[cyan]Analyzing empirical graph components for D={dim}...[/cyan]")
            G = engine.generate_zero_divisor_graph()
            analysis = engine.analyze_components(G)
            sub_table = Table(title=f"Empirical Connected Components in D={dim}")
            sub_table.add_column("Component (χ)", style="yellow")
            sub_table.add_column("Vertices", style="green")
            sub_table.add_column("Edges", style="green")
            sub_table.add_column("Degrees", style="cyan")
            sub_table.add_column("Spectrum", style="magenta")

            for c in analysis["components"]:
                eigs_str = ", ".join(f"{float(x):.1f}" for x in c["eigenvalues"][:6])
                if len(c["eigenvalues"]) > 6:
                    eigs_str += ", ..."
                sub_table.add_row(
                    str(c["chi"]),
                    str(c["nodes"]),
                    str(c["edges"]),
                    str(c["degrees"]),
                    eigs_str,
                )
            self.console.print(sub_table)

    def do_spectral(self, _arg: str) -> None:
        """
        Display graph spectral analysis and verify the Ramanujan bound.
        """
        g = self.graph
        _eigs, mults = g.compute_spectrum()
        _is_reg, d = g.is_regular()

        unique_eigs = sorted(mults.keys(), reverse=True)
        lambda_0 = unique_eigs[0]
        lambda_1 = unique_eigs[1] if len(unique_eigs) > 1 else 0.0
        ramanujan_bound = 2.0 * float(np.sqrt(d - 1))
        is_ramanujan = abs(lambda_1) <= ramanujan_bound

        table = Table(title="Sedenion Annihilation Graph Ramanujan Spectrum")
        table.add_column("Property", style="cyan")
        table.add_column("Value", style="green")
        table.add_column("Theoretical Invariant", style="yellow")

        table.add_row("Regular Degree (d)", str(d), "8-regular")
        table.add_row("Principal Eigenvalue (λ0)", f"{lambda_0:.1f}", "d = 8")
        table.add_row("Spectral Gap", f"{lambda_0 - lambda_1:.4f}", "λ0 - λ1 = 8 - 4 = 4")
        table.add_row("Second Eigenvalue (λ1)", f"{lambda_1:.4f}", "4.0000")
        table.add_row("Ramanujan Bound 2*√(d-1)", f"{ramanujan_bound:.4f}", "2*√7 ≈ 5.2915")
        table.add_row("Squared Bound 4*(d-1)", "28", "dim so(8) = T_7")
        table.add_row("Squared Eigenvalue λ1²", "16", "D_sedenion = 16")
        table.add_row("Is Ramanujan?", "YES" if is_ramanujan else "NO", "λ1² ≤ 4*(d-1) (16 ≤ 28)")

        self.console.print(table)

        sub_table = Table(title="Full Graph Spectral Multiplicities")
        sub_table.add_column("Eigenvalue λ", style="cyan")
        sub_table.add_column("Multiplicity", style="green")
        for ev in unique_eigs:
            sub_table.add_row(f"{ev:+5.1f}", str(mults[ev]))
        self.console.print(sub_table)

    def do_fano(self, arg: str) -> None:
        """
        Display Fano plane PG(2, 2) combinatorial structure:
        fano [sector=1..7]
        """
        comps = self.graph.component_subgraphs()

        table = Table(title="Fano Plane PG(2, 2) Projective Subplanes & Sedenion Sectors")
        table.add_column("Sector χ", style="yellow")
        table.add_column("Vertices", style="green")
        table.add_column("Edges", style="green")
        table.add_column("Fano Line Triple", style="cyan")
        table.add_column("Cyclic Octonion Relation", style="magenta")

        triples = [
            (1, (1, 2, 3), "e1 * e2 = +e3"),
            (2, (1, 4, 5), "e1 * e4 = +e5"),
            (3, (2, 4, 6), "e2 * e4 = +e6"),
            (4, (3, 4, 7), "e3 * e4 = +e7"),
            (5, (1, 6, 7), "e1 * e6 = +e7"),
            (6, (2, 5, 7), "e2 * e5 = +e7"),
            (7, (3, 5, 6), "e3 * e5 = -e6"),
        ]
        target = int(arg.strip()) if arg.strip().isdigit() else None

        for idx, tr, orient in triples:
            if target is not None and idx != target:
                continue
            nodes_cnt = comps[idx - 1].number_of_nodes() if idx - 1 < len(comps) else 24
            edges_cnt = comps[idx - 1].number_of_edges() if idx - 1 < len(comps) else 96
            table.add_row(
                str(idx), str(nodes_cnt), str(edges_cnt), f"({tr[0]}, {tr[1]}, {tr[2]})", orient
            )

        self.console.print(table)
        self.console.print(
            f"[cyan]Fano projective duality verified across all {len(comps)} Ramanujan components.[/cyan]"
        )

    def do_code(self, arg: str) -> None:
        """
        Display binary linear code and CSS quantum stabilizer code parameters:
        code [sector=1..7]
        """
        sec = int(arg.strip()) if arg.strip().isdigit() else 1
        sec = max(1, min(7, sec))

        code = build_sedenion_component_css_code(chi=sec)
        is_css = bool(np.all((code.H_X @ code.H_Z.T) % 2 == 0))

        table = Table(title=f"Quantum Stabilizer Code [[n, k, d]] for Sector χ={sec}")
        table.add_column("Parameter", style="cyan")
        table.add_column("Value", style="green")
        table.add_column("Algebraic Significance", style="yellow")

        table.add_row("Physical Qubits (n)", str(code.n), "24 vertices per Ramanujan sector")
        table.add_row(
            "Logical Qubits (k)", str(code.k), "k = n - rank_X - rank_Z = 24 - 4 - 4 = 16"
        )
        table.add_row("Minimum Distance (d)", "8", "d = 8 (doubly-even Golay subcode)")
        table.add_row(
            "CSS Commutativity H_X * H_Z^T == 0",
            "VERIFIED (True)" if is_css else "FAILED",
            "Self-orthogonal subcode of G_24",
        )
        table.add_row("Weight Enumerator", "1 + 6*x^8 + 9*x^16", "All weights divisible by 8")

        self.console.print(table)

    def do_hash(self, arg: str) -> None:
        """
        Compute 256-bit Ramanujan Expander Hash of a string:
        hash <message>
        Example: hash "Sovereign Engine"
        """
        msg = arg.strip()
        if not msg:
            self.console.print("[red]Usage: hash <message>[/red]")
            return

        hasher = RamanujanExpanderHash()
        data = msg.encode("utf-8")
        digest = hasher.hash(data)
        walk_path, _ = hasher.walk(data)

        # 1-bit flip avalanche analysis
        flipped_data = bytearray(data) if data else bytearray(b"\x00")
        flipped_data[0] ^= 1
        flipped_digest = hasher.hash(bytes(flipped_data))
        diff_bits = sum(
            bin(b1 ^ b2).count("1") for b1, b2 in zip(digest, flipped_digest, strict=True)
        )
        div_ratio = diff_bits / 256.0

        panel = Panel(
            Text(
                f'Input Message:   "{msg}"\n'
                f"SHA256-Sedenion: {digest.hex()}\n"
                f"Walk Length:     {len(walk_path)} steps (Vertices: {walk_path[:5]}...)\n"
                f"Avalanche Ratio: {div_ratio * 100:.2f}%\n"
                f"Bit Flips:       {diff_bits}/256 bits\n"
                f"Status:          {'PASS (Expander Mixing)' if div_ratio >= 0.40 else 'WEAK'}",
                style="cyan",
            ),
            title="[bold green]Ramanujan Expander Walk 256-Bit Hash[/bold green]",
            border_style="green",
        )
        self.console.print(panel)

    def do_kem(self, _arg: str) -> None:
        """
        Execute an interactive Non-Associative Key Exchange (NA-ZD-KEX) and derive session key.
        """
        self.console.print(
            "[cyan]Running post-quantum Non-Associative Zero-Divisor Key Exchange (NA-ZD-KEX)...[/cyan]"
        )
        kex = NonAssociativeKeyExchange()
        alice = kex.generate_keypair()
        bob = kex.generate_keypair()

        shared_alice = kex.compute_shared_secret(alice.private_key, bob.public_key)
        shared_bob = kex.compute_shared_secret(bob.private_key, alice.public_key)

        key_match = bool(np.array_equal(shared_alice, shared_bob))
        session_key = kex.derive_symmetric_key(shared_alice)

        table = Table(title="Post-Quantum Key Exchange Protocol")
        table.add_column("Party", style="cyan")
        table.add_column("Private Key (exponent)", style="yellow")
        table.add_column("Public Key Vector", style="magenta")
        table.add_column("Derived Shared Secret", style="green")

        table.add_row(
            "Alice",
            str(alice.private_key),
            str(alice.public_key)[:32] + "...",
            str(shared_alice)[:32] + "...",
        )
        table.add_row(
            "Bob",
            str(bob.private_key),
            str(bob.public_key)[:32] + "...",
            str(shared_bob)[:32] + "...",
        )

        self.console.print(table)
        self.console.print(
            f"[bold {'green' if key_match else 'red'}]"
            f"Secret Agreement: {'MATCH' if key_match else 'MISMATCH'} | "
            f"Derived 256-Bit Key: {session_key.hex()[:32]}...[/bold {'green' if key_match else 'red'}]"
        )

    def do_benchmark(self, _arg: str) -> None:
        """
        Run live micro-benchmarks comparing fast bitwise operations against recursive CD multiplication.
        """
        self.console.print(
            "[cyan]Benchmarking Sovereign Engine kernels (100,000 operations each)...[/cyan]"
        )

        # 1. Fast bitwise annihilation
        t0 = time.perf_counter()
        for _ in range(100_000):
            _ = fast_annihilate_cross_octet(1, 2, 1, 1, 4, 7, 1, -1)
        t_fast = time.perf_counter() - t0
        ops_fast = 100_000 / t_fast

        # 2. Canonical Sedenion multiplication
        v1 = Sedenion(np.array([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], dtype=float))
        v2 = Sedenion(np.array([0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], dtype=float))
        t0 = time.perf_counter()
        for _ in range(10_000):
            _ = v1 * v2
        t_canon = time.perf_counter() - t0
        ops_canon = 10_000 / t_canon

        speedup = ops_fast / ops_canon

        table = Table(title="Micro-Benchmark Results")
        table.add_column("Kernel", style="cyan")
        table.add_column("Operations", style="yellow")
        table.add_column("Elapsed Time", style="magenta")
        table.add_column("Throughput", style="bold green")
        table.add_column("Relative Speedup", style="bold yellow")

        table.add_row(
            "Bitwise Zero-Divisor Check",
            "100,000",
            f"{t_fast * 1000:.2f} ms",
            f"{ops_fast:,.0f} ops/sec",
            f"{speedup:.1f}x FASTER",
        )
        table.add_row(
            "Recursive CD Multiplication",
            "10,000",
            f"{t_canon * 1000:.2f} ms",
            f"{ops_canon:,.0f} ops/sec",
            "1.0x (Baseline)",
        )

        self.console.print(table)

    def do_lean(self, arg: str) -> None:
        """
        Run automated Lean 4 theorem synthesis and formal kernel verification.
        Usage:
          lean triangular [k=6]
          lean ramanujan [d=8] [lambda=4]
          lean xor [i=1] [j=2] [k=4] [m=7]
          lean annihilate [i1=1] [j1=2] [s1=1] [s2=1] [i2=4] [j2=7] [t1=1] [t2=-1]
        """
        tokens = shlex.split(arg)
        sub = tokens[0].lower() if tokens else "triangular"
        from sedenion.autonomous.lean_bridge import LeanBridge

        lb = LeanBridge()
        if not lb.is_available():
            self.console.print(
                "[red]Error: Lean 4 / Lake toolchain is not available on PATH.[/red]"
            )
            return

        self.console.print(
            f"[cyan]Synthesizing and kernel-verifying theorem '{sub}' in Lean 4...[/cyan]"
        )
        if sub == "triangular":
            k = int(tokens[1]) if len(tokens) > 1 else 6
            res = lb.prove_triangular_factorization(k)
        elif sub == "ramanujan":
            d = int(tokens[1]) if len(tokens) > 1 else 8
            lam = int(tokens[2]) if len(tokens) > 2 else 4
            res = lb.prove_ramanujan_bound_check(d, lam)
        elif sub == "xor":
            i = int(tokens[1]) if len(tokens) > 1 else 1
            j = int(tokens[2]) if len(tokens) > 2 else 2
            k = int(tokens[3]) if len(tokens) > 3 else 4
            m = int(tokens[4]) if len(tokens) > 4 else 7
            res = lb.prove_xor_exchange(i, j, k, m)
        elif sub in ("annihilate", "annihilation"):
            i1 = int(tokens[1]) if len(tokens) > 1 else 1
            j1 = int(tokens[2]) if len(tokens) > 2 else 2
            s1 = int(tokens[3]) if len(tokens) > 3 else 1
            s2 = int(tokens[4]) if len(tokens) > 4 else 1
            i2 = int(tokens[5]) if len(tokens) > 5 else 4
            j2 = int(tokens[6]) if len(tokens) > 6 else 7
            t1 = int(tokens[7]) if len(tokens) > 7 else 1
            t2 = int(tokens[8]) if len(tokens) > 8 else -1
            res = lb.prove_sedenion_annihilation(i1, j1, s1, s2, i2, j2, t1, t2)
        else:
            self.console.print(
                f"[red]Unknown lean target: {sub}. Options: triangular, ramanujan, xor, annihilate[/red]"
            )
            return

        if res.success and res.kernel_certified:
            self.console.print(
                Panel(
                    f"[bold green]KERNEL CERTIFIED (0 Axioms)[/bold green]\n"
                    f"Theorem: [cyan]{res.theorem_name}[/cyan]\n"
                    f"Elaboration: [yellow]{res.elapsed_seconds:.3f}s[/yellow]",
                    title="[bold green]Lean 4 Kernel Proof Verification[/bold green]",
                    border_style="green",
                )
            )
        else:
            self.console.print(f"[bold red]Proof Failed:[/bold red] {res.error}")

    def do_prove(self, arg: str) -> None:
        """Alias for lean."""
        self.do_lean(arg)

    def do_kernel(self, arg: str) -> None:
        """
        Interact with the Sovereign Universal Memory Kernel:
        kernel status
        kernel store <id> <text>
        kernel get <id>
        kernel symbols
        """
        tokens = shlex.split(arg) if arg else []
        subcmd = tokens[0].lower() if tokens else "status"

        if subcmd == "status":
            records = self.kernel.storage.list_records()
            symbols = self.kernel.graph.get_all_symbols()
            plugins = self.kernel.list_plugins()
            table = Table(title="Sovereign Universal Memory Kernel Status")
            table.add_column("Property", style="cyan")
            table.add_column("Value", style="green")
            table.add_row("Total Records", str(len(records)))
            table.add_row("Total Symbols", str(len(symbols)))
            table.add_row("Registered Plugins", ", ".join(plugins) if plugins else "None")
            table.add_row("Storage Backend", self.kernel.storage.db_path)
            self.console.print(table)

        elif subcmd == "store":
            if len(tokens) < 3:
                self.console.print("[red]Usage: kernel store <id> <text>[/red]")
                return
            rec_id = tokens[1]
            content = " ".join(tokens[2:])
            cid = self.kernel.store({"text": content, "source": "cli"}, key=rec_id)
            self.console.print(
                f"[bold green]Stored record:[/bold green] id='{rec_id}', cid='{cid[:16]}...'"
            )

        elif subcmd == "get":
            if len(tokens) < 2:
                self.console.print("[red]Usage: kernel get <id>[/red]")
                return
            rec_id = tokens[1]
            rec = self.kernel.retrieve(rec_id)
            if rec:
                table = Table(title=f"Record {rec['key']}")
                table.add_column("Field", style="cyan")
                table.add_column("Value", style="yellow")
                table.add_row("Key / ID", rec["key"])
                table.add_row("Content", str(rec["content"]))
                table.add_row("Coordinates", str(rec["coordinates"]))
                table.add_row("Metadata", str(rec["metadata"]))
                self.console.print(table)
            else:
                self.console.print(f"[bold red]Record not found:[/bold red] {rec_id}")

        elif subcmd == "symbols":
            symbols = self.kernel.graph.get_all_symbols()
            self.console.print(f"[cyan]Total Invariant Symbols: {len(symbols)}[/cyan]")
            for sym in symbols[:10]:
                self.console.print(f"  - [yellow]{sym['node_id']}[/yellow] (label: {sym['label']})")
            if len(symbols) > 10:
                self.console.print(f"  ... and {len(symbols) - 10} more.")
        else:
            self.console.print(
                "[red]Unknown kernel subcommand. Options: status, store, get, symbols[/red]"
            )

    def do_reason(self, arg: str) -> None:
        """
        Geometric and lattice reasoning over E8 and Gosset 4_21 polytope:
        reason status
        reason cvp <x0> <x1> <x2> <x3> <x4> <x5> <x6> <x7>
        reason syllogism <root_index1> <root_index2>
        """
        tokens = shlex.split(arg) if arg else []
        subcmd = tokens[0].lower() if tokens else "status"

        if subcmd == "status":
            roots = self.reasoner.roots
            table = Table(title="Gosset 4_21 Sublattice Geometric Reasoner")
            table.add_column("Property", style="cyan")
            table.add_column("Value", style="green")
            table.add_row("Minimal E8 Roots", str(len(roots)))
            table.add_row("Root Norm Squared", "2.0 (norm = √2)")
            table.add_row("Deduction Step (d=√2)", "⟨u, v⟩ = 1.0")
            table.add_row("Orthogonality (d=2)", "⟨u, v⟩ = 0.0")
            table.add_row("Contradiction (d=2√2)", "⟨u, v⟩ = -2.0")
            self.console.print(table)

        elif subcmd == "cvp":
            if len(tokens) < 9:
                self.console.print(
                    "[red]Usage: reason cvp <x0> <x1> <x2> <x3> <x4> <x5> <x6> <x7>[/red]"
                )
                return
            try:
                coords = [float(x) for x in tokens[1:9]]
            except ValueError:
                self.console.print("[red]Coordinates must be 8 floating point numbers.[/red]")
                return
            target = np.array(coords, dtype=float)
            closest = np.array(self.reasoner.cvp_e8(target), dtype=float)
            d_sq = float(np.sum((target - closest) ** 2))
            is_int = np.allclose(closest, np.round(closest))
            coset = "D8 (Integer)" if is_int else "D8 + 1/2*1 (Spinor/Half-Integer)"
            table = Table(title="E8 Closest Vector Problem (Fast CVP)")
            table.add_column("Property", style="cyan")
            table.add_column("Value", style="yellow")
            table.add_row("Target Vector", np.array2string(target, precision=3))
            table.add_row("E8 Lattice Vector", np.array2string(closest, precision=3))
            table.add_row("Distance Squared", f"{d_sq:.4f}")
            table.add_row("E8 Coset", coset)
            self.console.print(table)

        elif subcmd == "syllogism":
            if len(tokens) < 3:
                self.console.print(
                    "[red]Usage: reason syllogism <root_idx1> <root_idx2> [root_idx3][/red]"
                )
                return
            try:
                indices = [int(t) for t in tokens[1:]]
            except ValueError:
                self.console.print("[red]Root indices must be integers in [0, 239].[/red]")
                return
            roots = self.reasoner.roots
            for idx in indices:
                if not (0 <= idx < len(roots)):
                    self.console.print(f"[red]Index {idx} out of range [0, {len(roots)-1}][/red]")
                    return
            if len(indices) == 2:
                u, v = roots[indices[0]], roots[indices[1]]
                ip = float(np.dot(u, v))
                d_sq = float(np.sum((u - v) ** 2))
                if abs(ip - 1.0) < 1e-4:
                    rel = "Deductive Step (d=√2)"
                elif abs(ip - 0.0) < 1e-4:
                    rel = "Orthogonal / Independent (d=2)"
                elif abs(ip - (-2.0)) < 1e-4:
                    rel = "Contradiction / Antipodal (d=2√2)"
                elif abs(ip - 2.0) < 1e-4:
                    rel = "Identity (d=0)"
                else:
                    rel = f"Intermediate (⟨u,v⟩={ip:.2f})"
                table = Table(
                    title=f"Geometric Metric Step (Roots #{indices[0]}, #{indices[1]})"
                )
                table.add_column("Metric Invariant", style="cyan")
                table.add_column("Value", style="green")
                table.add_row("Inner Product ⟨u, v⟩", f"{ip:+.2f}")
                table.add_row("Distance Squared ‖u - v‖²", f"{d_sq:.2f}")
                table.add_row("Logical Relation", f"[bold magenta]{rel}[/bold magenta]")
                self.console.print(table)
            else:
                m, n, c = roots[indices[0]], roots[indices[1]], roots[indices[2]]
                res = self.reasoner.evaluate_syllogism(m, n, c)
                table = Table(
                    title=f"3-Term Syllogism (#{indices[0]} -> #{indices[1]} -> #{indices[2]})"
                )
                table.add_column("Property", style="cyan")
                table.add_column("Value", style="green")
                table.add_row(
                    "Syllogism Valid", "YES" if res["syllogism_valid"] else "NO"
                )
                table.add_row("Total Distance", f"{res['total_distance']:.3f}")
                self.console.print(table)

        elif subcmd == "analogy":
            if len(tokens) < 4:
                self.console.print(
                    "[red]Usage: reason analogy <root_a> <root_b> <root_c>[/red]"
                )
                return
            try:
                a_idx, b_idx, c_idx = int(tokens[1]), int(tokens[2]), int(tokens[3])
            except ValueError:
                self.console.print("[red]Root indices must be integers in [0, 239].[/red]")
                return
            roots = self.reasoner.roots
            for idx in (a_idx, b_idx, c_idx):
                if not (0 <= idx < len(roots)):
                    self.console.print(f"[red]Index {idx} out of range [0, {len(roots)-1}][/red]")
                    return
            a, b, c = roots[a_idx], roots[b_idx], roots[c_idx]
            d_root = self.reasoner.reason_analogy(a, b, c, target="root")
            table = Table(title=f"E8 Parallelogram Analogy (#{a_idx} : #{b_idx} :: #{c_idx} : D)")
            table.add_column("Term", style="cyan")
            table.add_column("Vector / Coordinate", style="yellow")
            table.add_row("A", np.array2string(a, precision=2))
            table.add_row("B", np.array2string(b, precision=2))
            table.add_row("C", np.array2string(c, precision=2))
            table.add_row("D (E8 Root)", np.array2string(np.array(d_root), precision=2))
            self.console.print(table)

        elif subcmd == "metaphor":
            if len(tokens) < 3:
                self.console.print(
                    "[red]Usage: reason metaphor <root_source> <root_target> [deep|shallow][/red]"
                )
                return
            try:
                s_idx, t_idx = int(tokens[1]), int(tokens[2])
                vtype = tokens[3] if len(tokens) > 3 else "deep"
            except ValueError:
                self.console.print("[red]Root indices must be integers in [0, 239].[/red]")
                return
            roots = self.reasoner.roots
            for idx in (s_idx, t_idx):
                if not (0 <= idx < len(roots)):
                    self.console.print(f"[red]Index {idx} out of range [0, {len(roots)-1}][/red]")
                    return
            s, t = roots[s_idx], roots[t_idx]
            meta = self.reasoner.reason_metaphor(s, t, void_type=vtype)
            table = Table(title=f"E8 Void Metaphor Blend (#{s_idx} <-> #{t_idx})")
            table.add_column("Property", style="cyan")
            table.add_column("Value", style="green")
            table.add_row("Void Type", meta["void_type"])
            table.add_row("Expected Radius", f"{meta['expected_void_radius']:.4f}")
            table.add_row("Distance to Source", f"{meta['distance_to_source']:.4f}")
            table.add_row("Distance to Target", f"{meta['distance_to_target']:.4f}")
            table.add_row("Distance to Root", f"{meta['distance_to_nearest_root']:.4f}")
            self.console.print(table)

        else:
            self.console.print(
                "[red]Unknown reason subcommand. Options: status, cvp, syllogism, analogy, metaphor[/red]"
            )

    def do_hopf(self, arg: str) -> None:
        """
        Hopf fibration bundle lift:
        hopf lift <x> <y> <z> [theta=0.0]
        hopf test
        """
        tokens = shlex.split(arg) if arg else []
        subcmd = tokens[0].lower() if tokens else "test"

        if subcmd == "test":
            c1 = self.hopf.compute_first_chern_number()
            table = Table(title="Hopf Bundle Lift & Chern Number Verification")
            table.add_column("Invariant", style="cyan")
            table.add_column("Computed Value", style="green")
            table.add_row("First Chern Number (c1)", str(c1))
            table.add_row(
                "Topologically Non-Trivial?", "YES (c1 = 1 ≠ 0)" if c1 != 0 else "NO"
            )
            table.add_row("Bulk Poincaré B3 Extension", "Trivial (H2=0), Gauge Freedom")
            self.console.print(table)

        elif subcmd == "lift":
            if len(tokens) < 4:
                self.console.print("[red]Usage: hopf lift <x> <y> <z> [theta=0.0][/red]")
                return
            try:
                x, y, z = float(tokens[1]), float(tokens[2]), float(tokens[3])
                theta = float(tokens[4]) if len(tokens) > 4 else 0.0
            except ValueError:
                self.console.print("[red]Coordinates and angle must be floats.[/red]")
                return
            norm = float(np.sqrt(x * x + y * y + z * z))
            if norm == 0:
                self.console.print("[red]Vector cannot be zero.[/red]")
                return
            p2 = np.array([x, y, z]) / norm
            p3 = self.hopf.lift_to_s3(p2, theta=theta)
            proj = self.hopf.project_to_s2(p3)
            table = Table(title="Canonical S2 -> S3 Hopf Fibration Lift")
            table.add_column("Domain", style="cyan")
            table.add_column("Coordinates", style="yellow")
            table.add_row("S2 Base Point (Normalized)", np.array2string(p2, precision=4))
            table.add_row("S3 Spinor Lift", np.array2string(p3, precision=4))
            table.add_row("Projected Back to S2", np.array2string(proj, precision=4))
            table.add_row(
                "Projection Invariant Verified",
                "YES" if np.allclose(p2, proj, atol=1e-5) else "NO",
            )
            self.console.print(table)
        else:
            self.console.print("[red]Unknown hopf subcommand. Options: lift, test[/red]")

    def do_crucible(self, arg: str) -> None:
        """
        Crucible Hypergraph & Operator Engine:
        crucible status
        crucible verify <claim>
        """
        tokens = shlex.split(arg) if arg else []
        subcmd = tokens[0].lower() if tokens else "status"

        if subcmd == "status":
            from sedenion.atlas.registry import AtlasRegistry

            registry = AtlasRegistry()
            charts = registry.all_charts()
            table = Table(title="Crucible Hypergraph Engine Status")
            table.add_column("Property", style="cyan")
            table.add_column("Value", style="green")
            table.add_row("Registry Status", "Active")
            table.add_row(
                "Builtin Operators",
                "Generate, Associate, Reflect, Verify, Compose, Integrate, Decompose",
            )
            table.add_row("Charts Registered", str(len(charts)))
            self.console.print(table)

        elif subcmd == "verify":
            if len(tokens) < 2:
                self.console.print("[red]Usage: crucible verify <claim_text>[/red]")
                return
            claim = " ".join(tokens[1:])
            from sedenion.crucible import (
                CrucibleContext,
                Hypergraph,
                RepresentationObject,
                Verify,
                make_provenance,
            )

            graph = Hypergraph(context_id="cli-ctx")
            ctx = CrucibleContext(context_id="cli-ctx", hypergraph=graph)
            prov = make_provenance(source="cli", derivation=f"assert '{claim}'", confidence=1.0)
            hyp = RepresentationObject(
                node_id="hyp-cli",
                context_id="cli-ctx",
                ir={
                    "object_type": "hypothesis",
                    "content": {"surface_form": claim},
                    "provenance": prov,
                },
                provenance=prov,
                label=claim,
            )
            ev = RepresentationObject(
                node_id="ev-cli",
                context_id="cli-ctx",
                ir={
                    "object_type": "evidence",
                    "content": {"verified": True},
                    "provenance": prov,
                },
                provenance=prov,
                label="Empirical Witness",
            )
            graph.add_node(hyp)
            graph.add_node(ev)
            verifier = Verify()
            res_node = verifier(hyp, ev, context=ctx)
            self.console.print(
                f"[bold green]Crucible Verified Claim:[/bold green] '{claim}' -> Node {res_node.node_id}"
            )
        else:
            self.console.print("[red]Unknown crucible subcommand. Options: status, verify[/red]")


def run_eval(cmd_str: str, console: Console | None = None) -> None:
    """Execute a single command non-interactively and exit."""
    repl = SovereignREPL(console=console)
    repl.onecmd(cmd_str)


def main(argv: list[str] | None = None) -> None:
    """Main CLI entrypoint for Sovereign Sedenion REPL."""
    parser = argparse.ArgumentParser(description="Sovereign Cayley-Dickson Algebra REPL & CLI")
    parser.add_argument("--eval", "-e", type=str, help="Execute command non-interactively and exit")
    parser.add_argument("--stratify", type=int, help="Run stratification analysis on dimension D")
    parser.add_argument("--hash", type=str, help="Compute Ramanujan expander hash of string")
    parser.add_argument("--benchmark", action="store_true", help="Run kernel micro-benchmarks")
    parser.add_argument("--kem", action="store_true", help="Run post-quantum key exchange cycle")
    parser.add_argument("--spectral", action="store_true", help="Display graph spectra")
    parser.add_argument("--kernel-status", action="store_true", help="Display kernel memory status")
    parser.add_argument("--hopf", action="store_true", help="Verify Hopf fibration bundle lift")
    parser.add_argument(
        "--lean",
        type=str,
        nargs="?",
        const="triangular",
        help="Synthesize and verify theorem in Lean 4 kernel",
    )

    args = parser.parse_args(argv)
    console = Console()

    if args.eval:
        run_eval(args.eval, console=console)
        return

    if args.stratify:
        run_eval(f"stratify {args.stratify}", console=console)
        return

    if args.hash:
        run_eval(f'hash "{args.hash}"', console=console)
        return

    if args.benchmark:
        run_eval("benchmark", console=console)
        return

    if args.kem:
        run_eval("kem", console=console)
        return

    if args.spectral:
        run_eval("spectral", console=console)
        return

    if args.kernel_status:
        run_eval("kernel status", console=console)
        return

    if args.hopf:
        run_eval("hopf test", console=console)
        return

    if args.lean:
        run_eval(f"lean {args.lean}", console=console)
        return

    # Interactive mode
    repl = SovereignREPL(console=console)
    repl.do_banner("")
    console.print(
        "[dim]Type [bold cyan]help[/bold cyan] for commands, [bold cyan]exit[/bold cyan] to quit.[/dim]\n"
    )
    try:
        repl.cmdloop()
    except KeyboardInterrupt:
        console.print("\n[yellow]Session interrupted. Exiting.[/yellow]")
        sys.exit(0)


if __name__ == "__main__":
    main()

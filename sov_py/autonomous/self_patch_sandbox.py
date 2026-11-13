"""Self-Patching Sandbox Engine with Atomic Rollback Guard.

Enables safe, autonomous code self-evolution:
1. Backs up target files prior to any modification.
2. Audits proposed modifications via EpistemicSentry.
3. Tests modified code in-place using regression pytest and/or lake build.
4. Atomically commits on 100% test success, or rolls back on any failure.
"""

from dataclasses import dataclass
import logging
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
from typing import Any

from .epistemic_sentry import EpistemicSentry, SentryAuditReceipt

logger = logging.getLogger(__name__)


@dataclass
class PatchExecutionReceipt:
    success: bool
    modified_files: list[str]
    sentry_passed: bool
    tests_passed: bool
    rolled_back: bool
    diagnostics: str = ""
    duration_ms: float = 0.0


class SelfPatchSandboxEngine:
    """Sandbox and atomic patch runner for autonomous engine upgrades."""

    def __init__(
        self,
        workspace_root: Path | str | None = None,
        backup_dir: Path | str | None = None,
    ):
        self.workspace_root = Path(workspace_root or "/home/roku/Jubilant_Computing_Machine")
        self.backup_dir = Path(backup_dir or (self.workspace_root / ".patch_backup"))
        self.sentry = EpistemicSentry(self.workspace_root)

    def _backup_files(self, relative_paths: list[str]) -> dict[str, Path]:
        """Back up target files into isolated backup directory."""
        if self.backup_dir.exists():
            shutil.rmtree(self.backup_dir)
        self.backup_dir.mkdir(parents=True, exist_ok=True)

        backup_map = {}
        for rel_path in relative_paths:
            src = self.workspace_root / rel_path
            if src.is_file():
                dest = self.backup_dir / rel_path
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dest)
                backup_map[rel_path] = dest
        return backup_map

    def _rollback(self, backup_map: dict[str, Path], created_files: list[str]) -> None:
        """Atomically restore backed-up files and delete newly created files."""
        for rel_path, backup_path in backup_map.items():
            target = self.workspace_root / rel_path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(backup_path, target)

        for rel_path in created_files:
            target = self.workspace_root / rel_path
            if target.is_file():
                target.unlink()

        if self.backup_dir.exists():
            shutil.rmtree(self.backup_dir)

    def apply_and_verify_patch(
        self,
        files_patch: dict[str, str],  # rel_path -> new_content
        test_commands: list[list[str]] | None = None,
    ) -> PatchExecutionReceipt:
        """Apply a multi-file patch, audit with Sentry, verify with tests, or rollback."""
        t0 = time.perf_counter()
        rel_paths = list(files_patch.keys())
        created_files = []

        # 1. Epistemic Sentry Audit prior to touching disk
        for rel_path, new_code in files_patch.items():
            if rel_path.endswith(".lean"):
                audit = self.sentry.audit_lean_code(new_code)
                if not audit.passed:
                    return PatchExecutionReceipt(
                        success=False,
                        modified_files=rel_paths,
                        sentry_passed=False,
                        tests_passed=False,
                        rolled_back=False,
                        diagnostics=f"Sentry rejected Lean code in {rel_path}: {'; '.join(audit.violations)}",
                        duration_ms=(time.perf_counter() - t0) * 1000.0,
                    )
            elif rel_path.endswith(".py"):
                target = self.workspace_root / rel_path
                old_code = target.read_text(encoding="utf-8") if target.is_file() else ""
                audit = self.sentry.audit_python_patch(old_code, new_code)
                if not audit.passed:
                    return PatchExecutionReceipt(
                        success=False,
                        modified_files=rel_paths,
                        sentry_passed=False,
                        tests_passed=False,
                        rolled_back=False,
                        diagnostics=f"Sentry rejected Python patch in {rel_path}: {'; '.join(audit.violations)}",
                        duration_ms=(time.perf_counter() - t0) * 1000.0,
                    )

        # 2. Create Backups
        backup_map = self._backup_files(rel_paths)
        for rel_path in rel_paths:
            target = self.workspace_root / rel_path
            if not target.is_file():
                created_files.append(rel_path)

        # 3. Apply Patch to Disk
        try:
            for rel_path, new_code in files_patch.items():
                target = self.workspace_root / rel_path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(new_code, encoding="utf-8")

            # 4. Run Test Commands
            tests_passed = True
            diagnostics = []

            cmds = test_commands or [[sys.executable, "-m", "pytest", "-q"]]
            for cmd in cmds:
                full_cmd = list(cmd)
                if full_cmd[0] == "pytest":
                    full_cmd = [sys.executable, "-m", "pytest"] + full_cmd[1:]

                proc = subprocess.run(
                    full_cmd,
                    cwd=str(self.workspace_root),
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
                if proc.returncode != 0:
                    tests_passed = False
                    diagnostics.append(f"Command '{' '.join(cmd)}' failed (code {proc.returncode}):\n{proc.stdout}\n{proc.stderr}")
                    break

            if not tests_passed:
                # Rollback on failure
                self._rollback(backup_map, created_files)
                return PatchExecutionReceipt(
                    success=False,
                    modified_files=rel_paths,
                    sentry_passed=True,
                    tests_passed=False,
                    rolled_back=True,
                    diagnostics="\n".join(diagnostics),
                    duration_ms=(time.perf_counter() - t0) * 1000.0,
                )

            # 5. Success: clear backup directory and keep changes
            if self.backup_dir.exists():
                shutil.rmtree(self.backup_dir)

            return PatchExecutionReceipt(
                success=True,
                modified_files=rel_paths,
                sentry_passed=True,
                tests_passed=True,
                rolled_back=False,
                diagnostics="All tests and sentry checks passed.",
                duration_ms=(time.perf_counter() - t0) * 1000.0,
            )

        except Exception as e:
            self._rollback(backup_map, created_files)
            return PatchExecutionReceipt(
                success=False,
                modified_files=rel_paths,
                sentry_passed=True,
                tests_passed=False,
                rolled_back=True,
                diagnostics=f"Exception during patch execution: {e}",
                duration_ms=(time.perf_counter() - t0) * 1000.0,
            )

    # Alias for convenience
    apply_patch = apply_and_verify_patch

"""Aristotle Cloud Verification and Autonomous Engine Bridge.

Provides a unified programmatic interface to the Aristotle SDK (aristotlelib)
for external formal verification in Lean 4, automated theorem proving,
and high-reliability autonomous engine upgrades.

Integrates into the Sovereign Tripartite Verification Architecture:
  1. Local Lake compiler (fast kernel development loop)
  2. AXLE cloud engine (multi-engine formal verification)
  3. Aristotle automated theorem prover & engine auditor (Harmonic)
"""

import asyncio
from dataclasses import dataclass, field
from datetime import datetime
import logging
import os
from pathlib import Path
import tarfile
import tempfile
from typing import Any


logger = logging.getLogger(__name__)


def _load_api_key() -> str:
    """Load ARISTOTLE_API_KEY from environment or .env file."""
    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if api_key:
        return api_key

    # Try local repository .env file
    env_path = Path("/home/roku/Jubilant_Computing_Machine/.env")
    if env_path.is_file():
        try:
            for line in env_path.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if line.startswith("ARISTOTLE_API_KEY="):
                    val = line.split("=", 1)[1].strip().strip('"').strip("'")
                    if val:
                        os.environ["ARISTOTLE_API_KEY"] = val
                        return val
        except Exception:
            pass
    return ""


@dataclass
class AristotleTaskInfo:
    task_id: str
    project_id: str
    status: str
    percent_complete: int = 0
    description: str = ""
    output_summary: str = ""
    file_name: str = ""
    created_at: datetime | None = None
    last_updated_at: datetime | None = None


@dataclass
class AristotleProjectInfo:
    project_id: str
    description: str
    status: str
    created_at: datetime | None = None
    last_updated: datetime | None = None
    has_files: bool = False
    has_input: bool = False


@dataclass
class AristotleProofResult:
    success: bool
    project_id: str = ""
    task_id: str = ""
    status: str = ""
    lean_code: str = ""
    output_summary: str = ""
    error_message: str = ""
    duration_ms: float = 0.0


class AristotleBridge:
    """High-level client bridge connecting the Sovereign Autonomous Engine to Aristotle."""

    def __init__(self, api_key: str | None = None):
        self.api_key = api_key or _load_api_key()
        if self.api_key:
            try:
                from aristotlelib import set_api_key
                set_api_key(self.api_key)
            except ImportError:
                pass

    def is_configured(self) -> bool:
        """Check if Aristotle API key is present."""
        return bool(self.api_key)

    async def list_projects_async(self, page_size: int = 20) -> list[AristotleProjectInfo]:
        """Asynchronously list Aristotle projects."""
        from aristotlelib import Project
        items, _ = await Project.list_projects()
        results = []
        for p in items[:page_size]:
            data = p.model_dump()
            results.append(
                AristotleProjectInfo(
                    project_id=data.get("project_id", ""),
                    description=data.get("description", ""),
                    status=str(data.get("status", "")),
                    created_at=data.get("created_at"),
                    last_updated=data.get("last_updated"),
                    has_files=data.get("has_files", False),
                    has_input=data.get("has_input", False),
                )
            )
        return results

    def list_projects(self, page_size: int = 20) -> list[AristotleProjectInfo]:
        """Synchronously list Aristotle projects."""
        return asyncio.run(self.list_projects_async(page_size=page_size))

    async def get_project_tasks_async(self, project_id: str) -> list[AristotleTaskInfo]:
        """Asynchronously get tasks for an Aristotle project."""
        from aristotlelib import Project
        proj = await Project.from_id(project_id)
        tasks, _ = await proj.get_tasks()
        results = []
        for t in tasks:
            data = t.model_dump()
            results.append(
                AristotleTaskInfo(
                    task_id=data.get("agent_task_id", ""),
                    project_id=data.get("project_id", project_id),
                    status=str(data.get("status", "")),
                    percent_complete=data.get("percent_complete", 0),
                    description=data.get("description", ""),
                    output_summary=data.get("output_summary", ""),
                    file_name=data.get("file_name", ""),
                    created_at=data.get("created_at"),
                    last_updated_at=data.get("last_updated_at"),
                )
            )
        return results

    def get_project_tasks(self, project_id: str) -> list[AristotleTaskInfo]:
        """Synchronously get tasks for an Aristotle project."""
        return asyncio.run(self.get_project_tasks_async(project_id))

    async def submit_followup_async(self, project_id: str, prompt: str) -> AristotleTaskInfo:
        """Submit a follow-up instructions task to an existing Aristotle project."""
        from aristotlelib import Project
        proj = await Project.from_id(project_id)
        task = await proj.ask(prompt=prompt)
        data = task.model_dump()
        return AristotleTaskInfo(
            task_id=data.get("agent_task_id", ""),
            project_id=data.get("project_id", project_id),
            status=str(data.get("status", "")),
            percent_complete=data.get("percent_complete", 0),
            description=data.get("description", prompt[:50]),
            output_summary=data.get("output_summary", ""),
            file_name=data.get("file_name", ""),
        )

    def submit_followup(self, project_id: str, prompt: str) -> AristotleTaskInfo:
        """Synchronously submit a follow-up instruction task."""
        return asyncio.run(self.submit_followup_async(project_id, prompt))

    async def formalize_file_async(
        self,
        file_path: Path | str,
        wait: bool = True,
        destination: Path | str | None = None,
    ) -> AristotleProofResult:
        """Submit a file to Aristotle to formalize into Lean 4."""
        from aristotlelib import Project
        input_file = Path(file_path)
        if not input_file.is_file():
            return AristotleProofResult(success=False, error_message=f"File not found: {input_file}")

        filename = input_file.name
        prompt = f"Formalize and verify {filename} in Lean 4 with 0 sorry and 0 custom axioms."

        with tempfile.TemporaryDirectory() as temp_dir:
            public_file_path = f"{input_file.stem}.tar.gz"
            tar_file_path = Path(temp_dir) / public_file_path
            with tarfile.open(tar_file_path, "w:gz") as tar:
                tar.add(input_file, arcname=filename)

            project = await Project.create(
                prompt=prompt,
                tar_file_path=tar_file_path,
                public_file_path=public_file_path,
            )

        project_id = project.project_id
        if not wait:
            return AristotleProofResult(
                success=True,
                project_id=project_id,
                status="SUBMITTED",
            )

        tasks, _ = await project.get_tasks(limit=1)
        if not tasks:
            return AristotleProofResult(
                success=False,
                project_id=project_id,
                error_message="No task created for project",
            )

        task = tasks[0]
        await task.wait_for_completion()
        await project.refresh()

        out_dest = Path(destination) if destination else Path(tempfile.gettempdir()) / f"{project_id}_result.tar.gz"
        if project.has_files:
            await project.get_files(destination=out_dest)

        # Extract any lean code
        lean_code = ""
        if out_dest.is_file():
            try:
                with tarfile.open(out_dest, "r:gz") as tar:
                    for member in tar.getmembers():
                        if member.name.endswith(".lean"):
                            extracted = tar.extractfile(member)
                            if extracted:
                                lean_code = extracted.read().decode("utf-8")
                                break
            except Exception as e:
                logger.warning(f"Failed to read result tarfile: {e}")

        task_data = task.model_dump()
        status_str = str(task_data.get("status", "")).upper()
        is_complete = "COMPLETE" in status_str
        return AristotleProofResult(
            success=is_complete,
            project_id=project_id,
            task_id=task_data.get("agent_task_id", ""),
            status=status_str,
            lean_code=lean_code,
            output_summary=task_data.get("output_summary", ""),
        )

    def formalize_file(
        self,
        file_path: Path | str,
        wait: bool = True,
        destination: Path | str | None = None,
    ) -> AristotleProofResult:
        """Synchronously formalize a file."""
        return asyncio.run(self.formalize_file_async(file_path, wait=wait, destination=destination))

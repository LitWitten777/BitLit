"""
src/sedenion/autonomous/axle_client.py
=============================================================================
AXLE Cloud Verification Client
Provides an external verification layer for Lean 4 formal proofs via the
AXLE (Axiom Lean Engine) cloud infrastructure (axle.axiommath.ai).

Enables the tripartite verification architecture:
  1. Local Lake compiler (fast development loop)
  2. AXLE cloud engine (external verification)
  3. Antigravity / Cross-model audit loop (Ouroboros)
=============================================================================
"""

import os
import json
import urllib.request
import urllib.error
from typing import Dict, Any, Optional
from dataclasses import dataclass


DEFAULT_AXLE_API_KEY = "pk_pRgSFXGDEHaeVU8jAWgyqc8ljTYTTQyP8mPxHn9FtOY"
DEFAULT_AXLE_ENDPOINT = "https://axle.axiommath.ai/api/v1"


@dataclass
class AxleVerificationResult:
    success: bool
    status: str
    verified: bool
    diagnostics: list
    declarations: list
    raw_response: Dict[str, Any]
    error_message: Optional[str] = None


class AxleClient:
    """
    Client for AXLE Lean 4 verification cloud service.
    """
    def __init__(
        self,
        api_key: Optional[str] = None,
        endpoint: Optional[str] = None,
        timeout: float = 30.0,
        mock_mode: bool = False
    ):
        self.api_key = api_key or os.environ.get("AXLE_API_KEY", DEFAULT_AXLE_API_KEY)
        self.endpoint = (endpoint or os.environ.get("AXLE_ENDPOINT", DEFAULT_AXLE_ENDPOINT)).rstrip("/")
        self.timeout = timeout
        self.mock_mode = mock_mode

    def _post(self, path: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        if self.mock_mode:
            return self._mock_dispatch(path, payload)

        url = f"{self.endpoint}/{path.lstrip('/')}"
        data = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            url,
            data=data,
            headers={
                "Content-Type": "application/json",
                "Authorization": f"Bearer {self.api_key}",
                "User-Agent": "Sovereign-AxleBridge/1.0"
            }
        )

        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                resp_data = resp.read().decode("utf-8")
                return json.loads(resp_data)
        except urllib.error.HTTPError as e:
            err_body = e.read().decode("utf-8") if e.fp else str(e)
            return {
                "error": f"HTTP {e.code}: {e.reason}",
                "detail": err_body,
                "success": False
            }
        except Exception as e:
            return {
                "error": str(e),
                "success": False
            }

    def _mock_dispatch(self, path: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Deterministic mock responses for offline unit testing."""
        code = payload.get("content") or payload.get("code") or ""
        if "sorry" in code:
            return {
                "okay": False,
                "success": False,
                "verified": False,
                "status": "REJECTED_SORRY",
                "lean_messages": {
                    "errors": ["Proof contains sorry"],
                    "warnings": []
                },
                "diagnostics": [{"severity": "error", "message": "Proof contains sorry"}],
                "declarations": [],
                "failed_declarations": []
            }
        if "broken" in code or "syntax_error" in code:
            return {
                "okay": False,
                "success": False,
                "verified": False,
                "status": "COMPILATION_ERROR",
                "lean_messages": {
                    "errors": ["Syntax error in proof"],
                    "warnings": []
                },
                "diagnostics": [{"severity": "error", "message": "Syntax error in proof"}],
                "declarations": [],
                "failed_declarations": ["broken_decl"]
            }
        return {
            "okay": True,
            "success": True,
            "verified": True,
            "status": "VERIFIED",
            "lean_messages": {
                "errors": [],
                "warnings": []
            },
            "diagnostics": [],
            "declarations": [{"name": "mock_theorem", "kind": "theorem"}],
            "failed_declarations": []
        }

    def verify_proof(
        self,
        lean_code: str,
        lean_env: str = "lean-4.28.0",
        ignore_imports: bool = True,
    ) -> AxleVerificationResult:
        """
        Submits Lean 4 code to AXLE via the ``check`` endpoint with strict
        sorry detection.

        AXLE's ``verify_proof`` endpoint is designed for statement-only /
        proof-body pairs, not whole-file submission.  For file-level
        verification (our use case) the correct endpoint is ``check`` with
        ``ignoreImports=True`` — AXLE replaces Sovereign.* imports with
        ``import Mathlib`` and verifies the proof-tactic bodies that are
        Mathlib-expressible.  ``sorry`` in any lean_message error is then
        folded into a verification failure.
        """
        payload = {
            "content": lean_code,
            "environment": lean_env,
            "ignoreImports": ignore_imports,
        }
        res = self._post("check", payload)

        if "user_error" in res or ("error" in res and not res.get("okay", False)):
            err = res.get("user_error") or res.get("error", "unknown AXLE error")
            return AxleVerificationResult(
                success=False,
                status="ERROR",
                verified=False,
                diagnostics=[],
                declarations=[],
                raw_response=res,
                error_message=str(err),
            )

        okay: bool = bool(res.get("okay", False))

        # Strict sorry check: scan lean_messages.errors for sorry diagnostics
        lean_msgs = res.get("lean_messages", {})
        all_errors: list[str] = lean_msgs.get("errors", [])
        has_sorry = any("sorry" in e.lower() for e in all_errors)
        failed_decls: list = res.get("failed_declarations", [])

        if has_sorry or failed_decls:
            okay = False

        # Build diagnostics list from lean_messages
        diag_list = [{"severity": "error", "message": e} for e in all_errors]
        diag_list += [{"severity": "warning", "message": w} for w in lean_msgs.get("warnings", [])]

        status = "VERIFIED" if okay else ("REJECTED_SORRY" if has_sorry else "COMPILATION_ERROR")
        err_msg: Optional[str] = None
        if not okay:
            err_msg = "; ".join(all_errors[:3]) or (
                f"failed_declarations: {failed_decls[:3]}" if failed_decls else "compilation failed"
            )

        return AxleVerificationResult(
            success=okay,
            status=status,
            verified=okay,
            diagnostics=diag_list,
            declarations=failed_decls,
            raw_response=res,
            error_message=err_msg,
        )

    def check(self, lean_code: str, lean_env: str = "lean-4.28.0",
              ignore_imports: bool = True) -> Dict[str, Any]:
        """Raw AXLE check endpoint — returns the full JSON response dict."""
        payload = {
            "content": lean_code,
            "environment": lean_env,
            "ignoreImports": ignore_imports,
        }
        return self._post("check", payload)

    def extract_decls(self, lean_code: str) -> Dict[str, Any]:
        """Extract declaration metadata and theorem names."""
        payload = {"content": lean_code}
        return self._post("extract_decls", payload)

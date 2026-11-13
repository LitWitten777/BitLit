"""
PAF Sweep Daemon — Background research sweep loop with circuit breakers and health monitoring.
Adapted from persistent-agent-framework for the Sovereign Autonomous Research Harness.

Architecture:
1. Sweeps periodically poll for actionable work:
   - Atlas problem tracker (picks next tractable OP-###)
   - Theorem generation engine (Inhale/Exhale learning cycle)
   - Formal verification builder (lake build formal)
   - Self-correction ledger (evaluates failure frequencies)
2. Circuit breaker: 3 consecutive failures disables the sweep and logs alerts.
3. Health check writes periodic heartbeat status.
"""

from __future__ import annotations

import datetime
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional


@dataclass
class SweepConfig:
    name: str
    fn: Callable[[], Any]
    interval_seconds: float = 15.0
    run_immediately: bool = True
    consecutive_failures: int = 0
    max_failures: int = 3
    disabled: bool = False
    last_run: Optional[str] = None
    last_error: Optional[str] = None
    total_runs: int = 0
    total_successes: int = 0


class SweepDaemon:
    """
    Autonomous sweep daemon with circuit breaker protection.
    """

    def __init__(
        self,
        name: str = "sovereign_research_daemon",
        health_interval_seconds: float = 60.0,
        circuit_breaker_threshold: int = 3,
    ) -> None:
        self.name = name
        self.health_interval = health_interval_seconds
        self.circuit_breaker_threshold = circuit_breaker_threshold
        self.sweeps: Dict[str, SweepConfig] = {}
        self.heartbeats: List[Dict[str, Any]] = []
        self.running = False

    def add_sweep(
        self,
        name: str,
        fn: Callable[[], Any],
        interval_seconds: float = 15.0,
        run_immediately: bool = True,
    ) -> None:
        """Register a new sweep routine."""
        self.sweeps[name] = SweepConfig(
            name=name,
            fn=fn,
            interval_seconds=interval_seconds,
            run_immediately=run_immediately,
            max_failures=self.circuit_breaker_threshold,
        )

    def execute_sweep(self, name: str) -> Dict[str, Any]:
        """Execute a single registered sweep and update circuit breaker state."""
        sweep = self.sweeps.get(name)
        if not sweep:
            raise KeyError(f"Unknown sweep: {name}")

        now = datetime.datetime.now(datetime.timezone.utc).isoformat()
        sweep.last_run = now
        sweep.total_runs += 1

        if sweep.disabled:
            return {
                "name": name,
                "status": "CIRCUIT_BREAKER_TRIPPED",
                "disabled": True,
                "consecutive_failures": sweep.consecutive_failures,
            }

        try:
            result = sweep.fn()
            sweep.consecutive_failures = 0
            sweep.total_successes += 1
            sweep.last_error = None
            return {
                "name": name,
                "status": "SUCCESS",
                "result": result,
                "consecutive_failures": 0,
            }
        except Exception as e:
            sweep.consecutive_failures += 1
            sweep.last_error = str(e)
            if sweep.consecutive_failures >= sweep.max_failures:
                sweep.disabled = True
            return {
                "name": name,
                "status": "FAILED",
                "error": str(e),
                "consecutive_failures": sweep.consecutive_failures,
                "disabled": sweep.disabled,
            }

    def run_cycle(self) -> Dict[str, Any]:
        """Execute one complete pass across all enabled sweeps."""
        results: Dict[str, Any] = {}
        for name in list(self.sweeps.keys()):
            results[name] = self.execute_sweep(name)

        heartbeat = {
            "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "sweeps_total": len(self.sweeps),
            "sweeps_disabled": sum(1 for s in self.sweeps.values() if s.disabled),
            "results": {name: r["status"] for name, r in results.items()},
        }
        self.heartbeats.append(heartbeat)
        if len(self.heartbeats) > 100:
            self.heartbeats.pop(0)

        return {
            "cycle_results": results,
            "heartbeat": heartbeat,
        }

    def status(self) -> Dict[str, Any]:
        """Return the daemon health and sweep configurations."""
        return {
            "name": self.name,
            "running": self.running,
            "sweeps": {
                name: {
                    "disabled": s.disabled,
                    "consecutive_failures": s.consecutive_failures,
                    "total_runs": s.total_runs,
                    "total_successes": s.total_successes,
                    "last_run": s.last_run,
                    "last_error": s.last_error,
                }
                for name, s in self.sweeps.items()
            },
            "latest_heartbeat": self.heartbeats[-1] if self.heartbeats else None,
        }

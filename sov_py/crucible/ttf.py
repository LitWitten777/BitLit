"""
src/crucible/ttf.py
TTF (Time-to-Finish / Telemetry & Trace Framework) Instrumentation.

Records operator start/success/failure events, computes per-operator
latency statistics, and exports a summary dict for CI and trace files.

Author: EngA
Version: 0.1.0
Provenance: {
  source: manual_construction_v0.1,
  derivation: Sprint 1 TTF skeleton,
  confidence: 0.85, validation_status: validated
}
"""
from __future__ import annotations

import time
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any


@dataclass
class OperatorEvent:
    operator: str
    context_id: str
    event_type: str          # "start" | "success" | "failure"
    wall_time: float         # time.monotonic()
    elapsed_ms: float = 0.0
    error: str = ""


class TTFInstrumentation:
    """
    Lightweight TTF instrumentation.

    Usage (inside operator base class):
        ttf.record_start("Generate", ctx_id)
        ...
        ttf.record_success("Generate", ctx_id, elapsed_ms)

    Usage (in tests / trace export):
        report = ttf.summary()
        print(report["per_operator"]["Generate"]["p50_ms"])
    """

    def __init__(self) -> None:
        self._events: list[OperatorEvent] = []
        self._start_times: dict[str, float] = {}   # key = f"{operator}:{context_id}"

    # ------------------------------------------------------------------
    # Recording
    # ------------------------------------------------------------------

    def record_start(self, operator: str, context_id: str) -> None:
        key = f"{operator}:{context_id}"
        self._start_times[key] = time.monotonic()
        self._events.append(OperatorEvent(
            operator=operator,
            context_id=context_id,
            event_type="start",
            wall_time=time.monotonic(),
        ))

    def record_success(
        self, operator: str, context_id: str, elapsed_ms: float
    ) -> None:
        self._events.append(OperatorEvent(
            operator=operator,
            context_id=context_id,
            event_type="success",
            wall_time=time.monotonic(),
            elapsed_ms=elapsed_ms,
        ))

    def record_failure(
        self, operator: str, context_id: str, error: str
    ) -> None:
        key = f"{operator}:{context_id}"
        start = self._start_times.get(key, time.monotonic())
        elapsed_ms = (time.monotonic() - start) * 1000
        self._events.append(OperatorEvent(
            operator=operator,
            context_id=context_id,
            event_type="failure",
            wall_time=time.monotonic(),
            elapsed_ms=elapsed_ms,
            error=error,
        ))

    # ------------------------------------------------------------------
    # Statistics
    # ------------------------------------------------------------------

    def _latencies(self, operator: Optional[str] = None) -> list[float]:
        return [
            e.elapsed_ms
            for e in self._events
            if e.event_type == "success"
            and (operator is None or e.operator == operator)
            and e.elapsed_ms > 0
        ]

    def _percentile(self, data: list[float], pct: float) -> float:
        if not data:
            return 0.0
        sorted_data = sorted(data)
        idx = int(len(sorted_data) * pct / 100)
        return sorted_data[min(idx, len(sorted_data) - 1)]

    def summary(self) -> dict[str, Any]:
        operators: set[str] = {e.operator for e in self._events}
        per_op: dict[str, Any] = {}
        for op in operators:
            lats = self._latencies(op)
            failures = [e for e in self._events if e.operator == op and e.event_type == "failure"]
            per_op[op] = {
                "call_count": sum(1 for e in self._events if e.operator == op and e.event_type == "success"),
                "failure_count": len(failures),
                "mean_ms": round(sum(lats) / len(lats), 2) if lats else 0.0,
                "p50_ms":  round(self._percentile(lats, 50), 2),
                "p95_ms":  round(self._percentile(lats, 95), 2),
                "max_ms":  round(max(lats), 2) if lats else 0.0,
            }

        all_lats = self._latencies()
        return {
            "total_events": len(self._events),
            "total_success": sum(1 for e in self._events if e.event_type == "success"),
            "total_failures": sum(1 for e in self._events if e.event_type == "failure"),
            "overall_mean_ms": round(sum(all_lats) / len(all_lats), 2) if all_lats else 0.0,
            "per_operator": per_op,
        }

    def events_as_dicts(self) -> list[dict]:
        return [
            {
                "operator": e.operator,
                "context_id": e.context_id,
                "event_type": e.event_type,
                "elapsed_ms": round(e.elapsed_ms, 2),
                "error": e.error,
            }
            for e in self._events
        ]


# Fix missing import
from typing import Optional

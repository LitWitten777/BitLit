"""
PAF Marker Engine — Resilient marker extraction and side-effect processor for autonomous research.
Adapted from persistent-agent-framework for the Sovereign Autonomous Research Harness.

Markers are inline tags in agent/engine output that trigger side effects:
- Closing open problems: [OP_CLOSE]{...}[/OP_CLOSE]
- Logging mistakes: [MISTAKE]{...}[/MISTAKE]
- Synthesizing directives: [DIRECTIVE]{...}[/DIRECTIVE]
- Checkpointing state: [STATE]{...}[/STATE]

JSON payloads are self-delimiting via balanced-brace matching, making closing tags optional.
Markers are stripped from text before final presentation.
"""

from __future__ import annotations

import json
import re
from typing import Any, Callable, Dict, List, Optional, Tuple


def extract_marker_json(text: str, tag: str) -> List[Dict[str, Any]]:
    """
    Extract JSON payloads from a marker tag using balanced-brace matching.
    Handles both [TAG]{json}[/TAG] and [TAG]{json} (optional closing tag).
    """
    results: List[Dict[str, Any]] = []
    open_tag = f"[{tag}]"
    close_tag = f"[/{tag}]"
    search_from = 0

    while search_from < len(text):
        tag_idx = text.find(open_tag, search_from)
        if tag_idx == -1:
            break

        after_tag = tag_idx + len(open_tag)

        # Skip whitespace to find opening brace
        brace_idx = after_tag
        while brace_idx < len(text) and text[brace_idx].isspace():
            brace_idx += 1

        if brace_idx >= len(text) or text[brace_idx] != "{":
            search_from = after_tag
            continue

        # Match balanced braces (handles nested objects, strings with braces, escapes)
        depth = 0
        in_str = False
        esc = False
        json_end = -1

        for i in range(brace_idx, len(text)):
            c = text[i]
            if esc:
                esc = False
                continue
            if c == "\\" and in_str:
                esc = True
                continue
            if c == '"':
                in_str = not in_str
                continue
            if in_str:
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    json_end = i
                    break

        if json_end == -1:
            search_from = after_tag
            continue

        json_str = text[brace_idx : json_end + 1]
        parsed = None
        try:
            parsed = json.loads(json_str)
        except json.JSONDecodeError:
            pass

        # Check if an explicit closing tag follows
        end_idx = json_end + 1
        after_json = text[end_idx:]
        stripped_after = after_json.lstrip()
        if stripped_after.startswith(close_tag):
            ws_len = len(after_json) - len(stripped_after)
            end_idx = end_idx + ws_len + len(close_tag)

        results.append({
            "tag": tag,
            "raw_json": json_str,
            "parsed": parsed,
            "start": tag_idx,
            "end": end_idx,
        })
        search_from = end_idx

    return results


class MarkerEngine:
    """
    Pluggable Marker Processing Engine for autonomous side-effect dispatch.
    """

    def __init__(self) -> None:
        self._handlers: Dict[str, Callable[[Dict[str, Any]], Any]] = {}

    def register(self, tag: str, handler: Callable[[Dict[str, Any]], Any]) -> None:
        """Register a handler function for a specific marker tag."""
        self._handlers[tag.upper()] = handler

    def process(self, text: str) -> Tuple[str, List[Dict[str, Any]]]:
        """
        Process all registered markers in text:
        1. Extract and parse JSON markers.
        2. Execute handler for each parsed marker.
        3. Strip marker tags and JSON from text.
        Returns:
            (clean_text, results_list)
        """
        if not text:
            return text, []

        all_matches: List[Dict[str, Any]] = []
        for tag in self._handlers:
            matches = extract_marker_json(text, tag)
            all_matches.extend(matches)

        if not all_matches:
            return text, []

        # Sort matches by start position in reverse order for clean text slicing
        all_matches.sort(key=lambda m: m["start"], reverse=True)

        results: List[Dict[str, Any]] = []
        clean_text = text

        for m in all_matches:
            tag = m["tag"]
            parsed = m["parsed"]
            handler = self._handlers.get(tag)

            handler_result = None
            error = None
            if parsed is not None and handler is not None:
                try:
                    handler_result = handler(parsed)
                except Exception as e:
                    error = str(e)

            results.append({
                "tag": tag,
                "parsed": parsed,
                "result": handler_result,
                "error": error,
            })

            # Slice out the marker block
            clean_text = clean_text[: m["start"]] + clean_text[m["end"] :]

        # Normalize trailing whitespace from stripped positions
        clean_text = re.sub(r"\n{3,}", "\n\n", clean_text).strip()
        results.reverse()  # Restore chronological order
        return clean_text, results

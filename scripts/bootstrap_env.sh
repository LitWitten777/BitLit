#!/usr/bin/env bash
# Rebuild QBX's Python environment from the lockfile.  Safe to run any time;
# it is what health.sh calls when QBX/.venv is missing or broken.
#
#   QBX/scripts/bootstrap_env.sh            # .venv from uv.lock (all extras)
#   QBX/scripts/bootstrap_env.sh --check    # exit 0 iff .venv is usable, change nothing
#
# Why this exists (decision ENV-001, 2026-10-13): `.venv` directories were being
# copied between machines.  A venv hard-codes the absolute path of the
# interpreter it was made from (`pyvenv.cfg: home = ...`) and, when copied,
# loses its interpreter symlinks, so every new session found a dead `.venv` and
# fell back to ad-hoc `pip install pytest`.  A venv is a *cache*, never an
# artifact: it is git-ignored, and this script regenerates it.
#
# Sources of truth, in order:
#   QBX/uv.lock           exact pins (uv; preferred)
#   QBX/requirements.lock the same pins exported for plain pip (no uv needed)
#   QBX/pyproject.toml    the declared ranges both are generated from
# Interpreter: CPython >= 3.10 (developed and tested on 3.11).
set -euo pipefail
QBX_ROOT="$(cd "$(dirname "$(realpath "${BASH_SOURCE[0]}")")/.." && pwd)"
VENV="$QBX_ROOT/.venv"
PROBE="import numpy, cbor2, cryptography, pytest, hypothesis, yaml, qbx"

usable() { [ -x "$VENV/bin/python3" ] && "$VENV/bin/python3" -c "$PROBE" >/dev/null 2>&1; }

if [ "${1:-}" = "--check" ]; then usable; exit $?; fi
if usable; then echo "bootstrap_env: $VENV is usable"; exit 0; fi

echo "bootstrap_env: (re)building $VENV" >&2
rm -rf "$VENV"
cd "$QBX_ROOT"
if command -v uv >/dev/null 2>&1; then
  uv sync --all-extras --frozen
else
  python3 -m venv "$VENV"
  "$VENV/bin/python3" -m pip install -q --upgrade pip
  "$VENV/bin/python3" -m pip install -q -r requirements.lock
  "$VENV/bin/python3" -m pip install -q --no-deps -e .
fi
usable && echo "bootstrap_env: OK ($("$VENV/bin/python3" --version))"

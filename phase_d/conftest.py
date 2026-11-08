"""Phase D test setup: make every workstream folder importable.

Each workstream keeps its Python package directly in its folder
(``phase_d/D4_consensus_protocol/d4_protocol/`` ...). Adding the folders to
``sys.path`` lets tests import ``d4_protocol`` etc. without packaging. The
foundation root (``contracts``, ``ws1_geometry``, ...) is added by
``foundation/conftest.py``. Shared file: agents do not edit it.
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_FOUNDATION = os.path.dirname(_HERE)
for _p in [_FOUNDATION] + sorted(
        os.path.join(_HERE, d) for d in os.listdir(_HERE)
        if os.path.isdir(os.path.join(_HERE, d)) and d[:1] == "D"):
    if _p not in sys.path:
        sys.path.insert(0, _p)

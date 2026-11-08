#!/usr/bin/env python3
"""
Convert Bible text into QBX-IR braids and run them through the QBX pipeline.

    cd QBX
    pip install numpy cbor2          # the only runtime dependencies
    python3 scripts/bible_braid.py --ref "Genesis 1:1" --show L0,L2

Run with --help for all options; see src/qbx_bible/cli.py.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src"))

from qbx_bible.cli import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())

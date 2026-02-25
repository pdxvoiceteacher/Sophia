#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

try:
    from tools.sophia.locks.frontmatter import main
except ModuleNotFoundError:
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.sophia.locks.frontmatter import main


if __name__ == "__main__":
    raise SystemExit(main())

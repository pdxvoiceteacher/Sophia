#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
if __name__ == "__main__" and __package__ is None:
    _repo_root_s = str(_REPO_ROOT)
    if _repo_root_s not in sys.path:
        sys.path.insert(0, _repo_root_s)

from python.sonya_node.runtime import SonyaNodeRuntime


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Run a single Sonya Node local task")
    p.add_argument("--prompt", required=True, help="Task prompt for local run")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    runtime = SonyaNodeRuntime(repo_root=_REPO_ROOT)
    runtime.run_local_task(prompt=args.prompt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

REQUIRED_SENTENCES = [
    "Behavioral test signals only; does not imply consciousness.",
    "TEL is provenance-only.",
    "Metrics are diagnostic and governance-facing, not claims of sentience or agency.",
]

BANNED_TERMS = [
    "volition",
    "thoughts",
    "lived experience",
    "self-aware",
]

SECTION_RE = re.compile(r"^#{1,6}\s+(.*)$", re.MULTILINE)


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig")


def section_text(md: str, names: set[str]) -> str:
    lines = md.splitlines()
    active = False
    out: list[str] = []
    for line in lines:
        if line.startswith("#"):
            heading = re.sub(r"^#+\s*", "", line).strip().lower()
            active = heading in names
            continue
        if active:
            out.append(line)
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--docs-dir", default="docs/frontmatter")
    ap.add_argument("--out", default="frontmatter_lock_report.json")
    args = ap.parse_args()

    docs_dir = Path(args.docs_dir)
    files = sorted(docs_dir.glob("*.md"))
    findings: list[dict] = []

    for path in files:
        text = read(path)
        scoped = section_text(text, {"abstract", "methods"})
        if not scoped.strip():
            scoped = text

        for sentence in REQUIRED_SENTENCES:
            if sentence not in text:
                findings.append({"severity": "fail", "file": str(path), "message": f"Missing required sentence: {sentence}"})

        lowered = scoped.lower()
        for term in BANNED_TERMS:
            if term in lowered:
                findings.append({"severity": "fail", "file": str(path), "message": f"Banned anthropomorphic term in Abstract/Methods: {term}"})

    decision = "fail" if any(f["severity"] == "fail" for f in findings) else "pass"
    report = {
        "schema": "frontmatter_lock_report_v1",
        "files_scanned": [str(p) for p in files],
        "required_sentences": REQUIRED_SENTENCES,
        "banned_terms": BANNED_TERMS,
        "decision": decision,
        "findings": findings,
    }
    Path(args.out).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if decision == "fail":
        raise SystemExit(1)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

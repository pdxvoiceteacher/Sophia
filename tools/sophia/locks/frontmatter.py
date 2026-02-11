from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

REQUIRED_SENTENCES = [
    "Behavioral test signals only; does not imply consciousness.",
    "TEL is provenance-only.",
    "Metrics are diagnostic and governance-facing, not claims of sentience or agency.",
]

ANTHROPOMORPHIC_TERMS = [
    "volition",
    "thoughts",
    "lived experience",
    "self-aware",
]

PROFILES: dict[str, dict[str, Any]] = {
    "publication": {
        "term_severity": "fail",
        "require_boundary_sentences": True,
        "description": "strict language controls for public-facing artifacts",
    },
    "research": {
        "term_severity": "warn",
        "require_boundary_sentences": True,
        "description": "exploration mode; language signals retained but non-blocking",
    },
    "safeguard": {
        "term_severity": "warn",
        "require_boundary_sentences": True,
        "description": "protective mode; language signals escalate governance posture only",
    },
}


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


def build_report(*, files: list[Path], findings: list[dict[str, Any]], mode: str, profile: str) -> dict[str, Any]:
    decision = "fail" if any(f["severity"] == "fail" for f in findings) else "pass"
    governance_hints = {
        "sentinel_state_hint": "protect" if profile == "safeguard" and findings else "normal",
        "due_process_required": bool(profile == "safeguard" and findings),
    }
    return {
        "schema": "frontmatter_lock_report_v1",
        "mode": mode,
        "profile": profile,
        "files_scanned": [str(p) for p in files],
        "required_sentences": REQUIRED_SENTENCES,
        "banned_terms": ANTHROPOMORPHIC_TERMS,
        "decision": decision,
        "findings": findings,
        "governance_hints": governance_hints,
    }


def run_frontmatter_lock(docs_dir: Path, out_path: Path, *, mode: str, profile: str) -> int:
    files = sorted(docs_dir.glob("*.md"))
    if mode == "off":
        report = {
            "schema": "frontmatter_lock_report_v1",
            "mode": mode,
            "profile": profile,
            "files_scanned": [str(p) for p in files],
            "required_sentences": REQUIRED_SENTENCES,
            "banned_terms": ANTHROPOMORPHIC_TERMS,
            "decision": "skipped",
            "findings": [],
            "governance_hints": {
                "sentinel_state_hint": "normal",
                "due_process_required": False,
            },
        }
        out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        return 0

    profile_cfg = PROFILES[profile]
    findings: list[dict[str, Any]] = []

    for path in files:
        text = read(path)
        scoped = section_text(text, {"abstract", "methods"})
        if not scoped.strip():
            scoped = text

        if profile_cfg["require_boundary_sentences"]:
            for sentence in REQUIRED_SENTENCES:
                if sentence not in text:
                    findings.append(
                        {
                            "severity": "fail",
                            "file": str(path),
                            "type": "boundary_sentence_missing",
                            "message": f"Missing required sentence: {sentence}",
                        }
                    )

        lowered = scoped.lower()
        for term in ANTHROPOMORPHIC_TERMS:
            if term in lowered:
                findings.append(
                    {
                        "severity": profile_cfg["term_severity"],
                        "file": str(path),
                        "type": "anthropomorphic_language_signal",
                        "message": f"Anthropomorphic term in Abstract/Methods: {term}",
                    }
                )

    report = build_report(files=files, findings=findings, mode=mode, profile=profile)
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    if report["decision"] == "fail" and mode == "enforce":
        return 1
    return 0


def build_arg_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser()
    ap.add_argument("--docs-dir", default="docs/frontmatter")
    ap.add_argument("--out", default="frontmatter_lock_report.json")
    ap.add_argument("--profile", choices=tuple(PROFILES.keys()), default="publication")
    ap.add_argument(
        "--mode",
        choices=("enforce", "warn", "off"),
        default="enforce",
        help="enforce: non-zero exit on fail findings, warn: always zero exit, off: skip checks",
    )
    return ap


def main() -> int:
    ap = build_arg_parser()
    args = ap.parse_args()
    return run_frontmatter_lock(Path(args.docs_dir), Path(args.out), mode=args.mode, profile=args.profile)


if __name__ == "__main__":
    raise SystemExit(main())

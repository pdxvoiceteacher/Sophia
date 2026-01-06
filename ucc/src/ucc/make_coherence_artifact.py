from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Dict, List, Optional

def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8-sig")

def _read_csv_dicts(p: Path) -> List[Dict[str, Any]]:
    if not p.exists():
        return []
    with p.open("r", encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))

def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Build a coherence artifact JSON from markdown + optional claims/sources CSVs.")
    ap.add_argument("--out", required=True, help="Output JSON path")
    ap.add_argument("--id", required=True, help="Artifact id")
    ap.add_argument("--domain", required=True, help="Domain label (e.g., research)")
    ap.add_argument("--question", required=True, help="Question being answered")
    ap.add_argument("--answer_md", required=True, help="Path to markdown writeup")
    ap.add_argument("--claims_csv", default="", help="Optional claims.csv path")
    ap.add_argument("--sources_csv", default="", help="Optional sources.csv path")
    ap.add_argument("--evidence_link", action="append", default=[], help="Evidence link (repeatable)")
    ap.add_argument("--reporting_primary", default="github issues", help="Primary disclosure channel")
    ap.add_argument("--reporting_escalation", default="maintainers", help="Escalation path")
    ap.add_argument("--notes", default="", help="Optional notes")

    args = ap.parse_args(argv)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    md_path = Path(args.answer_md)
    if not md_path.exists():
        print(f"answer_md file not found: {md_path}")
        return 2

    claims_path = Path(args.claims_csv) if args.claims_csv else None
    sources_path = Path(args.sources_csv) if args.sources_csv else None

    answer = _read_text(md_path)
    claims = _read_csv_dicts(claims_path) if claims_path else []
    sources = _read_csv_dicts(sources_path) if sources_path else []

    artifact: Dict[str, Any] = {
        "coherence_artifact": {
            "id": args.id,
            "domain": args.domain,
            "question": args.question,
            "answer": answer,
            # include required sections so coherence_audit can always evaluate structure
            "sections": {
                "assumptions": "auto: provided by author or left minimal for CI harness.",
                "limitations": "auto: CI harness artifact; not a full peer-reviewed writeup.",
                "uncertainty": "auto: CI harness artifact; treat as scaffold.",
                "disclosure": f"Generated via ucc.make_coherence_artifact from {md_path.as_posix()}",
                "summary": answer[:4000],
            },
            "claims": claims,
            "sources": sources,
            "evidence": {
                "links": list(args.evidence_link),
                "artifacts": [],
            },
            "reporting_channel": {
                "primary": args.reporting_primary,
                "escalation": args.reporting_escalation,
            },
            "notes": args.notes,
        }
    }

    out_path.write_text(json.dumps(artifact, indent=2, sort_keys=True), encoding="utf-8")
    print(f"Wrote: {out_path}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
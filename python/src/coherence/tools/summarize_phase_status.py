from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _entries(doc: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for key in ("targets", "records", "recommendations"):
        v = doc.get(key)
        if isinstance(v, list):
            rows.extend([r for r in v if isinstance(r, dict)])
    return rows


def _status(row: dict[str, Any]) -> str | None:
    for k, v in row.items():
        if k.endswith("Status") and isinstance(v, str):
            return v
    return None


def _phase(row: dict[str, Any], fallback: str) -> str:
    if isinstance(row.get("phaseId"), str) and row.get("phaseId"):
        return str(row["phaseId"])
    s = _status(row)
    if s:
        return s.split("-")[0]
    return fallback


def summarize_doc(doc: dict[str, Any], *, phase_hint: str = "unknown") -> dict[str, Any]:
    rows = _entries(doc)
    by_phase_status: dict[str, Counter[str]] = defaultdict(Counter)
    executive_review = 0
    action_counts = Counter()

    for row in rows:
        phase = _phase(row, phase_hint)
        status = _status(row) or "unknown"
        by_phase_status[phase][status] += 1
        if row.get("targetPublisherAction") == "docket" or row.get("requiresExecutiveReview") is True:
            executive_review += 1
        if isinstance(row.get("targetPublisherAction"), str):
            action_counts[str(row["targetPublisherAction"])] += 1

    return {
        "schema": doc.get("schema"),
        "totalEntries": len(rows),
        "byPhaseStatus": {phase: dict(sorted(counter.items())) for phase, counter in sorted(by_phase_status.items())},
        "executiveReviewCount": executive_review,
        "publisherActionCounts": {
            "watch": action_counts.get("watch", 0),
            "docket": action_counts.get("docket", 0),
            "suppress": action_counts.get("suppress", 0),
        },
    }


def markdown_summary(summary: dict[str, Any]) -> str:
    lines = [
        f"### Phase status summary (`{summary.get('schema')}`)",
        f"- Total entries: **{summary.get('totalEntries', 0)}**",
        f"- Executive review flags: **{summary.get('executiveReviewCount', 0)}**",
        f"- Publisher actions: watch={summary['publisherActionCounts']['watch']}, docket={summary['publisherActionCounts']['docket']}, suppress={summary['publisherActionCounts']['suppress']}",
        "- By phase/status:",
    ]
    for phase, counters in summary.get("byPhaseStatus", {}).items():
        inner = ", ".join(f"{k}={v}" for k, v in counters.items())
        lines.append(f"  - `{phase}`: {inner}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Summarize phase/status counts for bridge artifacts")
    parser.add_argument("artifacts", nargs="+", type=Path)
    parser.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = parser.parse_args(argv)

    combined = {
        "schema": "combined",
        "totalEntries": 0,
        "byPhaseStatus": defaultdict(Counter),
        "executiveReviewCount": 0,
        "publisherActionCounts": Counter(),
    }

    per_artifact = []
    for path in args.artifacts:
        s = summarize_doc(_load(path), phase_hint=path.stem)
        per_artifact.append({"artifact": str(path), **s})
        combined["totalEntries"] += s["totalEntries"]
        combined["executiveReviewCount"] += s["executiveReviewCount"]
        for phase, cnt in s["byPhaseStatus"].items():
            combined["byPhaseStatus"][phase].update(cnt)
        combined["publisherActionCounts"].update(s["publisherActionCounts"])

    combined_out = {
        "schema": "combined",
        "totalEntries": combined["totalEntries"],
        "byPhaseStatus": {phase: dict(sorted(c.items())) for phase, c in sorted(combined["byPhaseStatus"].items())},
        "executiveReviewCount": combined["executiveReviewCount"],
        "publisherActionCounts": {
            "watch": combined["publisherActionCounts"].get("watch", 0),
            "docket": combined["publisherActionCounts"].get("docket", 0),
            "suppress": combined["publisherActionCounts"].get("suppress", 0),
        },
        "artifacts": per_artifact,
    }

    if args.format == "json":
        print(json.dumps(combined_out, indent=2, ensure_ascii=False))
    else:
        print(markdown_summary(combined_out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

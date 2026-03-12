from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"

FINDING_TO_MODS = {
    "cascade.healthLow": {"noveltyWeight": 0.3, "pluralityWeight": 0.2},
    "capture.riskHigh": {"humilityWeight": 0.5},
    "discovery_corridor.lowPotential": {"noveltyWeight": 0.1},
}


def _load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_audit_file(bridge_root: Path, filename: str) -> Path:
    p1 = bridge_root / filename
    p2 = bridge_root / "bridge" / filename
    return p1 if p1.exists() else p2


def _load_findings(path: Path) -> list[dict[str, Any]]:
    payload = _load_json(path)
    if not isinstance(payload, dict):
        return []
    findings = payload.get("findings")
    if not isinstance(findings, list):
        return []
    return [f for f in findings if isinstance(f, dict)]


def build_ai_guidance(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []
    root = Path(bridge_root)

    for audit_file in ["cascade_audit.json", "discovery_corridor_audit.json"]:
        findings.extend(_load_findings(_resolve_audit_file(root, audit_file)))

    weights = {"noveltyWeight": 0.0, "pluralityWeight": 0.0, "humilityWeight": 0.0}
    requires_review = False

    for finding in findings:
        mods = FINDING_TO_MODS.get(str(finding.get("id")), {})
        for key, value in mods.items():
            weights[key] = min(1.0, weights[key] + value)
        if str(finding.get("advisory")) == "docket":
            requires_review = True

    guidance = {**weights, "requiresHumanReview": requires_review}
    Draft202012Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))).validate(guidance)

    out_path = Path(out_file) if out_file else root / "ai_guidance.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(guidance, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return guidance


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--out", dest="out_file", default=None)
    parser.add_argument("--output-file", dest="out_file", default=None)
    args = parser.parse_args(argv)

    guidance = build_ai_guidance(args.bridge_root, args.out_file)
    if not args.out_file:
        print(json.dumps(guidance, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

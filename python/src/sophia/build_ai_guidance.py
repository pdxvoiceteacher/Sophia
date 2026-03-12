from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"

FINDING_TO_MOD = {
    "cascade.healthLow": ("noveltyWeight", 0.2, "pluralityWeight", 0.3, "humilityWeight", 0.5),
    "discovery_corridor.lowPotential": ("noveltyWeight", 0.4, "pluralityWeight", 0.4),
}
DEFAULT_GUIDANCE = {
    "noveltyWeight": 0.1,
    "pluralityWeight": 0.1,
    "humilityWeight": 0.1,
    "requiresHumanReview": False,
}


def _load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_bridge_file(bridge_root: Path, filename: str) -> Path:
    return bridge_root / "bridge" / filename


def _load_findings(path: Path) -> list[dict[str, Any]]:
    payload = _load_json(path)
    if not isinstance(payload, dict):
        return []
    findings = payload.get("findings")
    if not isinstance(findings, list):
        return []
    return [f for f in findings if isinstance(f, dict)]


def build_ai_guidance(bridge_root: str, output_file: str | None = None) -> dict[str, Any]:
    guidance = DEFAULT_GUIDANCE.copy()

    cascade = _load_findings(_resolve_bridge_file(Path(bridge_root), "cascade_audit.json"))
    corridor = _load_findings(_resolve_bridge_file(Path(bridge_root), "discovery_corridor_audit.json"))

    for finding in cascade + corridor:
        if finding.get("advisory") == "docket":
            guidance["requiresHumanReview"] = True
        finding_id = finding.get("id")
        if finding_id in FINDING_TO_MOD:
            fields = FINDING_TO_MOD[finding_id]
            for i in range(0, len(fields), 2):
                key = fields[i]
                increment = fields[i + 1]
                guidance[key] = min(1.0, guidance.get(key, 0) + increment)

    Draft202012Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))).validate(guidance)

    if output_file:
        out = Path(output_file)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(guidance, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return guidance


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--output-file", help="File to write guidance JSON")
    args = parser.parse_args()

    guidance = build_ai_guidance(args.bridge_root, args.output_file)
    if not args.output_file:
        print(json.dumps(guidance, indent=2))

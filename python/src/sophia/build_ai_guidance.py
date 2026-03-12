from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"

MODIFIER_MAP = {
    "cascade.healthLow": ("noveltyWeight", 0.2),
    "capture.riskHigh": ("pluralityWeight", 0.3),
    "discovery_corridor.lowPotential": ("humilityWeight", 0.1),
}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def build_ai_guidance(cascade_audit: dict[str, Any], corridor_audit: dict[str, Any]) -> dict[str, Any]:
    guidance = {
        "noveltyWeight": 0.0,
        "pluralityWeight": 0.0,
        "humilityWeight": 0.0,
        "requiresHumanReview": False,
    }
    for audit in (cascade_audit, corridor_audit):
        findings = audit.get("findings", []) if isinstance(audit, dict) else []
        if not isinstance(findings, list):
            continue
        for finding in findings:
            if not isinstance(finding, dict):
                continue
            finding_id = finding.get("id")
            mod_key = MODIFIER_MAP.get(str(finding_id))
            if mod_key:
                guidance[mod_key[0]] = min(1.0, guidance[mod_key[0]] + mod_key[1])
            if finding.get("advisory") == "docket":
                guidance["requiresHumanReview"] = True

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(guidance)
    return guidance


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--cascade", required=True)
    parser.add_argument("--corridor", required=True)
    parser.add_argument("--out", dest="out_file", required=False)
    args = parser.parse_args(argv)

    cascade_data = _load_json(Path(args.cascade))
    corridor_data = _load_json(Path(args.corridor))
    guidance = build_ai_guidance(cascade_data, corridor_data)
    out_path = Path(args.out_file) if args.out_file else Path(args.cascade).parent / "ai_guidance.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(guidance, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0

    guidance = build_ai_guidance(args.bridge_root, args.output_file)
    if not args.output_file:
        print(json.dumps(guidance, indent=2))

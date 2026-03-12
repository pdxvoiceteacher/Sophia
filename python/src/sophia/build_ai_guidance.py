from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"
GUIDANCE_SCHEMA = "sophia/ai_guidance_v1"

CAUTION = (
    "This guidance is advisory-only and non-authoritative. It does not authorize closure, suppression, "
    "governance action, or canon formation. It suggests bounded response traits for keep-open operation."
)

FINDING_TO_MODIFIERS = {
    "cascade.healthLow": ["increase_plural_exploration", "increase_cross_domain_bridging", "increase_uncertainty_marking"],
    "cascade.risk": ["increase_plural_exploration", "avoid_canon_language"],
    "rupture.riskHigh": ["avoid_canon_language", "increase_epistemic_transparency", "reduce_premature_convergence"],
    "river.captureHigh": ["avoid_canon_language", "increase_epistemic_transparency"],
    "rebraid.alert": ["increase_cross_domain_bridging", "increase_plural_exploration"],
    "corridor.forming": ["increase_plural_exploration", "reduce_premature_convergence"],
}


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_bridge_file(bridge_root: Path, filename: str) -> Path | None:
    p1 = bridge_root / filename
    p2 = bridge_root / "bridge" / filename
    if p1.exists():
        return p1
    if p2.exists():
        return p2
    return None


def build_ai_guidance(*, bridge_root: Path) -> dict[str, Any]:
    inputs: list[str] = []
    modifiers: list[str] = []

    audit_files = [
        "cascade_audit.json",
        "rupture_audit.json",
        "knowledge_river_audit.json",
        "rebraid_audit.json",
        "discovery_corridor_audit.json",
        "viability_audit.json",
    ]

    for fn in audit_files:
        p = _resolve_bridge_file(bridge_root, fn)
        if p is None:
            continue
        inputs.append(fn)
        audit = _load_json(p) or {}
        findings = audit.get("findings") if isinstance(audit, dict) else []
        for f in findings if isinstance(findings, list) else []:
            if not isinstance(f, dict):
                continue
            fid = str(f.get("id", ""))
            for k, mods in FINDING_TO_MODIFIERS.items():
                if fid == k:
                    modifiers.extend(mods)
            if str(f.get("advisory")) == "docket":
                modifiers.append("request_human_review")

    if not modifiers:
        modifiers = ["increase_epistemic_transparency", "avoid_canon_language"]

    uniq: list[str] = []
    for m in modifiers:
        if m not in uniq:
            uniq.append(m)

    payload = {
        "schema": GUIDANCE_SCHEMA,
        "created_at": _utc_now_iso(),
        "caution": CAUTION,
        "modifiers": uniq,
        "inputs": inputs,
    }
    Draft202012Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bridge-root", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)

    payload = build_ai_guidance(bridge_root=args.bridge_root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[ok] wrote AI guidance: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

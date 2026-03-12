from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "viability_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/sophia/viability_audit_v1.schema.json"
EPSILON = 1e-6


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _as_number(value: Any, default: float = 0.0) -> float:
    return float(value) if isinstance(value, (int, float)) else default


def _fail_closed(reason: str, created_at: str = "1970-01-01T00:00:00Z") -> dict[str, Any]:
    return {
        "schema": "viability_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; use watch/docket follow-up and avoid closure or authority-transfer claims.",
        "decision": "warn",
        "findings": [
            {
                "id": "viability.missingInput",
                "severity": "warn",
                "type": "viability-alert",
                "advisory": "docket",
                "message": f"Missing or invalid viability inputs; fail-closed docket review required ({reason}).",
                "data": {},
            }
        ],
    }


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    path = bridge_root / "coherence_cascade_map.json"
    if not path.exists():
        payload = _fail_closed("coherence_cascade_map.json")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    doc = _load_json(path)
    created_at = str(doc.get("generatedAt") or "1970-01-01T00:00:00Z")

    cascade = doc.get("coherenceCascadeMap") if isinstance(doc.get("coherenceCascadeMap"), dict) else doc

    psi = _as_number(cascade.get("coherencePsi"), _as_number(cascade.get("psi")))
    plurality = _as_number(cascade.get("plurality"))
    trust = _as_number(cascade.get("trustLegibility"), _as_number(cascade.get("transparency")))
    memory = _as_number(cascade.get("memoryScore"))
    gradient = _as_number(cascade.get("anomalyGradient"), _as_number(cascade.get("gradient")))
    entropy_drift = _as_number(cascade.get("entropyDrift"))
    capture_pressure = _as_number(cascade.get("capturePressure"))

    numerator = psi * plurality * trust * memory * gradient
    denominator = entropy_drift + capture_pressure + EPSILON
    s_civ = numerator / denominator

    if s_civ <= 1.0:
        findings = [
            {
                "id": "viability.low",
                "severity": "warn",
                "type": "viability-alert",
                "advisory": "watch",
                "message": f"Civilization viability is low (S_civ={s_civ:.6f} <= 1).",
                "data": {
                    "S_civ": round(s_civ, 6),
                    "coherencePsi": round(psi, 6),
                    "plurality": round(plurality, 6),
                    "trustLegibility": round(trust, 6),
                    "memoryScore": round(memory, 6),
                    "anomalyGradient": round(gradient, 6),
                    "entropyDrift": round(entropy_drift, 6),
                    "capturePressure": round(capture_pressure, 6),
                },
            }
        ]
    else:
        findings = [
            {
                "id": "viability.ok",
                "severity": "info",
                "type": "viability-alert",
                "advisory": "watch",
                "message": f"Civilization viability is above threshold (S_civ={s_civ:.6f}).",
                "data": {
                    "S_civ": round(s_civ, 6),
                    "coherencePsi": round(psi, 6),
                    "plurality": round(plurality, 6),
                    "trustLegibility": round(trust, 6),
                    "memoryScore": round(memory, 6),
                    "anomalyGradient": round(gradient, 6),
                    "entropyDrift": round(entropy_drift, 6),
                    "capturePressure": round(capture_pressure, 6),
                },
            }
        ]

    payload = {
        "schema": "viability_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; use watch/docket follow-up and avoid closure or authority-transfer claims.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_cascade_viability(bridge_root: str, out_file: str) -> None:
    payload = build_outputs(bridge_root=Path(bridge_root))
    Path(out_file).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit cascade viability")
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=args.bridge_root)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

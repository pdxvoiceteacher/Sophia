from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/navigation_audit_v1.schema.json"

PSI_FLOOR = 0.5
DELTA_S_CEILING = 0.6
LAMBDA_CEILING = 0.6


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def audit_navigation(telemetry: dict[str, Any]) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []
    psi = telemetry.get("Psi", 0.0)
    delta_s = telemetry.get("deltaStrength", 0.0)
    lam = telemetry.get("lambdaCritical", 0.0)

    if isinstance(psi, (int, float)) and psi < PSI_FLOOR:
        findings.append(
            {
                "id": "coherence.psiLow",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": f"Psi {float(psi):.2f} below floor {PSI_FLOOR}",
                "data": {"psi": float(psi)},
            }
        )
    if isinstance(delta_s, (int, float)) and delta_s > DELTA_S_CEILING:
        findings.append(
            {
                "id": "coherence.deltaHigh",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": f"DeltaS {float(delta_s):.2f} above ceiling {DELTA_S_CEILING}",
                "data": {"deltaStrength": float(delta_s)},
            }
        )
    if isinstance(lam, (int, float)) and lam > LAMBDA_CEILING:
        findings.append(
            {
                "id": "coherence.lambdaHigh",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": f"Lambda {float(lam):.2f} above ceiling {LAMBDA_CEILING}",
                "data": {"lambdaCritical": float(lam)},
            }
        )

    return {
        "schema": "navigation_audit_v1",
        "decision": "pass" if not findings else "warn",
        "caution": "Advisory only. Canonical boundary: non-executive guidance with no authoritative commands.",
        "semanticMode": "non-executive",
        "findings": findings,
    }


def audit_navigation_state(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    telemetry_path = Path(bridge_root) / "bridge" / "navigation_state.json"
    if not telemetry_path.exists():
        payload = {
            "schema": "navigation_audit_v1",
            "decision": "fail",
            "caution": "Advisory only. Canonical boundary: non-executive guidance with no authoritative commands.",
            "semanticMode": "non-executive",
            "findings": [
                {
                    "id": "navigation.missing",
                    "severity": "warn",
                    "type": "audit",
                    "advisory": "docket",
                    "message": "Navigation telemetry is missing.",
                    "data": {},
                }
            ],
        }
    else:
        telemetry = _load_json(telemetry_path)
        payload = audit_navigation(telemetry)

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    output_path = Path(out_file) if out_file else Path(bridge_root) / "bridge" / "navigation_audit.json"
    _write_json(output_path, payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--output-file", default=None)
    parser.add_argument("--out", dest="output_file", default=None)
    args = parser.parse_args(argv)

    audit_navigation_state(args.bridge_root, args.output_file)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

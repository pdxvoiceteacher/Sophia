from __future__ import annotations

import argparse
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[1]
BRIDGE_DIR = REPO_ROOT / "bridge"
REGISTRY_DIR = REPO_ROOT / "registry"
SCHEMA_DIR = REPO_ROOT / "schema"

INPUTS = {
    "audit": BRIDGE_DIR / "environment_audit.json",
    "recommendations": BRIDGE_DIR / "environment_recommendations.json",
    "environment": BRIDGE_DIR / "environment_integrity_map.json",
    "anomaly": BRIDGE_DIR / "anomaly_domain_map.json",
    "maturity": BRIDGE_DIR / "evidence_maturity_report.json",
    "counter": BRIDGE_DIR / "counter_hypothesis_map.json",
    "verification_dashboard": REGISTRY_DIR / "verification_dashboard.json",
    "public_dashboard": REGISTRY_DIR / "public_record_dashboard.json",
    "symbolic_registry": REGISTRY_DIR / "symbolic_field_registry.json",
}

OUTPUTS = {
    "dashboard": REGISTRY_DIR / "environment_integrity_dashboard.json",
    "watchlist": REGISTRY_DIR / "anomaly_watchlist.json",
    "maturity": REGISTRY_DIR / "evidence_maturity_registry.json",
    "annotations": REGISTRY_DIR / "counter_hypothesis_annotations.json",
}

SCHEMAS = {
    "dashboard": SCHEMA_DIR / "environment_integrity_dashboard_v1.schema.json",
    "watchlist": SCHEMA_DIR / "anomaly_watchlist_v1.schema.json",
    "maturity": SCHEMA_DIR / "evidence_maturity_registry_v1.schema.json",
    "annotations": SCHEMA_DIR / "counter_hypothesis_annotations_v1.schema.json",
}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for k in ("targets", "records", "items", "entries"):
        v = payload.get(k)
        if isinstance(v, list):
            return [r for r in v if isinstance(r, dict)]
    return []


def _index(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for r in rows:
        tid = str(r.get("targetId") or "").strip()
        if tid:
            out[tid] = r
    return out


def _now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def build_outputs(*, reset: bool = False) -> dict[str, dict[str, Any]]:
    audit = _load_json(INPUTS["audit"])
    recommendations = _load_json(INPUTS["recommendations"])
    environment = _load_json(INPUTS["environment"])
    anomaly = _load_json(INPUTS["anomaly"])
    maturity = _load_json(INPUTS["maturity"])
    counter = _load_json(INPUTS["counter"])
    verification_dashboard = _load_json(INPUTS["verification_dashboard"])
    public_dashboard = _load_json(INPUTS["public_dashboard"])
    symbolic_registry = _load_json(INPUTS["symbolic_registry"])

    producer_commit = str(verification_dashboard.get("producerCommit") or "unknown")
    common = {
        "producerRepo": "Sophia",
        "producerModule": "scripts.build_environment_integrity_overlay",
        "producerCommit": producer_commit,
        "generatedAt": _now(),
        "caution": "Publisher surfaces only Sophia-audited environment-integrity materials; no automatic accusation or intervention occurs from this layer.",
    }

    if reset:
        empty = {
            "schemaVersion": "environment_integrity_dashboard_v1",
            **common,
            "metadataPanel": {"provenanceSummary": "reset", "markersCleared": True},
            "actionable": [],
        }
        return {
            "dashboard": empty,
            "watchlist": {"schemaVersion": "anomaly_watchlist_v1", **common, "items": []},
            "maturity": {"schemaVersion": "evidence_maturity_registry_v1", **common, "entries": []},
            "annotations": {"schemaVersion": "counter_hypothesis_annotations_v1", **common, "entries": []},
        }

    rec_rows = sorted(_rows(recommendations), key=lambda r: str(r.get("targetId", "")))
    env_by = _index(_rows(environment))
    anom_by = _index(_rows(anomaly))
    mat_by = _index(_rows(maturity))
    counter_by = _index(_rows(counter))

    actionable: list[dict[str, Any]] = []
    watch_items: list[dict[str, Any]] = []
    for rec in rec_rows:
        action = str(rec.get("targetPublisherAction") or "")
        if action == "suppress":
            continue
        tid = str(rec.get("targetId") or "")
        env = env_by.get(tid, {})
        anom = anom_by.get(tid, {})
        mat = mat_by.get(tid, {})
        ctr = counter_by.get(tid, {})

        item = {
            "targetId": tid,
            "anomalyDomain": env.get("anomalyDomain", anom.get("anomalyDomain", "mixed")),
            "attackSurfaceClass": env.get("attackSurfaceClass", anom.get("attackSurfaceClass", "platform")),
            "environmentIntegrityScore": env.get("environmentIntegrityScore", 0.0),
            "evidenceMaturity": mat.get("maturityClass", "artifact"),
            "counterHypothesis": {
                "count": len(ctr.get("counterHypotheses", [])),
                "status": ctr.get("recommendedClass", "watch"),
            },
            "provenanceMarkers": env.get("provenanceMarkers", []),
            "uiClass": "subtle-critical" if bool(env.get("requiresExecutiveReview")) else "subtle-info",
        }

        if action == "docket":
            actionable.append(item)
        elif action == "watch":
            watch_items.append(item)

    outputs = {
        "dashboard": {
            "schemaVersion": "environment_integrity_dashboard_v1",
            **common,
            "metadataPanel": {
                "provenanceSummary": "Verification, public-record, and symbolic registries were merged for differential review.",
                "markersCleared": False,
                "sourceDashboards": [
                    str(verification_dashboard.get("schemaVersion", "unknown")),
                    str(public_dashboard.get("schemaVersion", "unknown")),
                    str(symbolic_registry.get("schemaVersion", "unknown")),
                    str(audit.get("schemaVersion", "unknown")),
                ],
            },
            "actionable": actionable,
        },
        "watchlist": {"schemaVersion": "anomaly_watchlist_v1", **common, "items": watch_items},
        "maturity": {
            "schemaVersion": "evidence_maturity_registry_v1",
            **common,
            "entries": [
                {
                    "targetId": r.get("targetId"),
                    "maturityClass": r.get("maturityClass"),
                    "maturityScore": r.get("maturityScore"),
                    "missingVerificationSteps": r.get("missingVerificationSteps", []),
                    "provenanceMarkers": r.get("provenanceMarkers", []),
                }
                for r in _rows(maturity)
            ],
        },
        "annotations": {
            "schemaVersion": "counter_hypothesis_annotations_v1",
            **common,
            "entries": [
                {
                    "targetId": r.get("targetId"),
                    "primaryHypothesis": r.get("primaryHypothesis"),
                    "counterHypothesisCount": len(r.get("counterHypotheses", [])),
                    "recommendedClass": r.get("recommendedClass"),
                    "provenanceMarkers": r.get("provenanceMarkers", []),
                }
                for r in _rows(counter)
            ],
        },
    }
    return outputs


def validate_outputs(outputs: dict[str, dict[str, Any]]) -> None:
    for key, payload in outputs.items():
        schema = _load_json(SCHEMAS[key])
        Draft202012Validator(schema).validate(payload)


def write_outputs(outputs: dict[str, dict[str, Any]]) -> None:
    for key, payload in outputs.items():
        OUTPUTS[key].write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build environment integrity overlay registry artifacts")
    parser.add_argument("--reset", action="store_true", help="clear environment-integrity markers from overlay outputs")
    args = parser.parse_args(argv)

    outputs = build_outputs(reset=args.reset)
    validate_outputs(outputs)
    write_outputs(outputs)
    print("wrote environment-integrity overlay artifacts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

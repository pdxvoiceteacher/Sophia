from __future__ import annotations

import argparse
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[4]
BRIDGE_DIR = REPO_ROOT / "bridge"
REGISTRY_DIR = REPO_ROOT / "registry"
SCHEMA_DIR = REPO_ROOT / "schema"

INPUTS = {
    "verification": BRIDGE_DIR / "verification_task_map.json",
    "claim": BRIDGE_DIR / "claim_type_map.json",
    "entity": BRIDGE_DIR / "entity_resolution_map.json",
    "public_record": BRIDGE_DIR / "public_record_intake_map.json",
    "custody": BRIDGE_DIR / "chain_of_custody_report.json",
    "symbolic": BRIDGE_DIR / "symbolic_field_state.json",
    "warning": BRIDGE_DIR / "early_warning_signal_map.json",
    "verification_dashboard": REGISTRY_DIR / "verification_dashboard.json",
}

OUTPUTS = {
    "environment": BRIDGE_DIR / "environment_integrity_map.json",
    "anomaly": BRIDGE_DIR / "anomaly_domain_map.json",
    "maturity": BRIDGE_DIR / "evidence_maturity_report.json",
    "counter": BRIDGE_DIR / "counter_hypothesis_map.json",
}

SCHEMAS = {
    "environment": SCHEMA_DIR / "environment_integrity_map_v1.schema.json",
    "anomaly": SCHEMA_DIR / "anomaly_domain_map_v1.schema.json",
    "maturity": SCHEMA_DIR / "evidence_maturity_report_v1.schema.json",
    "counter": SCHEMA_DIR / "counter_hypothesis_map_v1.schema.json",
}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("targets", "records", "items", "entries"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _clamp01(v: float) -> float:
    return max(0.0, min(1.0, float(v)))


def _now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _target_ids(*rowsets: list[dict[str, Any]]) -> list[str]:
    ids: set[str] = set()
    for rows in rowsets:
        for row in rows:
            tid = str(row.get("targetId") or "").strip()
            if tid:
                ids.add(tid)
    return sorted(ids)


def _as_map(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        tid = str(row.get("targetId") or "").strip()
        if tid:
            out[tid] = row
    return out


def build_outputs() -> dict[str, dict[str, Any]]:
    verification = _rows(_load_json(INPUTS["verification"]))
    claim = _rows(_load_json(INPUTS["claim"]))
    entity = _rows(_load_json(INPUTS["entity"]))
    public_record = _rows(_load_json(INPUTS["public_record"]))
    custody = _rows(_load_json(INPUTS["custody"]))
    symbolic = _rows(_load_json(INPUTS["symbolic"]))
    warning = _rows(_load_json(INPUTS["warning"]))
    verification_dashboard = _load_json(INPUTS["verification_dashboard"])

    ver_by = _as_map(verification)
    claim_by = _as_map(claim)
    entity_by = _as_map(entity)
    public_by = _as_map(public_record)
    custody_by = _as_map(custody)
    symbolic_by = _as_map(symbolic)
    warning_by = _as_map(warning)

    ids = _target_ids(verification, claim, entity, public_record, custody, symbolic, warning)
    generated_at = _now()
    producer_commit = str(verification_dashboard.get("producerCommit") or "unknown")

    env_targets: list[dict[str, Any]] = []
    anomaly_targets: list[dict[str, Any]] = []
    maturity_targets: list[dict[str, Any]] = []
    counter_targets: list[dict[str, Any]] = []

    for i, tid in enumerate(ids, start=1):
        ver = ver_by.get(tid, {})
        cla = claim_by.get(tid, {})
        ent = entity_by.get(tid, {})
        pub = public_by.get(tid, {})
        cod = custody_by.get(tid, {})
        sym = symbolic_by.get(tid, {})
        warn = warning_by.get(tid, {})

        contradiction = _clamp01(float(ver.get("contradictionScore", warn.get("signalScore", 0.25))))
        ambiguity = _clamp01(float(ent.get("entityAmbiguity", sym.get("ambiguityScore", 0.25))))
        chain = _clamp01(float(cod.get("chainCompleteness", 0.5)))
        tamper = _clamp01(float(cod.get("tamperRisk", 0.25)))
        record_quality = _clamp01(float(pub.get("recordQuality", 0.5)))
        reliability = _clamp01(float(pub.get("claimReliability", 0.5)))
        stability = _clamp01(0.5 * (1.0 - ambiguity) + 0.5 * (1.0 - contradiction))
        provenance_coverage = _clamp01(0.5 * chain + 0.5 * reliability)
        integrity = _clamp01(0.35 * stability + 0.35 * provenance_coverage + 0.3 * (1.0 - tamper))

        domain = str(warn.get("anomalyDomain") or "").strip()
        if domain not in {"digital", "social_behavioral", "mixed"}:
            if contradiction > 0.6 and ambiguity > 0.6:
                domain = "mixed"
            elif contradiction >= ambiguity:
                domain = "digital"
            else:
                domain = "social_behavioral"

        attack_surface = str(warn.get("attackSurfaceClass") or "").strip()
        if attack_surface not in {"platform", "social", "account", "device", "network"}:
            target_type = str(ver.get("targetType") or "")
            attack_surface = {
                "identity": "account",
                "record": "platform",
                "network": "network",
                "persona": "social",
            }.get(target_type, "device")

        requires_review = integrity < 0.35 or contradiction > 0.72 or provenance_coverage < 0.42

        env_targets.append(
            {
                "environmentId": f"environment:{i:03d}",
                "targetId": tid,
                "anomalyDomain": domain,
                "attackSurfaceClass": attack_surface,
                "environmentIntegrityScore": round(integrity, 6),
                "observationStabilityScore": round(stability, 6),
                "provenanceCoverage": round(provenance_coverage, 6),
                "contradictionDensity": round(contradiction, 6),
                "requiresExecutiveReview": requires_review,
                "provenanceMarkers": ["verification", "public_record", "chain_of_custody", "symbolic_field"],
            }
        )

        anomaly_targets.append(
            {
                "anomalyId": f"anomaly:{i:03d}",
                "targetId": tid,
                "anomalyDomain": domain,
                "attackSurfaceClass": attack_surface,
                "anomalyScore": round(_clamp01(0.55 * contradiction + 0.45 * (1.0 - integrity)), 6),
                "watchStatus": "watch" if contradiction >= 0.35 else "baseline",
                "provenanceMarkers": ["early_warning", "verification", "symbolic_field"],
            }
        )

        maturity_score = _clamp01(0.4 * chain + 0.3 * record_quality + 0.3 * (1.0 - contradiction))
        if maturity_score >= 0.86:
            maturity_class = "conclusion_ready"
        elif maturity_score >= 0.68:
            maturity_class = "independently_verified"
        elif maturity_score >= 0.45:
            maturity_class = "repeatable_test"
        else:
            maturity_class = "artifact"

        missing_steps: list[str] = []
        if chain < 0.7:
            missing_steps.append("complete_chain_of_custody")
        if record_quality < 0.65:
            missing_steps.append("improve_source_quality")
        if contradiction > 0.5:
            missing_steps.append("run_differential_verification")
        escalation_risk = _clamp01(0.6 * (1.0 - maturity_score) + 0.4 * contradiction)

        maturity_targets.append(
            {
                "evidenceId": f"evidence:{i:03d}",
                "targetId": tid,
                "maturityClass": maturity_class,
                "maturityScore": round(maturity_score, 6),
                "missingVerificationSteps": missing_steps,
                "escalationRisk": round(escalation_risk, 6),
                "provenanceMarkers": ["public_record", "chain_of_custody", "verification"],
            }
        )

        primary_hypothesis = str(cla.get("claimType") or "observed anomaly may reflect benign variance")
        counter_hypotheses = [
            "measurement artifact produced signal distortion",
            "normal operational drift explains observed pattern",
        ]
        if domain == "mixed":
            counter_hypotheses.append("combined social and platform dynamics produce non-adversarial effects")

        differentiation_tasks = missing_steps or ["collect_additional_context"]
        ambiguity_persistence = round(_clamp01(0.7 * ambiguity + 0.3 * (1.0 - chain)), 6)
        if ambiguity_persistence >= 0.66:
            rec_class = "hold"
        elif contradiction >= 0.55:
            rec_class = "verify"
        else:
            rec_class = "watch"

        counter_targets.append(
            {
                "counterHypothesisId": f"counter:{i:03d}",
                "targetId": tid,
                "primaryHypothesis": primary_hypothesis,
                "counterHypotheses": counter_hypotheses,
                "differentiationTasks": differentiation_tasks,
                "ambiguityPersistence": ambiguity_persistence,
                "recommendedClass": rec_class,
                "provenanceMarkers": ["claim_type", "entity_resolution", "verification", "chain_of_custody"],
            }
        )

    common = {
        "producerRepo": "Sophia",
        "producerModule": "coherence.bridge.build_environment_integrity_state",
        "producerCommit": producer_commit,
        "generatedAt": generated_at,
    }
    return {
        "environment": {
            "schemaVersion": "environment_integrity_map_v1",
            **common,
            "caution": "CoherenceLattice formalizes environment-integrity and differential-verification signals only; it does not conclude manipulation occurred.",
            "targets": env_targets,
        },
        "anomaly": {
            "schemaVersion": "anomaly_domain_map_v1",
            **common,
            "caution": "Anomaly domains indicate differential-testing priorities and remain non-accusatory.",
            "targets": anomaly_targets,
        },
        "maturity": {
            "schemaVersion": "evidence_maturity_report_v1",
            **common,
            "caution": "Evidence maturity reflects current verification posture and can be revised with new evidence.",
            "targets": maturity_targets,
        },
        "counter": {
            "schemaVersion": "counter_hypothesis_map_v1",
            **common,
            "caution": "Counter-hypotheses preserve falsifiability and avoid totalizing narratives.",
            "targets": counter_targets,
        },
    }


def validate_outputs(outputs: dict[str, dict[str, Any]]) -> None:
    for key, payload in outputs.items():
        schema = _load_json(SCHEMAS[key])
        Draft202012Validator(schema).validate(payload)


def write_outputs(outputs: dict[str, dict[str, Any]]) -> None:
    for key, payload in outputs.items():
        OUTPUTS[key].write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build environment integrity bridge state artifacts")
    parser.parse_args(argv)

    outputs = build_outputs()
    validate_outputs(outputs)
    write_outputs(outputs)
    print("wrote environment-integrity bridge artifacts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

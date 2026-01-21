from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.telemetry import sophia_audit


def test_plan_v1_schema_and_risk_score(tmp_path: Path) -> None:
    findings = [
        {
            "id": "finding_missing_evidence",
            "severity": "warn",
            "type": "missing_evidence",
            "message": "Evidence missing.",
            "data": {},
        },
        {
            "id": "finding_counterevidence",
            "severity": "warn",
            "type": "missing_counterevidence",
            "message": "Counterevidence missing.",
            "data": {},
        },
    ]
    risk_score, _components = sophia_audit.compute_risk_score(
        findings,
        contradiction_clusters=[],
        ethical_symmetry=None,
        memory_drift_flag=False,
    )
    plan = sophia_audit.build_plan(
        run_id="test-run",
        decision="warn",
        findings=findings,
        risk_score=risk_score,
        repair_targets={},
    )
    assert plan["risk_score"] == risk_score
    assert plan["schema"] == "sophia_plan_v1"

    schema_path = Path("schema/sophia_plan_v1.schema.json")
    schema = json.loads(schema_path.read_text(encoding="utf-8-sig"))
    Draft202012Validator(schema).validate(plan)

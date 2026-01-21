from __future__ import annotations

import json
from pathlib import Path

from tools.telemetry import sophia_audit


def test_noise_suppression_downgrades_frequent_findings(tmp_path: Path) -> None:
    history_path = tmp_path / "runs" / "history" / "finding_stats.json"
    history_path.parent.mkdir(parents=True, exist_ok=True)
    history_path.write_text(
        json.dumps({"total_runs": 10, "findings": {"missing_evidence": 8}}),
        encoding="utf-8",
    )
    findings = [
        {
            "id": "finding_missing_evidence",
            "severity": "warn",
            "type": "missing_evidence",
            "message": "Evidence missing.",
            "data": {},
        }
    ]
    noise_adjustments = sophia_audit.apply_noise_suppression(findings, history_path, threshold=0.6)
    assert findings[0]["severity"] == "info"
    assert noise_adjustments

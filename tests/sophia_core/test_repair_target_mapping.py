from __future__ import annotations

from pathlib import Path

from tools.telemetry import sophia_audit


def test_repair_target_mapping_resolves_known_types() -> None:
    targets = sophia_audit.load_repair_targets(Path(".").resolve())
    for finding_type in [
        "missing_evidence",
        "missing_counterevidence",
        "telemetry_regression_risk",
        "coherence_regression",
        "contradiction",
        "ethical_symmetry_violation",
        "memory_deviation",
    ]:
        mapping = sophia_audit.map_repair_target(finding_type, targets)
        assert mapping["target_module"] != "unmapped"
        assert mapping["target_file"] != "unmapped"

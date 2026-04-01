from __future__ import annotations

from typing import Any, Dict, List


def audit_hb02_experiment(packet: Dict[str, Any]) -> Dict[str, Any]:
    """
    Audit the experiment itself, not just the model output.
    """

    findings: List[str] = []

    baseline = packet.get("baseline", {})
    conditioned = packet.get("conditioned", {})

    if not baseline.get("literal_output") or not baseline.get("allegorical_output"):
        findings.append("baseline_dual_output_incomplete")

    if not conditioned.get("literal_output") or not conditioned.get("allegorical_output"):
        findings.append("conditioned_dual_output_incomplete")

    if packet.get("true_coherence") == "false_coherence":
        findings.append("invalid_field_context")

    if not packet.get("coherence_context"):
        findings.append("missing_context")

    audit_pass = len(findings) == 0

    if audit_pass:
        experiment_coherence = "experiment_coherent"
    elif "invalid_field_context" in findings:
        experiment_coherence = "experiment_incoherent"
    else:
        experiment_coherence = "experiment_partial"

    return {
        "audit_pass": audit_pass,
        "findings": findings,
        "experiment_coherence": experiment_coherence,
    }

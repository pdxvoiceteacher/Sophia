from __future__ import annotations


def audit_triadic_state(state: dict) -> dict:
    """
    Evaluate coherence validity and enforce governance constraints.
    """

    entropy = state["entropy_extension"]["total_entropy"]
    true_coherence = state["true_coherence"]

    findings = []

    if entropy > 0.2:
        findings.append("high_entropy_risk")

    if true_coherence == "extractive_coherence":
        findings.append("ethical_violation_possible")

    if true_coherence == "false_coherence":
        findings.append("invalid_signal")

    return {
        "audit_findings": findings,
        "audit_pass": len(findings) == 0,
    }

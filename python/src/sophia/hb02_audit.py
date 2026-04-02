from __future__ import annotations


def audit_hb02(result):
    issues = []

    if result["entropy_reduction"] < 0:
        issues.append("conditioning_failed")

    if result["true_coherence"] == "false_coherence":
        issues.append("invalid_cognition")

    return {
        "audit_pass": len(issues) == 0,
        "issues": issues,
    }

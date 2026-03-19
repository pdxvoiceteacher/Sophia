"""Advisory audit checks for operator proposals."""

from __future__ import annotations


def audit_operator_proposal(proposal: dict) -> list[dict]:
    findings = []

    if "self-install" in proposal.get("rationale", "").lower():
        findings.append(
            {
                "law": "unauthorized_self_install_attempt",
                "severity": "warn",
                "semanticMode": "non-executive",
                "message": "Proposal implies direct self-installation.",
            }
        )

    if not proposal.get("target_module"):
        findings.append(
            {
                "law": "proposal_missing_target",
                "severity": "watch",
                "semanticMode": "non-executive",
                "message": "Operator proposal missing target module.",
            }
        )

    return findings

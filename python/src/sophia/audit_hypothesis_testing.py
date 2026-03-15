"""Advisory audit checks for hypothesis testing artifacts."""

from __future__ import annotations


def audit_hypothesis_testing(artifact: dict) -> list[dict]:
    findings = []

    tests = artifact.get("tests", [])
    successes = [test for test in tests if test.get("valid")]

    if len(successes) == 0:
        findings.append(
            {
                "law": "hypothesis_failure_cluster",
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "No hypothesis produced positive Ψ gain.",
            }
        )

    return findings

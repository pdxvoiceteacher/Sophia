from __future__ import annotations


def audit_terrace_formation(artifact: dict) -> list[dict]:
    """Advisory-only audit for terrace formation artifacts."""
    findings = []

    summary = artifact.get("summary", {})
    avg = float(summary.get("averageTerraceDensity", 0.0))
    max_t = float(summary.get("maxTerraceDensity", 0.0))

    if avg < 0.05:
        findings.append(
            {
                "severity": "info",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Terrace formation negligible.",
            }
        )

    if max_t > 0.95:
        findings.append(
            {
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Possible terrace saturation.",
            }
        )

    return findings

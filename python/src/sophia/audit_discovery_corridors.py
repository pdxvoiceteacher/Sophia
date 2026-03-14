def audit_discovery_corridors(artifact):

    findings = []

    if artifact["summary"]["corridorCount"] == 0:

        findings.append({
            "severity": "info",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No discovery corridors detected.",
        })

    return findings

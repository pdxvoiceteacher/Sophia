def audit_hypotheses(artifact):

    findings = []

    if artifact["summary"]["count"] == 0:
        findings.append({
            "severity": "info",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No hypotheses generated.",
        })

    return findings

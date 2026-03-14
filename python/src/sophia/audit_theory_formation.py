def audit_theories(artifact):

    findings = []

    for theory in artifact["theories"]:

        if theory["coherence_score"] < 0:

            findings.append({
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Theory reduces coherence.",
            })

    return findings

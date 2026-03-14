def audit_paradigm_shift(artifact):

    findings = []

    if artifact["new_corridors"] == 0:

        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Rupture detected but no new corridors formed.",
        })

    return findings

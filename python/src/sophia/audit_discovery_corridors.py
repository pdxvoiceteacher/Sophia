def audit_corridor_gradients(state):

    psi = state["Psi"]

    findings = []

    max_gradient = max(psi) - min(psi)

    if max_gradient < 0.01:
        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "No discovery gradients detected."
        })

    if max_gradient > 0.8:
        findings.append({
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Potential coherence shock detected."
        })

    return findings

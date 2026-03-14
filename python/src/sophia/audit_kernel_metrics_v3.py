def audit_kernel_metrics(event):
    findings = []

    residual = event["corridor_mass_balance_detail"]["residual_rel"]
    threshold = 1e-4

    if abs(residual) > threshold:
        findings.append({
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "law": "corridor_mass_balance",
            "message": "Corridor mass conservation exceeded tolerance.",
            "residual": residual,
        })

    phi_drift = event.get("phi_drift", 0.0)

    if abs(phi_drift) > 0.25:
        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "law": "epistemic_flux_conservation",
            "message": "Large coherence potential drift detected.",
            "phi_drift": phi_drift,
        })

    return findings

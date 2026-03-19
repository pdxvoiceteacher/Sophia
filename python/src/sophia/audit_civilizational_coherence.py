from __future__ import annotations


def audit_civilizational_coherence(artifact: dict) -> list[dict]:
    findings = []

    # Accept both shapes:
    # A) {"summary": {"regime": ...}, "metrics": {"S_civ": ...}}
    # B) {"S_civ": ...}  (current LAN-01 output)
    regime = artifact.get("summary", {}).get("regime", "unknown")
    if "metrics" in artifact and isinstance(artifact.get("metrics"), dict):
        scalar = float(artifact["metrics"].get("S_civ", 0.0))
    else:
        scalar = float(artifact.get("S_civ", 0.0))

    # If regime is not provided, derive a minimal regime label from S_civ.
    if regime == "unknown":
        if scalar <= 0.9:
            regime = "fragmentation_noise"
        elif 0.9 < scalar < 1.1:
            regime = "critical_boundary"
        else:
            regime = "stable"

    if regime == "critical_boundary":
        findings.append(
            {
                "severity": "watch",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Civilizational coherence near critical boundary.",
                "law": "civilizational_stability_threshold",
                "S_civ": scalar,
            }
        )

    if regime == "orthodoxy_collapse":
        findings.append(
            {
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Plurality collapse with high capture pressure detected.",
                "law": "orthodoxy_collapse",
                "S_civ": scalar,
            }
        )

    if regime == "fragmentation_noise":
        findings.append(
            {
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": f"Fragmentation detected: ΔS={1-scalar:.3f}, Ψ={scalar:.3f}",
                "law": "fragmentation_noise",
                "S_civ": scalar,
            }
        )

    if regime == "civilizational_rupture":
        findings.append(
            {
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "System-level rupture conditions detected.",
                "law": "civilizational_rupture",
                "S_civ": scalar,
            }
        )

    return findings

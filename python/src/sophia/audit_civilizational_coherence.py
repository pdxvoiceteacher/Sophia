from __future__ import annotations


def audit_civilizational_coherence(artifact: dict) -> list[dict]:
    findings = []

    regime = artifact.get("summary", {}).get("regime", "unknown")
    metrics = artifact.get("metrics", {})
    scalar = float(metrics.get("S_civ", 0.0))

    if regime == "critical_boundary":
        findings.append({
            "severity": "watch",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Civilizational coherence near critical boundary.",
            "law": "civilizational_stability_threshold",
            "S_civ": scalar,
        })

    if regime == "orthodoxy_collapse":
        findings.append({
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Plurality collapse with high capture pressure detected.",
            "law": "orthodoxy_collapse",
            "S_civ": scalar,
        })

    if regime == "fragmentation_noise":
        findings.append({
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "Entropy and trust/memory breakdown indicate fragmentation risk.",
            "law": "fragmentation_noise",
            "S_civ": scalar,
        })

    if regime == "civilizational_rupture":
        findings.append({
            "severity": "warn",
            "advisory": "watch",
            "semanticMode": "non-executive",
            "message": "System-level rupture conditions detected.",
            "law": "civilizational_rupture",
            "S_civ": scalar,
        })

    return findings

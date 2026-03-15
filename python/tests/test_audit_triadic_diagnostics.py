from sophia.audit_triadic_diagnostics import audit_triadic_diagnostics


def test_audit_triadic_diagnostics_no_findings_for_healthy_artifact() -> None:
    artifact = {
        "semanticMode": "non-executive",
        "system_status": "stable",
        "kernel_health": [],
        "governance_health": [],
        "epistemic_health": [],
    }

    findings = audit_triadic_diagnostics(artifact)

    assert findings == []


def test_audit_triadic_diagnostics_flags_mode_and_status_issues() -> None:
    artifact = {
        "semanticMode": "executive",
        "system_status": "degraded",
        "kernel_health": [],
        "governance_health": [],
        "epistemic_health": [],
    }

    findings = audit_triadic_diagnostics(artifact)

    assert findings == [
        {
            "law": "semantic_mode_violation",
            "severity": "warn",
            "semanticMode": "non-executive",
            "message": "Diagnostics artifact must remain non-executive.",
        },
        {
            "law": "system_instability",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Diagnostics indicate non-stable system status.",
        },
    ]


def test_audit_triadic_diagnostics_flags_health_categories() -> None:
    artifact = {
        "semanticMode": "non-executive",
        "system_status": "stable",
        "kernel_health": ["nan_detected"],
        "governance_health": ["policy_outlier", "projection_mismatch"],
        "epistemic_health": ["corridor_decay"],
    }

    findings = audit_triadic_diagnostics(artifact)

    assert findings == [
        {
            "law": "kernel_health_alerts",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "kernel_health contains 1 issue(s).",
        },
        {
            "law": "governance_health_alerts",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "governance_health contains 2 issue(s).",
        },
        {
            "law": "epistemic_health_alerts",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "epistemic_health contains 1 issue(s).",
        },
    ]

from sophia.audit_homeostasis import audit_homeostasis


def test_audit_homeostasis_warns_on_low_homeostasis() -> None:
    findings = audit_homeostasis({"H": 0.35})

    assert findings == [
        {
            "law": "epistemic_homeostasis",
            "severity": "warn",
            "advisory": "watch",
            "message": "Discovery collapse risk.",
        }
    ]


def test_audit_homeostasis_warns_on_high_homeostasis() -> None:
    findings = audit_homeostasis({"H": 1.25})

    assert findings == [
        {
            "law": "epistemic_homeostasis",
            "severity": "warn",
            "advisory": "watch",
            "message": "Exploration instability.",
        }
    ]


def test_audit_homeostasis_no_findings_within_band() -> None:
    findings = audit_homeostasis({"H": 0.9})

    assert findings == []

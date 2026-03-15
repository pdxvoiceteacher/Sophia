from sophia.audit_civilization_forecast import audit_civilization_forecast


def test_audit_civilization_forecast_detects_downward_trend() -> None:
    artifact = {
        "timeline": [
            {"knowledge": 0.8},
            {"knowledge": 0.7},
            {"knowledge": 0.6},
        ]
    }

    findings = audit_civilization_forecast(artifact)

    assert findings == [
        {
            "law": "civilizational_decay",
            "severity": "watch",
            "semanticMode": "non-executive",
            "message": "Knowledge forecast trends downward.",
        }
    ]


def test_audit_civilization_forecast_no_findings_for_flat_or_rising_trend() -> None:
    artifact = {
        "timeline": [
            {"knowledge": 0.4},
            {"knowledge": 0.4},
            {"knowledge": 0.5},
        ]
    }

    findings = audit_civilization_forecast(artifact)

    assert findings == []


def test_audit_civilization_forecast_no_findings_for_empty_timeline() -> None:
    findings = audit_civilization_forecast({"timeline": []})

    assert findings == []

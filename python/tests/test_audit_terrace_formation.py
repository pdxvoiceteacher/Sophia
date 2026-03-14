from sophia.audit_terrace_formation import audit_terrace_formation


def test_terrace_formation_advisory_findings():
    artifact = {
        "summary": {
            "averageTerraceDensity": 0.01,
            "maxTerraceDensity": 0.99,
        }
    }

    findings = audit_terrace_formation(artifact)

    assert len(findings) == 2
    assert all(f["semanticMode"] == "non-executive" for f in findings)

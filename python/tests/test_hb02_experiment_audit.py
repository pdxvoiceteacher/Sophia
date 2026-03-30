from sophia.hb02_experiment_audit import audit_hb02_experiment


def test_hb02_experiment_audit_coherent() -> None:
    result = audit_hb02_experiment(
        {
            "baseline": {
                "literal_output": "baseline literal",
                "allegorical_output": "baseline allegorical",
            },
            "conditioned": {
                "literal_output": "conditioned literal",
                "allegorical_output": "conditioned allegorical",
            },
            "true_coherence": "coherent",
            "coherence_context": "present",
        }
    )

    assert result == {
        "audit_pass": True,
        "findings": [],
        "experiment_coherence": "experiment_coherent",
    }


def test_hb02_experiment_audit_incoherent_on_invalid_field_context() -> None:
    result = audit_hb02_experiment(
        {
            "baseline": {
                "literal_output": "baseline literal",
                "allegorical_output": "baseline allegorical",
            },
            "conditioned": {
                "literal_output": "conditioned literal",
                "allegorical_output": "conditioned allegorical",
            },
            "true_coherence": "false_coherence",
            "coherence_context": "present",
        }
    )

    assert result["audit_pass"] is False
    assert result["experiment_coherence"] == "experiment_incoherent"
    assert result["findings"] == ["invalid_field_context"]


def test_hb02_experiment_audit_partial_when_outputs_or_context_missing() -> None:
    result = audit_hb02_experiment(
        {
            "baseline": {"literal_output": "baseline literal"},
            "conditioned": {"allegorical_output": "conditioned allegorical"},
            "true_coherence": "coherent",
            "coherence_context": "",
        }
    )

    assert result["audit_pass"] is False
    assert result["experiment_coherence"] == "experiment_partial"
    assert result["findings"] == [
        "baseline_dual_output_incomplete",
        "conditioned_dual_output_incomplete",
        "missing_context",
    ]

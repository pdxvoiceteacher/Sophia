from sophia.lens.coherence_lens import audit_dataset, evaluate_signal_quality


def test_evaluate_signal_quality_handles_none_and_non_string_fields() -> None:
    records = [
        {"title": None, "abstract": "Alpha beta"},
        {"title": 123, "abstract": None},
        {"title": "Gamma", "abstract": ["delta", "epsilon"]},
    ]

    result = evaluate_signal_quality(records)

    assert set(result.keys()) == {"signal_quality", "noise_ratio"}
    assert 0.0 <= result["signal_quality"] <= 1.0
    assert 0.0 <= result["noise_ratio"] <= 1.0


def test_audit_dataset_returns_auditable_per_record_relevance() -> None:
    records = [
        {"title": "", "abstract": None},
        {"title": "alpha beta", "abstract": "gamma"},
    ]

    result = audit_dataset(records)

    assert len(result) == 2
    assert result[0]["record"] == records[0]
    assert result[0]["relevance"] == 0.0
    assert result[0]["flag"] is True
    assert result[1]["record"] == records[1]
    assert 0.1 <= result[1]["relevance"] <= 1.0
    assert result[1]["flag"] is False

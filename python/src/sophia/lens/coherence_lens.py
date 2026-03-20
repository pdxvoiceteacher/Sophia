def _coerce_record_text(record):
    title = record.get("title") or ""
    abstract = record.get("abstract") or ""
    return (str(title) + " " + str(abstract)).lower()


def compute_relevance_score(record):
    """
    Compute a structural relevance proxy from token diversity in a single record.
    """
    terms = _coerce_record_text(record).split()
    if not terms:
        return 0.0

    diversity = len(set(terms)) / len(terms)
    return diversity


def evaluate_signal_quality(records):
    """
    PURELY statistical — no domain knowledge.
    """
    total_terms = 0
    unique_terms = set()
    for record in records:
        terms = _coerce_record_text(record).split()
        total_terms += len(terms)
        unique_terms.update(terms)
    if total_terms == 0:
        return {"signal_quality": 0.0, "noise_ratio": 1.0}
    diversity = len(unique_terms) / total_terms
    return {"signal_quality": diversity, "noise_ratio": 1 - diversity}


def apply_lens_weights(series, lens_metrics):
    """
    Adjust signal strength based on coherence quality (display/advisory only).
    """
    quality = lens_metrics["signal_quality"]
    return [(year, value * quality) for year, value in series]


def audit_dataset(records):
    results = []

    for record in records:
        score = compute_relevance_score(record)

        results.append(
            {
                "record": record,
                "relevance": score,
                "flag": score < 0.1,
            }
        )

    return results

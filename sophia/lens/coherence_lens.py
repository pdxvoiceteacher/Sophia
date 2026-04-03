def evaluate_signal_quality(records):
    """
    PURELY statistical — no domain knowledge.
    """

    total_terms = 0
    unique_terms = set()

    for r in records:
        text = (r.get("title", "") + " " + r.get("abstract", "")).lower()
        terms = text.split()

        total_terms += len(terms)
        unique_terms.update(terms)

    if total_terms == 0:
        return {
            "signal_quality": 0.0,
            "noise_ratio": 1.0,
        }

    diversity = len(unique_terms) / total_terms

    return {
        "signal_quality": diversity,
        "noise_ratio": 1 - diversity,
    }



def apply_lens_weights(series, lens_metrics):
    """
    Adjust signal strength based on coherence quality.
    """

    quality = lens_metrics["signal_quality"]

    adjusted = []
    for year, value in series:
        adjusted.append((year, value * quality))

    return adjusted

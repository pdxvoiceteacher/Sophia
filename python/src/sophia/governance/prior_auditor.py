# PURPOSE: Sophia formally audits prior-use mode compliance and routed answer integrity

import re


def _tokens(text: str) -> set[str]:
    toks = re.findall(r"[A-Za-z][A-Za-z0-9_\-]{2,}", (text or "").lower())
    stop = {
        "the",
        "and",
        "for",
        "with",
        "what",
        "which",
        "when",
        "where",
        "why",
        "how",
        "that",
        "this",
        "from",
        "into",
        "your",
        "their",
        "they",
        "are",
        "was",
        "were",
        "but",
        "can",
        "could",
        "should",
        "would",
        "have",
        "has",
    }
    return {t for t in toks if t not in stop}


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def audit_prior_use(packet: dict) -> dict:
    question_text = packet.get("question_text", "") or ""
    final_answer = packet.get("final_answer", "") or ""
    mode = packet.get("prior_injection_mode", "ignore")
    source_terms = packet.get("source_terms", [])
    trace = packet.get("prior_injection_trace", {}) or {}
    expected_return_track_id = packet.get("expected_return_track_id")
    answer_source_track = packet.get("answer_source_track")

    # Detect prompt contamination in the audit packet itself
    if question_text.lstrip().startswith("[ATLAS PRIOR INJECTION START]"):
        return {
            "formal_auditor": "Sophia",
            "audit_status": "warn",
            "audit_reason": "Audit packet question_text is contaminated by injected Atlas prompt text.",
            "mode_compliance": False,
            "question_relevance_score": 0.0,
            "prior_influence_score": 0.0,
            "source_grounding_preserved": False,
            "source_term_hits": 0,
            "recommendation": "fix_question_integrity_before_trusting_prior_use_audit",
        }

    answer_tokens = _tokens(final_answer)
    question_tokens = _tokens(question_text)

    question_relevance_score = _jaccard(answer_tokens, question_tokens)

    prior_overlap_scores = []
    injected_priors = trace.get("selected_priors", [])
    for p in injected_priors:
        prior_tokens = _tokens(p.get("excerpt", ""))
        prior_overlap_scores.append(_jaccard(answer_tokens, prior_tokens))

    prior_influence_score = max(prior_overlap_scores) if prior_overlap_scores else 0.0

    source_term_hits = 0
    final_lower = final_answer.lower()
    for term in source_terms:
        if term and term.lower() in final_lower:
            source_term_hits += 1

    source_grounding_preserved = source_term_hits > 0 if source_terms else True

    mode_compliance = True
    audit_status = "pass"
    audit_reason = "Prior usage appears consistent with Sophia governance mode."

    # Formal routing compliance check
    if expected_return_track_id and answer_source_track != expected_return_track_id:
        mode_compliance = False
        audit_status = "warn"
        audit_reason = (
            "Final answer source track does not match Sophia-routed return_track_id."
        )

    elif mode == "ignore":
        if prior_influence_score >= 0.08:
            mode_compliance = False
            audit_status = "warn"
            audit_reason = "Prior influence appears non-trivial despite ignore mode."

    elif mode == "background_only":
        if prior_influence_score >= 0.18:
            mode_compliance = False
            audit_status = "warn"
            audit_reason = "Background-only prior appears too dominant in final answer."

    elif mode == "answer_support":
        if question_relevance_score < 0.08:
            mode_compliance = False
            audit_status = "warn"
            audit_reason = "Answer-support prior did not preserve direct question relevance."
        elif not source_grounding_preserved:
            mode_compliance = False
            audit_status = "warn"
            audit_reason = "Answer-support prior appears to weaken source grounding."

    elif mode == "novelty_extension":
        if question_relevance_score < 0.08:
            mode_compliance = False
            audit_status = "warn"
            audit_reason = "Novelty extension appears to have displaced the direct answer."

    return {
        "formal_auditor": "Sophia",
        "audit_status": audit_status,
        "audit_reason": audit_reason,
        "mode_compliance": mode_compliance,
        "question_relevance_score": question_relevance_score,
        "prior_influence_score": prior_influence_score,
        "source_grounding_preserved": source_grounding_preserved,
        "source_term_hits": source_term_hits,
        "expected_return_track_id": expected_return_track_id,
        "answer_source_track": answer_source_track,
        "recommendation": (
            "keep" if audit_status == "pass" else "review_routing_or_question_integrity"
        ),
    }

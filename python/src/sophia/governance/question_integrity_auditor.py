# PURPOSE: Sophia formally audits question propagation across bridge artifacts


def audit_question_integrity(
    user_question_packet: dict | None,
    latest_nav_result: dict | None,
    atlas_query: dict | None,
    answer_relevance_packet: dict | None,
) -> dict:
    ingress_q = (user_question_packet or {}).get("user_question_text", "")
    nav_q = (latest_nav_result or {}).get("user_question_text", "")
    atlas_q = (atlas_query or {}).get("question_text", "")
    relevance_q = (answer_relevance_packet or {}).get("question_text", "")

    expected = ingress_q

    problems = []

    if not expected:
        problems.append("Pinned ingress user question is empty.")
    if nav_q != expected:
        problems.append("latest_nav_result.user_question_text does not match ingress question.")
    if atlas_q != expected:
        problems.append("atlas_query.question_text does not match ingress question.")
    if relevance_q != expected:
        problems.append("answer_relevance_packet.question_text does not match ingress question.")

    audit_status = "pass" if not problems else "warn"

    return {
        "formal_auditor": "Sophia",
        "audit_status": audit_status,
        "audit_reason": (
            "Question integrity preserved across runtime artifacts."
            if not problems
            else "Question integrity propagation failed across one or more runtime artifacts."
        ),
        "expected_question_text": expected,
        "latest_nav_result_question_text": nav_q,
        "atlas_query_question_text": atlas_q,
        "answer_relevance_question_text": relevance_q,
        "problems": problems,
        "recommendation": (
            "keep" if not problems else "repair_question_propagation_at_ingress_and_runtime"
        ),
    }

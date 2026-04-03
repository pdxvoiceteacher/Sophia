from pathlib import Path
import json

from fastapi import FastAPI
from sophia.governance.divergence_governor import evaluate_divergence
from sophia.governance.store import save_governance_decision
from sophia.governance.relevance_router import route_relevance_and_novelty
from sophia.governance.prior_router import route_prior_injection
from sophia.governance.prior_auditor import audit_prior_use
from sophia.governance.question_integrity_auditor import audit_question_integrity

app = FastAPI(title="Sophia Governance API", version="0.1.0")


@app.get("/health")
def health():
    return {"status": "ok", "service": "sophia"}


@app.post("/govern/divergence")
def govern_divergence():
    try:
        packet_path = Path(r"C:\UVLM\CoherenceLattice\bridge\governance_packet.json")
        if not packet_path.exists():
            return {"error": f"governance_packet.json not found at {packet_path}"}

        with open(packet_path, "r", encoding="utf-8") as f:
            packet = json.load(f)

        decision = evaluate_divergence(packet)

        out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\governance_decision.json")
        save_governance_decision(decision, out_path)

        return decision

    except Exception as e:
        import traceback

        return {
            "error": str(e),
            "traceback": traceback.format_exc(),
        }


@app.post("/govern/routing")
def govern_routing():
    packet_path = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_packet.json")
    if not packet_path.exists():
        return {"error": f"routing_packet.json not found at {packet_path}"}

    with open(packet_path, "r", encoding="utf-8") as f:
        packet = json.load(f)

    decision = route_relevance_and_novelty(packet)

    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_decision.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(decision, f, indent=2)

    return decision


@app.post("/govern/prior_injection")
def govern_prior_injection():
    routing_path = Path(r"C:\UVLM\CoherenceLattice\bridge\routing_packet.json")
    prior_path = Path(r"C:\UVLM\CoherenceLattice\bridge\atlas_prior_packet.json")

    if not routing_path.exists():
        return {"error": "routing_packet.json not found"}
    if not prior_path.exists():
        return {"error": "atlas_prior_packet.json not found"}

    routing_packet = json.loads(routing_path.read_text(encoding="utf-8"))
    atlas_prior_packet = json.loads(prior_path.read_text(encoding="utf-8"))

    decision = route_prior_injection(routing_packet, atlas_prior_packet)

    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\prior_injection_decision.json")
    out_path.write_text(json.dumps(decision, indent=2), encoding="utf-8")

    return decision


@app.post("/govern/prior_audit")
def govern_prior_audit():
    packet_path = Path(r"C:\UVLM\CoherenceLattice\bridge\prior_use_audit_packet.json")
    if not packet_path.exists():
        return {"error": "prior_use_audit_packet.json not found"}

    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    decision = audit_prior_use(packet)

    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\prior_audit_decision.json")
    out_path.write_text(json.dumps(decision, indent=2), encoding="utf-8")

    return decision


@app.post("/govern/question_integrity")
def govern_question_integrity():
    user_q_path = Path(r"C:\UVLM\CoherenceLattice\bridge\user_question_packet.json")
    nav_path = Path(r"C:\UVLM\CoherenceLattice\bridge\latest_nav_result.json")
    atlas_query_path = Path(r"C:\UVLM\CoherenceLattice\bridge\atlas_query.json")
    rel_path = Path(r"C:\UVLM\CoherenceLattice\bridge\answer_relevance_packet.json")

    user_question_packet = (
        json.loads(user_q_path.read_text(encoding="utf-8")) if user_q_path.exists() else {}
    )
    latest_nav_result = (
        json.loads(nav_path.read_text(encoding="utf-8")) if nav_path.exists() else {}
    )
    atlas_query = (
        json.loads(atlas_query_path.read_text(encoding="utf-8"))
        if atlas_query_path.exists()
        else {}
    )
    answer_relevance_packet = (
        json.loads(rel_path.read_text(encoding="utf-8")) if rel_path.exists() else {}
    )

    decision = audit_question_integrity(
        user_question_packet=user_question_packet,
        latest_nav_result=latest_nav_result,
        atlas_query=atlas_query,
        answer_relevance_packet=answer_relevance_packet,
    )

    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\question_integrity_audit.json")
    out_path.write_text(json.dumps(decision, indent=2), encoding="utf-8")

    return decision

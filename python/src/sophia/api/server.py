import json
import os
from pathlib import Path
from typing import Any

from fastapi import FastAPI

from sophia.governance.divergence_governor import evaluate_divergence
from sophia.governance.prior_auditor import audit_prior_use
from sophia.governance.prior_router import route_prior_injection
from sophia.governance.question_integrity_auditor import audit_question_integrity
from sophia.governance.relevance_router import route_relevance_and_novelty
from sophia.governance.store import save_governance_decision

app = FastAPI(title="Sophia Governance API", version="0.1.0")


def _resolve_bridge_root() -> Path:
    """
    Resolve the shared triadic bridge root.

    Priority:
      1) TRIADIC_BRIDGE_ROOT env var (explicit, OS-agnostic)
      2) COHERENCE_LATTICE_ROOT env var + /bridge
      3) sibling CoherenceLattice/bridge next to the Sophia repo
      4) fail with a clear error (do not silently invent paths)
    """
    env = os.getenv("TRIADIC_BRIDGE_ROOT")
    if env:
        return Path(env).expanduser().resolve()

    coh_root = os.getenv("COHERENCE_LATTICE_ROOT")
    if coh_root:
        candidate = (Path(coh_root) / "bridge").expanduser().resolve()
        if candidate.exists():
            return candidate

    repo_root = Path(__file__).resolve().parents[4]
    sibling = (repo_root.parent / "CoherenceLattice" / "bridge").resolve()
    if sibling.exists():
        return sibling

    raise RuntimeError(
        "Sophia cannot resolve triadic bridge root. "
        "Set TRIADIC_BRIDGE_ROOT to the CoherenceLattice bridge directory."
    )


BRIDGE_ROOT = _resolve_bridge_root()
GOVERNANCE_PACKET_FILE = BRIDGE_ROOT / "governance_packet.json"
GOVERNANCE_DECISION_FILE = BRIDGE_ROOT / "governance_decision.json"
ROUTING_PACKET_FILE = BRIDGE_ROOT / "routing_packet.json"
ROUTING_DECISION_FILE = BRIDGE_ROOT / "routing_decision.json"
ATLAS_QUERY_FILE = BRIDGE_ROOT / "atlas_query.json"
ATLAS_PRIOR_FILE = BRIDGE_ROOT / "atlas_prior_packet.json"
PRIOR_INJECTION_DECISION_FILE = BRIDGE_ROOT / "prior_injection_decision.json"
PRIOR_USE_AUDIT_PACKET_FILE = BRIDGE_ROOT / "prior_use_audit_packet.json"
PRIOR_AUDIT_DECISION_FILE = BRIDGE_ROOT / "prior_audit_decision.json"
USER_QUESTION_PACKET_FILE = BRIDGE_ROOT / "user_question_packet.json"
LATEST_NAV_RESULT_FILE = BRIDGE_ROOT / "latest_nav_result.json"
ANSWER_RELEVANCE_PACKET_FILE = BRIDGE_ROOT / "answer_relevance_packet.json"
QUESTION_INTEGRITY_AUDIT_FILE = BRIDGE_ROOT / "question_integrity_audit.json"


def _read_json_file(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json_file(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


@app.get("/health")
def health() -> dict[str, str]:
    return {"status": "ok", "service": "sophia"}


@app.post("/govern/divergence")
def govern_divergence() -> dict[str, Any]:
    if not GOVERNANCE_PACKET_FILE.exists():
        return {"error": f"governance_packet.json not found at {GOVERNANCE_PACKET_FILE}"}

    packet = _read_json_file(GOVERNANCE_PACKET_FILE)
    decision = evaluate_divergence(packet)
    save_governance_decision(decision, GOVERNANCE_DECISION_FILE)
    return decision


@app.post("/govern/routing")
def govern_routing() -> dict[str, Any]:
    if not ROUTING_PACKET_FILE.exists():
        return {"error": f"routing_packet.json not found at {ROUTING_PACKET_FILE}"}

    packet = _read_json_file(ROUTING_PACKET_FILE)
    decision = route_relevance_and_novelty(packet)
    _write_json_file(ROUTING_DECISION_FILE, decision)
    return decision


@app.post("/govern/prior_injection")
def govern_prior_injection() -> dict[str, Any]:
    if not ROUTING_PACKET_FILE.exists():
        return {"error": "routing_packet.json not found"}
    if not ATLAS_PRIOR_FILE.exists():
        return {"error": "atlas_prior_packet.json not found"}

    routing_packet = _read_json_file(ROUTING_PACKET_FILE)
    atlas_prior_packet = _read_json_file(ATLAS_PRIOR_FILE)

    decision = route_prior_injection(routing_packet, atlas_prior_packet)
    _write_json_file(PRIOR_INJECTION_DECISION_FILE, decision)
    return decision


@app.post("/govern/prior_audit")
def govern_prior_audit() -> dict[str, Any]:
    if not PRIOR_USE_AUDIT_PACKET_FILE.exists():
        return {"error": "prior_use_audit_packet.json not found"}

    packet = _read_json_file(PRIOR_USE_AUDIT_PACKET_FILE)
    decision = audit_prior_use(packet)
    _write_json_file(PRIOR_AUDIT_DECISION_FILE, decision)
    return decision


@app.post("/govern/question_integrity")
def govern_question_integrity() -> dict[str, Any]:
    user_question_packet = _read_json_file(USER_QUESTION_PACKET_FILE) if USER_QUESTION_PACKET_FILE.exists() else {}
    latest_nav_result = _read_json_file(LATEST_NAV_RESULT_FILE) if LATEST_NAV_RESULT_FILE.exists() else {}
    atlas_query = _read_json_file(ATLAS_QUERY_FILE) if ATLAS_QUERY_FILE.exists() else {}
    answer_relevance_packet = _read_json_file(ANSWER_RELEVANCE_PACKET_FILE) if ANSWER_RELEVANCE_PACKET_FILE.exists() else {}

    decision = audit_question_integrity(
        user_question_packet=user_question_packet,
        latest_nav_result=latest_nav_result,
        atlas_query=atlas_query,
        answer_relevance_packet=answer_relevance_packet,
    )
    _write_json_file(QUESTION_INTEGRITY_AUDIT_FILE, decision)
    return decision

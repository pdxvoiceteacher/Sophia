import json
from pathlib import Path

from fastapi import FastAPI

from sophia.governance.divergence_governor import evaluate_divergence
from sophia.governance.store import save_governance_decision

app = FastAPI(title="Sophia Governance API", version="0.1.0")


@app.post("/govern/divergence")
def govern_divergence():
    packet_path = Path("bridge") / "governance_packet.json"
    if not packet_path.exists():
        return {"error": "governance_packet.json not found"}

    with open(packet_path, "r", encoding="utf-8") as f:
        packet = json.load(f)

    decision = evaluate_divergence(packet)
    save_governance_decision(decision, Path("bridge") / "governance_decision.json")

    return decision

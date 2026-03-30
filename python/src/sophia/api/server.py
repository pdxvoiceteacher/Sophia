from pathlib import Path
import json

from fastapi import FastAPI
from sophia.governance.divergence_governor import evaluate_divergence
from sophia.governance.store import save_governance_decision

app = FastAPI(title="Sophia Governance API", version="0.1.0")


@app.get("/health")
def health():
    return {"status": "ok", "service": "sophia"}


@app.post("/govern/divergence")
def govern_divergence():
    packet_path = Path(r"C:\UVLM\CoherenceLattice\bridge\governance_packet.json")
    if not packet_path.exists():
        return {"error": f"governance_packet.json not found at {packet_path}"}

    with open(packet_path, "r", encoding="utf-8") as f:
        packet = json.load(f)

    decision = evaluate_divergence(packet)

    out_path = Path(r"C:\UVLM\CoherenceLattice\bridge\governance_decision.json")
    save_governance_decision(decision, out_path)

    return decision

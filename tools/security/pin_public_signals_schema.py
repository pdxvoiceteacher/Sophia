from __future__ import annotations
import json, hashlib
from pathlib import Path

schema_path = Path("ucc/schemas/public_signals/vote_proof_envelope_public_signals_v1.schema.json")
schema_sha = hashlib.sha256(schema_path.read_bytes()).hexdigest()

reg_path = Path("ucc/verifiers/registry.json")
reg = json.loads(reg_path.read_text(encoding="utf-8-sig")) if reg_path.exists() else {}

for vid in ["stub.sha256.v1", "stub.sha256.pinned.v1"]:
    if vid in reg:
        reg[vid]["signals_schema_path"] = str(schema_path).replace("\\","/")
        reg[vid]["signals_schema_sha256"] = schema_sha
        reg[vid]["signals_schema_required"] = True

reg_path.write_text(json.dumps(reg, indent=2, sort_keys=True), encoding="utf-8")
print("Pinned public_signals schema in registry for stub verifiers.")
print("signals_schema_sha256 =", schema_sha)

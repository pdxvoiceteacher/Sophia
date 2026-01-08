from __future__ import annotations
import json, hashlib
from pathlib import Path

schema = Path("ucc/schemas/public_signals/vote_proof_envelope_public_signals_v1.schema.json")
obj = json.loads(schema.read_text(encoding="utf-8-sig"))

# Write canonical JSON with LF and no BOM
txt = json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
with schema.open("w", encoding="utf-8", newline="\n") as f:
    f.write(txt)

sha = hashlib.sha256(schema.read_bytes()).hexdigest()

reg_path = Path("ucc/verifiers/registry.json")
reg = json.loads(reg_path.read_text(encoding="utf-8-sig"))

for vid in ("stub.sha256.v1", "stub.sha256.pinned.v1"):
    if vid in reg:
        reg[vid]["signals_schema_path"] = str(schema).replace("\\", "/")
        reg[vid]["signals_schema_sha256"] = sha
        reg[vid]["signals_schema_required"] = True

reg_txt = json.dumps(reg, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
with reg_path.open("w", encoding="utf-8", newline="\n") as f:
    f.write(reg_txt)

print("Pinned signals_schema_sha256 =", sha)

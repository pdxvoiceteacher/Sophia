from __future__ import annotations
import json, hashlib
from pathlib import Path

repo = Path(".")
cir_dir = repo / "ucc" / "circuits"
cir_dir.mkdir(parents=True, exist_ok=True)

# 1) Write strict public circuit descriptor (canonical JSON, LF, no BOM)
circuit_id = "vote_proof_envelope_public.v1"
cir_path = cir_dir / "vote_proof_envelope_public_v1.circuit.json"

descriptor = {
  "schema": "ucc.circuit_descriptor.v0",
  "name": "vote_proof_envelope_public_v1",
  "purpose": "Public deliberation strict circuit: binds ciphertext+nullifier+choice_hash and requires strict public input order",
  "public_signals": [
    "manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash","public_inputs"
  ],
  "constraints": {
    "public_inputs_order": ["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash"]
  },
  "verifier": {"alg": "STUB", "notes": "Placeholder; replace with real ZK circuit later."}
}

cir_txt = json.dumps(descriptor, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
cir_path.write_text(cir_txt, encoding="utf-8", newline="\n")

cir_sha = hashlib.sha256(cir_path.read_bytes()).hexdigest()

# 2) Update circuit registry with pinned sha
reg_path = cir_dir / "registry.json"
reg = json.loads(reg_path.read_text(encoding="utf-8-sig")) if reg_path.exists() else {}

reg[circuit_id] = {
  "enabled": True,
  "circuit_path": "ucc/circuits/vote_proof_envelope_public_v1.circuit.json",
  "circuit_sha256": cir_sha,
  "notes": "Strict circuit for public.deliberation scope"
}

reg_txt = json.dumps(reg, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
reg_path.write_text(reg_txt, encoding="utf-8", newline="\n")

print("Added circuit:", circuit_id)
print("Pinned circuit_sha256:", cir_sha)

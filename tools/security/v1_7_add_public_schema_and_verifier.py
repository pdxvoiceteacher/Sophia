from __future__ import annotations
import json, hashlib
from pathlib import Path

repo = Path(".")
schema_dir = repo / "ucc" / "schemas" / "public_signals"
schema_dir.mkdir(parents=True, exist_ok=True)

# Strict public schema: public_inputs.order must be the default order AND values length fixed at 6
strict_schema_path = schema_dir / "vote_proof_envelope_public_signals_v1.schema.json"
default_order = ["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash"]

strict_schema = {
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "ucc.public_signals.vote_proof_envelope_public.v1",
  "type": "object",
  "additionalProperties": False,
  "required": ["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash","public_inputs"],
  "properties": {
    "manifest_id": {"type":"string","minLength":1},
    "ballot_id": {"type":"string","minLength":1},
    "nullifier_sha256": {"type":"string","pattern":"^[0-9a-f]{64}$"},
    "ciphertext_sha256": {"type":"string","pattern":"^[0-9a-f]{64}$"},
    "aad_sha256": {"type":"string","pattern":"^[0-9a-f]{64}$"},
    "choice_hash": {"type":"string","pattern":"^[0-9a-f]{64}$"},
    "public_inputs": {
      "type":"object",
      "additionalProperties": False,
      "required":["format","version","order","values"],
      "properties":{
        "format":{"const":"snarkjs.public_inputs.v1"},
        "version":{"const":1},
        "order":{"const": default_order},
        "values":{"type":"array","minItems":6,"maxItems":6,"items":{"type":"string"}}
      }
    }
  }
}

strict_schema_path.write_text(json.dumps(strict_schema, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
schema_sha = hashlib.sha256(strict_schema_path.read_bytes()).hexdigest()

# Update verifier registry with a pinned public verifier mapped to public circuit
ver_reg_path = repo / "ucc" / "verifiers" / "registry.json"
ver_reg = json.loads(ver_reg_path.read_text(encoding="utf-8-sig"))

# Reuse dummy vk pin from existing pinned stub if available
vk_path = ver_reg.get("stub.sha256.pinned.v1", {}).get("vk_path")
vk_sha  = ver_reg.get("stub.sha256.pinned.v1", {}).get("vk_sha256")

if not vk_path or not vk_sha:
    raise SystemExit("Expected stub.sha256.pinned.v1 to exist with vk_path + vk_sha256 (dummy vk pin).")

ver_reg["stub.sha256.public.pinned.v1"] = {
  "kind":"stub",
  "alg":"PROOF_STUB_SHA256",
  "enabled": True,

  "vk_path": vk_path,
  "vk_sha256": vk_sha,
  "pin_required": True,

  "signals_schema_path": "ucc/schemas/public_signals/vote_proof_envelope_public_signals_v1.schema.json",
  "signals_schema_sha256": schema_sha,
  "signals_schema_required": True,

  "circuit_id": "vote_proof_envelope_public.v1",
  "circuit_required": True
}

ver_reg_path.write_text(json.dumps(ver_reg, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")

print("Wrote strict public signals schema + pinned sha:", schema_sha)
print("Added verifier: stub.sha256.public.pinned.v1")

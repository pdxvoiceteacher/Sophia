from __future__ import annotations

"""
Verifier Registry v0.6

Purpose:
- Provide a stable interface to select a proof verifier by verifier_id
- Allow swapping PROOF_STUB verifier for real ZK verifiers later
  without changing the proof envelope data model.

Supports:
- Built-in default registry
- Optional extension via JSON file path (env: UCC_VERIFIER_REGISTRY_PATH)
"""

from pathlib import Path
from typing import Any, Dict, Optional
import json
import os

DEFAULT_VERIFIER_ID = "stub.sha256.v1"

# Minimal built-in registry (extendable)
DEFAULT_REGISTRY: Dict[str, Dict[str, Any]] = {
    "stub.sha256.v1": {
        "kind": "stub",
        "alg": "PROOF_STUB_SHA256",
        "vk": None,
        "enabled": True,
    },
    # Future examples (placeholders):
    # "groth16.bn254.v1": {"kind": "snark", "alg": "GROTH16", "vk_path": "ucc/verifiers/groth16_bn254_vk.json", "enabled": False},
    # "plonk.bn254.v1":   {"kind": "snark", "alg": "PLONK",   "vk_path": "ucc/verifiers/plonk_bn254_vk.json",   "enabled": False},
}


def load_registry(extra_path: Optional[Path] = None) -> Dict[str, Dict[str, Any]]:
    reg = dict(DEFAULT_REGISTRY)

    p = extra_path
    if p is None:
        envp = os.getenv("UCC_VERIFIER_REGISTRY_PATH", "").strip()
        p = Path(envp) if envp else None

    if p and p.exists():
        try:
            obj = json.loads(p.read_text(encoding="utf-8-sig"))
            if isinstance(obj, dict):
                for k, v in obj.items():
                    if isinstance(k, str) and isinstance(v, dict):
                        reg[k] = v
        except Exception:
            # If registry file is malformed, keep defaults.
            pass

    return reg


def get_spec(verifier_id: str, registry: Optional[Dict[str, Dict[str, Any]]] = None) -> Dict[str, Any]:
    registry = registry or load_registry()
    spec = registry.get(verifier_id)
    if not spec:
        raise ValueError(f"Unknown verifier_id: {verifier_id}")
    if not spec.get("enabled", True):
        raise ValueError(f"Verifier disabled: {verifier_id}")
    return spec

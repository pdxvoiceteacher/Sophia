import json
import hashlib
from pathlib import Path

import pytest

from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, verify_proof_envelope


def _write_overlay_registry(path: Path, verifier_id: str, vk_path: Path, vk_sha256: str) -> None:
    path.write_text(
        json.dumps(
            {
                verifier_id: {
                    "kind": "stub",
                    "alg": "PROOF_STUB_SHA256",
                    "enabled": True,
                    "vk_path": str(vk_path),   # absolute path OK
                    "vk_sha256": vk_sha256,
                    "pin_required": True,
                }
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def test_vk_pinning_rejects_vk_sha_tamper(tmp_path: Path, monkeypatch):
    # Create a temp vk file + pinned registry
    vk = tmp_path / "vk.json"
    vk.write_text('{"vk":"one"}', encoding="utf-8")
    sha = hashlib.sha256(vk.read_bytes()).hexdigest()

    reg = tmp_path / "reg.json"
    _write_overlay_registry(reg, "test.pinned", vk, sha)
    monkeypatch.setenv("UCC_VERIFIER_REGISTRY_PATH", str(reg))

    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="test.pinned")

    # Carries pinned sha
    assert proof["vk_sha256"] == sha

    # Verifies OK
    verify_proof_envelope(proof)

    # Tamper proof's vk_sha256 => must fail
    proof2 = dict(proof)
    proof2["vk_sha256"] = "deadbeef"
    with pytest.raises(ValueError):
        verify_proof_envelope(proof2)


def test_vk_file_sha_mismatch_rejected(tmp_path: Path, monkeypatch):
    vk = tmp_path / "vk.json"
    vk.write_text('{"vk":"one"}', encoding="utf-8")
    sha = hashlib.sha256(vk.read_bytes()).hexdigest()

    reg = tmp_path / "reg.json"
    _write_overlay_registry(reg, "test.pinned", vk, sha)
    monkeypatch.setenv("UCC_VERIFIER_REGISTRY_PATH", str(reg))

    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="test.pinned")

    # OK initially
    verify_proof_envelope(proof)

    # Mutate vk file => registry pin must fail on next verify
    vk.write_text('{"vk":"two"}', encoding="utf-8")
    with pytest.raises(ValueError):
        verify_proof_envelope(proof)


def test_default_stub_roundtrip(tmp_path: Path):
    # No overlay registry; uses default stub verifier
    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal)
    assert "verifier_id" in proof
    assert "vk_sha256" in proof
    verify_proof_envelope(proof)

import json
import hashlib
import os
import subprocess
import sys
from pathlib import Path


def test_build_envelope_derives_all_signals_from_public_json(tmp_path: Path):
    repo_root = Path(__file__).resolve().parents[2]
    script = (repo_root / "tools" / "security" / "build_proof_envelope_snarkjs.py").resolve()

    # Arrange temp vote dir
    vote = tmp_path / "vote"
    (vote / "secret_v03" / "commits").mkdir(parents=True)
    (vote / "secret_v03" / "proofs").mkdir(parents=True)

    manifest_id = "m"
    ballot_id = "b"
    nullifier = "n"
    cts = "c"
    aad = "a"
    ch = "h"

    # Overlay verifier registry with a SNARK verifier (GROTH16) so builder will accept it.
    # We also include a dummy vk pin; the builder only reads vk_sha256 for metadata.
    vk = tmp_path / "vk.json"
    vk.write_text('{"vk":"dummy"}', encoding="utf-8")
    vk_sha = hashlib.sha256(vk.read_bytes()).hexdigest()

    reg = tmp_path / "reg.json"
    reg.write_text(json.dumps({
        "test.groth16": {
            "kind": "snark",
            "alg": "GROTH16",
            "enabled": True,
            "vk_path": str(vk),      # absolute path OK (we support this)
            "vk_sha256": vk_sha,
            "pin_required": False
        }
    }, indent=2), encoding="utf-8")

    # vote_manifest.json uses the SNARK verifier
    (vote / "vote_manifest.json").write_text(json.dumps({
        "manifest_id": manifest_id,
        "proof_policy": {"verifier_id": "test.groth16"}
    }), encoding="utf-8")

    # prover_manifest.json defines order and public_json_path
    (vote / "prover_manifest.json").write_text(json.dumps({
        "schema_id": "ucc.prover_manifest.v2",
        "version": 2,
        "vote_dir": str(vote),
        "verifier_id": "test.groth16",
        "circuit_id": "vote_proof_envelope.v1",
        "backend": {"name": "snarkjs", "alg": "GROTH16", "mode": "fullprover"},
        "artifacts": {
            "vk_path": str(vk),
            "proof_json_path": "proof.json",
            "public_json_path": "public.json"
        },
        "outputs": {"proof_envelope_path": "secret_v03/proofs/proof_b.json"},
        "public_inputs": {
            "format": "snarkjs.public_inputs.v1",
            "version": 1,
            "order": ["manifest_id","ballot_id","nullifier_sha256","ciphertext_sha256","aad_sha256","choice_hash"],
            "strict": True
        }
    }), encoding="utf-8")

    # commit file (cross-check only)
    commit = {
        "ballot_id": ballot_id,
        "nullifier_sha256": nullifier,
        "ciphertext_sha256": cts,
        "aad_sha256": aad
    }
    commit_path = vote / "secret_v03" / "commits" / "commit_b.json"
    commit_path.write_text(json.dumps(commit), encoding="utf-8")

    # dummy groth16 proof json (shape-valid enough for wrapping)
    proof_json = {"pi_a":[1,2], "pi_b":[[1,2],[3,4]], "pi_c":[5,6]}
    proof_path = vote / "proof.json"
    proof_path.write_text(json.dumps(proof_json), encoding="utf-8")

    # public.json is authoritative
    public_path = vote / "public.json"
    public_path.write_text(json.dumps([manifest_id, ballot_id, nullifier, cts, aad, ch]), encoding="utf-8")

    # Run builder script with overlay registry env
    env = dict(os.environ)
    env["UCC_VERIFIER_REGISTRY_PATH"] = str(reg)

    p = subprocess.run(
        [sys.executable, str(script), "--vote-dir", str(vote), "--commit", str(commit_path), "--proof-json", str(proof_path)],
        cwd=str(repo_root),
        env=env,
        capture_output=True,
        text=True,
        check=True,
    )

    out_path = vote / "secret_v03" / "proofs" / f"proof_{ballot_id}.json"
    env_doc = json.loads(out_path.read_text(encoding="utf-8"))

    ps = env_doc["public_signals"]
    assert ps["manifest_id"] == manifest_id
    assert ps["ballot_id"] == ballot_id
    assert ps["choice_hash"] == ch
    assert "public_inputs" in ps
    assert ps["public_inputs"]["values"][0] == manifest_id


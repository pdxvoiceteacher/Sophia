import json
from pathlib import Path
import hashlib

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest
from ucc.vote_guardrail import audit_vote_manifest


def test_public_deliberation_requires_proof_policy_strict(tmp_path: Path):
    outdir = tmp_path / "vote"
    m = build_vote_manifest(
        title="Public Vote",
        purpose_id="p",
        purpose_statement="s",
        scope="public.deliberation",
        anonymity_mode="secret",
        tally_mode="encrypted",
        anti_coercion=True,
        weighting_mode="one_person_one_vote",
        electorate_type="did_vc",
        electorate_rules={"issuer":"UVLM","vc_type":"MemberCredential"},
        # no proof_policy
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))
    msha = hashlib.sha256(mp.read_bytes()).hexdigest()

    rep = audit_vote_manifest(manifest, manifest_sha256=msha, strict=True)
    assert rep["passed"] is False


def test_public_deliberation_accepts_required_proof_policy(tmp_path: Path):
    outdir = tmp_path / "vote2"
    m = build_vote_manifest(
        title="Public Vote OK",
        purpose_id="p",
        purpose_statement="s",
        scope="public.deliberation",
        anonymity_mode="secret",
        tally_mode="encrypted",
        anti_coercion=True,
        weighting_mode="one_person_one_vote",
        electorate_type="did_vc",
        electorate_rules={"issuer":"UVLM","vc_type":"MemberCredential"},
        proof_policy={
            "verifier_id":"stub.sha256.public.pinned.v1",
            "circuit_id":"vote_proof_envelope_public.v1"
        },
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))
    msha = hashlib.sha256(mp.read_bytes()).hexdigest()

    rep = audit_vote_manifest(manifest, manifest_sha256=msha, strict=True)
    assert rep["passed"] is True

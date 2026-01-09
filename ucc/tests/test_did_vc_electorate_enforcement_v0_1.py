import json
import hashlib
from pathlib import Path
import pytest

pytest.importorskip("coherenceledger")

from coherenceledger.keystore import KeyStore

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest
from ucc.vote_ballot import build_ballot, write_ballot
from ucc.vote_tally import write_tally

from ucc.vc_issuer import issue_vc
from ucc.vc_registry import load_registry, save_registry, add_vc, revoke_vc


def _write_vc_into_registry(reg_path: Path, vc: dict) -> None:
    reg = load_registry(reg_path)
    add_vc(reg, vc)
    save_registry(reg_path, reg)

    # vc_verify expects the VC JSON file to exist next to registry, named vc_<id with : replaced>.json
    vc_path = reg_path.parent / f"vc_{vc['id'].replace(':','_')}.json"
    vc_path.write_text(json.dumps(vc, indent=2, sort_keys=True), encoding="utf-8")
    return


def _make_manifest(*, issuer_did: str, registry_path: Path) -> dict:
    return build_vote_manifest(
        title="VC Vote",
        purpose_id="ucc.demo.vc",
        purpose_statement="did_vc enforcement test",
        scope="org.governance",
        anonymity_mode="open",
        tally_mode="plaintext",
        electorate_type="did_vc",
        electorate_rules={
            "vc_type": "MemberCredential",
            "issuer_did": issuer_did,
            "registry_path": str(registry_path),
        },
        weighting_mode="one_person_one_vote",
        weighting_params={},
    )


def test_write_ballot_rejects_without_vc(tmp_path: Path):
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()

    issuer_ks = repo_root / ".secrets" / "issuer.json"
    voter_ks  = repo_root / ".secrets" / "voter.json"
    KeyStore(path=issuer_ks).generate()
    KeyStore(path=voter_ks).generate()

    issuer_did, _ = KeyStore(path=issuer_ks).load_keypair()
    voter_did, _  = KeyStore(path=voter_ks).load_keypair()

    reg_path = repo_root / "vc_registry.json"
    save_registry(reg_path, load_registry(reg_path))  # initialize empty registry

    outdir = tmp_path / "vote"
    manifest = _make_manifest(issuer_did=issuer_did.did, registry_path=reg_path)
    mp = write_vote_manifest(outdir=outdir, manifest=manifest, sign=False, anchor=False, repo_root=repo_root, keystore_path=issuer_ks, ledger_path=repo_root/"ledger.jsonl")
    manifest_obj = json.loads(mp.read_text(encoding="utf-8"))

    ballot = build_ballot(manifest_id=manifest_obj["manifest_id"], ballot_type="single_choice", selection={"choice": "YES"})

    with pytest.raises(ValueError):
        write_ballot(outdir=outdir, ballot=ballot, manifest=manifest_obj, sign=True, anchor=False, repo_root=repo_root, keystore_path=voter_ks, ledger_path=repo_root/"ledger.jsonl")


def test_write_ballot_accepts_with_valid_vc(tmp_path: Path):
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()

    issuer_ks = repo_root / ".secrets" / "issuer.json"
    voter_ks  = repo_root / ".secrets" / "voter.json"
    KeyStore(path=issuer_ks).generate()
    KeyStore(path=voter_ks).generate()

    issuer_did, _ = KeyStore(path=issuer_ks).load_keypair()
    voter_did, _  = KeyStore(path=voter_ks).load_keypair()

    reg_path = repo_root / "vc_registry.json"

    vc = issue_vc(
        issuer_did=issuer_did.did,
        subject_did=voter_did.did,
        types=["MemberCredential"],
        subject_claims={"role": "member"},
        keystore_path=issuer_ks,
    )
    _write_vc_into_registry(reg_path, vc)

    outdir = tmp_path / "vote"
    manifest = _make_manifest(issuer_did=issuer_did.did, registry_path=reg_path)
    mp = write_vote_manifest(outdir=outdir, manifest=manifest, sign=False, anchor=False, repo_root=repo_root, keystore_path=issuer_ks, ledger_path=repo_root/"ledger.jsonl")
    manifest_obj = json.loads(mp.read_text(encoding="utf-8"))

    ballot = build_ballot(manifest_id=manifest_obj["manifest_id"], ballot_type="single_choice", selection={"choice": "YES"})
    bp = write_ballot(outdir=outdir, ballot=ballot, manifest=manifest_obj, sign=True, anchor=False, repo_root=repo_root, keystore_path=voter_ks, ledger_path=repo_root/"ledger.jsonl")
    assert bp.exists()


def test_tally_marks_ballot_invalid_if_vc_revoked_after_cast(tmp_path: Path):
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()

    issuer_ks = repo_root / ".secrets" / "issuer.json"
    voter_ks  = repo_root / ".secrets" / "voter.json"
    KeyStore(path=issuer_ks).generate()
    KeyStore(path=voter_ks).generate()

    issuer_did, _ = KeyStore(path=issuer_ks).load_keypair()
    voter_did, _  = KeyStore(path=voter_ks).load_keypair()

    reg_path = repo_root / "vc_registry.json"

    vc = issue_vc(
        issuer_did=issuer_did.did,
        subject_did=voter_did.did,
        types=["MemberCredential"],
        subject_claims={"role": "member"},
        keystore_path=issuer_ks,
    )
    _write_vc_into_registry(reg_path, vc)

    outdir = tmp_path / "vote"
    manifest = _make_manifest(issuer_did=issuer_did.did, registry_path=reg_path)
    mp = write_vote_manifest(outdir=outdir, manifest=manifest, sign=False, anchor=False, repo_root=repo_root, keystore_path=issuer_ks, ledger_path=repo_root/"ledger.jsonl")
    manifest_obj = json.loads(mp.read_text(encoding="utf-8"))

    # cast ballot while VC valid
    ballot = build_ballot(manifest_id=manifest_obj["manifest_id"], ballot_type="single_choice", selection={"choice": "YES"})
    write_ballot(outdir=outdir, ballot=ballot, manifest=manifest_obj, sign=True, anchor=False, repo_root=repo_root, keystore_path=voter_ks, ledger_path=repo_root/"ledger.jsonl")

    # revoke after casting
    reg = load_registry(reg_path)
    revoke_vc(reg, vc["id"], "revoked after cast")
    save_registry(reg_path, reg)

    tp = write_tally(
        outdir=outdir,
        manifest_path=mp,
        verify_ballot_signatures=True,
        strict=True,
        sign=False,
        anchor=False,
        repo_root=repo_root,
        keystore_path=issuer_ks,
        ledger_path=repo_root/"ledger.jsonl",
        ledger_purpose="ucc.vote_tally.anchor",
    )

    t = json.loads(tp.read_text(encoding="utf-8"))
    assert t["ballots"]["valid"] == 0
    assert t["ballots"]["invalid"] == 1
    assert t.get("counts", {}) == {}

import json
from pathlib import Path
import pytest

pytest.importorskip("coherenceledger")

from coherenceledger.keystore import KeyStore
from ucc.vc_issuer import issue_vc
from ucc.vc_registry import load_registry, save_registry, add_vc, revoke_vc
from ucc.vc_verify import verify_vc_signature, find_valid_vc_for_subject


def test_vc_signature_and_revocation(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / ".secrets").mkdir()

    issuer_ks = repo / ".secrets" / "issuer.json"
    KeyStore(path=issuer_ks).generate()
    issuer_did, _ = KeyStore(path=issuer_ks).load_keypair()

    subject = "did:key:subject123"

    vc = issue_vc(
        issuer_did=issuer_did.did,
        subject_did=subject,
        types=["MemberCredential"],
        subject_claims={"role":"member"},
        keystore_path=issuer_ks,
    )
    verify_vc_signature(vc)

    reg_path = repo / "vc_registry.json"
    reg = load_registry(reg_path)
    add_vc(reg, vc)
    save_registry(reg_path, reg)

    # write VC file where vc_verify expects it (registry parent)
    vc_path = reg_path.parent / f"vc_{vc['id'].replace(':','_')}.json"
    vc_path.write_text(json.dumps(vc), encoding="utf-8")

    vc2 = find_valid_vc_for_subject(registry_path=reg_path, subject_did=subject, vc_type="MemberCredential", issuer_did=issuer_did.did)
    assert vc2["id"] == vc["id"]

    # revoke -> must fail
    reg = load_registry(reg_path)
    revoke_vc(reg, vc["id"], "test")
    save_registry(reg_path, reg)

    with pytest.raises(ValueError):
        find_valid_vc_for_subject(registry_path=reg_path, subject_did=subject, vc_type="MemberCredential", issuer_did=issuer_did.did)

import json
from pathlib import Path
import importlib.util

import pytest

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest
from ucc.vote_ballot import build_ballot, write_ballot


def test_ballot_writes_minimal(tmp_path: Path):
    # manifest (open)
    m = build_vote_manifest(
        title="M",
        purpose_id="p",
        purpose_statement="s",
        scope="org.governance",
        anonymity_mode="open",
    )
    outdir = tmp_path / "vote"
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    # ballot
    b = build_ballot(
        manifest_id=manifest["manifest_id"],
        ballot_type="single_choice",
        selection={"choice": "YES"},
    )
    bp = write_ballot(outdir=outdir, ballot=b, manifest=manifest, sign=False, anchor=False)
    assert bp.exists()
    data = json.loads(bp.read_text(encoding="utf-8"))
    assert data["manifest_id"] == manifest["manifest_id"]
    assert data["ballot"]["type"] == "single_choice"


@pytest.mark.skipif(importlib.util.find_spec("coherenceledger") is None, reason="coherenceledger not installed")
def test_ballot_can_sign_and_anchor(tmp_path: Path):
    from coherenceledger.keystore import KeyStore
    from coherenceledger.ledger import Ledger
    from coherenceledger.crypto import b64decode, load_public_key_raw

    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()
    keystore = repo_root / ".secrets" / "coherenceledger_keystore.json"
    ledger = repo_root / "ledger.jsonl"

    ks = KeyStore(path=keystore)
    ks.generate()

    # manifest open
    outdir = tmp_path / "vote2"
    m = build_vote_manifest(
        title="Signed Vote",
        purpose_id="p2",
        purpose_statement="s2",
        scope="org.governance",
        anonymity_mode="open",
    )
    mp = write_vote_manifest(
        outdir=outdir,
        manifest=m,
        sign=False,
        anchor=False,
        repo_root=repo_root,
        keystore_path=keystore,
        ledger_path=ledger,
    )
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    b = build_ballot(
        manifest_id=manifest["manifest_id"],
        ballot_type="single_choice",
        selection={"choice": "YES"},
    )
    bp = write_ballot(
        outdir=outdir,
        ballot=b,
        manifest=manifest,
        sign=True,
        anchor=True,
        repo_root=repo_root,
        keystore_path=keystore,
        ledger_path=ledger,
        ledger_purpose="ucc.vote_ballot.cast",
    )

    data = json.loads(bp.read_text(encoding="utf-8"))
    assert "signature" in data
    sig = data["signature"]

    # verify payload signature
    body = dict(data)
    body.pop("signature", None)
    try:
        from coherenceledger import jcs
        payload = jcs.dumps(body).encode("utf-8")
    except Exception:
        import json as _json
        payload = _json.dumps(body, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode("utf-8")

    pub = load_public_key_raw(b64decode(sig["public_key_b64"]))
    pub.verify(b64decode(sig["signature"]), payload)

    L = Ledger(path=ledger)
    L.verify()


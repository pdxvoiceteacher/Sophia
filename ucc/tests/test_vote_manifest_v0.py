import json
from pathlib import Path
import importlib.util

import pytest

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest


def test_vote_manifest_writes_minimal(tmp_path: Path):
    outdir = tmp_path / "vote"
    m = build_vote_manifest(
        title="Test Vote",
        purpose_id="test.purpose",
        purpose_statement="Test purpose statement",
        scope="org.governance",
    )
    p = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    assert p.exists()
    data = json.loads(p.read_text(encoding="utf-8"))
    for k in ("version","manifest_id","created_at","purpose","electorate","anonymity","weighting","timeline"):
        assert k in data


@pytest.mark.skipif(importlib.util.find_spec("coherenceledger") is None, reason="coherenceledger not installed")
def test_vote_manifest_can_sign_and_anchor(tmp_path: Path):
    # local-only security test: uses temp keystore + temp ledger
    from coherenceledger.keystore import KeyStore
    from coherenceledger.ledger import Ledger
    from coherenceledger.crypto import b64decode, load_public_key_raw

    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()
    keystore = repo_root / ".secrets" / "coherenceledger_keystore.json"
    ledger = repo_root / "ledger.jsonl"

    # Create keystore
    ks = KeyStore(path=keystore)
    ks.generate_and_store()

    outdir = tmp_path / "vote2"
    m = build_vote_manifest(
        title="Signed Vote",
        purpose_id="test.signed",
        purpose_statement="Signed purpose statement",
        scope="dao.governance",
        anonymity_mode="secret",
        tally_mode="encrypted",
        anti_coercion=True,
        weighting_mode="coherence",
        weighting_params={"metric": "Psi", "cap": 3},
    )

    p = write_vote_manifest(
        outdir=outdir,
        manifest=m,
        sign=True,
        anchor=True,
        repo_root=repo_root,
        keystore_path=keystore,
        ledger_path=ledger,
        ledger_purpose="ucc.vote_manifest.anchor",
    )

    # Verify manifest signature exists
    data = json.loads(p.read_text(encoding="utf-8"))
    assert "signature" in data
    sig = data["signature"]
    assert "did" in sig and "signature" in sig and "public_key_b64" in sig

    # Verify ledger chain
    L = Ledger(path=ledger)
    L.verify()

    # Verify signature cryptographically (payload is manifest without signature)
    body = dict(data)
    body.pop("signature", None)

    # Prefer coherenceledger canonicalization if present
    try:
        from coherenceledger import jcs
        payload = jcs.dumps(body).encode("utf-8")
    except Exception:
        import json as _json
        payload = _json.dumps(body, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode("utf-8")

    pub = load_public_key_raw(b64decode(sig["public_key_b64"]))
    pub.verify(b64decode(sig["signature"]), payload)

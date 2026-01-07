import json
from pathlib import Path
import importlib.util

import pytest

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest
from ucc.vote_ballot import build_ballot, write_ballot
from ucc.vote_tally import write_tally


def test_tally_counts_single_choice(tmp_path: Path):
    # manifest (open)
    outdir = tmp_path / "vote"
    m = build_vote_manifest(
        title="M",
        purpose_id="p",
        purpose_statement="s",
        scope="org.governance",
        anonymity_mode="open",
    electorate_rules={"max_ballots_per_did": 2},
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    # ballots
    b1 = build_ballot(manifest_id=manifest["manifest_id"], ballot_type="single_choice", selection={"choice": "YES"})
    b2 = build_ballot(manifest_id=manifest["manifest_id"], ballot_type="single_choice", selection={"choice": "NO"})
    b3 = build_ballot(manifest_id=manifest["manifest_id"], ballot_type="single_choice", selection={"choice": "YES"})

    write_ballot(outdir=outdir, ballot=b1, manifest=manifest, sign=False, anchor=False)
    write_ballot(outdir=outdir, ballot=b2, manifest=manifest, sign=False, anchor=False)
    write_ballot(outdir=outdir, ballot=b3, manifest=manifest, sign=False, anchor=False)

    tp = write_tally(outdir=outdir, manifest_path=mp, verify_ballot_signatures=False, strict=False, sign=False, anchor=False)
    t = json.loads(tp.read_text(encoding="utf-8"))
    assert t["counts"]["YES"] == 2
    assert t["counts"]["NO"] == 1


@pytest.mark.skipif(importlib.util.find_spec("coherenceledger") is None, reason="coherenceledger not installed")
def test_tally_can_sign_and_anchor(tmp_path: Path):
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

    outdir = tmp_path / "vote2"
    m = build_vote_manifest(
        title="M2",
        purpose_id="p2",
        purpose_statement="s2",
        scope="org.governance",
        anonymity_mode="open",
    electorate_rules={"max_ballots_per_did": 2},
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False, repo_root=repo_root, keystore_path=keystore, ledger_path=ledger)
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    # signed ballots (open)
    b1 = build_ballot(manifest_id=manifest["manifest_id"], ballot_type="single_choice", selection={"choice":"YES"})
    b2 = build_ballot(manifest_id=manifest["manifest_id"], ballot_type="single_choice", selection={"choice":"YES"})
    write_ballot(outdir=outdir, ballot=b1, manifest=manifest, sign=True, anchor=False, repo_root=repo_root, keystore_path=keystore, ledger_path=ledger)
    write_ballot(outdir=outdir, ballot=b2, manifest=manifest, sign=True, anchor=False, repo_root=repo_root, keystore_path=keystore, ledger_path=ledger)

    tp = write_tally(
        outdir=outdir,
        manifest_path=mp,
        verify_ballot_signatures=True,
        strict=True,
        sign=True,
        anchor=True,
        repo_root=repo_root,
        keystore_path=keystore,
        ledger_path=ledger,
        ledger_purpose="ucc.vote_tally.anchor",
    )

    t = json.loads(tp.read_text(encoding="utf-8"))
    assert "signature" in t
    sig = t["signature"]

    # verify tally signature
    body = dict(t)
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

def test_tally_coherence_weighting_registry(tmp_path: Path):
    # Requires coherenceledger (installed in your venv & in CI workflows that install it)
    from coherenceledger.keystore import KeyStore

    # Make a small repo root with keystore so we can sign a ballot and know the DID
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    (repo_root / ".secrets").mkdir()
    keystore = repo_root / ".secrets" / "ks.json"
    KeyStore(path=keystore).generate()

    # Create an OPEN manifest with coherence weighting + cap
    outdir = tmp_path / "vote"
    m = build_vote_manifest(
        title="M",
        purpose_id="p",
        purpose_statement="s",
        scope="org.governance",
        anonymity_mode="open",
        tally_mode="plaintext",
        weighting_mode="coherence",
        weighting_params={"scale": 1.0, "cap": 1.0},
    )
    mp = write_vote_manifest(outdir=outdir, manifest=m, sign=False, anchor=False)
    manifest = json.loads(mp.read_text(encoding="utf-8"))

    # Sign one ballot (gives us a DID)
    b = build_ballot(
        manifest_id=manifest["manifest_id"],
        ballot_type="single_choice",
        selection={"choice": "YES"},
    )
    write_ballot(outdir=outdir, ballot=b, manifest=manifest, sign=True, anchor=False, repo_root=repo_root, keystore_path=keystore, ledger_path=repo_root / "ledger.jsonl")

    # Build registry giving that DID score 0.5 -> expected weighted YES = 0.5
    did_obj, _ = KeyStore(path=keystore).load_keypair()
    reg = {did_obj.did: 0.5}

    from ucc.vote_tally import tally_ballots
    ballots = list((outdir / "ballots").glob("*.json"))
    t = tally_ballots(
        manifest=manifest,
        ballot_paths=ballots,
        verify_ballot_signatures=True,
        strict=True,
        coherence_registry=reg,
    )

    assert t["weighted_counts"]["YES"] == pytest.approx(0.5)



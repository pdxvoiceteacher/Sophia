import json
from pathlib import Path
import importlib.util

import pytest

from ucc.vote_ballot_secret import build_secret_commit_and_reveal, write_secret_commit, write_secret_reveal
from ucc.vote_tally_secret import tally_secret


def test_secret_commit_reveal_tally(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-123"

    c1, r1 = build_secret_commit_and_reveal(manifest_id=mid, choice="YES", nullifier_hex="aa"*16, salt_hex="bb"*16)
    write_secret_commit(outdir=outdir, commit_doc=c1)
    write_secret_reveal(outdir=outdir, reveal_doc=r1)

    t = tally_secret(outdir=outdir, manifest_id=mid, strict=True)
    assert t["counts"]["YES"] == 1
    assert t["ballots"]["valid"] == 1
    assert t["passed_nullifier_check"] is True


def test_secret_nullifier_replay_rejected(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-123"

    c1, r1 = build_secret_commit_and_reveal(manifest_id=mid, choice="YES", nullifier_hex="aa"*16, salt_hex="bb"*16)
    write_secret_commit(outdir=outdir, commit_doc=c1)

    # second commit with same nullifier should fail
    c2, r2 = build_secret_commit_and_reveal(manifest_id=mid, choice="NO", nullifier_hex="aa"*16, salt_hex="cc"*16)
    with pytest.raises(ValueError):
        write_secret_commit(outdir=outdir, commit_doc=c2)

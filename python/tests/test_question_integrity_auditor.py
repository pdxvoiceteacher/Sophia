import json
import os
from pathlib import Path

_TEST_BRIDGE_ROOT = Path(__file__).resolve().parents[2] / ".tmp" / "triadic_bridge"
os.environ.setdefault("TRIADIC_BRIDGE_ROOT", str(_TEST_BRIDGE_ROOT))

from sophia.api.server import BRIDGE_ROOT, govern_question_integrity
from sophia.governance.question_integrity_auditor import audit_question_integrity


def test_audit_question_integrity_pass() -> None:
    packet = {"user_question_text": "What is corridor confidence?"}

    decision = audit_question_integrity(
        user_question_packet=packet,
        latest_nav_result=packet,
        atlas_query={"question_text": "What is corridor confidence?"},
        answer_relevance_packet={"question_text": "What is corridor confidence?"},
    )

    assert decision["audit_status"] == "pass"
    assert decision["recommendation"] == "keep"


def test_audit_question_integrity_warns_on_mismatch() -> None:
    decision = audit_question_integrity(
        user_question_packet={"user_question_text": "Q1"},
        latest_nav_result={"user_question_text": "Q2"},
        atlas_query={"question_text": "Q1"},
        answer_relevance_packet={"question_text": "Q3"},
    )

    assert decision["audit_status"] == "warn"
    assert len(decision["problems"]) == 2


def test_govern_question_integrity_reads_and_writes_files(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)

    packet_dir = BRIDGE_ROOT
    packet_dir.mkdir(parents=True, exist_ok=True)

    (packet_dir / "user_question_packet.json").write_text(
        json.dumps({"user_question_text": "What is governance routing?"}),
        encoding="utf-8",
    )
    (packet_dir / "latest_nav_result.json").write_text(
        json.dumps({"user_question_text": "What is governance routing?"}),
        encoding="utf-8",
    )
    (packet_dir / "atlas_query.json").write_text(
        json.dumps({"question_text": "What is governance routing?"}),
        encoding="utf-8",
    )
    (packet_dir / "answer_relevance_packet.json").write_text(
        json.dumps({"question_text": "What is governance routing?"}),
        encoding="utf-8",
    )

    decision = govern_question_integrity()

    assert decision["audit_status"] == "pass"
    out = packet_dir / "question_integrity_audit.json"
    saved = json.loads(out.read_text(encoding="utf-8"))
    assert saved == decision

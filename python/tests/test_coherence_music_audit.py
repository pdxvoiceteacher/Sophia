from pathlib import Path

from coherence_music.raga import bhairav_profile
from coherence_music.engine import EngineConfig, CoherenceMusicEngine
from coherence_music.midi import write_midi
from coherence_music.analyze import write_trace_and_audit

def test_music_audit_outputs(tmp_path: Path):
    metrics = {
        "E": [0.2, 0.8, 0.2, 0.2],
        "T": [0.2, 0.6, 0.2, 0.2],
        "DELTA_S": [0.1, 0.3, 0.2, 0.1],
        "E_SYM": [0.40, 0.46, 0.45, 0.44],
        "LAMBDA": [0.2, 0.8, 0.3, 0.2],
    }
    profile = bhairav_profile(tonic_midi=60)
    cfg = EngineConfig(seed=123, bpm=90, dur_beats=1.0)
    eng = CoherenceMusicEngine(profile, cfg)

    seq = eng.generate(metrics, name="test_bhairav")
    midi_path = write_midi(seq.flatten_notes(), tmp_path / "t.mid", bpm=seq.bpm)

    out = write_trace_and_audit(tmp_path, metrics, seq, midi_path=midi_path, evidence_links=["https://example.com"])

    assert out["trace_json"].exists()
    assert out["trace_csv"].exists()
    assert out["audit_json"].exists()
    assert out["audit_md"].exists()
    assert out["ucc_artifact_json"].exists()

    # sanity: audit JSON has expected keys
    import json
    a = json.loads(out["audit_json"].read_text(encoding="utf-8"))
    assert "counts_by_category" in a
    assert "metric_lifts" in a
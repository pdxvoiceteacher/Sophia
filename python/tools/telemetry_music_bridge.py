from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import List, Tuple

def freq_to_midi(freq: float) -> int:
    return int(round(69 + 12.0 * math.log(freq / 440.0, 2)))

def parse_chords(csv_path: Path) -> List[Tuple[str, List[float]]]:
    chords: List[Tuple[str, List[float]]] = []
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        r = csv.reader(f)
        _ = next(r, None)
        for row in r:
            if not row or len(row) < 6:
                continue
            chord = row[1].strip()
            if chord == "__SUMMARY__":
                continue

            rest = row[5:]
            split = None
            for i, tok in enumerate(rest):
                t = tok.strip()
                if "." in t or "e" in t.lower():
                    split = i
                    break
            if split is None:
                continue

            freqs: List[float] = []
            for tok in rest[split:]:
                try:
                    freqs.append(float(tok))
                except Exception:
                    pass
            if freqs:
                chords.append((chord, freqs))
    return chords

def write_midi(chords: List[Tuple[str, List[float]]], out_path: Path, tempo_bpm: int = 120) -> None:
    import mido
    mid = mido.MidiFile(ticks_per_beat=480)
    tr = mido.MidiTrack()
    mid.tracks.append(tr)

    tr.append(mido.MetaMessage("set_tempo", tempo=mido.bpm2tempo(tempo_bpm), time=0))

    dur = 480   # 1 beat chord
    gap = 120   # small rest

    for _, freqs in chords:
        notes = [max(0, min(127, freq_to_midi(f))) for f in freqs]
        for n in notes:
            tr.append(mido.Message("note_on", note=n, velocity=64, time=0))
        first = True
        for n in notes:
            tr.append(mido.Message("note_off", note=n, velocity=64, time=(dur if first else 0)))
            first = False
        tr.append(mido.Message("note_on", note=0, velocity=0, time=gap))

    mid.save(str(out_path))

def latest_run_dir(runs_root: Path) -> Path:
    runs = [p for p in runs_root.iterdir() if p.is_dir()]
    if not runs:
        raise SystemExit(f"no runs in {runs_root}")
    runs.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return runs[0]

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", default="", help="paper/out/runs/<run_id>")
    ap.add_argument("--tempo", type=int, default=120)
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    runs_root = repo_root / "paper" / "out" / "runs"
    run_dir = Path(args.run_dir) if args.run_dir else latest_run_dir(runs_root)
    artifacts = run_dir / "artifacts"

    maj_csv = artifacts / "music_chords_major.csv"
    min_csv = artifacts / "music_chords_minor.csv"
    if not maj_csv.exists() or not min_csv.exists():
        raise SystemExit("missing music chord CSVs in run artifacts")

    maj = parse_chords(maj_csv)
    minn = parse_chords(min_csv)

    out_maj = artifacts / "music_major.mid"
    out_min = artifacts / "music_minor.mid"

    write_midi(maj, out_maj, tempo_bpm=args.tempo)
    write_midi(minn, out_min, tempo_bpm=args.tempo)

    print(f"Wrote MIDI: {out_maj}")
    print(f"Wrote MIDI: {out_min}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
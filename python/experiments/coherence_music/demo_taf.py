from pathlib import Path

from coherence_music.taf import taf_theme_notes
from coherence_music.core import Sequence
from coherence_music.midi import write_midi

out = Path("python/experiments/coherence_music/out")
out.mkdir(parents=True, exist_ok=True)

seq = Sequence(phrases=taf_theme_notes(), bpm=96, name="TAF_theme")
midi_path = write_midi(seq.flatten_notes(), out / "taf_theme.mid", bpm=seq.bpm)

print("Wrote:", midi_path)

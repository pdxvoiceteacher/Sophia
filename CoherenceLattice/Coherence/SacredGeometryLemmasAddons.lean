import Mathlib
import CoherenceLattice.Coherence.SacredGeometryAddons

set_option linter.style.commandStart false
set_option linter.style.emptyLine false

namespace Coherence
namespace SacredGeometryLemmas

noncomputable section

open Coherence.SacredGeometry

/-- Centered-hex recurrence: N(n+1) = N(n) + 6*(n+1). -/
lemma centeredHex_succ (n : Nat) :
    centeredHex (n + 1) = centeredHex n + 6 * (n + 1) := by
  -- centeredHex n = 3*n*(n+1) + 1
  -- centeredHex (n+1) = 3*(n+1)*(n+2) + 1 = centeredHex n + 6*(n+1)
  simp [centeredHex]
  ring

/-- Basic ordering: fourth < fifth (4/3 < 3/2). -/
lemma ratioFourth_lt_ratioFifth : ratioFourth < ratioFifth := by
  norm_num [ratioFourth, ratioFifth]

/-- Basic ordering: fifth < octave (3/2 < 2). -/
lemma ratioFifth_lt_ratioOctave : ratioFifth < ratioOctave := by
  norm_num [ratioFifth, ratioOctave]

/-- Basic ordering: fourth < octave (4/3 < 2). -/
lemma ratioFourth_lt_ratioOctave : ratioFourth < ratioOctave := by
  norm_num [ratioFourth, ratioOctave]

end
end SacredGeometryLemmas
end Coherence
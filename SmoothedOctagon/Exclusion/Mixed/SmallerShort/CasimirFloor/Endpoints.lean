module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ShapeCurve

/-!
# Smaller-short window, Casimir floor: the three scalar endpoints

Each endpoint is `Z - log(y)/7` with rational `Z` and `0 < y < 1`; `log y ≤ 2(z + z³/3 + z⁵/5)`,
`z = (y - 1)/(y + 1)` (`cas_log_le_quintic`), and direct rational substitution gives margins
greater than `1/12500`, `1/5000` and `3/10⁶`.

## Main API

`cas_closed_ends`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The three endpoints**: `Φ(13/6, 1/19, 3)`, `Ψ(13/6, 0, 13/5)` and
`Ψ(13/6, 1/19, 13/5)` exceed `1829/10000`. -/
theorem cas_closed_ends :
    1829 / 10000 < casPhiC (13 / 6) (1 / 19) 3 ∧ 1829 / 10000 < casPsiC (13 / 6) 0 (13 / 5) ∧
      1829 / 10000 < casPsiC (13 / 6) (1 / 19) (13 / 5) := by
  have h1 := cas_log_le_quintic (y := 103488 / 134749) (by norm_num) (by norm_num)
  have h2 := cas_log_le_quintic (y := 12 / 19) (by norm_num) (by norm_num)
  have h3 := cas_log_le_quintic (y := 2524608 / 3353029) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · unfold casPhiC casClosedPhiC
    norm_num [casClosedG, casClosedWc, casClosedRest, casClosedEL, casClosedP, ssDg, ssUbar]
    linarith
  · unfold casPsiC casClosedPsiC
    norm_num [casClosedG, casClosedWc, casClosedRest, casClosedEL, casClosedP, ssDg, ssUbar]
    linarith
  · unfold casPsiC casClosedPsiC
    norm_num [casClosedG, casClosedWc, casClosedRest, casClosedEL, casClosedP, ssDg, ssUbar]
    linarith

end SmoothedOctagon

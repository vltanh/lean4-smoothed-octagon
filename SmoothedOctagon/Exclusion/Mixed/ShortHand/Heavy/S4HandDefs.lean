module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Closed
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6HandJet

/-!
# Gate S4, hand proof: the two central lower bounds on the actual shape curve

With `S4Closed`'s closed forms `Φ = Γ - r₀/7`, `Ψ = Γ - r₁/7` (in the variables
`x, a = α, b = β, u`), the leaf
`hs4_floor_box` concerns their values on the actual shape curve

`a = 1 + e d`, `b = x(1 + d)`, `u = ū(x, b)`, `2 ≤ x ≤ 13/6`, `0 ≤ d ≤ 1/19`, `13/5 ≤ e ≤ 3`,

written here `hl46PhiC x d e` and `hl46PsiC x d e`. The six comparisons W1-W6 are stated on these
functions in `S4HandW*`.

## Main API

* `hl46PhiC`, `hl46PsiC`.
* `hl46_log_le_quintic`: `log y ≤ 2(z + z³/3 + z⁵/5)`, `z = (y - 1)/(y + 1)`, for `0 < y ≤ 1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `Φ` on the actual shape curve `a = 1 + ed`, `b = x(1 + d)`, `u = ū(x, b)`. -/
noncomputable def hl46PhiC (x d e : ℝ) : ℝ :=
  hh46S4PhiC x (x * (1 + d)) (1 + e * d) (hsUbar x (x * (1 + d)))

/-- `Ψ` on the actual shape curve `a = 1 + ed`, `b = x(1 + d)`, `u = ū(x, b)`. -/
noncomputable def hl46PsiC (x d e : ℝ) : ℝ :=
  hh46S4PsiC x (x * (1 + d)) (1 + e * d) (hsUbar x (x * (1 + d)))

/-- `log y ≤ 2(z + z³/3 + z⁵/5)`, `z = (y - 1)/(y + 1)`, for `0 < y ≤ 1` (`hs_log_ge_quintic` at
`1/y`). -/
theorem hl46_log_le_quintic {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    log y ≤ 2 * ((y - 1) / (y + 1) + ((y - 1) / (y + 1)) ^ 3 / 3 + ((y - 1) / (y + 1)) ^ 5 / 5) := by
  have h := hs_log_ge_quintic (z := y⁻¹) ((one_le_inv₀ hy).2 hy1)
  have e : (y⁻¹ - 1) / (y⁻¹ + 1) = -((y - 1) / (y + 1)) := by
    field_simp; ring
  rw [e, Real.log_inv] at h
  have e3 : (-((y - 1) / (y + 1))) ^ 3 = -((y - 1) / (y + 1)) ^ 3 := by ring
  have e5 : (-((y - 1) / (y + 1))) ^ 5 = -((y - 1) / (y + 1)) ^ 5 := by ring
  rw [e3, e5] at h
  linarith

end SmoothedOctagon

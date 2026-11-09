module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ClosedForms
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Jets

/-!
# Smaller-short window, Casimir floor: the two central lower bounds on the actual shape curve

With the closed forms `Φ = Γ - r₀/7`, `Ψ = Γ - r₁/7` of `CasimirFloor/ClosedForms` (in the
variables `x, a = α, b = β, u`), the floor
`cas_floor_box` concerns their values on the actual shape curve

`a = 1 + e d`, `b = x(1 + d)`, `u = ū(x, b)`, `2 ≤ x ≤ 13/6`, `0 ≤ d ≤ 1/19`, `13/5 ≤ e ≤ 3`,

written here `casPhiC x d e` and `casPsiC x d e`. The six comparisons W1-W6 are stated on these
functions in the step modules of `SmallerShort/CasimirFloor/`.

## Main API

* `casPhiC`, `casPsiC`.
* `cas_log_le_quintic`: `log y ≤ 2(z + z³/3 + z⁵/5)`, `z = (y - 1)/(y + 1)`, for `0 < y ≤ 1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `Φ` on the actual shape curve `a = 1 + ed`, `b = x(1 + d)`, `u = ū(x, b)`. -/
noncomputable def casPhiC (x d e : ℝ) : ℝ :=
  casClosedPhiC x (x * (1 + d)) (1 + e * d) (ssUbar x (x * (1 + d)))

/-- `Ψ` on the actual shape curve `a = 1 + ed`, `b = x(1 + d)`, `u = ū(x, b)`. -/
noncomputable def casPsiC (x d e : ℝ) : ℝ :=
  casClosedPsiC x (x * (1 + d)) (1 + e * d) (ssUbar x (x * (1 + d)))

/-- `log y ≤ 2(z + z³/3 + z⁵/5)`, `z = (y - 1)/(y + 1)`, for `0 < y ≤ 1` (`ss_log_ge_quintic` at
`1/y`). -/
theorem cas_log_le_quintic {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    log y ≤ 2 * ((y - 1) / (y + 1) + ((y - 1) / (y + 1)) ^ 3 / 3 + ((y - 1) / (y + 1)) ^ 5 / 5) := by
  have h := ss_log_ge_quintic (z := y⁻¹) ((one_le_inv₀ hy).2 hy1)
  have e : (y⁻¹ - 1) / (y⁻¹ + 1) = -((y - 1) / (y + 1)) := by
    field_simp; ring
  rw [e, Real.log_inv] at h
  have e3 : (-((y - 1) / (y + 1))) ^ 3 = -((y - 1) / (y + 1)) ^ 3 := by ring
  have e5 : (-((y - 1) / (y + 1))) ^ 5 = -((y - 1) / (y + 1)) ^ 5 := by ring
  rw [e3, e5] at h
  linarith

end SmoothedOctagon

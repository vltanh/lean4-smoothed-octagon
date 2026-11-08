module

public import SmoothedOctagon.Exclusion.Forward.Scalar
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Case F: numerical constants and the competitive Casimir cap

* `ff_octagonCost_lt`: `A_oct < 3.1268` (`A_oct ≈ 3.126049`).
* `ff_octagonCost_lt'`: `A_oct < 2501/800`; `ff_octagonCost_gt`: `A_oct > 3.126`.
* `ff_gam2_cap`: from the spectral bound `C ≥ (π/3)(κ + 3/2)` and `C ≤ A_oct`,
  `γ² = κ²/12 < 23/125` (HAND_PROOF_REFINEMENTS §1, with the weaker constant `23/125`).
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `A_oct = √12 (8 - √32 - log 2)/(√8 - 1) < 3.1268`. -/
theorem ff_octagonCost_lt : octagonCost < 3.1268 := by
  have h12 : √12 < 3.4641017 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h32 : 5.6568542 < √32 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h8 : 2.8284271 < √8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  have h12p : 0 ≤ √12 := Real.sqrt_nonneg _
  have hD : 0 < √8 - 1 := by linarith
  have hN : 0 ≤ 8 - √32 - Real.log 2 := by
    have : √32 < 5.6569 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [octagonCost, octagonDensity, mul_div_assoc', div_lt_iff₀ hD]
  have : √12 * (8 - √32 - Real.log 2) ≤ 3.4641017 * (8 - √32 - Real.log 2) :=
    mul_le_mul_of_nonneg_right h12.le hN
  nlinarith

/-- `A_oct < 2501/800 = 3.12625` (GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD (3)). -/
theorem ff_octagonCost_lt' : octagonCost < 2501 / 800 := by
  have h12 : √12 < 3.4641017 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h32 : 5.6568542 < √32 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h8 : 2.8284271 < √8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  have h12p : 0 ≤ √12 := Real.sqrt_nonneg _
  have hD : 0 < √8 - 1 := by linarith
  have hN : 0 ≤ 8 - √32 - Real.log 2 := by
    have : √32 < 5.6569 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [octagonCost, octagonDensity, mul_div_assoc', div_lt_iff₀ hD]
  have : √12 * (8 - √32 - Real.log 2) ≤ 3.4641017 * (8 - √32 - Real.log 2) :=
    mul_le_mul_of_nonneg_right h12.le hN
  nlinarith

/-- `A_oct > 3.126`. -/
theorem ff_octagonCost_gt : 3.126 < octagonCost := by
  have h12 : 3.4641016 < √12 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h32 : √32 < 5.6568543 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h8 : √8 < 2.8284272 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h8' : 2.8284271 < √8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_lt_d9
  have hD : 0 < √8 - 1 := by linarith
  have hN : 1.6499 ≤ 8 - √32 - Real.log 2 := by linarith
  rw [octagonCost, octagonDensity, mul_div_assoc', lt_div_iff₀ hD]
  have : 3.4641016 * (8 - √32 - Real.log 2) ≤ √12 * (8 - √32 - Real.log 2) :=
    mul_le_mul_of_nonneg_right h12.le (by linarith)
  nlinarith

/-- **The competitive Casimir cap** (HAND_PROOF_REFINEMENTS §1): if `x = κ² > 0` and the cost `c`
satisfies `(π/3)(κ + 3/2) ≤ c ≤ A_oct`, then `γ² = x/12 < 23/125`. -/
theorem ff_gam2_cap {x c : ℝ} (hx : 0 < x) (h : π / 3 * (√x + 3 / 2) ≤ c)
    (hc : c ≤ octagonCost) : x / 12 < 23 / 125 := by
  have hA := ff_octagonCost_lt
  have hpi := Real.pi_gt_d6
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have hk : √x < 1.4859 := by
    by_contra hcon
    push Not at hcon
    have : π / 3 * (1.4859 + 3 / 2) ≤ π / 3 * (√x + 3 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    nlinarith
  have hsq : x = √x ^ 2 := (Real.sq_sqrt hx.le).symm
  nlinarith

end SmoothedOctagon

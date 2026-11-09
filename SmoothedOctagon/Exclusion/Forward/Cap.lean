module

public import SmoothedOctagon.Exclusion.Forward.Log
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Case F: numerical constants and the competitive Casimir cap

* `ff_octagonCost_lt_sqrt`: `A_oct < 29√3/16`, from the midpoint logarithm bound.
* `ff_octagonCost_lt`: `A_oct < 3.1268` (`A_oct ≈ 3.126049`).
* `ff_octagonCost_lt'`: `A_oct < 2501/800`; `ff_octagonCost_gt`: `A_oct > 3.126`.
* `ff_gam2_cap`: from the spectral bound `C ≥ (π/3)(κ + 3/2)` and `C ≤ A_oct`,
  `γ² = κ²/12 < 23/125`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The exact octagon comparison used by the exterior budget. -/
theorem ff_octagonCost_lt_sqrt : octagonCost < 29 * √3 / 16 := by
  have h2 : (1 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3 : 0 < √3 := by positivity
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hmid := ff_log_gt_midpoint h2
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hmid
  have emid : 4 * (√2 - 1) / (√2 + 1) = 12 - 8 * √2 := by
    field_simp
    nlinarith only [hsq2]
  have hlog : 12 - 8 * √2 < Real.log 2 := by
    rw [← emid, show 4 * (√2 - 1) / (√2 + 1) = 2 * (2 * (√2 - 1) / (√2 + 1)) by ring]
    linarith only [hmid]
  have hs12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs32 : √32 = 4 * √2 := by
    rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  have hs8 : √8 = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hD : 0 < 2 * √2 - 1 := by linarith
  have h70 : 70 * √2 < 99 := by nlinarith only [hsq2, Real.sqrt_nonneg 2]
  rw [octagonCost, octagonDensity, hs12, hs32, hs8, mul_div_assoc', div_lt_iff₀ hD]
  have hN : 8 - 4 * √2 - Real.log 2 < 4 * (√2 - 1) := by linarith only [hlog]
  have hfirst := mul_lt_mul_of_pos_left hN (by positivity : 0 < 2 * √3)
  have hlast : 8 * √3 * (√2 - 1) < 29 * √3 / 16 * (2 * √2 - 1) := by
    have := mul_lt_mul_of_pos_left h70 h3
    nlinarith only [this]
  nlinarith only [hfirst, hlast]

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

/-- `A_oct < 2501/800 = 3.12625`. -/
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

/-- **The competitive Casimir cap**: if `x = κ² > 0` and the cost `c` satisfies
`(π/3)(κ + 3/2) ≤ c ≤ A_oct`, then `γ² = x/12 < 23/125`, since `A_oct < 3.1268` and `π > 3.141592`
force `κ < 1.4859`. -/
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

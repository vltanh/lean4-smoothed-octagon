module

public import SmoothedOctagon.Exclusion.Forward.Log
public import SmoothedOctagon.Period.OctagonCost

/-!
# Cost comparisons and the competitive Casimir cap

The exterior budget uses the exact midpoint-logarithm comparison with `29√3/16`.
The positive-moment cost ratio supplies the competitive Casimir cap.
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

/-- The spectral moment cap implies `γ² < 23/125` on the scalar forward domain. -/
theorem ff_gam2_cap {x c : ℝ} (hx : 0 < x) (h : π/3*(√x+3/2) ≤ c)
    (hc : c ≤ octagonCost) : x/12 < 23/125 := by
  have hcap := octagon_spectral_cap hx h hc
  linarith only [hcap]

end SmoothedOctagon

module

public import SmoothedOctagon.Foundations.SwitchingMargin
public import SmoothedPolygons.Ch7.HMax

/-!
# Quantitative switching gaps for normalized strong lifts

The scalar margin for `hmaxF` gives a uniform cubic lower bound for the actual switching
function `χ₃₂` on the explicit constant-control segment. Time reversal gives the corresponding
bound for `χ₃₁`. Uniqueness of the strong lift extends both bounds to every `IsStrongLift` with
`λ_cost = -1` and `1 / √3 < y₀ < 1`.

These hypotheses describe the strong lifts constructed in `SmoothedPolygons`. They do not describe
all Pontryagin extremals, and the estimates do not assert global optimality of the octagon.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set SmoothedPolygons

/-- The normalized explicit strong lift has a cubic gap from its initial switch:
`χ₃₂(t) ≥ (√3 / 2) t³` on the full constant-control segment. -/
theorem strong_chi32_cubic_lower_bound {y0 t : ℝ}
    (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (ht : t ∈ Icc 0 (switchTime y0)) :
    √3 / 2 * t ^ 3 ≤ switchingFn 2 1 (strongΛR y0 t) (segX y0 t) := by
  let y : ℝ := 1 + 3 * y0 ^ 2
  let W : ℝ := exp (√3 * y0 * t)
  have hy2 : 2 < y := (hmax_y_mem hy0 hy1).1
  have hW1 : 1 ≤ W := (hmax_W_mem hy0 ht).1
  have hW4 : y * W ≤ 4 := (hmax_W_mem hy0 ht).2
  have hypos : 0 < y := by linarith
  have hy0pos : 0 < y0 := lt_trans (by positivity) hy0
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW1
  have ht0 : 0 ≤ t := ht.1
  have hW2 : W < 2 := by
    have h := mul_lt_mul_of_pos_right hy2 hWpos
    linarith
  have h2W : 0 < 2 - W := by linarith
  have hyr : y ≤ y * W := by
    calc y = y * 1 := (mul_one y).symm
      _ ≤ y * W := mul_le_mul_of_nonneg_left hW1 hypos.le
  have hmargin := hmaxF_uniform_cubic_lower_bound hy2.le hyr hW4
  have hWproduct : W * (2 - W) ≤ 1 := by
    nlinarith only [sq_nonneg (W - 1)]
  have hycube : 2 * y ^ 2 ≤ y ^ 3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hy2.le) (sq_nonneg y)]
  have htime : √3 * y0 * t ≤ W - 1 := by
    have h := add_one_le_exp (√3 * y0 * t)
    change √3 * y0 * t + 1 ≤ W at h
    linarith
  have hcube : (3 * √3) * y0 ^ 3 * t ^ 3 ≤ (W - 1) ^ 3 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ √3 * y0 * t) htime 3
    have h3cube : (√3 : ℝ) ^ 3 = 3 * √3 := by
      rw [pow_succ, Real.sq_sqrt (by norm_num)]
    simpa only [mul_pow, h3cube] using hp
  let D : ℝ := 3 * y ^ 2 * W * y0 ^ 3 * (2 - W)
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  rw [chi32_eq y0 hy0 hy1 t ht]
  change √3 / 2 * t ^ 3 ≤ 2 * hmaxF y (y * W) / D
  rw [le_div_iff₀ hD]
  have hscaled : 4 * ((√3 / 2 * t ^ 3) * D) ≤ 8 * hmaxF y (y * W) := by
    calc
      4 * ((√3 / 2 * t ^ 3) * D) =
          (6 * √3 * y ^ 2 * y0 ^ 3 * t ^ 3) * (W * (2 - W)) := by
            dsimp only [D]
            ring
      _ ≤ (6 * √3 * y ^ 2 * y0 ^ 3 * t ^ 3) * 1 :=
        mul_le_mul_of_nonneg_left hWproduct (by positivity)
      _ = (2 * y ^ 2) * ((3 * √3) * y0 ^ 3 * t ^ 3) := by ring
      _ ≤ y ^ 3 * ((3 * √3) * y0 ^ 3 * t ^ 3) :=
        mul_le_mul_of_nonneg_right hycube (by positivity)
      _ ≤ y ^ 3 * (W - 1) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = (y * W - y) ^ 3 := by ring
      _ ≤ 8 * hmaxF y (y * W) := by
        have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hmargin
        simpa only [mul_comm] using h
  linarith only [hscaled]

/-- Time reversal gives the cubic gap from the terminal switch for the explicit lift. -/
theorem strong_chi31_cubic_lower_bound {y0 t : ℝ}
    (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (ht : t ∈ Icc 0 (switchTime y0)) :
    √3 / 2 * (switchTime y0 - t) ^ 3 ≤
      switchingFn 2 0 (strongΛR y0 t) (segX y0 t) := by
  have ht' : switchTime y0 - t ∈ Icc 0 (switchTime y0) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsym := chi31_eq_chi32 y0 hy0 hy1 (switchTime y0 - t) ht'
  rw [sub_sub_cancel] at hsym
  rw [hsym]
  exact strong_chi32_cubic_lower_bound hy0 hy1 ht'

/-- Both margins hold for any strong lift with the explicit normalization `λ_cost = -1`.
This does not quantify over arbitrary Pontryagin extremals or arbitrary smoothed polygons. -/
theorem normalizedStrongLift_switching_cubic_lower_bounds {y0 t : ℝ}
    (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (h : IsStrongLift y0 Λ₁ ΛR (-1)) (ht : t ∈ Icc 0 (switchTime y0)) :
    √3 / 2 * t ^ 3 ≤ switchingFn 2 1 (ΛR t) (segX y0 t) ∧
      √3 / 2 * (switchTime y0 - t) ^ 3 ≤ switchingFn 2 0 (ΛR t) (segX y0 t) := by
  have hΛ : ΛR t = strongΛR y0 t := by
    simpa using (strongLift_unique y0 hy0 hy1 Λ₁ ΛR (-1) h t ht).2
  rw [hΛ]
  exact ⟨strong_chi32_cubic_lower_bound hy0 hy1 ht,
    strong_chi31_cubic_lower_bound hy0 hy1 ht⟩

end SmoothedOctagon

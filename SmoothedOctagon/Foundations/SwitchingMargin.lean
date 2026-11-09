module

public import SmoothedPolygons.Ch7.StrongTransversality
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# A quantitative margin for the switching expression

The reference project already proves qualitative nonnegativity and positivity of
`SmoothedPolygons.hmaxF` in `Ch7.HMaxInequality`. This module gives an explicit rational
lower bound for the same expression, using two logarithm inequalities,
`log u ≥ 2(u - 1)/(u + 1)` for `u ≥ 1` and `log v ≤ v - 1` for `v > 0`, and a rational identity.
It does not import or use the reference project's derivative proof.

For `2 ≤ y ≤ r ≤ 4`, the principal estimate is

`r * (r - y)^3 / (4 * (r + y)) ≤ hmaxF y r`.

In particular, `(r - y)^3 / 8 ≤ hmaxF y r`. The bound degenerates on the switching
diagonal `r = y`; it is not a positive lower bound on switching intervals or their lengths.
The expression `hmaxF` is the one whose sign Hales–Vajjha establish in the proof of their
Lemma 7.5.3.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

/-- The standard lower logarithm bound, in the ratio coordinates used below. -/
private lemma log_ratio_lower_bound {y r : ℝ} (hy : 0 < y) (hyr : y ≤ r) :
    2 * (r - y) / (r + y) ≤ Real.log (r / y) := by
  have hr : 0 < r := hy.trans_le hyr
  have hratio : 1 ≤ r / y := by
    rw [le_div_iff₀ hy]
    simpa using hyr
  have h := Real.le_log_one_add_of_nonneg (sub_nonneg.mpr hratio)
  have harg : 1 + (r / y - 1) = r / y := by ring
  have hden : r / y - 1 + 2 = r / y + 1 := by ring
  rw [harg, hden] at h
  have hsum : 0 < r + y := add_pos hr hy
  have hratioPos : 0 < r / y + 1 := by positivity
  have hfrac : 2 * (r / y - 1) / (r / y + 1) =
      2 * (r - y) / (r + y) := by
    field_simp [hy.ne', hsum.ne', hratioPos.ne']
  rwa [hfrac] at h

/-- Exact residual identity behind the rational lower bound. Both residuals on the
right are nonnegative when `2 ≤ y ≤ r`; the correction in the first line is also
nonnegative when `r ≤ 4`. The expression on the left is the upstream `hmaxF`. -/
theorem hmaxF_margin_identity {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    hmaxF y r -
        ((r - y) ^ 2 * (4 - r) * (r ^ 2 + 3 * r * y + 4 * y ^ 2) /
            (4 * r * (r + y)) +
          r * (r - y) ^ 3 / (4 * (r + y))) =
      y * (y ^ 2 + r * (y - 2)) *
          (Real.log (r / y) - 2 * (r - y) / (r + y)) +
        y ^ 2 * (r - y) * ((4 - r) / r - Real.log (4 / r)) := by
  have hsum : 0 < r + y := add_pos hr hy
  unfold hmaxF
  rw [Real.log_div hr.ne' hy.ne',
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hr.ne',
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hy.ne']
  field_simp [hy.ne', hr.ne', hsum.ne']
  ring

/-- The full rational lower bound. This comparison itself only needs `2 ≤ y ≤ r`;
the restriction `r ≤ 4` is needed when discarding its boundary correction. -/
theorem hmaxF_rational_lower_bound {y r : ℝ} (hy : 2 ≤ y) (hyr : y ≤ r) :
    (r - y) ^ 2 * (4 - r) * (r ^ 2 + 3 * r * y + 4 * y ^ 2) /
          (4 * r * (r + y)) +
        r * (r - y) ^ 3 / (4 * (r + y)) ≤ hmaxF y r := by
  have hy0 : 0 < y := by linarith
  have hr0 : 0 < r := hy0.trans_le hyr
  have hlogLower := log_ratio_lower_bound hy0 hyr
  have hlogUpper : Real.log (4 / r) ≤ (4 - r) / r := by
    calc
      Real.log (4 / r) ≤ 4 / r - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (by norm_num) hr0)
      _ = (4 - r) / r := by field_simp [hr0.ne']
  have hA : 0 ≤ y * (y ^ 2 + r * (y - 2)) :=
    mul_nonneg hy0.le
      (add_nonneg (sq_nonneg y) (mul_nonneg hr0.le (sub_nonneg.mpr hy)))
  have hB : 0 ≤ y ^ 2 * (r - y) :=
    mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hyr)
  apply sub_nonneg.mp
  rw [hmaxF_margin_identity hy0 hr0]
  exact add_nonneg (mul_nonneg hA (sub_nonneg.mpr hlogLower))
    (mul_nonneg hB (sub_nonneg.mpr hlogUpper))

/-- A cubic margin for the upstream switching expression on the full triangle
`2 ≤ y ≤ r ≤ 4`. No sign of a denominator is implicit in the hypotheses. -/
theorem hmaxF_cubic_lower_bound {y r : ℝ}
    (hy : 2 ≤ y) (hyr : y ≤ r) (hr : r ≤ 4) :
    r * (r - y) ^ 3 / (4 * (r + y)) ≤ hmaxF y r := by
  have hy0 : 0 < y := by linarith
  have hr0 : 0 < r := hy0.trans_le hyr
  have hcorrection : 0 ≤
      (r - y) ^ 2 * (4 - r) * (r ^ 2 + 3 * r * y + 4 * y ^ 2) /
        (4 * r * (r + y)) := by
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (sq_nonneg (r - y)) (sub_nonneg.mpr hr)) (by positivity)
    · positivity
  linarith [hmaxF_rational_lower_bound hy hyr]

/-- A uniform cubic margin depending only on the distance from the diagonal.
It follows from `r / (r + y) ≥ 1 / 2` when `0 < y ≤ r`. -/
theorem hmaxF_uniform_cubic_lower_bound {y r : ℝ}
    (hy : 2 ≤ y) (hyr : y ≤ r) (hr : r ≤ 4) :
    (r - y) ^ 3 / 8 ≤ hmaxF y r := by
  have hy0 : 0 < y := by linarith
  have hr0 : 0 < r := hy0.trans_le hyr
  have hden : 0 < 4 * (r + y) := by positivity
  have hcube : 0 ≤ (r - y) ^ 3 := pow_nonneg (sub_nonneg.mpr hyr) 3
  refine le_trans ?_ (hmaxF_cubic_lower_bound hy hyr hr)
  apply (le_div_iff₀ hden).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hyr) hcube]

/-- Qualitative nonnegativity, recovered from the quantitative lower bound. -/
theorem hmaxF_nonneg_from_margin {y r : ℝ}
    (hy : 2 ≤ y) (hyr : y ≤ r) (hr : r ≤ 4) : 0 ≤ hmaxF y r := by
  exact (div_nonneg (pow_nonneg (sub_nonneg.mpr hyr) 3) (by norm_num)).trans
    (hmaxF_uniform_cubic_lower_bound hy hyr hr)

/-- The upstream expression is strictly positive off its switching diagonal. -/
theorem hmaxF_pos_from_margin {y r : ℝ}
    (hy : 2 ≤ y) (hyr : y < r) (hr : r ≤ 4) : 0 < hmaxF y r := by
  exact (div_pos (pow_pos (sub_pos.mpr hyr) 3) (by norm_num)).trans_le
    (hmaxF_uniform_cubic_lower_bound hy hyr.le hr)

/-- The diagonal is the complete zero set on the triangle. This recovers the
qualitative conclusion already available upstream, now with an explicit margin. -/
theorem hmaxF_eq_zero_iff_from_margin {y r : ℝ}
    (hy : 2 ≤ y) (hyr : y ≤ r) (hr : r ≤ 4) :
    hmaxF y r = 0 ↔ r = y := by
  constructor
  · intro hf
    rcases hyr.lt_or_eq with hlt | heq
    · have hpos := hmaxF_pos_from_margin hy hlt hr
      rw [hf] at hpos
      exact False.elim ((lt_irrefl (0 : ℝ)) hpos)
    · exact heq.symm
  · rintro rfl
    unfold hmaxF
    ring

end SmoothedOctagon

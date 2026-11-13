module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen

/-!
# Concavity of the small-gap residual in the ratio

At unit shape the residual has the form `Aq² + Eq - D - Cq log q`.
Its second derivative is `2A - C/q`. On `1 ≤ q ≤ 8/7`, it is negative
as soon as `7C - 16A` is positive. The coefficient of the incoming norm
in `A` is negative, so the universal norm floor `3/4` suffices.
-/

@[expose] public section

namespace SmoothedOctagon

private noncomputable def chiA (t x v : ℝ) : ℝ :=
  t * (5 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x - t ^ 2 + 4 * t * x ^ 3 - 2 * t * x ^ 2 - 4 * t * x + x ^ 4)
    - t * x ^ 2 * (x + 2) ^ 2 * v
    - t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + t ^ 2 + 2 * t * x ^ 2 + x ^ 2 + 2 * x - x * (x + 2) * v

private noncomputable def chiC (t x : ℝ) : ℝ :=
  t * (t + x) * (1 + x) * (1 + 2 * t * x + x ^ 2)

private noncomputable def chiE (t x v : ℝ) : ℝ :=
  -t * (2 * t ^ 3 * x + 5 * t ^ 2 * x ^ 2 - 2 * t ^ 2 * x - 2 * t ^ 2 + 2 * t * x ^ 3 - 6 * t * x ^ 2 - 4 * t * x - 2
    * x ^ 3 - x ^ 2)
    + t * x * (1 + x) * (2 * t + x ^ 2 + 3 * x) * v
    + t ^ 3 * x + t ^ 2 * x ^ 2 - 2 * t ^ 2 * x - t ^ 2 - t * x ^ 2 - x ^ 2 - x
    + x * (1 - t) * (1 + x) * v

private theorem chi_decomp (t x v q : ℝ) :
    nsrN t x 1 q v (Real.log q) =
      chiA t x v * q ^ 2 + chiE t x v * q - t * (t + x) ^ 2 * (1 + x) ^ 2 - chiC t x * q * Real.log q := by
  unfold nsrN chiA chiE chiC
  ring

private theorem chi_curvature {t x v : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj : 0 ≤ 2 * t + x - 1) (hv : 3 / 4 ≤ v) : 0 < 7 * chiC t x - 16 * chiA t x v := by
  let h := 1 - 2 * t
  let j := 2 * t + x - 1
  have hh : 1 / 5 ≤ h := by dsimp [h]; linarith only [ht1]
  have hh1 : h ≤ 1 / 3 := by dsimp [h]; linarith only [ht]
  have hh0 : 0 < h := by linarith only [hh]
  have hj0 : 0 ≤ j := hj
  have hx : 0 < x := by dsimp [h] at hh0; linarith only [hh0, hj]
  have h2 : h ^ 2 ≤ h / 3 := by nlinarith only [mul_nonneg hh0.le (sub_nonneg.mpr hh1)]
  have h3 : h ^ 3 ≤ h / 9 := by
    have := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)
    nlinarith only [this, h2]
  have h4 : h ^ 4 ≤ h ^ 2 / 9 := by nlinarith only [h2, sq_nonneg (h / 3 - h ^ 2)]
  have b0 : 0 < -(h + 1) / 4 * (16 * h ^ 4 + 23 * h ^ 3 - 9 * h ^ 2 - 7 * h + 1) := by
    have h3' : h ^ 3 ≤ h ^ 2 / 3 := by
      nlinarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
    have : 16 * h ^ 4 + 23 * h ^ 3 - 9 * h ^ 2 - 7 * h + 1 < 0 := by linarith only [h4, h3', h2, hh]
    exact mul_pos_of_neg_of_neg (by linarith only [hh0]) this
  have b1 : 0 ≤ -(h + 1) / 4 * (87 * h ^ 3 + 12 * h ^ 2 - 55 * h - 12) := by
    have : 87 * h ^ 3 + 12 * h ^ 2 - 55 * h - 12 ≤ 0 := by linarith only [h3, h2, hh0]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [hh0]) this
  have b2 : 0 ≤ -(66 * h ^ 3 + 33 * h ^ 2 - 58 * h - 33) / 2 := by linarith only [h3, h2, hh0]
  have b3 : 0 ≤ 67 / 4 * (1 - h ^ 2) := by nlinarith only [h2, hh1]
  have b4 : 0 ≤ 3 / 2 * (1 - h) := by linarith only [hh1]
  have heq : 7 * chiC t x - 16 * chiA t x v =
      -(h + 1) / 4 * (16 * h ^ 4 + 23 * h ^ 3 - 9 * h ^ 2 - 7 * h + 1)
      + (-(h + 1) / 4 * (87 * h ^ 3 + 12 * h ^ 2 - 55 * h - 12)) * j
      + (-(66 * h ^ 3 + 33 * h ^ 2 - 58 * h - 33) / 2) * j ^ 2
      + (67 / 4 * (1 - h ^ 2)) * j ^ 3 + (3 / 2 * (1 - h)) * j ^ 4
      + 16 * x * (x + 2) * (1 + t * x * (x + 2)) * (v - 3 / 4) := by
    dsimp [h, j, chiA, chiC]
    ring
  rw [heq]
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hv0 : 0 ≤ v - 3 / 4 := sub_nonneg.mpr hv
  positivity

private theorem chi_log_quad_concave {A E D C : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ 7 * C - 16 * A) :
    ConcaveOn ℝ (Set.Icc 1 (8 / 7)) (fun q => A * q ^ 2 + E * q - D - C * q * Real.log q) := by
  let f := fun q : ℝ => A * q ^ 2 + E * q - D - C * q * Real.log q
  let f' := fun q : ℝ => 2 * A * q + E - C * (Real.log q + 1)
  have hd (q : ℝ) (hq : 0 < q) : HasDerivAt f (f' q) q := by
    have hl := (hasDerivAt_id q).mul (Real.hasDerivAt_log hq.ne')
    have hp := (((hasDerivAt_id q).pow 2).const_mul A).add ((hasDerivAt_id q).const_mul E)
    convert (hp.sub_const D).sub (hl.const_mul C) using 1
    · funext z
      change A * z ^ 2 + E * z - D - C * z * Real.log z = (A * z ^ 2 + E * z - D) - C * (z * Real.log z)
      ring
    · dsimp [f']; field_simp
  have hd' (q : ℝ) (hq : 0 < q) : HasDerivAt f' (2 * A - C / q) q := by
    convert (((hasDerivAt_id q).const_mul (2 * A)).add_const E).sub
      (((Real.hasDerivAt_log hq.ne').add_const 1).const_mul C) using 1
    · funext z; rfl
    · simp [div_eq_mul_inv]
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun q hq => (hd q (by linarith only [hq.1])).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (by rw [interior_Icc] at hq; linarith only [hq.1])).hasDerivWithinAt)
    (fun q hq => (hd' q (by rw [interior_Icc] at hq; linarith only [hq.1])).hasDerivWithinAt)
  intro q hq
  rw [interior_Icc] at hq
  have hq0 : 0 < q := by linarith only [hq.1]
  have hmul := mul_le_mul_of_nonneg_right (show 2 * A ≤ 7 * C / 8 by linarith only [hA]) hq0.le
  have hcap := mul_le_mul_of_nonneg_left hq.2.le (show 0 ≤ 7 * C / 8 by positivity)
  have : 2 * A ≤ C / q := (le_div_iff₀ hq0).mpr (by nlinarith only [hmul, hcap])
  exact sub_nonpos.mpr this

/-- The unit-shape residual is concave on the ratio interval containing `χ ≤ 4/7`. -/
theorem nsf_chi_concave {t x v : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj : 0 ≤ 2 * t + x - 1) (hv : 3 / 4 ≤ v) :
    ConcaveOn ℝ (Set.Icc 1 (8 / 7)) (fun q => nsrN t x 1 q v (Real.log q)) := by
  have hx : 0 < x := by linarith only [ht1, hj]
  have ht0 : 0 < t := by linarith only [ht]
  have hC : 0 ≤ chiC t x := by unfold chiC; positivity
  simpa only [chi_decomp] using chi_log_quad_concave (E := chiE t x v)
    (D := t * (t + x) ^ 2 * (1 + x) ^ 2) hC (chi_curvature ht ht1 hj hv).le

/-- The polynomial secant ceiling also satisfies the universal norm floor. -/
theorem nsf_chi_V2_ge {t x : ℝ} (ht1 : t ≤ 2 / 5)
    (hj : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30) : 3 / 4 ≤ nsfV2 t x := by
  have hx : 0 < x := by linarith only [ht1, hj]
  have hW : 0 < 1 + x := by positivity
  have hb : 0 ≤ 1 / 2 - x / 3 + x ^ 2 / 12 - t := by nlinarith only [ht1, hj1, sq_nonneg x]
  have heq : nsfV2 t x - 3 / 4 =
      (2 * t + x - 1) ^ 2 / (4 * (1 + x) ^ 2)
      + (1 - t) * x / (1 + x) ^ 2 * (1 / 2 - x / 3 + x ^ 2 / 12 - t) := by
    unfold nsfV2
    field_simp
    ring
  have hc : 0 ≤ 1 - t := by linarith only [ht1]
  have : 0 ≤ nsfV2 t x - 3 / 4 := by rw [heq]; positivity
  exact sub_nonneg.mp this

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.ChiConcavity
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The two endpoints of the small-gap ratio interval

The left endpoint is positive because the order gap dominates its cubic tail.
At the right endpoint, the constant and linear terms increase with the order
parameter. The remaining negative terms are bounded by a short geometric tail.
-/

@[expose] public section

namespace SmoothedOctagon

private noncomputable def chiEndpointA0 (h : ℝ) : ℝ :=
  60 * h ^ 10 + 840 * h ^ 9 + 3525 * h ^ 8 + 8503 * h ^ 7 + 12935 * h ^ 6 + 11607 * h ^ 5 + 5285 * h ^ 4 + 685 * h ^ 3
    - 207 * h ^ 2 - 35 * h + 2

private noncomputable def chiEndpointA1 (h : ℝ) : ℝ :=
  88 * h ^ 9 + 3364 * h ^ 8 + 13909 * h ^ 7 + 29018 * h ^ 6 + 34865 * h ^ 5 + 21082 * h ^ 4 + 2959 * h ^ 3 - 2466 * h
    ^ 2 - 941 * h - 118

private noncomputable def chiEndpointA2 (h : ℝ) : ℝ :=
  -(h + 1) ^ 2 * (1260 * h ^ 6 - 6016 * h ^ 5 - 6063 * h ^ 4 - 4086 * h ^ 3 + 1024 * h ^ 2 + 1030 * h + 3)

private noncomputable def chiEndpointA3 (h : ℝ) : ℝ :=
  -(h + 1) * (6048 * h ^ 6 - 3448 * h ^ 5 + 253 * h ^ 4 + 15330 * h ^ 3 + 4104 * h ^ 2 - 3770 * h - 1237)

private noncomputable def chiEndpointA4 (h : ℝ) : ℝ :=
  -4 * (h + 1) * (3115 * h ^ 5 - 1245 * h ^ 4 + 851 * h ^ 3 + 2317 * h ^ 2 - 1158 * h - 112)

private noncomputable def chiEndpointA5 (h : ℝ) : ℝ :=
  -4 * (h + 1) * (3570 * h ^ 4 - 2395 * h ^ 3 - 2733 * h ^ 2 - 289 * h + 1927)

private noncomputable def chiEndpointA6 (h : ℝ) : ℝ :=
  -4 * (h + 1) * (2373 * h ^ 3 - 2239 * h ^ 2 - 3813 * h + 3415)

private noncomputable def chiEndpointA7 (h : ℝ) : ℝ :=
  -16 * (h - 1) * (215 * h ^ 2 + 199 * h - 367)

private noncomputable def chiEndpointA8 (h : ℝ) : ℝ :=
  -528 * (h - 1) * (h + 1)

private noncomputable def chiEndpointP (h j : ℝ) : ℝ :=
  chiEndpointA0 h +
  chiEndpointA1 h * j +
  chiEndpointA2 h * j ^ 2 +
  chiEndpointA3 h * j ^ 3 +
  chiEndpointA4 h * j ^ 4 +
  chiEndpointA5 h * j ^ 5 +
  chiEndpointA6 h * j ^ 6 +
  chiEndpointA7 h * j ^ 7 +
  chiEndpointA8 h * j ^ 8

private theorem chiEndpointA0_deriv (h : ℝ) :
    HasDerivAt chiEndpointA0 (600 * h ^ 9 + 7560 * h ^ 8 + 28200 * h ^ 7 + 59521 * h ^ 6 + 77610 * h ^ 5 + 58035 * h ^
      4 + 21140 * h ^ 3 + 2055 * h ^ 2 - 414 * h - 35) h := by
  let p : Polynomial ℝ := Polynomial.C (2) + Polynomial.C (-35) * Polynomial.X + Polynomial.C (-207) * Polynomial.X ^
    2 + Polynomial.C (685) * Polynomial.X ^ 3 + Polynomial.C (5285) * Polynomial.X ^ 4 + Polynomial.C (11607) *
    Polynomial.X ^ 5 + Polynomial.C (12935) * Polynomial.X ^ 6 + Polynomial.C (8503) * Polynomial.X ^ 7 + Polynomial.C
    (3525) * Polynomial.X ^ 8 + Polynomial.C (840) * Polynomial.X ^ 9 + Polynomial.C (60) * Polynomial.X ^ 10
  convert p.hasDerivAt h using 1
  · funext z; simp [p, chiEndpointA0]; ring
  · simp only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
      Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    norm_num
    ring

private theorem chiEndpointA1_deriv (h : ℝ) :
    HasDerivAt chiEndpointA1 (792 * h ^ 8 + 26912 * h ^ 7 + 97363 * h ^ 6 + 174108 * h ^ 5 + 174325 * h ^ 4 + 84328 *
      h ^ 3 + 8877 * h ^ 2 - 4932 * h - 941) h := by
  let p : Polynomial ℝ := Polynomial.C (-118) + Polynomial.C (-941) * Polynomial.X + Polynomial.C (-2466) *
    Polynomial.X ^ 2 + Polynomial.C (2959) * Polynomial.X ^ 3 + Polynomial.C (21082) * Polynomial.X ^ 4 + Polynomial.C
    (34865) * Polynomial.X ^ 5 + Polynomial.C (29018) * Polynomial.X ^ 6 + Polynomial.C (13909) * Polynomial.X ^ 7 +
    Polynomial.C (3364) * Polynomial.X ^ 8 + Polynomial.C (88) * Polynomial.X ^ 9
  convert p.hasDerivAt h using 1
  · funext z; simp [p, chiEndpointA1]; ring
  · simp only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
      Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    norm_num
    ring

/-- The low terms increase with the order parameter; no subdivision is needed. -/
private theorem chiEndpoint_low {h : ℝ} (hh : 6 / 25 ≤ h) :
    18 ≤ chiEndpointA0 h ∧ -400 ≤ chiEndpointA1 h := by
  have hm0 : MonotoneOn chiEndpointA0 (Set.Ici (6 / 25)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun h _ => (chiEndpointA0_deriv h).continuousAt.continuousWithinAt)
      (fun h _ => (chiEndpointA0_deriv h).hasDerivWithinAt)
    intro h hh
    rw [interior_Ici] at hh
    change (6 / 25 : ℝ) < h at hh
    have h0 : 0 ≤ h := by linarith only [hh]
    have h2 : h / 5 ≤ h ^ 2 := by nlinarith only [mul_nonneg h0 (show 0 ≤ h - 1 / 5 by linarith only [hh])]
    have h3 : h ^ 2 / 5 ≤ h ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg h) (show 0 ≤ h - 1 / 5 by linarith only
      [hh])]
    have hlo : 0 ≤ 21140 * h ^ 3 + 2055 * h ^ 2 - 414 * h - 35 := by linarith only [h2, h3, hh]
    have hrest : 0 ≤ 600 * h ^ 9 + 7560 * h ^ 8 + 28200 * h ^ 7 + 59521 * h ^ 6 + 77610 * h ^ 5 + 58035 * h ^ 4 := by
      positivity
    linarith only [hlo, hrest]
  have hm1 : MonotoneOn chiEndpointA1 (Set.Ici (6 / 25)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun h _ => (chiEndpointA1_deriv h).continuousAt.continuousWithinAt)
      (fun h _ => (chiEndpointA1_deriv h).hasDerivWithinAt)
    intro h hh
    rw [interior_Ici] at hh
    change (6 / 25 : ℝ) < h at hh
    have h0 : 0 ≤ h := by linarith only [hh]
    have h2 : 6 / 25 * h ≤ h ^ 2 := by nlinarith only [mul_nonneg h0 (sub_nonneg.mpr hh.le)]
    have h3 : 6 / 25 * h ^ 2 ≤ h ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh.le)]
    have h4 : 6 / 25 * h ^ 3 ≤ h ^ 4 := by nlinarith only [mul_nonneg (pow_nonneg h0 3) (sub_nonneg.mpr hh.le)]
    have hlo : 0 ≤ 174325 * h ^ 4 + 84328 * h ^ 3 + 8877 * h ^ 2 - 4932 * h - 941 := by linarith only [h2, h3, h4, hh]
    have hrest : 0 ≤ 792 * h ^ 8 + 26912 * h ^ 7 + 97363 * h ^ 6 + 174108 * h ^ 5 := by positivity
    linarith only [hlo, hrest]
  constructor
  · exact (by norm_num [chiEndpointA0] : (18 : ℝ) ≤ chiEndpointA0 (6 / 25)).trans
      (hm0 (by simp) hh hh)
  · exact (by norm_num [chiEndpointA1] : (-400 : ℝ) ≤ chiEndpointA1 (6 / 25)).trans
      (hm1 (by simp) hh hh)

/-- Higher powers cannot overturn the constant and linear terms. -/
private theorem chiEndpoint_tail {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
    -700 ≤ chiEndpointA2 h ∧ 0 ≤ chiEndpointA3 h ∧ 0 ≤ chiEndpointA4 h ∧
      -11000 ≤ chiEndpointA5 h ∧ -19000 ≤ chiEndpointA6 h ∧
      -6000 ≤ chiEndpointA7 h ∧ 0 ≤ chiEndpointA8 h := by
  have u (n : ℕ) : h ^ n ≤ (1 / 3 : ℝ) ^ n := pow_le_pow_left₀ hh hh1 n
  have rel (n : ℕ) : h ^ (n + 1) ≤ h ^ n / 3 := by
    have := mul_le_mul_of_nonneg_left hh1 (pow_nonneg hh n)
    simpa [pow_succ, div_eq_mul_inv] using this
  have h2 : h ^ 2 ≤ h / 3 := by simpa using rel 1
  have h3 : h ^ 3 ≤ h / 9 := by linarith only [rel 2, h2]
  have h4 : h ^ 4 ≤ h / 27 := by linarith only [rel 3, h3]
  have h5 : h ^ 5 ≤ h / 81 := by linarith only [rel 4, h4]
  have h6 : h ^ 6 ≤ h / 243 := by linarith only [rel 5, h5]
  have hW : 0 ≤ h + 1 := by positivity
  constructor
  · have hlo : -700 ≤ -1260 * h ^ 8 - 3087 * h ^ 2 - 1036 * h - 3 := by linarith only [u 8, u 2, hh1]
    have hrest : 0 ≤ chiEndpointA2 h - (-1260 * h ^ 8 - 3087 * h ^ 2 - 1036 * h - 3) := by
      unfold chiEndpointA2; ring_nf; positivity
    linarith only [hlo, hrest]
  constructor
  · have : 6048 * h ^ 6 - 3448 * h ^ 5 + 253 * h ^ 4 + 15330 * h ^ 3 + 4104 * h ^ 2 - 3770 * h - 1237 ≤ 0 := by
      linarith only [h6, h4, h3, h2, hh, pow_nonneg hh 5]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [hW]) this
  constructor
  · have : 3115 * h ^ 5 - 1245 * h ^ 4 + 851 * h ^ 3 + 2317 * h ^ 2 - 1158 * h - 112 ≤ 0 := by
      linarith only [h5, h3, h2, hh, pow_nonneg hh 4]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [hW]) this
  constructor
  · have hb : 3570 * h ^ 4 - 2395 * h ^ 3 - 2733 * h ^ 2 - 289 * h + 1927 ≤ 2000 := by
      linarith only [u 4, pow_nonneg hh 3, sq_nonneg h, hh]
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * (h + 1) by positivity)
    change - 11000 ≤ -4 * (h + 1) * (3570 * h ^ 4 - 2395 * h ^ 3 - 2733 * h ^ 2 - 289 * h + 1927)
    nlinarith only [hm, hh1]
  constructor
  · have hb : 2373 * h ^ 3 - 2239 * h ^ 2 - 3813 * h + 3415 ≤ 3503 := by
      linarith only [u 3, sq_nonneg h, hh]
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * (h + 1) by positivity)
    change - 19000 ≤ -4 * (h + 1) * (2373 * h ^ 3 - 2239 * h ^ 2 - 3813 * h + 3415)
    nlinarith only [hm, hh1]
  constructor
  · have hlo : -6000 ≤ -3440 * h ^ 3 - 5872 := by linarith only [u 3]
    have hrest : 0 ≤ chiEndpointA7 h - (-3440 * h ^ 3 - 5872) := by
      unfold chiEndpointA7; ring_nf; positivity
    linarith only [hlo, hrest]
  · unfold chiEndpointA8
    have : 0 ≤ 1 - h ^ 2 := by linarith only [u 2]
    nlinarith only [this]

private theorem chiEndpointP_pos {h j : ℝ} (hh : 6 / 25 ≤ h) (hh1 : h ≤ 1 / 3)
    (hj : 0 ≤ j) (hj1 : j ≤ 1 / 30) : 0 < chiEndpointP h j := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  obtain ⟨h0, h1⟩ := chiEndpoint_low hh
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := chiEndpoint_tail hh0 hh1
  have hrest : 0 ≤ chiEndpointP h j - (18 - 400 * j - 700 * j ^ 2 - 11000 * j ^ 5 - 19000 * j ^ 6 - 6000 * j ^ 7) :=
    by
    have h0' : 0 ≤ chiEndpointA0 h - 18 := sub_nonneg.mpr h0
    have h1' : 0 ≤ chiEndpointA1 h + 400 := by linarith only [h1]
    have h2' : 0 ≤ chiEndpointA2 h + 700 := by linarith only [h2]
    have h5' : 0 ≤ chiEndpointA5 h + 11000 := by linarith only [h5]
    have h6' : 0 ≤ chiEndpointA6 h + 19000 := by linarith only [h6]
    have h7' : 0 ≤ chiEndpointA7 h + 6000 := by linarith only [h7]
    have heq : chiEndpointP h j - (18 - 400 * j - 700 * j ^ 2 - 11000 * j ^ 5 - 19000 * j ^ 6 - 6000 * j ^ 7) =
        (chiEndpointA0 h - 18) + (chiEndpointA1 h + 400) * j + (chiEndpointA2 h + 700) * j ^ 2
        + chiEndpointA3 h * j ^ 3 + chiEndpointA4 h * j ^ 4 + (chiEndpointA5 h + 11000) * j ^ 5
        + (chiEndpointA6 h + 19000) * j ^ 6 + (chiEndpointA7 h + 6000) * j ^ 7 + chiEndpointA8 h * j ^ 8 := by
      unfold chiEndpointP; ring
    rw [heq]; positivity
  have j2 : j ^ 2 ≤ j / 30 := by nlinarith only [mul_nonneg hj (sub_nonneg.mpr hj1)]
  have j4 : j ^ 4 ≤ (1 / 30 : ℝ) ^ 4 := pow_le_pow_left₀ hj hj1 4
  have j5 : j ^ 5 ≤ j / 810000 := by
    have := mul_le_mul_of_nonneg_right j4 hj
    nlinarith only [this]
  have j6 : j ^ 6 ≤ j ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show j ≤ 1 by linarith only [hj1]) (pow_nonneg hj 5)
    nlinarith only [this]
  have j7 : j ^ 7 ≤ j ^ 5 := by
    have := mul_le_mul_of_nonneg_left (show j ≤ 1 by linarith only [hj1]) (pow_nonneg hj 6)
    nlinarith only [this, j6]
  linarith only [hrest, j2, j5, j6, j7, hj1]

/-- The unit-shape residual is positive at the right end of the ratio interval. -/
theorem nsf_chi_right {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 19 / 50)
    (hj : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30) :
    0 < nsrN t x 1 (4 * (1 + x) / (7 * (t + x))) (nsfV2 t x)
      (nsrLp (4 * (1 + x) / (7 * (t + x)))) := by
  let h := 1 - 2 * t
  let j := 2 * t + x - 1
  have hx : 0 < x := by linarith only [ht1, hj]
  have ht0 : 0 < t := by linarith only [ht]
  have hp : 0 < t + x := by positivity
  have hW : 0 < 1 + x := by positivity
  have hQ : 0 < 4 * (1 + x) / (7 * (t + x)) + 1 := by positivity
  have hP := chiEndpointP_pos (h := h) (j := j) (by dsimp [h]; linarith only [ht1])
    (by dsimp [h]; linarith only [ht]) hj hj1
  have heq : chiEndpointP h j = 1176 * (h + 2 * j + 1) ^ 2 * (15 * h + 22 * j + 15) *
      nsrN t x 1 (4 * (1 + x) / (7 * (t + x))) (nsfV2 t x)
        (nsrLp (4 * (1 + x) / (7 * (t + x)))) := by
    dsimp [h, j, chiEndpointP, chiEndpointA0, chiEndpointA1, chiEndpointA2, chiEndpointA3,
      chiEndpointA4, chiEndpointA5, chiEndpointA6, chiEndpointA7, chiEndpointA8, nsrN, nsfV2, nsrLp]
    field_simp
    ring
  rw [heq] at hP
  have hh : 0 < h := by dsimp [h]; linarith only [ht1]
  exact pos_of_mul_pos_right hP (by positivity)

/-- At ratio one, the order parameter dominates all the negative gap terms. -/
theorem nsf_chi_left {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30) :
    0 < nsrN t x 1 1 (nsfV2 t x) 0 := by
  let h := 1 - 2 * t
  let j := 2 * t + x - 1
  let R := h ^ 3 * (h ^ 3 + 2 * h ^ 2 + 4 * h + 2) + h ^ 3 * (5 * h ^ 2 + 7 * h + 8) * j
    + 2 * h * (5 * h ^ 3 + 4 * h ^ 2 - 3) * j ^ 2 + 2 * (h - 1) * (5 * h ^ 2 + 6 * h + 2) * j ^ 3
    + (5 * h ^ 2 - 2 * h - 4) * j ^ 4 + (h - 1) * j ^ 5
  have hh : 1 / 5 ≤ h := by dsimp [h]; linarith only [ht1]
  have hh1 : h ≤ 1 / 3 := by dsimp [h]; linarith only [ht]
  have hh0 : 0 < h := by linarith only [hh]
  have hj0 : 0 ≤ j := hj
  have hjcap : j ≤ 1 := by dsimp [j]; linarith only [hj1]
  have hR : 2 * h ^ 3 - 6 * h * j ^ 2 - 10 * j ^ 3 - 5 * j ^ 4 - j ^ 5 ≤ R := by
    have h3 : 0 ≤ 10 * h ^ 3 + 2 * h ^ 2 - 8 * h + 6 := by
      nlinarith only [hh1, pow_nonneg hh0.le 3, sq_nonneg h]
    have h4 : 0 ≤ 5 * h ^ 2 - 2 * h + 1 := by nlinarith only [hh1, sq_nonneg h]
    have heq : R - (2 * h ^ 3 - 6 * h * j ^ 2 - 10 * j ^ 3 - 5 * j ^ 4 - j ^ 5) =
        h ^ 3 * (h ^ 3 + 2 * h ^ 2 + 4 * h) + h ^ 3 * (5 * h ^ 2 + 7 * h + 8) * j
        + (10 * h ^ 4 + 8 * h ^ 3) * j ^ 2 + (10 * h ^ 3 + 2 * h ^ 2 - 8 * h + 6) * j ^ 3
        + (5 * h ^ 2 - 2 * h + 1) * j ^ 4 + h * j ^ 5 := by dsimp [R]; ring
    have : 0 ≤ R - (2 * h ^ 3 - 6 * h * j ^ 2 - 10 * j ^ 3 - 5 * j ^ 4 - j ^ 5) := by rw [heq]; positivity
    exact sub_nonneg.mp this
  have h2 : (1 / 25 : ℝ) ≤ h ^ 2 := by nlinarith only [hh, sq_nonneg (h - 1 / 5)]
  have h3 : h / 25 ≤ h ^ 3 := by
    have := mul_le_mul_of_nonneg_right h2 hh0.le
    nlinarith only [this]
  have j2 : j ^ 2 ≤ 1 / 900 := by
    have := pow_le_pow_left₀ hj0 hj1 2
    norm_num at this
    exact this
  have hj2 := mul_le_mul_of_nonneg_left j2 hh0.le
  have j3 : j ^ 3 ≤ 1 / 27000 := by
    have := pow_le_pow_left₀ hj0 hj1 3
    norm_num at this
    exact this
  have j4 : j ^ 4 ≤ j ^ 3 := by
    have := mul_le_mul_of_nonneg_left hjcap (pow_nonneg hj0 3)
    nlinarith only [this]
  have j5 : j ^ 5 ≤ j ^ 3 := by
    have := mul_le_mul_of_nonneg_left hjcap (pow_nonneg hj0 4)
    nlinarith only [this, j4]
  have hRpos : 0 < R := by linarith only [hR, h3, hj2, j3, j4, j5, hh]
  have hx : 0 < x := by dsimp [h] at hh0; linarith only [hh0, hj]
  have hW : 0 < 1 + x := by positivity
  have heq : 48 * (1 + x) ^ 2 * nsrN t x 1 1 (nsfV2 t x) 0 = (h + 1) ^ 2 * R := by
    dsimp [h, j, R, nsrN, nsfV2]
    field_simp
    ring
  have hpos : 0 < 48 * (1 + x) ^ 2 * nsrN t x 1 1 (nsfV2 t x) 0 := by rw [heq]; positivity
  exact pos_of_mul_pos_right hpos (by positivity)

end SmoothedOctagon

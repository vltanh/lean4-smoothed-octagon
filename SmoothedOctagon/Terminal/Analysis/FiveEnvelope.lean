module

public import SmoothedOctagon.Terminal.Analysis.LogBounds
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# The five-piece logarithmic envelope

FAP (19)-(22). With `h(t) = -2t log t/(1 - t) - log(1 + t)` on `(0, 1)`:

* `ra_fiveH`: the function `h`.
* `ra_fiveH_concaveOn`: `x ↦ h(√x)` is concave on `(0, 1)` (FAP (21)).
* `ra_fiveH_circle_le`: `h(a) + h(b) ≤ 2 h(√2/2)` for `a, b > 0`, `a² + b² = 1` (two-point Jensen).
* `ra_five_envelope`: for `0 < t < 1`, with `F` the function of FAP (17),
  `F(t) + 2 log(1 - t) ≤ (3 + 2√2) log 2 + 2 log(2 - √2)` (FAP (19), through the identity (22)).
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- `h(t) = -2t log t/(1 - t) - log(1 + t)` (FAP §5). -/
noncomputable def ra_fiveH (t : ℝ) : ℝ := -2 * t * Real.log t / (1 - t) - Real.log (1 + t)

/-- `h'(t) = 2E/(1 - t)² - 1/(1 + t)`, `E = t - 1 - log t`. -/
private noncomputable def hd (t : ℝ) : ℝ := 2 * (t - 1 - Real.log t) / (1 - t) ^ 2 - 1 / (1 + t)

private lemma h_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt ra_fiveH (hd t) t := by
  have h1 := (((hasDerivAt_id' t).const_mul (-2)).mul (Real.hasDerivAt_log ht0.ne')).div
    ((hasDerivAt_id' t).const_sub 1) (by linarith : (1 : ℝ) - t ≠ 0)
  have h2 := ((hasDerivAt_id' t).const_add 1).log (by linarith : (1 : ℝ) + t ≠ 0)
  have h := h1.sub h2
  convert h using 1
  · funext x
    simp only [ra_fiveH, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
  · simp only [hd, Pi.mul_apply]
    have : (1 : ℝ) - t ≠ 0 := by linarith
    have : (1 : ℝ) + t ≠ 0 := by linarith
    field_simp
    ring

/-- `k(t) = h'(t)/t`. -/
private noncomputable def kk (t : ℝ) : ℝ := hd t / t

/-- `k'(t) = (t h'' - h')/t²`, with `t h'' - h'` as in FAP (21). -/
private noncomputable def kd (t : ℝ) : ℝ :=
  (-2 / (1 - t) + 2 * (3 * t - 1) * (t - 1 - Real.log t) / (1 - t) ^ 3 +
    (1 + 2 * t) / (1 + t) ^ 2) / t ^ 2

private lemma kk_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt kk (kd t) t := by
  have h1t : (1 : ℝ) - t ≠ 0 := by linarith
  have h1t' : (1 : ℝ) + t ≠ 0 := by linarith
  have hE := ((hasDerivAt_id' t).sub_const 1).sub (Real.hasDerivAt_log ht0.ne')
  have hP := ((hasDerivAt_id' t).const_sub 1).pow 2
  have hA := (hE.const_mul 2).div hP (pow_ne_zero 2 h1t)
  have hB := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id' t).const_add 1) h1t'
  have h := (hA.sub hB).div (hasDerivAt_id' t) ht0.ne'
  convert h using 1
  · funext x
    simp only [kk, hd, Pi.div_apply, Pi.sub_apply, Pi.pow_apply]
  · simp only [kd, Pi.div_apply, Pi.sub_apply, Pi.pow_apply]
    norm_num
    field_simp
    ring

/-- `t h'' - h' ≤ 0` (FAP (21)). -/
private lemma kd_nonpos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : kd t ≤ 0 := by
  have h1t : 0 < 1 - t := by linarith
  set E := t - 1 - Real.log t with hE_def
  have hE0 : 0 ≤ E := by
    have := Real.log_le_sub_one_of_pos ht0
    linarith
  have hE1 : 2 * t * E ≤ (1 - t) ^ 2 := by
    have hL := ra_half_sub_inv_le_log ht0 ht1.le
    have e : t * (t - t⁻¹) = t ^ 2 - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hL ht0.le]
  have key : -2 / (1 - t) + 2 * (3 * t - 1) * E / (1 - t) ^ 3 + (1 + 2 * t) / (1 + t) ^ 2 =
      (-2 * (1 - t) ^ 2 * (1 + t) ^ 2 + 2 * (3 * t - 1) * E * (1 + t) ^ 2 +
        (1 + 2 * t) * (1 - t) ^ 3) / ((1 - t) ^ 3 * (1 + t) ^ 2) := by
    field_simp
  have hnum : -2 * (1 - t) ^ 2 * (1 + t) ^ 2 + 2 * (3 * t - 1) * E * (1 + t) ^ 2 +
      (1 + 2 * t) * (1 - t) ^ 3 ≤ 0 := by
    rcases le_or_gt t (1 / 3) with h3 | h3
    · have a1 : 0 ≤ (1 - 3 * t) * E * (1 + t) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) hE0) (sq_nonneg _)
      have a2 : 0 ≤ (1 - t) ^ 2 * (1 + 3 * t + 4 * t ^ 2) :=
        mul_nonneg (sq_nonneg _) (by positivity)
      nlinarith
    · have a1 : (3 * t - 1) * (1 + t) ^ 2 * (2 * t * E) ≤
          (3 * t - 1) * (1 + t) ^ 2 * (1 - t) ^ 2 :=
        mul_le_mul_of_nonneg_left hE1 (mul_nonneg (by linarith) (sq_nonneg _))
      have a2 : (1 - t) ^ 3 * (t ^ 2 - t - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg h1t.le 3) (by nlinarith)
      have a3 : t * (-2 * (1 - t) ^ 2 * (1 + t) ^ 2 + 2 * (3 * t - 1) * E * (1 + t) ^ 2 +
          (1 + 2 * t) * (1 - t) ^ 3) ≤ 0 := by nlinarith
      by_contra hc
      have := mul_pos ht0 (not_le.1 hc)
      linarith
  rw [kd, ← hE_def, key]
  exact div_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hnum (by positivity))
    (sq_nonneg _)

private lemma kk_antitoneOn : AntitoneOn kk (Ioo 0 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1) (f' := kd)
    (fun x hx => (kk_hasDerivAt hx.1 hx.2).continuousAt.continuousWithinAt) ?_ ?_
  · intro x hx
    rw [interior_Ioo] at hx ⊢
    exact (kk_hasDerivAt hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact kd_nonpos hx.1 hx.2

private lemma g_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => ra_fiveH (√x)) (kk (√x) / 2) x := by
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hs1 : √x < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
  have h := (h_hasDerivAt hs0 hs1).comp x (Real.hasDerivAt_sqrt hx0.ne')
  convert h using 1
  · rfl
  · unfold kk
    field_simp

/-- **Concavity** (FAP (21)): `x ↦ h(√x)` is concave on `(0, 1)`. -/
theorem ra_fiveH_concaveOn : ConcaveOn ℝ (Ioo 0 1) (fun x => ra_fiveH (√x)) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioo 0 1)
  · exact fun x hx => (g_hasDerivAt hx.1 hx.2).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    exact fun x hx => (g_hasDerivAt hx.1 hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx y hy hxy
    rw [(g_hasDerivAt hx.1 hx.2).deriv, (g_hasDerivAt hy.1 hy.2).deriv]
    have hsx : √x ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.sqrt_pos.2 hx.1, by rw [Real.sqrt_lt' one_pos]; linarith [hx.2]⟩
    have hsy : √y ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.sqrt_pos.2 hy.1, by rw [Real.sqrt_lt' one_pos]; linarith [hy.2]⟩
    have := kk_antitoneOn hsx hsy (Real.sqrt_le_sqrt hxy)
    linarith

/-- **Two-point Jensen on the circle**: `h(a) + h(b) ≤ 2 h(√2/2)` for `a, b > 0`,
`a² + b² = 1`. -/
theorem ra_fiveH_circle_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    ra_fiveH a + ra_fiveH b ≤ 2 * ra_fiveH (√2 / 2) := by
  have ha2 : a ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hb2 : b ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have h := ra_fiveH_concaveOn.2 ha2 hb2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le] at h
  have hmid : 1 / 2 * a ^ 2 + 1 / 2 * b ^ 2 = (√2 / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    linarith
  rw [hmid, Real.sqrt_sq (by positivity)] at h
  linarith

/-- The maximal value: `log 2 + 2 h(√2/2) = (3 + 2√2) log 2 + 2 log(2 - √2)` (FAP (20)). -/
private lemma fiveH_max_value :
    Real.log 2 + 2 * ra_fiveH (√2 / 2) = (3 + 2 * √2) * Real.log 2 + 2 * Real.log (2 - √2) := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hslt : √2 < 2 := by nlinarith
  have hlog : Real.log (√2 / 2) = -(Real.log 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    ring
  have hplus : Real.log (1 + √2 / 2) = Real.log (2 + √2) - Real.log 2 := by
    rw [show 1 + √2 / 2 = (2 + √2) / 2 by ring, Real.log_div (by positivity) (by norm_num)]
  have hminus : Real.log (2 - √2) = Real.log 2 - Real.log (2 + √2) := by
    rw [show 2 - √2 = 2 / (2 + √2) by
      field_simp
      linear_combination -hs2, Real.log_div (by norm_num) (by positivity)]
  have hq : -2 * (√2 / 2) * -(Real.log 2 / 2) / (1 - √2 / 2) = (1 + √2) * Real.log 2 := by
    rw [div_eq_iff (by linarith)]
    linear_combination (Real.log 2 / 2) * hs2
  rw [ra_fiveH, hlog, hplus, hminus, hq]
  ring

/-- `F(t) + 2 log(1 - t) = log 2 + h(α) + h(β)`, `α = 2t/(1 + t²)`, `β = (1 - t²)/(1 + t²)`
(FAP (22)). -/
private lemma five_identity {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 + t) / (1 - t)) ^ 2 * Real.log ((1 + t ^ 2) / (2 * t)) +
        Real.log ((1 + t ^ 2) / (1 - t ^ 2)) / t ^ 2 + Real.log (2 * t / (1 - t ^ 2)) +
        2 * Real.log (1 - t) =
      Real.log 2 + ra_fiveH (2 * t / (1 + t ^ 2)) + ra_fiveH ((1 - t ^ 2) / (1 + t ^ 2)) := by
  have hm : 0 < 1 - t := by linarith
  have hp : 0 < 1 + t := by linarith
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hmp : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
  have hm2 : 0 < 1 - t ^ 2 := by rw [hmp]; positivity
  have l1 : Real.log ((1 + t ^ 2) / (2 * t)) =
      Real.log (1 + t ^ 2) - (Real.log 2 + Real.log t) := by
    rw [Real.log_div hq.ne' (by positivity), Real.log_mul (by norm_num) ht0.ne']
  have l2 : Real.log ((1 + t ^ 2) / (1 - t ^ 2)) =
      Real.log (1 + t ^ 2) - (Real.log (1 - t) + Real.log (1 + t)) := by
    rw [Real.log_div hq.ne' hm2.ne', hmp, Real.log_mul hm.ne' hp.ne']
  have l3 : Real.log (2 * t / (1 - t ^ 2)) =
      Real.log 2 + Real.log t - (Real.log (1 - t) + Real.log (1 + t)) := by
    rw [Real.log_div (by positivity) hm2.ne', hmp, Real.log_mul hm.ne' hp.ne',
      Real.log_mul (by norm_num) ht0.ne']
  have l4 : Real.log (2 * t / (1 + t ^ 2)) = Real.log 2 + Real.log t - Real.log (1 + t ^ 2) := by
    rw [Real.log_div (by positivity) hq.ne', Real.log_mul (by norm_num) ht0.ne']
  have l5 : Real.log (1 + 2 * t / (1 + t ^ 2)) = 2 * Real.log (1 + t) - Real.log (1 + t ^ 2) := by
    rw [show 1 + 2 * t / (1 + t ^ 2) = (1 + t) ^ 2 / (1 + t ^ 2) by field_simp; ring,
      Real.log_div (by positivity) hq.ne', Real.log_pow]
    push_cast
    ring
  have l6 : Real.log ((1 - t ^ 2) / (1 + t ^ 2)) =
      Real.log (1 - t) + Real.log (1 + t) - Real.log (1 + t ^ 2) := by
    rw [Real.log_div hm2.ne' hq.ne', hmp, Real.log_mul hm.ne' hp.ne']
  have l7 : Real.log (1 + (1 - t ^ 2) / (1 + t ^ 2)) = Real.log 2 - Real.log (1 + t ^ 2) := by
    rw [show 1 + (1 - t ^ 2) / (1 + t ^ 2) = 2 / (1 + t ^ 2) by field_simp; ring,
      Real.log_div (by norm_num) hq.ne']
  have d1 : 1 - 2 * t / (1 + t ^ 2) = (1 - t) ^ 2 / (1 + t ^ 2) := by field_simp; ring
  have d2 : 1 - (1 - t ^ 2) / (1 + t ^ 2) = 2 * t ^ 2 / (1 + t ^ 2) := by field_simp; ring
  rw [ra_fiveH, ra_fiveH, l1, l2, l3, l4, l5, l6, l7, d1, d2]
  field_simp
  ring

/-- **The five-piece envelope** (FAP (19)-(22)): for `0 < t < 1`,
`F(t) + 2 log(1 - t) ≤ (3 + 2√2) log 2 + 2 log(2 - √2)`. -/
theorem ra_five_envelope {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 + t) / (1 - t)) ^ 2 * Real.log ((1 + t ^ 2) / (2 * t)) +
        Real.log ((1 + t ^ 2) / (1 - t ^ 2)) / t ^ 2 + Real.log (2 * t / (1 - t ^ 2)) +
        2 * Real.log (1 - t) ≤
      (3 + 2 * √2) * Real.log 2 + 2 * Real.log (2 - √2) := by
  rw [five_identity ht0 ht1, ← fiveH_max_value]
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hm2 : 0 < 1 - t ^ 2 := by nlinarith
  have hcirc : (2 * t / (1 + t ^ 2)) ^ 2 + ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 = 1 := by
    field_simp
    ring
  have := ra_fiveH_circle_le (by positivity) (by positivity) hcirc
  linarith

end SmoothedOctagon

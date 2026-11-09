module

public meta import SmoothedOctagon.Tactic.Deriv

public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Case M2, smaller-short side: logarithm bounds and the turn secant as an average

Real analysis shared by the smaller-short reduction: monotonicity from a derivative sign,
logarithm bounds, and the turn secant as the average of its integrand.

## Main API

* `ss_le_of_deriv`, `ss_lt_of_deriv`: monotonicity on `[x, y]` from a derivative sign.
* Logarithm bounds for `z ≥ 1`: `ss_log_le_half` (`log z ≤ (z - z⁻¹)/2`), `ss_log_ge_pade`
  (`2(z - 1)/(z + 1) ≤ log z`), `ss_log_ge_cubic` (`2w + (2/3)w³ ≤ log z`, `w = (z - 1)/(z + 1)`),
  `ss_log_le_pade3` (`log z ≤ (z - 1)(z² + 10z + 1)/(6z(z + 1))`).
* `ss_gB B t = 1 - Bt/(B + t)²` (the integrand `g_B`) and its primitive `ss_FB B t`
  (`ss_FB_hasDerivAt`); `ss_sec_mul`: `(P - A) Sec(A, B, P) = F_B(P) - F_B(A)`;
  `ss_m2g_eq`: `m2g A B = ss_gB B A`.
* Comparisons of the secant with bounds of its integrand: `ss_sec_ge`, `ss_sec_le`, `ss_sec_gt`.
* `ss_sec_add`: additivity of `(P - A) Sec(A, B, P)` over adjacent intervals.
* Monotonicity of `g_B` (`ss_gB_sub`): `ss_sec_gt_right`, `ss_sec_ge_right`, `ss_sec_le_left`
  (`[A, P] ⊆ (0, B]`), `ss_sec_le_right` (`[B, P]`).
* `ss_sec_cross`: `Sec(a, B, C) < Sec(a, C, B)` for `a < B < C`.
* `ss_V_lt_limit`: `Sec(a, C, C) < 3/2 - log 2`; `ss_V_le` gives a rational face cap.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### Monotonicity from a derivative -/

theorem ss_le_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z) (hnn : ∀ z ∈ Ioo x y, 0 ≤ f' z) : f x ≤ f y := by
  have hmono : MonotoneOn f (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (Ioo_subset_Icc_self hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z (Ioo_subset_Icc_self hz)).deriv]
      exact hnn z hz
  exact hmono (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy

theorem ss_lt_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z) (hpos : ∀ z ∈ Ioo x y, 0 < f' z) : f x < f y := by
  have hmono : StrictMonoOn f (Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x y)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z (Ioo_subset_Icc_self hz)).deriv]
      exact hpos z hz
  exact hmono (left_mem_Icc.2 hxy.le) (right_mem_Icc.2 hxy.le) hxy

/-! ### Logarithm bounds -/

/-- `log z ≤ (z - z⁻¹)/2` for `z ≥ 1` (derivative `(z - 1)²/(2z²)`). -/
theorem ss_log_le_half {z : ℝ} (hz : 1 ≤ z) : Real.log z ≤ (z - z⁻¹) / 2 := by
  have h := ss_le_of_deriv (f := fun t => (t - t⁻¹) / 2 - Real.log t)
    (f' := fun t => (t - 1) ^ 2 / (2 * t ^ 2)) hz (fun t ht => ?_) (fun t ht => by positivity)
  · simp only [inv_one, sub_self, zero_div, Real.log_one] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have := (((hasDerivAt_id' t).sub (hasDerivAt_inv ht.ne')).div_const 2).sub
    (Real.hasDerivAt_log ht.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `2(z - 1)/(z + 1) ≤ log z` for `z ≥ 1` (derivative `(z - 1)²/(z(z + 1)²)`). -/
theorem ss_log_ge_pade {z : ℝ} (hz : 1 ≤ z) : 2 * (z - 1) / (z + 1) ≤ Real.log z := by
  have h := ss_le_of_deriv (f := fun t => Real.log t - 2 * (t - 1) / (t + 1))
    (f' := fun t => (t - 1) ^ 2 / (t * (t + 1) ^ 2)) hz (fun t ht => ?_) (fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity)
  · simp only [Real.log_one, sub_self, mul_zero, zero_div] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have h1 : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 t := by
    simpa using ((hasDerivAt_id t).sub_const 1).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => t + 1) 1 t := by simpa using (hasDerivAt_id t).add_const 1
  have := (Real.hasDerivAt_log ht.ne').sub (h1.div h2 (by positivity))
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `2w + (2/3)w³ ≤ log z` for `z ≥ 1`, `w = (z - 1)/(z + 1)` (two terms of `2 artanh w`;
derivative `(z - 1)⁴/(z(z + 1)⁴)`). -/
theorem ss_log_ge_cubic {z : ℝ} (hz : 1 ≤ z) :
    2 * ((z - 1) / (z + 1)) + 2 / 3 * ((z - 1) / (z + 1)) ^ 3 ≤ Real.log z := by
  have h := ss_le_of_deriv
    (f := fun t => Real.log t - (2 * ((t - 1) / (t + 1)) + 2 / 3 * ((t - 1) / (t + 1)) ^ 3))
    (f' := fun t => (t - 1) ^ 4 / (t * (t + 1) ^ 4)) hz (fun t ht => ?_) (fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity)
  · simp only [Real.log_one, sub_self, zero_div, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have hw : HasDerivAt (fun t : ℝ => (t - 1) / (t + 1)) (2 / (t + 1) ^ 2) t := by
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 t := by simpa using (hasDerivAt_id t).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => t + 1) 1 t := by simpa using (hasDerivAt_id t).add_const 1
    refine (h1.div h2 (by positivity)).congr_deriv ?_
    field_simp
    ring
  have := (Real.hasDerivAt_log ht.ne').sub ((hw.const_mul 2).add (((hw.mul hw).mul hw).const_mul
    (2 / 3)))
  convert this using 1
  · funext s; simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; ring
  · simp only [Pi.mul_apply]
    field_simp
    ring

/-- `log z ≤ (z - 1)(z² + 10z + 1)/(6z(z + 1))` for `z ≥ 1` (derivative
`(z - 1)⁴/(6z²(z + 1)²)`). -/
theorem ss_log_le_pade3 {z : ℝ} (hz : 1 ≤ z) :
    Real.log z ≤ (z - 1) * (z ^ 2 + 10 * z + 1) / (6 * z * (z + 1)) := by
  have h := ss_le_of_deriv
    (f := fun t => (t - 1) * (t ^ 2 + 10 * t + 1) / (6 * t * (t + 1)) - Real.log t)
    (f' := fun t => (t - 1) ^ 4 / (6 * t ^ 2 * (t + 1) ^ 2)) hz (fun t ht => ?_)
    (fun t ht => by positivity)
  · simp only [sub_self, zero_mul, zero_div, Real.log_one] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have h1 : HasDerivAt (fun t : ℝ => (t - 1) * (t ^ 2 + 10 * t + 1))
      (3 * t ^ 2 + 18 * t - 9) t := by
    have := ((hasDerivAt_id' t).sub_const 1).mul
      ((((hasDerivAt_id' t).mul (hasDerivAt_id' t)).add ((hasDerivAt_id' t).const_mul 10)).add_const 1)
    convert this using 1
    · funext s; simp only [Pi.mul_apply, Pi.add_apply]; ring
    · simp only [Pi.mul_apply, Pi.add_apply]; ring
  have h2 : HasDerivAt (fun t : ℝ => 6 * t * (t + 1)) (12 * t + 6) t := by
    have := ((hasDerivAt_id' t).const_mul 6).mul ((hasDerivAt_id' t).add_const 1)
    convert this using 1
    · ring
  have := (h1.div h2 (by positivity)).sub (Real.hasDerivAt_log ht.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-! ### The turn secant as an average -/

/-- The integrand `g_B(t) = 1 - Bt/(B + t)²` of the secant. -/
noncomputable def ss_gB (B t : ℝ) : ℝ := 1 - B * t / (B + t) ^ 2

/-- A primitive of `g_B`: `F_B(t) = t - B²/(t + B) - B log(t + B)`. -/
noncomputable def ss_FB (B t : ℝ) : ℝ := t - B ^ 2 / (t + B) - B * Real.log (t + B)

theorem ss_FB_hasDerivAt {B t : ℝ} (hB : 0 < B) (ht : 0 < t) : HasDerivAt (ss_FB B) (ss_gB B t) t := by
  have hs : 0 < t + B := by linarith
  have h1 : HasDerivAt (fun t : ℝ => t + B) 1 t := by simpa using (hasDerivAt_id t).add_const B
  have := ((hasDerivAt_id' t).sub ((hasDerivAt_const t (B ^ 2)).div h1 hs.ne')).sub
    ((h1.log hs.ne').const_mul B)
  refine this.congr_deriv ?_
  unfold ss_gB
  field_simp
  ring

/-- `m2g A B = g_B(A)`. -/
theorem ss_m2g_eq {A B : ℝ} (h : 0 < A + B) : m2g A B = ss_gB B A := by
  unfold m2g ss_gB
  have : B + A ≠ 0 := by linarith
  field_simp
  ring

/-- **The secant integrates its integrand**: `(P - A) Sec(A, B, P) = F_B(P) - F_B(A)`. -/
theorem ss_sec_mul {A B P : ℝ} (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) :
    (P - A) * m2Sec A B P = ss_FB B P - ss_FB B A := by
  by_cases h : A = P
  · subst h; ring
  rw [m2Sec_of_ne h, Real.log_div (by positivity) (by positivity)]
  have hPA : P - A ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  unfold ss_FB
  rw [add_comm P B, add_comm A B]
  field_simp
  ring

/-- **Additivity of the secant integral** over `[A, M] ∪ [M, P]`. -/
theorem ss_sec_add {A B M P : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 0 < M) (hP : 0 < P) :
    (P - A) * m2Sec A B P = (M - A) * m2Sec A B M + (P - M) * m2Sec M B P := by
  rw [ss_sec_mul hA hB hP, ss_sec_mul hA hB hM, ss_sec_mul hM hB hP]
  ring

/-- A lower bound of the integrand on `(A, P)` bounds the secant from below. -/
theorem ss_sec_ge {A B P L : ℝ} (hA : 0 < A) (hB : 0 < B) (hAP : A < P)
    (h : ∀ t ∈ Ioo A P, L ≤ ss_gB B t) : L ≤ m2Sec A B P := by
  have hP : 0 < P := by linarith
  have hm := ss_le_of_deriv (f := fun t => ss_FB B t - L * t) (f' := fun t => ss_gB B t - L) hAP.le
    (fun t ht => by
      have := (ss_FB_hasDerivAt hB (lt_of_lt_of_le hA ht.1)).sub ((hasDerivAt_id' t).const_mul L)
      convert this using 1; ring)
    (fun t ht => by linarith [h t ht])
  have e := ss_sec_mul hA hB hP
  have : L * (P - A) ≤ (P - A) * m2Sec A B P := by rw [e]; linarith
  nlinarith

/-- An upper bound of the integrand on `(A, P)` bounds the secant from above. -/
theorem ss_sec_le {A B P L : ℝ} (hA : 0 < A) (hB : 0 < B) (hAP : A < P)
    (h : ∀ t ∈ Ioo A P, ss_gB B t ≤ L) : m2Sec A B P ≤ L := by
  have hP : 0 < P := by linarith
  have hm := ss_le_of_deriv (f := fun t => L * t - ss_FB B t) (f' := fun t => L - ss_gB B t) hAP.le
    (fun t ht => by
      have := ((hasDerivAt_id' t).const_mul L).sub (ss_FB_hasDerivAt hB (lt_of_lt_of_le hA ht.1))
      convert this using 1; ring)
    (fun t ht => by linarith [h t ht])
  have e := ss_sec_mul hA hB hP
  have : (P - A) * m2Sec A B P ≤ L * (P - A) := by rw [e]; linarith
  nlinarith

/-- A strict lower bound of the integrand on `(A, P)` bounds the secant strictly from below. -/
theorem ss_sec_gt {A B P L : ℝ} (hA : 0 < A) (hB : 0 < B) (hAP : A < P)
    (h : ∀ t ∈ Ioo A P, L < ss_gB B t) : L < m2Sec A B P := by
  have hP : 0 < P := by linarith
  have hm := ss_lt_of_deriv (f := fun t => ss_FB B t - L * t) (f' := fun t => ss_gB B t - L) hAP
    (fun t ht => by
      have := (ss_FB_hasDerivAt hB (lt_of_lt_of_le hA ht.1)).sub ((hasDerivAt_id' t).const_mul L)
      convert this using 1; ring)
    (fun t ht => by linarith [h t ht])
  have e := ss_sec_mul hA hB hP
  have : L * (P - A) < (P - A) * m2Sec A B P := by rw [e]; linarith
  nlinarith

/-- The integrand is monotone away from `B`: `g_B(t) - g_B(t') = B(t' - t)(B² - tt')/((B+t)²(B+t')²)`. -/
theorem ss_gB_sub {B t t' : ℝ} (hB : 0 < B) (ht : 0 < t) (ht' : 0 < t') :
    ss_gB B t - ss_gB B t' = B * (t' - t) * (B ^ 2 - t * t') / ((B + t) ^ 2 * (B + t') ^ 2) := by
  unfold ss_gB
  have h1 : B + t ≠ 0 := by positivity
  have h2 : B + t' ≠ 0 := by positivity
  field_simp
  ring

/-- On `(0, B]` the integrand decreases: the secant over `[A, P] ⊆ (0, B]` exceeds `g_B(P)`. -/
theorem ss_sec_gt_right {A B P : ℝ} (hA : 0 < A) (hAP : A < P) (hPB : P ≤ B) :
    ss_gB B P < m2Sec A B P := by
  have hB : 0 < B := by linarith
  refine ss_sec_gt hA hB hAP fun t ht => ?_
  have ht0 : 0 < t := by linarith [ht.1]
  have hP : 0 < P := by linarith
  have e := ss_gB_sub hB ht0 hP
  have : 0 < B * (P - t) * (B ^ 2 - t * P) / ((B + t) ^ 2 * (B + P) ^ 2) := by
    have h1 : 0 < P - t := by linarith [ht.2]
    have h2 : 0 < B ^ 2 - t * P := by nlinarith [ht.2]
    positivity
  linarith

/-- The weak form of `ss_sec_gt_right`, allowing `A = P`. -/
theorem ss_sec_ge_right {A B P : ℝ} (hA : 0 < A) (hAP : A ≤ P) (hPB : P ≤ B) :
    ss_gB B P ≤ m2Sec A B P := by
  rcases eq_or_lt_of_le hAP with h | h
  · subst h; rw [m2Sec_self, ss_m2g_eq (by linarith)]
  · exact (ss_sec_gt_right hA h hPB).le

/-- On `(0, B]` the integrand decreases: the secant over `[A, P] ⊆ (0, B]` is at most `g_B(A)`. -/
theorem ss_sec_le_left {A B P : ℝ} (hA : 0 < A) (hAP : A ≤ P) (hPB : P ≤ B) :
    m2Sec A B P ≤ ss_gB B A := by
  have hB : 0 < B := by linarith
  rcases eq_or_lt_of_le hAP with h | h
  · subst h; rw [m2Sec_self, ss_m2g_eq (by linarith)]
  refine ss_sec_le hA hB h fun t ht => ?_
  have ht0 : 0 < t := by linarith [ht.1]
  have e := ss_gB_sub hB hA ht0
  have : 0 ≤ B * (t - A) * (B ^ 2 - A * t) / ((B + A) ^ 2 * (B + t) ^ 2) := by
    have h1 : 0 ≤ t - A := by linarith [ht.1]
    have h2 : 0 ≤ B ^ 2 - A * t := by nlinarith [ht.2]
    positivity
  linarith

/-- On `[B, ∞)` the integrand increases: the secant over `[B, P]` is at most `g_B(P)`. -/
theorem ss_sec_le_right {B P : ℝ} (hB : 0 < B) (hBP : B ≤ P) : m2Sec B B P ≤ ss_gB B P := by
  rcases eq_or_lt_of_le hBP with h | h
  · subst h; rw [m2Sec_self, ss_m2g_eq (by linarith)]
  refine ss_sec_le hB hB h fun t ht => ?_
  have ht0 : 0 < t := by linarith [ht.1]
  have hP : 0 < P := by linarith
  have e := ss_gB_sub hB ht0 hP
  have : B * (P - t) * (B ^ 2 - t * P) / ((B + t) ^ 2 * (B + P) ^ 2) ≤ 0 := by
    have h1 : 0 ≤ P - t := by linarith [ht.2]
    have h2 : B ^ 2 - t * P ≤ 0 := by nlinarith [ht.1]
    have : B * (P - t) * (B ^ 2 - t * P) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB.le h1) h2
    exact div_nonpos_of_nonpos_of_nonneg this (by positivity)
  linarith

/-- **The equal-centre average comparison**: for `a < B < C`, `Sec(a, B, C) < Sec(a, C, B)`. Along
`t = a + s(C - a)`, `t' = a + s(B - a)` the integrands satisfy `g_B(t) < g_C(t')` for `s < 1`. -/
theorem ss_sec_cross {a B C : ℝ} (ha : 0 < a) (haB : a < B) (hBC : B < C) :
    m2Sec a B C < m2Sec a C B := by
  have hB : 0 < B := by linarith
  have hC : 0 < C := by linarith
  have hCa : 0 < C - a := by linarith
  have hBa : 0 < B - a := by linarith
  have hd := ss_lt_of_deriv (x := 0) (y := 1)
    (f := fun s => ss_FB C (a + s * (B - a)) / (B - a) - ss_FB B (a + s * (C - a)) / (C - a))
    (f' := fun s => ss_gB C (a + s * (B - a)) - ss_gB B (a + s * (C - a))) zero_lt_one
    (fun s hs => by
      have i1 : HasDerivAt (fun s : ℝ => a + s * (B - a)) (B - a) s := by
        simpa using ((hasDerivAt_id' s).mul_const (B - a)).const_add a
      have i2 : HasDerivAt (fun s : ℝ => a + s * (C - a)) (C - a) s := by
        simpa using ((hasDerivAt_id' s).mul_const (C - a)).const_add a
      have p1 : 0 < a + s * (B - a) := by nlinarith [hs.1]
      have p2 : 0 < a + s * (C - a) := by nlinarith [hs.1]
      have := (((ss_FB_hasDerivAt hC p1).comp s i1).div_const (B - a)).sub
        (((ss_FB_hasDerivAt hB p2).comp s i2).div_const (C - a))
      convert this using 1
      · funext x; simp only [Pi.sub_apply, Function.comp]
      · field_simp)
    (fun s hs => by
      set t := a + s * (C - a) with htdef
      set t' := a + s * (B - a) with ht'def
      have ht : 0 < t := by nlinarith [hs.1]
      have ht' : 0 < t' := by nlinarith [hs.1]
      have htC : t < C := by nlinarith [hs.2]
      have ht'B : t' < B := by nlinarith [hs.2]
      have hk1 : 0 < t * C - t' * B := by
        have : t * C - t' * B = (C - B) * (a + s * (C + B - a)) := by rw [htdef, ht'def]; ring
        rw [this]
        exact mul_pos (by linarith) (by nlinarith [hs.1])
      have hk2 : 0 < B * C - t * t' := by nlinarith [mul_lt_mul'' htC ht'B ht.le ht'.le]
      have e : ss_gB C t' - ss_gB B t =
          (t * C - t' * B) * (B * C - t * t') / ((B + t) ^ 2 * (C + t') ^ 2) := by
        unfold ss_gB
        have h1 : B + t ≠ 0 := by positivity
        have h2 : C + t' ≠ 0 := by positivity
        field_simp
        ring
      rw [e]
      positivity)
  have e1 := ss_sec_mul ha hB hC
  have e2 := ss_sec_mul ha hC hB
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at hd
  have k1 : m2Sec a B C = (ss_FB B C - ss_FB B a) / (C - a) := by
    rw [eq_div_iff hCa.ne', mul_comm, e1]
  have k2 : m2Sec a C B = (ss_FB C B - ss_FB C a) / (B - a) := by
    rw [eq_div_iff hBa.ne', mul_comm, e2]
  rw [k1, k2, sub_div, sub_div]
  linarith




/-- A strict upper bound on the integrand gives a strict upper bound on its mean. -/
theorem ss_sec_lt {A B P L : ℝ} (hA : 0 < A) (hB : 0 < B) (hAP : A < P)
    (h : ∀ t ∈ Ioo A P, ss_gB B t < L) : m2Sec A B P < L := by
  have hP : 0 < P := by linarith
  have hm := ss_lt_of_deriv (f := fun t => L * t - ss_FB B t) (f' := fun t => L - ss_gB B t) hAP
    (fun t ht => by
      have hd := ((hasDerivAt_id' t).const_mul L).sub (ss_FB_hasDerivAt hB (lt_of_lt_of_le hA ht.1))
      convert hd using 1; ring)
    (fun t ht => by linarith only [h t ht])
  have he := ss_sec_mul hA hB hP
  have : (P - A) * m2Sec A B P < L * (P - A) := by rw [he]; linarith only [hm]
  nlinarith only [this, hAP]

/-- On the decreasing side of the kernel, its interval mean is below its left value. -/
theorem ss_sec_lt_left {A B P : ℝ} (hA : 0 < A) (hAP : A < P) (hPB : P ≤ B) :
    m2Sec A B P < ss_gB B A := by
  have hB : 0 < B := by linarith
  refine ss_sec_lt hA hB hAP fun t ht => ?_
  have ht0 : 0 < t := by linarith [ht.1]
  have he := ss_gB_sub hB hA ht0
  have hpos : 0 < B * (t - A) * (B ^ 2 - A * t) / ((B + A) ^ 2 * (B + t) ^ 2) := by
    have h1 : 0 < t - A := by linarith [ht.1]
    have h2 : 0 < B ^ 2 - A * t := by nlinarith [ht.2]
    positivity
  linarith only [he, hpos]

private noncomputable def ssMean_central (a : ℝ) : ℝ :=
  1 + 1 / (2 * (1 + a)) - Real.log (2 / (1 + a)) / (1 - a)

private theorem ssMean_eq {a : ℝ} (ha1 : a < 1) :
    m2Sec a 1 1 = ssMean_central a := by
  rw [m2Sec_of_ne (by linarith)]
  unfold ssMean_central
  rw [show a + 1 = 1 + a by ring]
  norm_num
  ring

private theorem ssMean_deriv {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    HasDerivAt ssMean_central ((ssMean_central a - ss_gB 1 a) / (1 - a)) a := by
  have h1 : 0 < 1 + a := by linarith
  have hb : 0 < 1 - a := by linarith
  unfold ssMean_central ss_gB
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssMean_lt_origin {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ssMean_central a < 3 / 2 - Real.log 2 := by
  have hm := ss_lt_of_deriv (f := fun s => -ssMean_central s)
    (f' := fun s => -((ssMean_central s - ss_gB 1 s) / (1 - s))) ha
    (fun s hs => (ssMean_deriv hs.1 (hs.2.trans_lt ha1)).neg)
    (fun s hs => by
      have hleft := ss_sec_lt_left (B := 1) hs.1 (hs.2.trans ha1) le_rfl
      rw [ssMean_eq (hs.2.trans ha1)] at hleft
      have hb : 0 < 1 - s := by linarith [hs.2]
      exact neg_pos.mpr (div_neg_of_neg_of_pos (sub_neg.mpr hleft) hb))
  have he : ssMean_central 0 = 3 / 2 - Real.log 2 := by norm_num [ssMean_central]
  rw [he] at hm
  linarith only [hm]

/-- The exact global central secant ceiling, given by the full interval mean. -/
theorem ss_V_lt_limit {a C : ℝ} (ha : 0 < a) (haC : a < C) : m2Sec a C C < 3 / 2 - Real.log 2 := by
  have hC : 0 < C := by linarith
  have hr : 0 < a / C := by positivity
  have hr1 : a / C < 1 := (div_lt_one hC).mpr haC
  have he : m2Sec a C C = ssMean_central (a / C) := by
    rw [m2Sec_of_ne haC.ne]
    unfold ssMean_central
    have hl : (2 : ℝ) / (1 + a / C) = (C + C) / (a + C) := by field_simp; ring
    rw [hl]
    field_simp
    ring
  rw [he]
  exact ssMean_lt_origin hr hr1

/-- A rational face cap, obtained from the exact central mean and its logarithm bound. -/
theorem ss_V_le {a C : ℝ} (ha : 0 < a) (haC : a < C) : m2Sec a C C ≤ 13 / 16 := by
  have hlog := ss_log_ge_cubic (z := 2) (by norm_num)
  norm_num at hlog
  have hcap : 3 / 2 - Real.log 2 < 13 / 16 := by linarith only [hlog]
  exact (ss_V_lt_limit ha haC).le.trans hcap.le

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.Residual

/-!
# Case M2, forward successor: rational upper bounds for the incoming secant

For the normalized incoming secant `v = Sec(t, 1 - t, t + x) = 1 + c²/W - c log W/x`
(`c = 1 - t`, `W = 1 + x`, `p = t + x`, `g = 1 - cp/W²`):

* `nsfVG`, `nsf_secN_lt_VG`: **the positive-integral bound** `v < v_G = g + (cx/W²)(T_G(x) - t)`,
  `T_G = (90 - 19x²)/(12(x² + 10x + 15))`, from
  `log(1 + x) > x(43x³ + 252x² + 390x + 180)/(12W²(x² + 10x + 15))` (`nsf_log_gt_G`, whose
  difference has derivative `x⁶/(W³(x² + 10x + 15)²)`);
* `nsfV2`, `nsf_secN_lt_V2`: the polynomial bound with `T₀ < 1/2 - x/3 + x²/12`;
* `nsfVq`, `nsf_secN_lt_Vq`: the Padé bound `v < V = 1 + c²/W - 3c(x + 2)/(x² + 6x + 6)`;
* `nsf_VG_sub_g`: `v_G - g = (cx/W²)(T_G - t)`.

Each bound is a monotone one-variable comparison of `log(1 + x)` with a rational function
(derivative sign).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The positive-integral secant majorant `v_G`. -/
noncomputable def nsfVG (t x : ℝ) : ℝ :=
  1 - (1 - t) * (t + x) / (1 + x) ^ 2 +
    (1 - t) * x / (1 + x) ^ 2 * ((90 - 19 * x ^ 2) / (12 * (x ^ 2 + 10 * x + 15)) - t)

/-- A logarithm lower bound from a derivative comparison: if `N(0) = 0`, `D > 0` on `[0, ∞)` and
`(N/D)' < 1/(1 + z)` on `(0, ∞)`, then `N(x)/D(x) < log(1 + x)` for `x > 0`. -/
theorem nsf_log_gt_of {N D N' D' : ℝ → ℝ} (h0 : N 0 = 0) (hD : ∀ z, 0 ≤ z → 0 < D z)
    (hN : ∀ z, HasDerivAt N (N' z) z) (hDd : ∀ z, HasDerivAt D (D' z) z)
    (hpos : ∀ z, 0 < z → 0 < 1 / (1 + z) - (N' z * D z - N z * D' z) / D z ^ 2)
    {x : ℝ} (hx : 0 < x) : N x / D x < Real.log (1 + x) := by
  have hmono := nsr_strictMonoOn_Ici (a := 0) (f := fun z => Real.log (1 + z) - N z / D z)
    (f' := fun z => 1 / (1 + z) - (N' z * D z - N z * D' z) / D z ^ 2) (fun z hz => ?_) hpos
  · have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
    simp only [add_zero, Real.log_one, h0, zero_div, sub_zero] at this
    linarith
  · have hz1 : (1 + z) ≠ 0 := by linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have := (h1.log hz1).sub ((hN z).div (hDd z) (hD z hz).ne')
    refine this.congr_deriv ?_
    simp

/-- `log(1 + x) > x(43x³ + 252x² + 390x + 180)/(12(x + 1)²(x² + 10x + 15))` for `x > 0`. -/
theorem nsf_log_gt_G {x : ℝ} (hx : 0 < x) :
    x * (43 * x ^ 3 + 252 * x ^ 2 + 390 * x + 180) / (12 * (x + 1) ^ 2 * (x ^ 2 + 10 * x + 15)) <
      Real.log (1 + x) := by
  refine nsf_log_gt_of (N := fun z => z * (43 * z ^ 3 + 252 * z ^ 2 + 390 * z + 180))
    (D := fun z => 12 * (z + 1) ^ 2 * (z ^ 2 + 10 * z + 15))
    (N' := fun z => 172 * z ^ 3 + 756 * z ^ 2 + 780 * z + 180)
    (D' := fun z => 24 * (z + 1) * (z ^ 2 + 10 * z + 15) + 12 * (z + 1) ^ 2 * (2 * z + 10))
    (by norm_num) (fun z hz => by positivity) (fun z => ?_) (fun z => ?_) (fun z hz => ?_) hx
  · have h := ((((hasDerivAt_pow 4 z).const_mul (43 : ℝ)).add ((hasDerivAt_pow 3 z).const_mul (252 : ℝ))).add
      ((hasDerivAt_pow 2 z).const_mul (390 : ℝ))).add ((hasDerivAt_id z).const_mul (180 : ℝ))
    refine (h.congr_deriv (by norm_num; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp; ring
  · have h := ((((((hasDerivAt_pow 4 z).const_mul (12 : ℝ)).add ((hasDerivAt_pow 3 z).const_mul (144 : ℝ))).add
      ((hasDerivAt_pow 2 z).const_mul (432 : ℝ))).add ((hasDerivAt_id z).const_mul (480 : ℝ))).add_const (180 : ℝ))
    refine (h.congr_deriv (by norm_num; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp; ring
  · have e : 1 / (1 + z) - ((172 * z ^ 3 + 756 * z ^ 2 + 780 * z + 180) *
        (12 * (z + 1) ^ 2 * (z ^ 2 + 10 * z + 15)) - z * (43 * z ^ 3 + 252 * z ^ 2 + 390 * z + 180) *
        (24 * (z + 1) * (z ^ 2 + 10 * z + 15) + 12 * (z + 1) ^ 2 * (2 * z + 10))) /
        (12 * (z + 1) ^ 2 * (z ^ 2 + 10 * z + 15)) ^ 2 =
        z ^ 6 / ((z + 1) ^ 3 * (z ^ 2 + 10 * z + 15) ^ 2) := by
      have : (1 + z) ≠ 0 := by linarith
      have : (z + 1) ≠ 0 := by linarith
      have : z ^ 2 + 10 * z + 15 ≠ 0 := by positivity
      field_simp
      ring
    rw [e]; positivity

/-- **The positive-integral secant bound** `v < v_G`, from `nsf_log_gt_G`. -/
theorem nsf_secN_lt_VG {t x : ℝ} (hx : 0 < x) (ht : t < 1) : nsrSecN t x < nsfVG t x := by
  have hl := nsf_log_gt_G hx
  have h1 : 0 < 1 - t := by linarith
  have e : nsfVG t x - nsrSecN t x = (1 - t) / x * (Real.log (1 + x) -
      x * (43 * x ^ 3 + 252 * x ^ 2 + 390 * x + 180) / (12 * (x + 1) ^ 2 * (x ^ 2 + 10 * x + 15))) := by
    unfold nsfVG nsrSecN
    have : (1 + x) ≠ 0 := by linarith
    have : (x + 1) ≠ 0 := by linarith
    have : x ^ 2 + 10 * x + 15 ≠ 0 := by positivity
    field_simp
    ring
  have : 0 < (1 - t) / x * (Real.log (1 + x) -
      x * (43 * x ^ 3 + 252 * x ^ 2 + 390 * x + 180) / (12 * (x + 1) ^ 2 * (x ^ 2 + 10 * x + 15))) :=
    mul_pos (div_pos h1 hx) (by linarith)
  linarith

/-- `v_G - g = (cx/W²)(T_G(x) - t)`. -/
theorem nsf_VG_sub_g (t x : ℝ) :
    nsfVG t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2) =
      (1 - t) * x / (1 + x) ^ 2 * ((90 - 19 * x ^ 2) / (12 * (x ^ 2 + 10 * x + 15)) - t) := by
  unfold nsfVG; ring

/-- **The integral derivative floor**: the actual floor `v ≥ g` and `v < v_G` give `t < T_G(x)`,
i.e. `12(x² + 10x + 15)t < 90 - 19x²`. -/
theorem nsf_t_lt_TG {t x v : ℝ} (ht1 : t < 1) (hx : 0 < x) (hv : v = nsrSecN t x)
    (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) :
    12 * (x ^ 2 + 10 * x + 15) * t < 90 - 19 * x ^ 2 := by
  have h := nsf_secN_lt_VG hx ht1
  rw [← hv] at h
  have e := nsf_VG_sub_g t x
  have hpos : 0 < (1 - t) * x / (1 + x) ^ 2 *
      ((90 - 19 * x ^ 2) / (12 * (x ^ 2 + 10 * x + 15)) - t) := by linarith
  have hc : 0 < (1 - t) * x / (1 + x) ^ 2 := by
    apply div_pos (mul_pos (by linarith) hx) (by positivity)
  have := pos_of_mul_pos_right hpos hc.le
  have hR : 0 < 12 * (x ^ 2 + 10 * x + 15) := by positivity
  rw [sub_pos, lt_div_iff₀ hR] at this
  linarith

/-- The polynomial secant majorant `V₂`. -/
noncomputable def nsfV2 (t x : ℝ) : ℝ :=
  1 - (1 - t) * (t + x) / (1 + x) ^ 2 + (1 - t) * x / (1 + x) ^ 2 * (1 / 2 - x / 3 + x ^ 2 / 12 - t)

/-- `log(1 + x) > x(x + 2)(6 + 6x - x²)/(12(1 + x)²)` for `x > 0` (equivalent to
`T₀ < 1/2 - x/3 + x²/12`). -/
theorem nsf_log_gt_2 {x : ℝ} (hx : 0 < x) :
    x * (x + 2) * (6 + 6 * x - x ^ 2) / (12 * (1 + x) ^ 2) < Real.log (1 + x) := by
  refine nsf_log_gt_of (N := fun z => z * (z + 2) * (6 + 6 * z - z ^ 2))
    (D := fun z => 12 * (1 + z) ^ 2) (N' := fun z => -4 * z ^ 3 + 12 * z ^ 2 + 36 * z + 12)
    (D' := fun z => 24 * (1 + z))
    (by norm_num) (fun z hz => by positivity) (fun z => ?_) (fun z => ?_) (fun z hz => ?_) hx
  · have h := ((((hasDerivAt_pow 4 z).const_mul (-1 : ℝ)).add ((hasDerivAt_pow 3 z).const_mul (4 : ℝ))).add
      ((hasDerivAt_pow 2 z).const_mul (18 : ℝ))).add ((hasDerivAt_id z).const_mul (12 : ℝ))
    refine (h.congr_deriv (by norm_num; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp; ring
  · have h := ((((hasDerivAt_pow 2 z).const_mul (12 : ℝ)).add ((hasDerivAt_id z).const_mul (24 : ℝ))).add_const (12 : ℝ))
    refine (h.congr_deriv (by norm_num; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp; ring
  · have e : 1 / (1 + z) - ((-4 * z ^ 3 + 12 * z ^ 2 + 36 * z + 12) * (12 * (1 + z) ^ 2) -
        z * (z + 2) * (6 + 6 * z - z ^ 2) * (24 * (1 + z))) / (12 * (1 + z) ^ 2) ^ 2 =
        z ^ 4 / (6 * (1 + z) ^ 3) := by
      have : (1 + z) ≠ 0 := by linarith
      field_simp
      ring
    rw [e]; positivity

/-- `v < V₂`. -/
theorem nsf_secN_lt_V2 {t x : ℝ} (hx : 0 < x) (ht : t < 1) : nsrSecN t x < nsfV2 t x := by
  have hl := nsf_log_gt_2 hx
  have h1 : 0 < 1 - t := by linarith
  have e : nsfV2 t x - nsrSecN t x = (1 - t) / x * (Real.log (1 + x) -
      x * (x + 2) * (6 + 6 * x - x ^ 2) / (12 * (1 + x) ^ 2)) := by
    unfold nsfV2 nsrSecN
    have : (1 + x) ≠ 0 := by linarith
    field_simp
    ring
  have : 0 < (1 - t) / x * (Real.log (1 + x) -
      x * (x + 2) * (6 + 6 * x - x ^ 2) / (12 * (1 + x) ^ 2)) :=
    mul_pos (div_pos h1 hx) (by linarith)
  linarith

/-- The Padé secant majorant `V`. -/
noncomputable def nsfVq (t x : ℝ) : ℝ :=
  1 + (1 - t) ^ 2 / (1 + x) - 3 * (1 - t) * (x + 2) / (x ^ 2 + 6 * x + 6)

/-- `log(1 + x) > 3x(x + 2)/(x² + 6x + 6)` for `x > 0`. -/
theorem nsf_log_gt_q {x : ℝ} (hx : 0 < x) :
    3 * x * (x + 2) / (x ^ 2 + 6 * x + 6) < Real.log (1 + x) := by
  exact nsr_log_one_add_jensen hx

/-- `v < V`, from `nsf_log_gt_q`. -/
theorem nsf_secN_lt_Vq {t x : ℝ} (hx : 0 < x) (ht : t < 1) : nsrSecN t x < nsfVq t x := by
  exact nsr_secN_lt_jensen hx ht

end SmoothedOctagon

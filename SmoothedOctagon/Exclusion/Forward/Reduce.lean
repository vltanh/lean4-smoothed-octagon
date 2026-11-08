module

public import SmoothedOctagon.Exclusion.Forward.Log

/-!
# Case F: both norm residuals reduce to equal neighbours

`HAND_FORWARD_CONDITIONAL_NORM_BOUNDS` §4: at fixed `U, z, h`, the residuals `𝓔_Σ` and `𝓔_v` do not
increase with the larger neighbour `w ∈ [z, 4/3]`.

Route: instead of the derivative identities CNB (29)-(30), the increments are compared directly:
`m(w) - m(z) = α(w - z)` (`ff_m_sub_eq`), `A(w) - A(z) ≤ (w - z) B(t_w)` with
`B(t_w) = 1 - 1/T + 1/T²` (`ff_A_sub_le`, `B` increases), and, for `𝓔_Σ`, the monotonicity of
`V(w) = 3/4 + L(w, T²/W)` (CNB (28): each coefficient of `L` increases in `w`, `h f(h)/(h - 1)`
increases in `h`, and `T²/W` increases in `w`) together with `V(w) ≥ B(t_w)`.

## Main API

* `ff_psi_mono`: `f(h)/(h - 1)` increases on `(1, ∞)`.
* `ff_L_mono_h`, `ff_L_mono_w`, `ff_L_ge_sq`.
* `ff_A_sub_le`, `ff_m_sub_eq`.
* `ff_resS_le_sym`, `ff_resV_le_sym`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `f'(h) (h - 1) ≥ f(h)` for `h ≥ 1` (convexity of `f` on `[1, ∞)`, `f(1) = 0`). -/
theorem ff_f_le_slope {h : ℝ} (hh : 1 ≤ h) : ff_f h ≤ (h - 1) ^ 3 / (2 * h ^ 2) := by
  have key := ff_le_of_deriv (f := fun s ↦ (s - 1) ^ 3 / (2 * s ^ 2) - ff_f s)
    (f' := fun s ↦ (s - 1) ^ 2 / s ^ 3) hh (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have : ff_f 1 = 0 := by simp [ff_f]
    rw [this] at key
    linarith
  · have hs0 : 0 < s := by linarith [hs.1]
    have h1 := Real.hasDerivAt_log hs0.ne'
    have h2 := (hasDerivAt_id s).inv hs0.ne'
    have h3 : HasDerivAt (fun s : ℝ ↦ (s - 1) ^ 3) (3 * (s - 1) ^ 2) s := by
      convert ((hasDerivAt_id' s).sub_const 1).fun_pow 3 using 1; norm_num
    have h4 : HasDerivAt (fun s : ℝ ↦ 2 * s ^ 2) (2 * (2 * s)) s := by
      simpa using (hasDerivAt_pow 2 s).const_mul 2
    have h := (h3.div h4 (by positivity)).sub ((((hasDerivAt_id s).sub h2).div_const 2).sub h1)
    convert h using 1
    · ext y; simp [ff_f]
    · simp only [id]; field_simp; ring
  · have hs0 : 0 < s := by linarith [hs.1]
    positivity

/-- `ψ(h) = f(h)/(h - 1)` increases on `(1, ∞)`. -/
theorem ff_psi_mono {h h' : ℝ} (hh : 1 < h) (hhh : h ≤ h') :
    ff_f h / (h - 1) ≤ ff_f h' / (h' - 1) := by
  refine ff_le_of_deriv (f := fun s ↦ ff_f s / (s - 1))
    (f' := fun s ↦ ((s - 1) ^ 2 / (2 * s ^ 2) * (s - 1) - ff_f s) / (s - 1) ^ 2) hhh
    (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have hs1 : 1 < s := lt_of_lt_of_le hh hs.1
    have hs0 : 0 < s := by linarith
    have h1 := Real.hasDerivAt_log hs0.ne'
    have h2 := (hasDerivAt_id s).inv hs0.ne'
    have hf : HasDerivAt ff_f ((s - 1) ^ 2 / (2 * s ^ 2)) s := by
      have h := (((hasDerivAt_id s).sub h2).div_const 2).sub h1
      convert h using 1
      · ext y; simp [ff_f]
      · simp only [id]; field_simp; ring
    have h := hf.div ((hasDerivAt_id' s).sub_const 1) (by linarith)
    convert h using 1
    simp only [mul_one]
  · have hs1 : 1 < s := lt_of_lt_of_le hh hs.1
    apply div_nonneg _ (by positivity)
    have := ff_f_le_slope hs1.le
    have e : (s - 1) ^ 2 / (2 * s ^ 2) * (s - 1) = (s - 1) ^ 3 / (2 * s ^ 2) := by ring
    linarith

/-- `L(w, h)` increases in `h ≥ 1`. -/
theorem ff_L_mono_h {w h h' : ℝ} (hw : 1 ≤ w) (hh : 1 < h) (hhh : h ≤ h') : ff_L w h ≤ ff_L w h' := by
  unfold ff_L
  have hp := ff_psi_mono hh hhh
  have hp0 : 0 ≤ ff_f h / (h - 1) := div_nonneg (ff_f_nonneg hh.le) (by linarith)
  have hw1 : 0 < 1 + w := by linarith
  have t1 : (w - 1) * ((w - 1) + 2 * w * (h - 1)) / (4 * (1 + w) ^ 2) ≤
      (w - 1) * ((w - 1) + 2 * w * (h' - 1)) / (4 * (1 + w) ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
  have t2 : w * h / (1 + w) * (ff_f h / (h - 1)) ≤ w * h' / (1 + w) * (ff_f h' / (h' - 1)) := by
    apply mul_le_mul _ hp hp0 (div_nonneg (by nlinarith) hw1.le)
    apply div_le_div_of_nonneg_right _ hw1.le; nlinarith
  linarith

/-- `L(w, h)` increases in `w ≥ 1` (CONDITIONAL_NORM_BOUNDS (28)). -/
theorem ff_L_mono_w {w w' h : ℝ} (hw : 1 ≤ w) (hww : w ≤ w') (hh : 1 < h) :
    ff_L w h ≤ ff_L w' h := by
  have hp0 : 0 ≤ ff_f h / (h - 1) := div_nonneg (ff_f_nonneg hh.le) (by linarith)
  have e : ∀ x : ℝ, 0 < 1 + x → ff_L x h = (x - 1) ^ 2 / (4 * (1 + x) ^ 2) +
      x * (x - 1) / (2 * (1 + x) ^ 2) * (h - 1) + x / (1 + x) * (h * (ff_f h / (h - 1))) := by
    intro x hx; unfold ff_L; field_simp; ring
  rw [e w (by linarith), e w' (by linarith)]
  have hw1 : 0 < 1 + w := by linarith
  have hw1' : 0 < 1 + w' := by linarith
  have c1 : (w - 1) ^ 2 / (4 * (1 + w) ^ 2) ≤ (w' - 1) ^ 2 / (4 * (1 + w') ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (w - 1) * (1 + w') ≤ (w' - 1) * (1 + w) := by nlinarith
    have h0 : 0 ≤ (w - 1) * (1 + w') := by nlinarith
    nlinarith [mul_le_mul this this h0 (by nlinarith)]
  have c2 : w * (w - 1) / (2 * (1 + w) ^ 2) ≤ w' * (w' - 1) / (2 * (1 + w') ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hww) (sub_nonneg.2 hw), mul_nonneg (sub_nonneg.2 hww)
      (mul_nonneg (sub_nonneg.2 hw) (sub_nonneg.2 hw)), mul_nonneg (sub_nonneg.2 hww)
      (mul_nonneg (sub_nonneg.2 hww) (sub_nonneg.2 hw))]
  have c3 : w / (1 + w) ≤ w' / (1 + w') := by
    rw [div_le_div_iff₀ hw1 hw1']; nlinarith
  have hq : 0 ≤ h * (ff_f h / (h - 1)) := mul_nonneg (by linarith) hp0
  have := mul_le_mul_of_nonneg_right c2 (by linarith : (0 : ℝ) ≤ h - 1)
  have := mul_le_mul_of_nonneg_right c3 hq
  linarith

/-- `L(w, h) ≥ (w - 1)²/(4(1 + w)²) = B(t_w) - 3/4` for `w ≥ 1`, `h ≥ 1`. -/
theorem ff_L_ge_sq {w h : ℝ} (hw : 1 ≤ w) (hh : 1 < h) :
    (w - 1) ^ 2 / (4 * (1 + w) ^ 2) ≤ ff_L w h := by
  unfold ff_L
  have hp0 : 0 ≤ ff_f h / (h - 1) := div_nonneg (ff_f_nonneg hh.le) (by linarith)
  have t1 : (w - 1) ^ 2 / (4 * (1 + w) ^ 2) ≤ (w - 1) * ((w - 1) + 2 * w * (h - 1)) / (4 * (1 + w) ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have t2 : 0 ≤ w * h / (1 + w) * (ff_f h / (h - 1)) :=
    mul_nonneg (div_nonneg (by nlinarith) (by linarith)) hp0
  linarith

/-- `A(w) - A(z) ≤ (w - z)(1 - 1/T + 1/T²)` for `1 ≤ z ≤ w`. -/
theorem ff_A_sub_le {U z w : ℝ} (hU : 0 < U) (hz : 1 ≤ z) (hzw : z ≤ w) :
    ff_A U z w - ff_A U z z ≤ (w - z) * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2) := by
  set B := 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 with hB
  have key := ff_le_of_deriv (f := fun s ↦ s * B - ff_A U z s)
    (f' := fun s ↦ B - (1 - 1 / (1 + s) + 1 / (1 + s) ^ 2)) hzw (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · linarith
  · have hs1 : 0 < 1 + s := by linarith [hs.1]
    have hK : 0 < 1 + U := by linarith
    have hz0 : 0 < 1 + z := by linarith
    have hlog : HasDerivAt (fun s ↦ Real.log (ff_q U z s)) (1 / (1 + s)) s := by
      have hq : HasDerivAt (fun s ↦ (1 + z) * (1 + s) / (1 + U)) ((1 + z) * 1 / (1 + U)) s :=
        (((hasDerivAt_id' s).const_add 1).const_mul (1 + z)).div_const (1 + U)
      have hq0 : (1 + z) * (1 + s) / (1 + U) ≠ 0 := by positivity
      have := hq.log hq0
      show HasDerivAt (fun s ↦ Real.log ((1 + z) * (1 + s) / (1 + U))) _ s
      refine this.congr_deriv ?_
      field_simp
    have hinv : HasDerivAt (fun s : ℝ ↦ 1 / (1 + s)) (-1 / (1 + s) ^ 2) s := by
      have := ((hasDerivAt_id' s).const_add 1).inv hs1.ne'
      convert this using 1
      · ext y; simp
    have hA : HasDerivAt (fun s ↦ ff_A U z s) (1 - 1 / (1 + s) + 1 / (1 + s) ^ 2) s := by
      have := (((((hasDerivAt_id' s).const_add (1 + z)).sub_const (1 / (1 + z))).sub hinv).add_const
        (1 / (1 + U))).sub hlog
      have h2 : HasDerivAt (fun s ↦ ff_A U z s) (1 - -1 / (1 + s) ^ 2 - 1 / (1 + s)) s := this
      exact h2.congr_deriv (by ring)
    have := ((hasDerivAt_id' s).mul_const B).sub hA
    convert this using 1
    ring
  · have hs0 : 1 ≤ s := le_trans hz hs.1
    have hs1 : 0 < 1 + s := by linarith
    have hw1 : 0 < 1 + w := by linarith
    -- `c ↦ 1 - c + c²` decreases on `c ≤ 1/2`, and `1/(1 + s) ≥ 1/(1 + w)`
    have c1 : 1 / (1 + w) ≤ 1 / (1 + s) := one_div_le_one_div_of_le hs1 (by linarith [hs.2])
    have c2 : 1 / (1 + s) ≤ 1 / 2 := by rw [div_le_div_iff₀ hs1 (by norm_num)]; linarith
    have e1 : 1 / (1 + w) ^ 2 = (1 / (1 + w)) ^ 2 := (one_div_pow _ _).symm
    have e2 : 1 / (1 + s) ^ 2 = (1 / (1 + s)) ^ 2 := (one_div_pow _ _).symm
    rw [hB, e1, e2]
    nlinarith [mul_nonneg (sub_nonneg.2 c1) (by linarith : (0 : ℝ) ≤ 1 - 1 / (1 + s) - 1 / (1 + w))]

/-- `m(w) - m(z) = α(w - z)` (`m` is affine in `w`, CNB (27)). -/
theorem ff_m_sub_eq {U z w h : ℝ} (hU : 0 < U) (hz : 0 < z) :
    ff_m U z w h - ff_m U z z h = ff_alpha U z h * (w - z) := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  unfold ff_m ff_alpha ff_q
  field_simp
  ring

theorem ff_alpha_pos {U z h : ℝ} (hU : 0 < U) (hz : 0 < z) (hh : 1 ≤ h) : 0 < ff_alpha U z h := by
  unfold ff_alpha
  apply div_pos _ (by positivity)
  apply mul_pos (by linarith); nlinarith

/-- `r = αA - B - (3/4)(n + m)` restated through `ff_r` differences: the `w`-dependence of `r` is
`α(A(w) - A(z)) - (3/4)(m(w) - m(z))`. -/
private lemma ff_r_sub {U z w h : ℝ} (_hU : 0 < U) (hz : 0 < z) (hw : 0 < w) (_hh : 0 < h)
    (hr : ∀ w' : ℝ, 0 < w' → ff_alpha U z h * ff_A U z w' - ff_B U z h =
      3 / 4 * (ff_n U z h + ff_m U z w' h) + ff_r U z w' h) :
    ff_r U z w h - ff_r U z z h = ff_alpha U z h * (ff_A U z w - ff_A U z z) -
      3 / 4 * (ff_m U z w h - ff_m U z z h) := by
  have h1 := hr w hw
  have h2 := hr z hz
  linear_combination h2 - h1

/-- **`𝓔_v` reduces to equal neighbours** (CONDITIONAL_NORM_BOUNDS (30)). -/
theorem ff_resV_le_sym' {U z w h : ℝ} (hU : 0 < U) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hw : w ≤ 4 / 3) (hh : 1 < h)
    (hr : ∀ w' : ℝ, 0 < w' → ff_alpha U z h * ff_A U z w' - ff_B U z h =
      3 / 4 * (ff_n U z h + ff_m U z w' h) + ff_r U z w' h) :
    ff_resV U z w h ≤ ff_resV U z z h := by
  have hrs := ff_r_sub (U := U) (z := z) (w := w) (h := h) hU (by linarith) (by linarith) (by linarith) hr
  have hms := ff_m_sub_eq (w := w) (h := h) hU (by linarith : 0 < z)
  have hA := ff_A_sub_le hU hz hzw
  have hα := ff_alpha_pos (z := z) hU (by linarith) hh.le
  have hw1 : 0 < 1 + w := by linarith
  have hBw : 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 ≤ 37 / 49 := by
    have c1 : 3 / 7 ≤ 1 / (1 + w) := by rw [div_le_div_iff₀ (by norm_num) hw1]; linarith
    have c2 : 1 / (1 + w) ≤ 1 / 2 := by rw [div_le_div_iff₀ hw1 (by norm_num)]; linarith
    have : 1 / (1 + w) ^ 2 = (1 / (1 + w)) ^ 2 := (one_div_pow _ _).symm
    rw [this]; nlinarith
  have key : ff_resV U z w h - ff_resV U z z h = ff_alpha U z h * (ff_A U z w - ff_A U z z) -
      49 / 64 * (ff_alpha U z h * (w - z)) := by
    unfold ff_resV; rw [← hms]; linear_combination hrs
  have h1 := mul_le_mul_of_nonneg_left hA hα.le
  have h2 : ff_alpha U z h * ((w - z) * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2)) ≤
      ff_alpha U z h * ((w - z) * (37 / 49)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBw (by linarith)) hα.le
  have h3 : 0 ≤ ff_alpha U z h * (w - z) := mul_nonneg hα.le (by linarith)
  nlinarith

/-- **`𝓔_Σ` reduces to equal neighbours** (CONDITIONAL_NORM_BOUNDS (29)), given `m - n ≥ 0`. -/
theorem ff_resS_le_sym' {U z w h : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hw : w ≤ 4 / 3) (hh : 1 < h) (hmn : 0 ≤ ff_m U z z h - ff_n U z h)
    (hr : ∀ w' : ℝ, 0 < w' → ff_alpha U z h * ff_A U z w' - ff_B U z h =
      3 / 4 * (ff_n U z h + ff_m U z w' h) + ff_r U z w' h) :
    ff_resS U z w h ≤ ff_resS U z z h := by
  have hU0 : 0 < U := by linarith
  have hrs := ff_r_sub (U := U) (z := z) (w := w) (h := h) hU0 (by linarith) (by linarith) (by linarith) hr
  have hms := ff_m_sub_eq (w := w) (h := h) hU0 (by linarith : 0 < z)
  have hA := ff_A_sub_le hU0 hz hzw
  have hα := ff_alpha_pos (z := z) hU0 (by linarith) hh.le
  -- `I(w) = T²/W` increases and exceeds one
  set Iz := (1 + z) ^ 2 / (z ^ 2 + U) with hIz
  set Iw := (1 + w) ^ 2 / (w ^ 2 + U) with hIw
  have hIz1 : 1 < Iz := by rw [hIz, lt_div_iff₀ (by positivity)]; nlinarith
  have hII : Iz ≤ Iw := by
    rw [hIz, hIw, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 + w) ^ 2 * (z ^ 2 + U) - (1 + z) ^ 2 * (w ^ 2 + U) =
        (w - z) * (U * (w + z + 2) - 2 * w * z - w - z) := by ring
    have h2 : 0 ≤ U * (w + z + 2) - 2 * w * z - w - z := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hzw) h2]
  have hLL : ff_L z Iz ≤ ff_L w Iw :=
    le_trans (ff_L_mono_w hz hzw hIz1) (ff_L_mono_h (le_trans hz hzw) hIz1 hII)
  have hLsq := ff_L_ge_sq (le_trans hz hzw) (lt_of_lt_of_le hIz1 hII)
  have hw1 : 0 < 1 + w := by linarith
  have hBw : 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 - 3 / 4 = (w - 1) ^ 2 / (4 * (1 + w) ^ 2) := by
    field_simp; ring
  have key : ff_resS U z w h - ff_resS U z z h =
      ff_alpha U z h * (ff_A U z w - ff_A U z z) - 3 / 4 * (ff_alpha U z h * (w - z)) -
        (ff_alpha U z h * (w - z) * ff_L w Iw + (ff_m U z z h - ff_n U z h) * (ff_L w Iw - ff_L z Iz)) := by
    unfold ff_resS; rw [← hIz, ← hIw, ← hms]; linear_combination hrs
  rw [← sub_nonpos, key]
  have h1 := mul_le_mul_of_nonneg_left hA hα.le
  have h3 : 0 ≤ ff_alpha U z h * (w - z) := mul_nonneg hα.le (by linarith)
  have h4 := mul_nonneg hmn (sub_nonneg.2 hLL)
  have h5 := mul_le_mul_of_nonneg_left hLsq h3
  have e5 : ff_alpha U z h * ((w - z) * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2)) =
      ff_alpha U z h * (w - z) * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 - 3 / 4) +
        3 / 4 * (ff_alpha U z h * (w - z)) := by ring
  rw [hBw] at e5
  linarith

end SmoothedOctagon

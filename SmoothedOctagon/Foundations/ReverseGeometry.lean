module

public import SmoothedOctagon.Foundations.LowCostWinding
public import SmoothedOctagon.Foundations.BalancedClock
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# Reconstructing a balanced disk from a low-cost cyclic frame

The region is the radial hull of the first contact curve. Simplicity is proved from
winding: the reflected first row turns once, and the determinant-one identity
prevents the first column from being opposite to that row. The resulting continuous
angle comparison forces the first contact curve to turn once as well. Its positive
angular derivative then gives injectivity on the full period.

The upstream local-convexity theorem supplies convexity from the actual a.e.
curvature and Lipschitz derivative data. No simple curve or convex disk is assumed.
The hypotheses describe a global cyclic smooth extension; constructing that
extension from an integral-admissible trajectory is a separate analytic step.

Source draft only: compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Set Real Matrix PlaneCurve SmoothedPolygons

/-- The six contact curves associated with a global matrix frame. -/
noncomputable def frameContact (g : ℝ → Mat2) (j : ZMod 6) (t : ℝ) : Fin 2 → ℝ :=
  g t *ᵥ sixthRoot j

lemma cyclicFrame_add_nat {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) (n : ℕ) (t : ℝ) :
    g (t + n * T) = g t * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = (t + n * T) + T by push_cast; ring,
      hshift, ih, pow_succ]
    exact Matrix.mul_assoc _ _ _

lemma cyclicFrame_periodic {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) : Function.Periodic g (6 * T) := by
  intro t
  have h := cyclicFrame_add_nat hshift 6 t
  simpa only [Nat.cast_ofNat, oct_R_pow_six, Matrix.mul_one] using h

lemma frameContact_contDiff {g : ℝ → Mat2}
    (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j)) (j : ZMod 6) :
    ContDiff ℝ 1 (frameContact g j) := by
  apply contDiff_pi.mpr
  intro i
  simpa only [frameContact, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    ((hgc i 0).mul (contDiff_const (c := sixthRoot j 0))).add
      ((hgc i 1).mul (contDiff_const (c := sixthRoot j 1)))

lemma frameContact_hasDerivAt {g X : ℝ → Mat2}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t) (j : ZMod 6) (t : ℝ) :
    HasDerivAt (frameContact g j) ((g t * X t) *ᵥ sixthRoot j) t :=
  (hg t).mulVec_const (sixthRoot j)

lemma frameContact_ne_zero {g : ℝ → Mat2} (hdet : ∀ t, (g t).det = 1)
    (j : ZMod 6) (t : ℝ) : frameContact g j t ≠ 0 := by
  intro hz
  have hd : (g t).det ≠ 0 := by rw [hdet t]; norm_num
  exact oct_sixthRoot_ne_zero j (Matrix.eq_zero_of_mulVec_eq_zero hd hz)

lemma frameContact_star {g X : ℝ → Mat2}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (j : ZMod 6) (t : ℝ) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      deriv (frameContact g j) t =
        α • (frameContact g (j + 1) t - frameContact g j t) +
          β • frameContact g (j + 1) t := by
  obtain ⟨α, β, hα, hβ, h⟩ := oct_star_mulVec (hstar t) j
  refine ⟨α, β, hα, hβ, ?_⟩
  rw [(frameContact_hasDerivAt hg j t).deriv]
  simp only [frameContact]
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_sub]

lemma frameContact_cross_pos {g X : ℝ → Mat2}
    (hdet : ∀ t, (g t).det = 1)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (j : ZMod 6) (t : ℝ) :
    0 < cross (frameContact g j t) (deriv (frameContact g j) t) := by
  obtain ⟨α, β, hα, hβ, hd⟩ := frameContact_star hg hstar j t
  exact oct_det2_pos_of_star hα hβ hd ((oct_isMultiPoint_mulVec (hdet t) j).2.2)

lemma frameContact_shift {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) (j : ZMod 6) (t : ℝ) :
    frameContact g j (t + T) = frameContact g (j + 1) t := by
  simp only [frameContact]
  rw [hshift, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot]

lemma frameContact_add_nat {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) (n : ℕ) (t : ℝ) :
    frameContact g 0 (t + n * T) = frameContact g (n : ZMod 6) t := by
  simp only [frameContact]
  rw [cyclicFrame_add_nat hshift, ← Matrix.mulVec_mulVec, oct_R_pow_mulVec_sixthRoot,
    zero_add]

lemma frameContact_periodic {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) (j : ZMod 6) :
    Function.Periodic (frameContact g j) (6 * T) := by
  intro t
  simp only [frameContact, cyclicFrame_periodic hshift t]

lemma frameContact_eq_shift {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) (j : ZMod 6) :
    frameContact g j = fun t ↦ frameContact g 0 (t + j.val * T) := by
  funext t
  rw [frameContact_add_nat hshift, ZMod.natCast_zmod_val]

/-- Positive cross product gives a strictly increasing continuous angle without any
assumption of simplicity or closedness. -/
lemma angle_strictMono_of_cross_pos {γ : ℝ → Fin 2 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0)
    (hcross : ∀ t, 0 < cross (γ t) (deriv γ t)) : StrictMono (sc_angle γ) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_angle_of_contDiff hγ hne)
  intro t
  rw [sc_logDeriv_im]
  exact div_pos (hcross t) (Complex.normSq_pos.2 fun hz ↦ hne t (sc_toC_eq_zero.1 hz))

lemma continuous_angle_of_contDiff {γ : ℝ → Fin 2 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0) : Continuous (sc_angle γ) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_angle_of_contDiff hγ hne t).continuousAt

lemma sc_toC_R_mulVec (v : Fin 2 → ℝ) :
    sc_toC (R *ᵥ v) = Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) * sc_toC v := by
  have hre : (Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I)).re = 1 / 2 := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  have him : (Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I)).im = √3 / 2 := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
  apply Complex.ext
  · rw [Complex.mul_re, hre, him]
    simp [sc_toC_re, sc_toC_im, R, dotProduct, Fin.sum_univ_two]
    ring
  · rw [Complex.mul_im, hre, him]
    simp [sc_toC_re, sc_toC_im, R, dotProduct, Fin.sum_univ_two]
    ring

lemma reflectedFirstRow_shift {g : ℝ → Mat2} {T : ℝ}
    (hshift : ∀ t, g (t + T) = g t * R) (t : ℝ) :
    reflectedFirstRow g (t + T) = R *ᵥ reflectedFirstRow g t := by
  ext i
  fin_cases i <;>
    simp [reflectedFirstRow, hshift, R, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- A fixed rotation of a curve after a time shift makes its logarithmic derivative
periodic, hence makes the lifted angle additive under that time shift. -/
lemma angle_add_of_rotated_period {γ : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0)
    (hshift : ∀ t, γ (t + T) = R *ᵥ γ t) (t : ℝ) :
    sc_angle γ (t + T) = sc_angle γ t + sc_angle γ T := by
  have hD : ∀ t, HasDerivAt γ (deriv γ t) t :=
    fun t ↦ ((hγ.differentiable one_ne_zero) t).hasDerivAt
  have hdshift : ∀ t, deriv γ (t + T) = R *ᵥ deriv γ t := by
    intro t
    have hleft := (hD (t + T)).comp_add_const t T
    have hright : HasDerivAt (fun u ↦ R *ᵥ γ u) (R *ᵥ deriv γ t) t := by
      simpa using (hasDerivAtEntrywise_const R t).mulVec (hD t)
    rw [show (fun u ↦ γ (u + T)) = (fun u ↦ R *ᵥ γ u) from funext hshift] at hleft
    exact hleft.unique hright
  have hperiod : Function.Periodic (sc_logDeriv γ) T := by
    intro s
    simp only [sc_logDeriv, hshift s, hdshift s, sc_toC_R_mulVec,
      mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
  have hc := continuous_logDeriv_of_contDiff hγ hne
  have hlog : sc_log γ (t + T) = sc_log γ t + sc_log γ T := by
    simpa only [sc_log, zero_add] using
      hperiod.intervalIntegral_add_eq_add 0 t (fun a b ↦ hc.intervalIntegrable a b)
  simp only [sc_angle, hlog, Complex.add_im]

/-- The low-cost primary row angle, repeated through the actual cyclic identity,
gives one full reflected-row turn over the six-contact period. -/
lemma lowCost_reflectedFirstRow_full_angle {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 < T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hXc : Continuous X)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (hg0 : g 0 = 1)
    (hshift : ∀ t, g (t + T) = g t * R)
    (hcost : reinhardtCost T X < π) :
    sc_angle (reflectedFirstRow g) (6 * T) = 2 * π := by
  have hgT : g T = R := by simpa only [zero_add, hg0, Matrix.one_mul] using hshift 0
  have hprimary := lowCost_reflectedFirstRow_angle hT hgc hdet hXc hg hstar hg0 hgT hcost
  have hadd := angle_add_of_rotated_period (reflectedFirstRow_contDiff hgc)
    (reflectedFirstRow_ne_zero hdet) (reflectedFirstRow_shift hshift)
  have hiter : ∀ n : ℕ, sc_angle (reflectedFirstRow g) (n * T) =
      (n : ℝ) * sc_angle (reflectedFirstRow g) T := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, sc_angle_zero]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ) * T = (n : ℝ) * T + T by push_cast; ring, hadd, ih]
      push_cast
      ring
  calc
    sc_angle (reflectedFirstRow g) (6 * T) = 6 * sc_angle (reflectedFirstRow g) T := hiter 6
    _ = 2 * π := by rw [hprimary]; ring

/-- The first column cannot have an angle exactly `π` above the reflected first row.
An opposite positive-scalar relation between these vectors would force `det g ≤ 0`. -/
lemma firstContact_angle_ne_row_add_pi {g : ℝ → Mat2}
    (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hg0 : g 0 = 1) (t : ℝ) :
    sc_angle (frameContact g 0) t ≠ sc_angle (reflectedFirstRow g) t + π := by
  intro heq
  let γ := frameContact g 0
  let δ := reflectedFirstRow g
  let c : ℝ := Real.exp ((sc_log γ t).re - (sc_log δ t).re)
  change sc_angle γ t = sc_angle δ t + π at heq
  have hc : 0 < c := Real.exp_pos _
  have hγ0 : sc_toC (γ 0) = 1 := by simp [γ, frameContact, hg0, algA_sixthRoot_zero, sc_toC]
  have hδ0 : sc_toC (δ 0) = 1 := by simp [δ, reflectedFirstRow, hg0, sc_toC]
  have hγexp := toComplex_eq_exp_log_of_contDiff (frameContact_contDiff hgc 0)
    (frameContact_ne_zero hdet 0) t
  have hδexp := toComplex_eq_exp_log_of_contDiff (reflectedFirstRow_contDiff hgc)
    (reflectedFirstRow_ne_zero hdet) t
  change sc_toC (γ t) = sc_toC (γ 0) * Complex.exp (sc_log γ t) at hγexp
  change sc_toC (δ t) = sc_toC (δ 0) * Complex.exp (sc_log δ t) at hδexp
  rw [hγ0, one_mul] at hγexp
  rw [hδ0, one_mul] at hδexp
  have him : (sc_log γ t - sc_log δ t).im = π := by
    change sc_angle γ t - sc_angle δ t = π
    linarith
  have hexp : Complex.exp (sc_log γ t - sc_log δ t) = -(c : ℂ) := by
    apply Complex.ext
    · simp only [Complex.exp_re, him, Real.cos_pi, Complex.sub_re, mul_neg_one,
        Complex.neg_re, Complex.ofReal_re]
      rfl
    · simp only [Complex.exp_im, him, Real.sin_pi, mul_zero, Complex.neg_im,
        Complex.ofReal_im, neg_zero]
  have hvec : γ t = (-c) • δ t := by
    apply sc_toC_injective
    rw [sc_toC_smul, Complex.ofReal_neg, hγexp, hδexp]
    calc
      Complex.exp (sc_log γ t) =
          Complex.exp (sc_log γ t - sc_log δ t) * Complex.exp (sc_log δ t) := by
        rw [← Complex.exp_add, sub_add_cancel]
      _ = -(c : ℂ) * Complex.exp (sc_log δ t) := by rw [hexp]
  have h0 := congrFun hvec 0
  have h1 := congrFun hvec 1
  simp only [γ, δ, frameContact, algA_sixthRoot_zero, reflectedFirstRow,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_zero, add_zero, Pi.smul_apply, smul_eq_mul,
    neg_mul, mul_neg, neg_neg] at h0 h1
  have hp : g t 0 0 = 0 := by
    have hm : (1 + c) * g t 0 0 = 0 := by nlinarith [h0]
    exact (mul_eq_zero.mp hm).resolve_left (by positivity)
  have hd := hdet t
  rw [Matrix.det_fin_two, hp, h1] at hd
  nlinarith [mul_nonneg hc.le (sq_nonneg (g t 0 1))]

/-- Low cost forces the first contact curve to make exactly one turn. The proof
uses the row winding and determinant obstruction, not injectivity of the curve. -/
lemma lowCost_firstContact_full_angle {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 < T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hXc : Continuous X)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (hg0 : g 0 = 1)
    (hshift : ∀ t, g (t + T) = g t * R)
    (hcost : reinhardtCost T X < π) :
    sc_angle (frameContact g 0) (6 * T) = 2 * π := by
  let γ := frameContact g 0
  let δ := reflectedFirstRow g
  have hγ := frameContact_contDiff hgc 0
  have hne := frameContact_ne_zero hdet 0
  have hmono := angle_strictMono_of_cross_pos hγ hne (frameContact_cross_pos hdet hg hstar 0)
  have hP : 0 < 6 * T := by positivity
  have hrow := lowCost_reflectedFirstRow_full_angle hT hgc hdet hXc hg hstar hg0 hshift hcost
  have hDc : Continuous (fun s ↦ sc_angle γ s - sc_angle δ s) :=
    (continuous_angle_of_contDiff hγ hne).sub
      (continuous_angle_of_contDiff (reflectedFirstRow_contDiff hgc)
        (reflectedFirstRow_ne_zero hdet))
  have hupper : sc_angle γ (6 * T) - sc_angle δ (6 * T) < π := by
    by_contra hnot
    obtain ⟨s, hs, hπ⟩ := intermediate_value_Icc hP.le hDc.continuousOn
      ⟨by simpa only [sc_angle_zero, sub_self] using Real.pi_pos.le, not_lt.1 hnot⟩
    change sc_angle (frameContact g 0) s - sc_angle (reflectedFirstRow g) s = π at hπ
    exact firstContact_angle_ne_row_add_pi hgc hdet hg0 s (by linarith)
  have hγ0 : sc_toC (γ 0) = 1 := by simp [γ, frameContact, hg0, algA_sixthRoot_zero, sc_toC]
  have hγP : γ (6 * T) = γ 0 := by simpa only [zero_add] using frameContact_periodic hshift 0 0
  have hexp : Complex.exp (sc_log γ (6 * T)) = 1 := by
    have h := toComplex_eq_exp_log_of_contDiff hγ hne (6 * T)
    change sc_toC (γ (6 * T)) = sc_toC (γ 0) * Complex.exp (sc_log γ (6 * T)) at h
    rw [hγP, hγ0, one_mul] at h
    exact h.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  have hphase : sc_angle γ (6 * T) = (n : ℝ) * (2 * π) := by
    simp only [sc_angle, hn]
    simp
  have hpos : 0 < sc_angle γ (6 * T) := by
    simpa only [sc_angle_zero] using hmono hP
  have hnpos : 0 < n := by
    have hnr : 0 < (n : ℝ) := (mul_pos_iff_of_pos_right two_pi_pos).1 (hphase ▸ hpos)
    exact_mod_cast hnr
  have hnlt : n < 2 := by
    by_contra hnnot
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast not_lt.1 hnnot
    have hm := mul_le_mul_of_nonneg_right hnr two_pi_pos.le
    change sc_angle γ (6 * T) - sc_angle (reflectedFirstRow g) (6 * T) < π at hupper
    rw [hrow, hphase] at hupper
    nlinarith [Real.pi_pos]
  have hn1 : n = 1 := by omega
  simpa only [hn1, Int.cast_one, one_mul] using hphase

/-- Strict angle growth and one full turn imply simplicity on a full period. -/
lemma curve_injOn_of_full_angle {γ : ℝ → Fin 2 → ℝ} {P : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0)
    (hcross : ∀ t, 0 < cross (γ t) (deriv γ t))
    (hP : sc_angle γ P = 2 * π) : InjOn γ (Ico 0 P) := by
  have hmono := angle_strictMono_of_cross_pos hγ hne hcross
  have hC0 : sc_toC (γ 0) ≠ 0 := fun h ↦ hne 0 (sc_toC_eq_zero.1 h)
  intro a ha b hb hab
  by_contra hneab
  wlog hlt : a < b generalizing a b
  · exact this hb ha hab.symm (Ne.symm hneab)
      (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hneab))
  have hexp : Complex.exp (sc_log γ b) = Complex.exp (sc_log γ a) := by
    apply mul_left_cancel₀ hC0
    rw [← toComplex_eq_exp_log_of_contDiff hγ hne b,
      ← toComplex_eq_exp_log_of_contDiff hγ hne a, hab]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  have hphase : sc_angle γ b = sc_angle γ a + (n : ℝ) * (2 * π) := by
    have him := congrArg Complex.im hn
    simp at him
    change (sc_log γ b).im = (sc_log γ a).im + _
    linarith
  have h1 := hmono hlt
  have h2 := hmono hb.2
  have h3 := hmono.monotone ha.1
  rw [sc_angle_zero] at h3
  have hnpos : 0 < n := by
    have hnr : 0 < (n : ℝ) := by
      apply (mul_pos_iff_of_pos_right two_pi_pos).1
      linarith
    exact_mod_cast hnr
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hm := mul_le_mul_of_nonneg_right hnr two_pi_pos.le
  rw [hP] at h2
  linarith

/-- The explicit radial hull of the first contact of a global cyclic frame. -/
noncomputable def cyclicFrameDisk (g : ℝ → Mat2) (T : ℝ) : Set (Fin 2 → ℝ) :=
  radialHull (frameContact g 0) 0 (6 * T)

/-- A global low-cost cyclic smooth frame with the actual star and a.e. curvature
constraints constructs a balanced disk in circle representation. Simplicity,
convexity, compactness, interior, symmetry, and boundary images are conclusions. -/
theorem lowCost_cyclicFrame_isBalancedPair {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 < T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hXc : Continuous X)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (hLip : LipschitzOnEntrywise X univ)
    (hg0 : g 0 = 1) (hshift : ∀ t, g (t + T) = g t * R)
    (hcurv : ∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (frameContact g j) t)
      (deriv (deriv (frameContact g j)) t))
    (hcost : reinhardtCost T X < π) :
    IsBalancedPair (cyclicFrameDisk g T) (frameContact g) T ∧
      IsCircleRepresentation (frameContact g) := by
  have hP : 0 < 6 * T := by positivity
  have hperiod := cyclicFrame_periodic hshift
  have hvel := frame_velocity_lipschitz_periodic hg hLip hP hperiod
  have hdlip : ∀ j, ∃ C, LipschitzWith C (deriv (frameContact g j)) :=
    contact_derivatives_lipschitz_of_frame_velocity (fun _ _ ↦ rfl) hg hvel
  have hcross := frameContact_cross_pos hdet hg hstar
  have hinj0 : InjOn (frameContact g 0) (Ico 0 (6 * T)) :=
    curve_injOn_of_full_angle (frameContact_contDiff hgc 0) (frameContact_ne_zero hdet 0)
      (hcross 0) (lowCost_firstContact_full_angle hT hgc hdet hXc hg hstar hg0 hshift hcost)
  have hcurve : IsStarCurve (frameContact g 0) (6 * T) :=
    ⟨hP, frameContact_contDiff hgc 0, frameContact_periodic hshift 0, hinj0, hcross 0⟩
  have hinj : ∀ j, InjOn (frameContact g j) (Ico 0 (6 * T)) := by
    intro j
    rw [frameContact_eq_shift hshift j]
    exact oct_injOn_shift hP (frameContact_periodic hshift 0) hinj0 _
  have himage : ∀ j, frameContact g j '' Ico 0 (6 * T) = frontier (cyclicFrameDisk g T) := by
    intro j
    rw [cyclicFrameDisk, hcurve.frontier_radialHull,
      oct_image_Ico hP (frameContact_periodic hshift j),
      oct_image_Ico hP (frameContact_periodic hshift 0), frameContact_eq_shift hshift j]
    exact (Equiv.addRight ((j.val : ℝ) * T)).surjective.range_comp (frameContact g 0)
  have hneg : ∀ x ∈ cyclicFrameDisk g T, -x ∈ cyclicFrameDisk g T := by
    rintro x ⟨t, _, r, hr, rfl⟩
    refine ⟨oct_red (6 * T) (t + 3 * T),
      Ico_subset_Icc_self (oct_red_mem hP _), r, hr, ?_⟩
    have h3 := frameContact_add_nat hshift 3 t
    have hm := ((oct_isMultiPoint_mulVec (hdet t)) 0).2.1
    simp only [zero_add] at hm
    change frameContact g 3 t = -frameContact g 0 t at hm
    push_cast at h3
    rw [oct_periodic_red (frameContact_periodic hshift 0), h3, hm, smul_neg]
  have hreg : ∀ j t, deriv (frameContact g j) t ≠ 0 := by
    intro j t hz
    have hp := hcross j t
    rw [hz] at hp
    simp [cross] at hp
  refine ⟨⟨⟨hcurve.convex_radialHull (hdlip 0) (hcurv 0), hcurve.isCompact_radialHull,
    ⟨0, hcurve.zero_mem_interior_radialHull⟩, hneg⟩,
    fun j ↦ ⟨frameContact_contDiff hgc j, hreg j⟩, hdlip,
    fun t ↦ oct_isMultiPoint_mulVec (hdet t), hcurv, frameContact_star hg hstar,
    hT, frameContact_periodic hshift, hinj, himage⟩, ?_⟩
  intro j
  simp only [frameContact, hg0, Matrix.one_mulVec]

end SmoothedOctagon

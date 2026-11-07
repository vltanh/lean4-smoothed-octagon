module

public import SmoothedPolygons.Ch4.TerminalTime
public import Basic.Analysis.Convex.StarCurve
public import Mathlib.Tactic

/-!
# A cost bound excludes extra winding of a smooth star trajectory

The control endpoint `g(T) = R` alone allows extra turns. For a smooth `SL₂` arc satisfying
`g' = g X` with star states, the reflected first row has positive angular speed bounded
above by `-traceForm J X`. Hence a cost below `π` forces its lifted endpoint angle to be
exactly `π / 3`, with no additional multiple of `2π`.

The logarithmic-angle proof is adapted from the pinned `PlaneCurve.StarCurve` implementation,
with its periodicity and simplicity assumptions removed: only `C¹` and nonvanishing are
needed for that analytic construction. No simplicity of a control trajectory is assumed.

The exported trajectory theorem has explicit global smooth-arc hypotheses. Extending an
arbitrary integral-admissible segment to this interface and reconstructing a balanced disk
are supplied separately in `CyclicExtension` and `ReverseGeometry`; `ReverseComparison`
assembles their consequences. This module supplies the smooth-arc winding ingredient.
Source draft; Lean compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Matrix PlaneCurve SmoothedPolygons

/-- Continuity of the logarithmic derivative needs no closed-curve or simplicity hypothesis. -/
theorem continuous_logDeriv_of_contDiff {γ : ℝ → Fin 2 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0) : Continuous (sc_logDeriv γ) := by
  unfold sc_logDeriv
  exact (sc_continuous_toC.comp (hγ.continuous_deriv le_rfl)).div
    (sc_continuous_toC.comp hγ.continuous)
    (fun t hz ↦ hne t (sc_toC_eq_zero.mp hz))

theorem hasDerivAt_log_of_contDiff {γ : ℝ → Fin 2 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0) (t : ℝ) :
    HasDerivAt (sc_log γ) (sc_logDeriv γ t) t :=
  ((continuous_logDeriv_of_contDiff hγ hne).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem hasDerivAt_angle_of_contDiff {γ : ℝ → Fin 2 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0) (t : ℝ) :
    HasDerivAt (sc_angle γ) (sc_logDeriv γ t).im t :=
  (Complex.imCLM.hasFDerivAt (x := sc_log γ t)).comp_hasDerivAt t
    (hasDerivAt_log_of_contDiff hγ hne t)

/-- Exponential reconstruction of a nonvanishing `C¹` curve from its logarithmic integral.
In particular, the angle is a genuine continuous lift, rather than a principal argument. -/
theorem toComplex_eq_exp_log_of_contDiff {γ : ℝ → Fin 2 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0) (t : ℝ) :
    sc_toC (γ t) = sc_toC (γ 0) * Complex.exp (sc_log γ t) := by
  have hzc : ∀ s, HasDerivAt (fun u ↦ sc_toC (γ u)) (sc_toC (deriv γ s)) s := by
    intro s
    have hd := ((hγ.differentiable (by norm_num)) s).hasDerivAt
    exact ((hasDerivAt_pi.mp hd 0).ofReal_comp).add
      (((hasDerivAt_pi.mp hd 1).ofReal_comp).mul_const Complex.I)
  have hd : ∀ s, HasDerivAt
      (fun u ↦ sc_toC (γ u) * Complex.exp (-sc_log γ u)) 0 s := by
    intro s
    have h := (hzc s).mul (hasDerivAt_log_of_contDiff hγ hne s).neg.cexp
    convert h using 1
    have hz : sc_toC (γ s) ≠ 0 := fun hz ↦ hne s (sc_toC_eq_zero.mp hz)
    simp only [sc_logDeriv]
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simp only [sc_log_zero, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The positive quadratic form controlling the angle of a reflected row. -/
def starRowQuadratic (X : Mat2) (z : Fin 2 → ℝ) : ℝ :=
  -X 0 1 * (z 0) ^ 2 - 2 * X 0 0 * z 0 * z 1 + X 1 0 * (z 1) ^ 2

private lemma star_row_coefficients {X : Mat2} (hX : IsStarState X) :
    0 < X 1 0 ∧ X 1 1 = -X 0 0 ∧
      -(X 0 0) ^ 2 - X 0 1 * X 1 0 = 1 := by
  have htr := hX.1
  have hdet := hX.2.1
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have h0 := hX.2.2.1
  have h1 := hX.2.2.2.1
  unfold ρ₀ at h0
  unfold ρ₁ at h1
  have h3 : 0 < √3 := by positivity
  have hp := (div_pos_iff_of_pos_right h3).mp h0
  have hm := (div_pos_iff_of_pos_right h3).mp h1
  have hd : X 1 1 = -X 0 0 := by linarith
  refine ⟨by linarith, hd, ?_⟩
  rw [hd] at hdet
  nlinarith

/-- Positive definiteness follows by completing the square, using `det X = 1`. -/
theorem starRowQuadratic_pos {X : Mat2} (hX : IsStarState X)
    {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 < starRowQuadratic X z := by
  obtain ⟨hc, _, hdet⟩ := star_row_coefficients hX
  have hid : X 1 0 * starRowQuadratic X z =
      (X 1 0 * z 1 - X 0 0 * z 0) ^ 2 + (z 0) ^ 2 := by
    unfold starRowQuadratic
    linear_combination (z 0) ^ 2 * hdet
  by_cases h0 : z 0 = 0
  · have h1 : z 1 ≠ 0 := by
      intro h1
      apply hz
      ext i
      fin_cases i <;> simp [h0, h1]
    simpa [starRowQuadratic, h0] using mul_pos hc (sq_pos_of_ne_zero h1)
  · have hp : 0 < X 1 0 * starRowQuadratic X z := by
      rw [hid]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h0)
    exact pos_of_mul_pos_right hp hc.le

/-- The trace of the positive quadratic form bounds its value on every vector. -/
theorem starRowQuadratic_le_trace {X : Mat2} (hX : IsStarState X) (z : Fin 2 → ℝ) :
    starRowQuadratic X z ≤ (X 1 0 - X 0 1) * ((z 0) ^ 2 + (z 1) ^ 2) := by
  let w : Fin 2 → ℝ := ![-z 1, z 0]
  have hw : 0 ≤ starRowQuadratic X w := by
    by_cases hw0 : w = 0
    · simp [hw0, starRowQuadratic]
    · exact (starRowQuadratic_pos hX hw0).le
  dsimp [starRowQuadratic, w] at hw ⊢
  nlinarith

/-- Reflecting the first row turns the right matrix equation into a positively turning
plane curve. The reflection is essential for the sign convention. -/
def reflectedFirstRow (g : ℝ → Mat2) (t : ℝ) : Fin 2 → ℝ :=
  ![g t 0 0, -g t 0 1]

theorem reflectedFirstRow_contDiff {g : ℝ → Mat2}
    (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j)) :
    ContDiff ℝ 1 (reflectedFirstRow g) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa only [reflectedFirstRow, Fin.zero_eta, Matrix.cons_val_zero] using hgc 0 0
  · simpa only [reflectedFirstRow, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      using (hgc 0 1).neg

theorem reflectedFirstRow_ne_zero {g : ℝ → Mat2}
    (hdet : ∀ t, (g t).det = 1) (t : ℝ) : reflectedFirstRow g t ≠ 0 := by
  intro hz
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  simp only [reflectedFirstRow, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have hd := hdet t
  rw [Matrix.det_fin_two] at hd
  have h1' : g t 0 1 = 0 := by linarith
  rw [h0, h1'] at hd
  norm_num at hd

theorem reflectedFirstRow_hasDerivAt {g X : ℝ → Mat2}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t) (t : ℝ) :
    HasDerivAt (reflectedFirstRow g)
      (![(g t * X t) 0 0, -(g t * X t) 0 1]) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa only [reflectedFirstRow, Fin.zero_eta, Matrix.cons_val_zero] using hg t 0 0
  · simpa only [reflectedFirstRow, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      using (hg t 0 1).fun_neg

theorem reflectedFirstRow_cross {g X : ℝ → Mat2}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (t : ℝ) :
    cross (reflectedFirstRow g t) (deriv (reflectedFirstRow g) t) =
      starRowQuadratic (X t) (reflectedFirstRow g t) := by
  have hdiag := (star_row_coefficients (hstar t)).2.1
  rw [(reflectedFirstRow_hasDerivAt hg t).deriv]
  simp only [cross, reflectedFirstRow, starRowQuadratic, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.mul_apply, Fin.sum_univ_two, hdiag]
  ring

/-- The reflected-row angular speed is positive and bounded by the cost density divided
by `3/2`. This estimate does not assume a simple or once-winding path. -/
theorem reflectedFirstRow_angularSpeed_bounds {g X : ℝ → Mat2}
    (hdet : ∀ t, (g t).det = 1)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (t : ℝ) :
    0 < (sc_logDeriv (reflectedFirstRow g) t).im ∧
      (sc_logDeriv (reflectedFirstRow g) t).im ≤ -traceForm J (X t) := by
  have hz := reflectedFirstRow_ne_zero hdet t
  have hn : 0 < Complex.normSq (sc_toC (reflectedFirstRow g t)) :=
    Complex.normSq_pos.mpr (fun h ↦ hz (sc_toC_eq_zero.mp h))
  have hnorm : Complex.normSq (sc_toC (reflectedFirstRow g t)) =
      (reflectedFirstRow g t 0) ^ 2 + (reflectedFirstRow g t 1) ^ 2 := by
    simp [Complex.normSq_apply, sc_toC_re, sc_toC_im, pow_two]
  have htrace : -traceForm J (X t) = X t 1 0 - X t 0 1 := by
    simp [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct]
    ring
  rw [sc_logDeriv_im, reflectedFirstRow_cross hg hstar t]
  refine ⟨div_pos (starRowQuadratic_pos (hstar t) hz) hn, ?_⟩
  rw [div_le_iff₀ hn, htrace, hnorm]
  exact starRowQuadratic_le_trace (hstar t) (reflectedFirstRow g t)

theorem reflectedFirstRow_angle_strictMono {g X : ℝ → Mat2}
    (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) :
    StrictMono (sc_angle (reflectedFirstRow g)) :=
  strictMono_of_hasDerivAt_pos
    (hasDerivAt_angle_of_contDiff (reflectedFirstRow_contDiff hgc)
      (reflectedFirstRow_ne_zero hdet))
    (fun t ↦ (reflectedFirstRow_angularSpeed_bounds hdet hg hstar t).1)

/-- Integrated angular control by the actual Reinhardt cost. -/
theorem reflectedFirstRow_angle_le_cost {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 ≤ T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hXc : Continuous X)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) :
    (3 / 2 : ℝ) * sc_angle (reflectedFirstRow g) T ≤ reinhardtCost T X := by
  have hγ := reflectedFirstRow_contDiff hgc
  have hne := reflectedFirstRow_ne_zero hdet
  have hlogc := continuous_logDeriv_of_contDiff hγ hne
  have hanglec := Complex.continuous_im.comp hlogc
  have htracec : Continuous fun t ↦ traceForm J (X t) :=
    (continuous_const.matrix_mul hXc).matrix_trace
  have hangleint : (∫ t in (0 : ℝ)..T, (sc_logDeriv (reflectedFirstRow g) t).im) =
      sc_angle (reflectedFirstRow g) T := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_angle_of_contDiff hγ hne t)
      (hanglec.intervalIntegrable 0 T)
    simpa only [sc_angle_zero, sub_zero] using h
  have hle := intervalIntegral.integral_mono_on hT
    (hanglec.intervalIntegrable 0 T) (htracec.neg.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    (fun t _ ↦ (reflectedFirstRow_angularSpeed_bounds hdet hg hstar t).2)
  simp only [Function.comp_def, Pi.neg_apply] at hle
  rw [hangleint, intervalIntegral.integral_neg] at hle
  unfold reinhardtCost
  linarith

/-- A smooth star trajectory from `I` to `R` with cost below `π` has exactly the primary
reflected-row turn `π/3`. The endpoint condition alone would allow extra integer turns. -/
theorem lowCost_reflectedFirstRow_angle {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 < T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hXc : Continuous X)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (hg0 : g 0 = 1) (hgT : g T = R)
    (hcost : reinhardtCost T X < π) :
    sc_angle (reflectedFirstRow g) T = π / 3 := by
  have hγ := reflectedFirstRow_contDiff hgc
  have hne := reflectedFirstRow_ne_zero hdet
  have hmono : StrictMono (sc_angle (reflectedFirstRow g)) :=
    reflectedFirstRow_angle_strictMono hgc hdet hg hstar
  have hpos : 0 < sc_angle (reflectedFirstRow g) T := by
    simpa only [sc_angle_zero] using hmono hT
  have hbound := reflectedFirstRow_angle_le_cost hT.le hgc hdet hXc hg hstar
  have hz0 : sc_toC (reflectedFirstRow g 0) = 1 := by
    simp [reflectedFirstRow, hg0, sc_toC]
  have hzT : sc_toC (reflectedFirstRow g T) =
      Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
      simp [reflectedFirstRow, hgT, R]
    · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
      simp [reflectedFirstRow, hgT, R]
  have hexp : Complex.exp (sc_log (reflectedFirstRow g) T) =
      Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
    have h := toComplex_eq_exp_log_of_contDiff hγ hne T
    rw [hz0, one_mul] at h
    exact h.symm.trans hzT
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hphase : sc_angle (reflectedFirstRow g) T = π / 3 + (n : ℝ) * (2 * π) := by
    have hi := congrArg Complex.im hn
    simp at hi
    change (sc_log (reflectedFirstRow g) T).im = _
    linarith
  have hn0 : n = 0 := by
    by_contra hne0
    rcases lt_or_gt_of_ne hne0 with hneg | hposn
    · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      have hm := mul_le_mul_of_nonneg_right hle two_pi_pos.le
      linarith [Real.pi_pos]
    · have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have hm := mul_le_mul_of_nonneg_right hge two_pi_pos.le
      linarith [Real.pi_pos]
  simpa only [hn0, Int.cast_zero, zero_mul, add_zero] using hphase

/-- The low-cost arc stays in the coordinate chart `g₀₀ > 0`. This also prevents an
extra turn of its first column; reconstructing the full balanced disk is still separate. -/
theorem lowCost_first_matrix_entry_pos {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 < T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1) (hXc : Continuous X)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) (hg0 : g 0 = 1) (hgT : g T = R)
    (hcost : reinhardtCost T X < π) {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 < g t 0 0 := by
  have hmono := reflectedFirstRow_angle_strictMono hgc hdet hg hstar
  have hterminal := lowCost_reflectedFirstRow_angle hT hgc hdet hXc hg hstar hg0 hgT hcost
  have hlo : 0 ≤ sc_angle (reflectedFirstRow g) t := by
    simpa only [sc_angle_zero] using hmono.monotone ht.1
  have hhi : sc_angle (reflectedFirstRow g) t ≤ π / 3 := by
    rw [← hterminal]
    exact hmono.monotone ht.2
  have hcos : 0 < Real.cos (sc_angle (reflectedFirstRow g) t) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hz0 : sc_toC (reflectedFirstRow g 0) = 1 := by
    simp [reflectedFirstRow, hg0, sc_toC]
  have hz := toComplex_eq_exp_log_of_contDiff (reflectedFirstRow_contDiff hgc)
    (reflectedFirstRow_ne_zero hdet) t
  rw [hz0, one_mul] at hz
  have hre := congrArg Complex.re hz
  simp only [sc_toC_re, reflectedFirstRow, Matrix.cons_val_zero, Complex.exp_re] at hre
  rw [hre]
  exact mul_pos (Real.exp_pos _) hcos

end SmoothedOctagon

module

public import SmoothedOctagon.Reduction.Clearance.Algebra
public import Basic.Analysis.Calculus.MatrixFTC
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The left-and-right angular identity and the winding bound

Write a frame `h = sI + tJ + uH + vK₀`, so `s + it = scb_zc h` and `s² + t² - u² - v² = det h = 1`.
For an admissible trajectory `h' = hY` the `J` coefficients of `h⁻¹h'` and `h'h⁻¹` give
`ρ + ρ_R = 2 Im(conj(z) z')` with `z = s + it`. The continuous logarithm `L(t) = ∫₀ᵗ z'/z` satisfies
`z = exp L` (`z(0) = 1`), and `z(T) = e^{iπ/3}` because `h(T) = R`, so `Im L(T) ∈ π/3 + 2πℤ`; it is
positive since `Im(z'/z) = (ρ + ρ_R)/(2|z|²) > 0`, hence at least `π/3`, and `|z| ≥ 1` gives
`∫(ρ + ρ_R) ≥ 2 Im L(T) ≥ 2π/3`.

Main API:

* `scb_zc`: `z(M) = (M₀₀ + M₁₁)/2 + i (M₁₀ - M₀₁)/2`; `scb_zc_normSq_ge` (`|z|² ≥ 1` for
  `det M = 1`), `scb_angular` (the angular identity).
* `scb_continuousOn_rho`, `scb_continuousOn_rhoR`: continuity of `ρ(Y)` and `ρ_R(h, Y)` along an
  admissible trajectory.
* `scb_winding`: for an admissible `(T, u, h, Y)`, `2π/3 ≤ ∫₀ᵀ (ρ(Y) + ρ_R(h, Y))`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Real Filter Topology

/-- `z(M) = s + it` for `M = sI + tJ + uH + vK₀`. -/
noncomputable def scb_zc (M : Mat2) : ℂ :=
  (((M 0 0 + M 1 1) / 2 : ℝ) : ℂ) + (((M 1 0 - M 0 1) / 2 : ℝ) : ℂ) * Complex.I

theorem scb_zc_re (M : Mat2) : (scb_zc M).re = (M 0 0 + M 1 1) / 2 := by simp [scb_zc]

theorem scb_zc_im (M : Mat2) : (scb_zc M).im = (M 1 0 - M 0 1) / 2 := by simp [scb_zc]

theorem scb_continuous_zc : Continuous scb_zc := by
  unfold scb_zc; fun_prop

/-- `|z|² = s² + t² = 1 + u² + v² ≥ 1` when `det M = 1`. -/
theorem scb_zc_normSq_ge {M : Mat2} (hM : M.det = 1) : 1 ≤ Complex.normSq (scb_zc M) := by
  rw [Complex.normSq_apply, scb_zc_re, scb_zc_im]
  rw [Matrix.det_fin_two] at hM
  nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0)]

/-- **The angular identity**: `2(s t' - t s') = ρ(Y) det h + ρ_R(h, Y)` with `s + it = z(h)`,
`s' + it' = z(hY)`, for traceless `Y`; both sides are expanded in the entries. -/
theorem scb_angular (h : Mat2) {Y : Mat2} (hY : Y.trace = 0) :
    2 * ((scb_zc h).re * (scb_zc (h * Y)).im - (scb_zc h).im * (scb_zc (h * Y)).re) =
      scb_rho Y * h.det + scb_rhoR h Y := by
  have h11 : Y 1 1 = -Y 0 0 := by rw [Matrix.trace_fin_two] at hY; linarith
  have key := scb_rhoR_eq h Y
  rw [scb_zc_re, scb_zc_im, scb_zc_re, scb_zc_im, scb_rho_eq, Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h11] at key ⊢
  linear_combination (-1 / 2 : ℝ) * key

theorem scb_continuous_rho : Continuous scb_rho := by
  unfold scb_rho traceForm
  exact continuous_const.mul (continuous_const.matrix_mul continuous_id).matrix_trace

theorem scb_continuous_rhoR : Continuous fun p : Mat2 × Mat2 ↦ scb_rhoR p.1 p.2 := by
  unfold scb_rhoR
  exact scb_continuous_rho.comp ((continuous_fst.matrix_mul continuous_snd).matrix_mul
    continuous_fst.matrix_adjugate)

section Admissible

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {h Y : ℝ → Mat2}

theorem scb_continuousOn_frame (hst : IsStateTrajectory T u h Y) :
    ContinuousOn h (Icc 0 T) :=
  Matrix.continuousOn_of_eq_add_integral hst.2.2.2.2.1

theorem scb_continuousOn_state (hst : IsStateTrajectory T u h Y) :
    ContinuousOn Y (Icc 0 T) :=
  Matrix.continuousOn_of_eq_add_integral hst.2.2.2.2.2

theorem scb_continuousOn_rho (hst : IsStateTrajectory T u h Y) :
    ContinuousOn (fun s ↦ scb_rho (Y s)) (Icc 0 T) :=
  scb_continuous_rho.comp_continuousOn (scb_continuousOn_state hst)

theorem scb_continuousOn_rhoR (hst : IsStateTrajectory T u h Y) :
    ContinuousOn (fun s ↦ scb_rhoR (h s) (Y s)) (Icc 0 T) := by
  have hp : ContinuousOn (fun s ↦ (h s, Y s)) (Icc 0 T) :=
    (scb_continuousOn_frame hst).prodMk (scb_continuousOn_state hst)
  exact scb_continuous_rhoR.comp_continuousOn (f := fun s ↦ (h s, Y s)) hp

/-- The frame of a state trajectory has derivative `h(s) Y(s)` at interior times. -/
theorem scb_hasDerivAtEntrywise_frame (hst : IsStateTrajectory T u h Y) {s : ℝ}
    (hs : s ∈ Ioo 0 T) : Matrix.HasDerivAtEntrywise h (h s * Y s) s :=
  Matrix.hasDerivAtEntrywise_of_eq_add_integral hst.2.2.2.2.1 hs
    (((scb_continuousOn_frame hst).mul (scb_continuousOn_state hst)).continuousAt
      (Icc_mem_nhds hs.1 hs.2))

theorem scb_hasDerivAt_zc (hst : IsStateTrajectory T u h Y) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ scb_zc (h r)) (scb_zc (h s * Y s)) s := by
  have hd := scb_hasDerivAtEntrywise_frame hst hs
  unfold scb_zc
  exact (((hd 0 0).add (hd 1 1)).div_const 2).ofReal_comp.add
    ((((hd 1 0).sub (hd 0 1)).div_const 2).ofReal_comp.mul_const Complex.I)

/-- **The winding bound**. For an admissible trajectory (`h(0) = I`, `h(T) = R`),
`∫₀ᵀ (ρ + ρ_R) ≥ 2π/3`, by the continuous logarithm of `z(h)` as in the module description. -/
theorem scb_winding (hadm : IsReinhardtAdmissible T u h Y) :
    2 * π / 3 ≤ ∫ s in (0 : ℝ)..T, (scb_rho (Y s) + scb_rhoR (h s) (Y s)) := by
  obtain ⟨hst, h0, hTR, -⟩ := hadm
  have hT : 0 < T := hst.1
  have hdet : ∀ s ∈ Icc 0 T, (h s).det = 1 := fun s hs ↦ (hst.2.2.2.1 s hs).1
  have hstar : ∀ s ∈ Icc 0 T, IsStarState (Y s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  have hhc := scb_continuousOn_frame hst
  have hYc := scb_continuousOn_state hst
  set z : ℝ → ℂ := fun r ↦ scb_zc (h r) with hz
  set zp : ℝ → ℂ := fun r ↦ scb_zc (h r * Y r) with hzp
  have hzc : ContinuousOn z (Icc 0 T) := scb_continuous_zc.comp_continuousOn hhc
  have hzpc : ContinuousOn zp (Icc 0 T) := scb_continuous_zc.comp_continuousOn (hhc.mul hYc)
  have hnormSq : ∀ s ∈ Icc 0 T, 1 ≤ Complex.normSq (z s) := fun s hs ↦
    scb_zc_normSq_ge (hdet s hs)
  have hz0 : ∀ s ∈ Icc 0 T, z s ≠ 0 := fun s hs h0 ↦ by
    have := hnormSq s hs
    rw [h0, map_zero] at this
    linarith
  set f : ℝ → ℂ := fun r ↦ zp r / z r with hf
  have hfc : ContinuousOn f (Icc 0 T) := hzpc.div hzc hz0
  have hfi : IntervalIntegrable f volume 0 T := (hfc.mono (by
    rw [uIcc_of_le hT.le])).intervalIntegrable
  set L : ℝ → ℂ := fun s ↦ ∫ r in (0 : ℝ)..s, f r with hL
  have hLc : ContinuousOn L (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := f) (hfc.integrableOn_Icc.mono_set (by rw [uIcc_of_le hT.le]))
    rwa [uIcc_of_le hT.le] at this
  have hLd : ∀ s ∈ Ioo 0 T, HasDerivAt L (f s) s := by
    intro s hs
    exact intervalIntegral.integral_hasDerivAt_right
      (hfi.mono_set (by
        rw [uIcc_of_le hT.le, uIcc_of_le hs.1.le]
        exact Icc_subset_Icc_right hs.2.le))
      ((hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
      (hfc.continuousAt (Icc_mem_nhds hs.1 hs.2))
  -- `z exp(-L)` is constant
  set φ : ℝ → ℂ := fun s ↦ z s * Complex.exp (-L s) with hφ
  have hφc : ContinuousOn φ (Icc 0 T) :=
    hzc.mul (Complex.continuous_exp.comp_continuousOn hLc.neg)
  have hφd : ∀ s ∈ Ioo 0 T, HasDerivAt φ 0 s := by
    intro s hs
    have h1 := (scb_hasDerivAt_zc hst hs).mul (hLd s hs).neg.cexp
    convert h1 using 1
    have hzs : z s ≠ 0 := hz0 s (Ioo_subset_Icc_self hs)
    simp only [hf]
    field_simp
    ring
  have hφT : φ T = φ 0 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hφc hφd
      (intervalIntegrable_const (c := (0 : ℂ)))
    rw [intervalIntegral.integral_zero] at this
    exact (sub_eq_zero.mp this.symm)
  have hφ0 : φ 0 = 1 := by
    simp [hφ, hz, hL, h0, scb_zc]
  have hzT : z T = Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    simp only [hz, hTR, scb_zc, SmoothedPolygons.R]
    simp
  have hexpL : Complex.exp (L T) = Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
    rw [← hzT]
    have e : z T * Complex.exp (-L T) = 1 := by rw [← hφ0, ← hφT]
    have := congrArg (· * Complex.exp (L T)) e
    simp only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one,
      one_mul] at this
    exact this.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpL
  have hLim : (L T).im = π / 3 + 2 * π * n := by
    rw [hn]
    simp
    ring
  -- `Im L(T) = ∫ Im(z'/z)`
  have hIm : (L T).im = ∫ r in (0 : ℝ)..T, (f r).im := by
    simp only [hL]
    exact (Complex.imCLM.intervalIntegral_comp_comm hfi).symm
  -- `Im(z'/z) = (ρ + ρ_R)/(2|z|²)`
  have hfim : ∀ r ∈ Icc 0 T, (f r).im =
      (scb_rho (Y r) + scb_rhoR (h r) (Y r)) / 2 / Complex.normSq (z r) := by
    intro r hr
    have ha := scb_angular (h r) (hstar r hr).1
    rw [hdet r hr, mul_one] at ha
    simp only [hf, hz, hzp, Complex.div_im]
    rw [← ha]
    ring
  have hρpos : ∀ r ∈ Icc 0 T, 0 < scb_rho (Y r) + scb_rhoR (h r) (Y r) := fun r hr ↦
    add_pos (scb_rho_pos (hstar r hr)) (scb_rhoR_pos (hdet r hr) (hstar r hr))
  have hfim_pos : ∀ r ∈ Icc 0 T, 0 < (f r).im := by
    intro r hr
    rw [hfim r hr]
    have := hnormSq r hr
    have := hρpos r hr
    positivity
  have hfim_le : ∀ r ∈ Icc 0 T,
      (f r).im ≤ (scb_rho (Y r) + scb_rhoR (h r) (Y r)) / 2 := by
    intro r hr
    rw [hfim r hr]
    exact div_le_self (by linarith [hρpos r hr]) (hnormSq r hr)
  have hfimi : IntervalIntegrable (fun r ↦ (f r).im) volume 0 T :=
    (Complex.continuous_im.comp_continuousOn hfc |>.mono (by
      rw [uIcc_of_le hT.le])).intervalIntegrable
  have hint_pos : 0 < ∫ r in (0 : ℝ)..T, (f r).im :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hfimi
      (fun r hr ↦ hfim_pos r (Ioo_subset_Icc_self hr)) hT
  have hn0 : (0 : ℝ) ≤ n := by
    have : 0 < π / 3 + 2 * π * n := by rw [← hLim, hIm]; exact hint_pos
    have hn' : (-1 : ℝ) < n := by
      by_contra hc
      push Not at hc
      nlinarith [Real.pi_pos]
    exact_mod_cast (show (-1 : ℤ) < n by exact_mod_cast hn')
  have hρc : ContinuousOn (fun s ↦ scb_rho (Y s) + scb_rhoR (h s) (Y s)) (Icc 0 T) :=
    (scb_continuousOn_rho hst).add (scb_continuousOn_rhoR hst)
  have hρi : IntervalIntegrable (fun s ↦ (scb_rho (Y s) + scb_rhoR (h s) (Y s)) / 2) volume 0 T :=
    ((hρc.div_const 2).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hmono : ∫ r in (0 : ℝ)..T, (f r).im ≤
      ∫ r in (0 : ℝ)..T, (scb_rho (Y r) + scb_rhoR (h r) (Y r)) / 2 :=
    intervalIntegral.integral_mono_on hT.le hfimi hρi hfim_le
  rw [intervalIntegral.integral_div] at hmono
  rw [← hIm, hLim] at hmono
  nlinarith [Real.pi_pos]

end Admissible

end SmoothedOctagon.Reduction

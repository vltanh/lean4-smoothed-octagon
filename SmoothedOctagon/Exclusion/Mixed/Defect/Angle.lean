module

public import SmoothedOctagon.Exclusion.Forward.Wire

/-!
# The continuous polar angle of the costate frame, on subintervals

The spectral angle bound on an arbitrary subinterval of one period. For a
normal period with negative elliptic `Λ₁(0) = -κ h₀ J h₀⁻¹` put `B(t) = h₀⁻¹ g(t)` and
`z(t) = z(B(t))` (`Reduction.scb_zc`). Then `z(t) = z(0) exp(L(t))` on `[0, T]` for a continuous
complex logarithm `L` with `L(0) = 0`; its imaginary part `Θ = Im L` is the continuous polar angle
`∫₀ᵗ (ρ + ρ_R)/(2|z|²)`, strictly increasing, and on every subinterval
`(κ + 3/2)(Θ(t) - Θ(s)) ≤ 3 ∫ₛᵗ ρ` (the pointwise spectral bound `3 m_b ≥ (κ + 3/2) θ'`).

The proof is that of `ifc_winding` and `ifc_spectral` (`Exclusion/Forward/Wire`), with the
logarithm kept on every subinterval.

## Main API

* `NormalPeriod.df_angle`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real Set Reduction MeasureTheory

namespace NormalPeriod

variable (P : NormalPeriod)

/-- **The continuous polar angle on subintervals**. -/
theorem df_angle (hdet : 0 < (P.Λ₁ 0).det) (h10 : (P.Λ₁ 0) 1 0 < 0) :
    ∃ h₀ : Mat2, h₀.det = 1 ∧ P.Λ₁ 0 = -√(P.Λ₁ 0).det • (h₀ * J * h₀.adjugate) ∧
    ∃ L : ℝ → ℂ, L 0 = 0 ∧
      (∀ t ∈ Icc 0 P.T,
        scb_zc (h₀.adjugate * P.g t) = scb_zc h₀.adjugate * Complex.exp (L t)) ∧
      (∀ s t, 0 ≤ s → s < t → t ≤ P.T → (L s).im < (L t).im) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ P.T →
        (√(P.Λ₁ 0).det + 3 / 2) * ((L t).im - (L s).im) ≤
          3 * ∫ r in s..t, scb_rho (P.X r)) := by
  have hΛtr := (P.extremal.2.2.2.2.2.2.2.1 0 ⟨le_rfl, P.T_pos.le⟩).1
  obtain ⟨h₀, hh₀, hrep⟩ := el_negEll_repr hΛtr hdet h10
  refine ⟨h₀, hh₀, hrep, ?_⟩
  set κ := √(P.Λ₁ 0).det with hκ
  have hκpos : 0 < κ := Real.sqrt_pos.2 hdet
  have hT := P.T_pos
  obtain ⟨hst, hg0, -, -, -, -, -, -, -, -, -⟩ := P.extremal
  have hgc := scb_continuousOn_frame hst
  have hXc := scb_continuousOn_state hst
  have hdg : ∀ s ∈ Icc 0 P.T, (P.g s).det = 1 := fun s hs ↦ (hst.2.2.2.1 s hs).1
  have hstar : ∀ s ∈ Icc 0 P.T, IsStarState (P.X s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  set B : ℝ → Mat2 := fun s ↦ h₀.adjugate * P.g s with hB
  have hdetadj : h₀.adjugate.det = 1 := by
    rw [Matrix.det_adjugate, hh₀]; simp
  have hBc : ContinuousOn B (Icc 0 P.T) := continuousOn_const.mul hgc
  have hBd : ∀ s ∈ Ioo 0 P.T, Matrix.HasDerivAtEntrywise B (B s * P.X s) s := by
    intro s hs
    have := (scb_hasDerivAtEntrywise_frame hst hs).const_mul h₀.adjugate
    simpa [hB, Matrix.mul_assoc] using this
  have hBdet : ∀ s ∈ Icc 0 P.T, (B s).det = 1 := fun s hs ↦ by
    simp only [hB, Matrix.det_mul, hdetadj, hdg s hs, mul_one]
  -- `tr(Λ₁ X) = 2κ ρ_R` and `2κ ρ_R ≤ 3ρ` (as in `ifc_spectral`)
  have hcons := scb_conservation P.extremal
  have hρR : ∀ s ∈ Icc 0 P.T,
      traceForm (P.Λ₁ s) (P.X s) = 2 * κ * scb_rhoR (B s) (P.X s) := by
    intro s hs
    have hinv : (P.g s)⁻¹ = (P.g s).adjugate := by
      rw [Matrix.inv_def, hdg s hs]; simp
    have hadjB : (B s).adjugate = (P.g s).adjugate * h₀ := by
      simp only [hB, Matrix.adjugate_mul_distrib]
      rw [Matrix.adjugate_adjugate _ (by simp)]
      simp
    rw [hcons s hs, hrep, hinv, scb_rhoR, scb_rho, hadjB]
    simp only [traceForm, hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have key : ∀ A B C D E F : Mat2, (A * (B * (C * (D * (E * F))))).trace =
        (F * (A * (B * (C * (D * E))))).trace := by
      intro A B C D E F; rw [Matrix.trace_mul_comm F]; simp only [Matrix.mul_assoc]
    have : ((P.g s).adjugate * (h₀ * J * h₀.adjugate) * P.g s * P.X s).trace =
        (J * (h₀.adjugate * P.g s * P.X s * ((P.g s).adjugate * h₀))).trace := by
      simp only [Matrix.mul_assoc]
      rw [key J, key h₀]
    rw [this]; ring
  have hkR : ∀ s ∈ Icc 0 P.T, 2 * κ * scb_rhoR (B s) (P.X s) ≤ 3 * scb_rho (P.X s) := by
    intro s hs
    have h1 := scb_traceForm_le_zero P.extremal s hs
    have h2 := hρR s hs
    simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul] at h1
    simp only [traceForm] at h2
    simp only [scb_rho, traceForm]
    rw [h2] at h1
    linarith
  -- the pointwise bound `θ' ≤ 6ρ/(2κ + 3)`
  have hle : ∀ s ∈ Icc 0 P.T,
      (scb_rho (P.X s) + scb_rhoR (B s) (P.X s)) / 2 / Complex.normSq (scb_zc (B s)) ≤
        6 / (2 * κ + 3) * scb_rho (P.X s) := by
    intro s hs
    have hk := hkR s hs
    have hkey := ifc_spec_key (hBdet s hs) (hstar s hs)
    have hρ := scb_rho_pos (hstar s hs)
    have hρR' := scb_rhoR_pos (hBdet s hs) (hstar s hs)
    have hN := scb_zc_normSq_ge (hBdet s hs)
    set r := scb_rho (P.X s)
    set rR := scb_rhoR (B s) (P.X s)
    set Nz := Complex.normSq (scb_zc (B s))
    have h1 : (r + rR) * (2 * κ + 3) * rR ≤ 3 * (r + rR) ^ 2 := by nlinarith
    have h2 : (r + rR) * (2 * κ + 3) * rR ≤ 12 * Nz * r * rR := by nlinarith
    have h3 : (r + rR) * (2 * κ + 3) ≤ 12 * Nz * r := by
      by_contra hc; push Not at hc; nlinarith
    rw [div_div, div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, mul_comm, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  -- the complex logarithm of `z` (as in `ifc_winding`)
  set z : ℝ → ℂ := fun r ↦ scb_zc (B r) with hz
  set zp : ℝ → ℂ := fun r ↦ scb_zc (B r * P.X r) with hzp
  have hzc : ContinuousOn z (Icc 0 P.T) := scb_continuous_zc.comp_continuousOn hBc
  have hzpc : ContinuousOn zp (Icc 0 P.T) := scb_continuous_zc.comp_continuousOn (hBc.mul hXc)
  have hnormSq : ∀ s ∈ Icc 0 P.T, 1 ≤ Complex.normSq (z s) := fun s hs ↦
    scb_zc_normSq_ge (hBdet s hs)
  have hz0 : ∀ s ∈ Icc 0 P.T, z s ≠ 0 := fun s hs h0 ↦ by
    have := hnormSq s hs
    rw [h0, map_zero] at this
    linarith
  have hzd : ∀ s ∈ Ioo 0 P.T, HasDerivAt z (zp s) s := by
    intro s hs
    have hd := hBd s hs
    simp only [hz, hzp, scb_zc]
    exact (((hd 0 0).add (hd 1 1)).div_const 2).ofReal_comp.add
      ((((hd 1 0).sub (hd 0 1)).div_const 2).ofReal_comp.mul_const Complex.I)
  set f : ℝ → ℂ := fun r ↦ zp r / z r with hf
  have hfc : ContinuousOn f (Icc 0 P.T) := hzpc.div hzc hz0
  have hfi : IntervalIntegrable f volume 0 P.T := (hfc.mono (by
    rw [uIcc_of_le hT.le])).intervalIntegrable
  have hfi' : ∀ s t, 0 ≤ s → s ≤ P.T → 0 ≤ t → t ≤ P.T → IntervalIntegrable f volume s t :=
    fun s t hs0 hsT ht0 htT ↦ (hfc.mono (uIcc_subset_Icc ⟨hs0, hsT⟩ ⟨ht0, htT⟩)).intervalIntegrable
  set L : ℝ → ℂ := fun s ↦ ∫ r in (0 : ℝ)..s, f r with hL
  have hLc : ContinuousOn L (Icc 0 P.T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := P.T)
      (f := f) (hfc.integrableOn_Icc.mono_set (by rw [uIcc_of_le hT.le]))
    rwa [uIcc_of_le hT.le] at this
  have hLd : ∀ s ∈ Ioo 0 P.T, HasDerivAt L (f s) s := by
    intro s hs
    exact intervalIntegral.integral_hasDerivAt_right
      (hfi.mono_set (by
        rw [uIcc_of_le hT.le, uIcc_of_le hs.1.le]
        exact Icc_subset_Icc_right hs.2.le))
      ((hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
      (hfc.continuousAt (Icc_mem_nhds hs.1 hs.2))
  set φ : ℝ → ℂ := fun s ↦ z s * Complex.exp (-L s) with hφ
  have hφc : ContinuousOn φ (Icc 0 P.T) :=
    hzc.mul (Complex.continuous_exp.comp_continuousOn hLc.neg)
  have hφd : ∀ s ∈ Ioo 0 P.T, HasDerivAt φ 0 s := by
    intro s hs
    have h1 := (hzd s hs).mul (hLd s hs).neg.cexp
    convert h1 using 1
    have hzs : z s ≠ 0 := hz0 s (Ioo_subset_Icc_self hs)
    simp only [hf]
    field_simp
    ring
  have hφ0 : φ 0 = z 0 := by simp [hφ, hL]
  have hφt : ∀ t ∈ Icc 0 P.T, φ t = φ 0 := by
    intro t ht
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hφc.mono (Icc_subset_Icc_right ht.2))
      (fun r hr ↦ hφd r ⟨hr.1, hr.2.trans_le ht.2⟩)
      (intervalIntegrable_const (c := (0 : ℂ)))
    rw [intervalIntegral.integral_zero] at this
    exact (sub_eq_zero.mp this.symm)
  -- the angular velocity
  have hfim : ∀ r ∈ Icc 0 P.T, (f r).im =
      (scb_rho (P.X r) + scb_rhoR (B r) (P.X r)) / 2 / Complex.normSq (z r) := by
    intro r hr
    have ha := scb_angular (B r) (hstar r hr).1
    rw [hBdet r hr, mul_one] at ha
    simp only [hf, hz, hzp, Complex.div_im]
    rw [← ha]
    ring
  have hfim_pos : ∀ r ∈ Icc 0 P.T, 0 < (f r).im := by
    intro r hr
    rw [hfim r hr]
    have := hnormSq r hr
    have := scb_rho_pos (hstar r hr)
    have := scb_rhoR_pos (hBdet r hr) (hstar r hr)
    positivity
  have hIm : ∀ s t, 0 ≤ s → s ≤ P.T → 0 ≤ t → t ≤ P.T →
      (L t).im - (L s).im = ∫ r in s..t, (f r).im := by
    intro s t hs0 hsT ht0 htT
    have e : L t - L s = ∫ r in s..t, f r :=
      intervalIntegral.integral_interval_sub_left (hfi' 0 t le_rfl hT.le ht0 htT)
        (hfi' 0 s le_rfl hT.le hs0 hsT)
    rw [← Complex.sub_im, e]
    exact (Complex.imCLM.intervalIntegral_comp_comm (hfi' s t hs0 hsT ht0 htT)).symm
  refine ⟨L, by simp [hL], ?_, ?_, ?_⟩
  · intro t ht
    have e1 : z t = φ t * Complex.exp (L t) := by
      simp only [hφ, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    have e2 : z 0 = scb_zc h₀.adjugate := by simp [hz, hB, hg0]
    rw [show scb_zc (h₀.adjugate * P.g t) = z t from rfl, e1, hφt t ht, hφ0, e2]
  · intro s t hs hst' htT
    have hsT : s ≤ P.T := hst'.le.trans htT
    have := hIm s t hs hsT (hs.trans hst'.le) htT
    have hpos : 0 < ∫ r in s..t, (f r).im :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        ((Complex.continuous_im.comp_continuousOn hfc).mono
          (uIcc_subset_Icc ⟨hs, hsT⟩ ⟨hs.trans hst'.le, htT⟩)).intervalIntegrable
        (fun r hr ↦ hfim_pos r ⟨hs.trans hr.1.le, hr.2.le.trans htT⟩) hst'
    linarith
  · intro s t hs hst' htT
    have hsT : s ≤ P.T := hst'.trans htT
    have ht0 : 0 ≤ t := hs.trans hst'
    have hsub : Icc s t ⊆ Icc 0 P.T := Icc_subset_Icc hs htT
    rw [hIm s t hs hsT ht0 htT]
    have hρc : ContinuousOn (fun s ↦ scb_rho (P.X s)) (Icc 0 P.T) :=
      scb_continuous_rho.comp_continuousOn hXc
    have hi1 : IntervalIntegrable (fun r ↦ (f r).im) volume s t :=
      ((Complex.continuous_im.comp_continuousOn hfc).mono
        (uIcc_subset_Icc ⟨hs, hsT⟩ ⟨ht0, htT⟩)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun r ↦ 6 / (2 * κ + 3) * scb_rho (P.X r)) volume s t :=
      ((hρc.const_smul (6 / (2 * κ + 3))).mono
        (uIcc_subset_Icc ⟨hs, hsT⟩ ⟨ht0, htT⟩)).intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on hst' hi1 hi2 (fun r hr ↦ by
      rw [hfim r (hsub hr)]; exact hle r (hsub hr))
    rw [intervalIntegral.integral_const_mul] at hmono
    set I := ∫ r in s..t, scb_rho (P.X r)
    have e : (κ + 3 / 2) * (6 / (2 * κ + 3)) = 3 := by field_simp; ring
    calc (κ + 3 / 2) * ∫ r in s..t, (f r).im ≤ (κ + 3 / 2) * (6 / (2 * κ + 3) * I) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 3 * I := by rw [← mul_assoc, e]

end NormalPeriod

end SmoothedOctagon

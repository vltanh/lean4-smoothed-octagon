module

public import SmoothedOctagon.Reduction.Clearance.Budget

/-!
# A frame bound depending on the total cost

A bound on the Frobenius norm of the frame. Along a state trajectory with
`g(0) = I`, `f = ‖g‖_F² = tr(gᵀg)` satisfies `f' = 2 tr(X gᵀg) ≤ 2ρ f` (`X = ρJ + S`,
`‖S‖² = 2(ρ² - 1)`, and `gᵀg` is positive definite with determinant one), so
`f(t) ≤ 2 exp(2∫₀ᵗ ρ) ≤ 2 e^{2C/3}`, and `‖g‖_F² < 42` when the cost is at most `A_oct`.

Main API:

* `scb_frame_deriv_le`: `Σᵢⱼ gᵢⱼ (gX)ᵢⱼ ≤ ρ(X) ‖g‖_F²` for `det g = 1` and a star state `X`.
* `scb_frobSq_frame_le_exp`: `‖g(t)‖_F² ≤ 2 exp(2 ∫₀ᵗ ρ)` on `[0, T]`.
* `scb_frobSq_frame_le`: `‖g(t)‖_F² ≤ 42` on `[0, T]` when the cost is at most `A_oct`.
* `scb_frobSq_conj_le`: `‖g⁻¹ M g‖_F² ≤ ‖g‖_F⁴ ‖M‖_F²` for `det g = 1`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Real

private theorem scb_cs_aux {a b c p q r : ℝ} (hdX : -a ^ 2 - b * c = 1)
    (hpq : p * q - r ^ 2 = 1) (hp : 0 ≤ p) (hq : 0 ≤ q) (hρ : 0 < (c - b) / 2) :
    a * (p - q) + (b + c) * r ≤ (c - b) / 2 * (p + q) := by
  have hρ1 : ((c - b) / 2) ^ 2 - 1 = a ^ 2 + ((b + c) / 2) ^ 2 := by
    linear_combination hdX
  have hCS : (a * (p - q) + (b + c) * r) ^ 2 ≤
      (a ^ 2 + ((b + c) / 2) ^ 2) * ((p - q) ^ 2 + (2 * r) ^ 2) := by
    nlinarith [sq_nonneg (a * (2 * r) - (b + c) / 2 * (p - q))]
  have h4 : (p - q) ^ 2 + (2 * r) ^ 2 = (p + q) ^ 2 - 4 := by
    linear_combination -4 * hpq
  rw [← hρ1, h4] at hCS
  have hρsq : 1 ≤ ((c - b) / 2) ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg ((b + c) / 2)]
  have e : ((c - b) / 2 * (p + q)) ^ 2 = (((c - b) / 2) ^ 2 - 1) * ((p + q) ^ 2 - 4) +
      (4 * ((c - b) / 2) ^ 2 + (p + q) ^ 2 - 4) := by ring
  have hsq : (a * (p - q) + (b + c) * r) ^ 2 ≤ ((c - b) / 2 * (p + q)) ^ 2 := by
    rw [e]; nlinarith [sq_nonneg (p + q)]
  exact le_of_sq_le_sq hsq (by positivity)

/-- `tr(X gᵀg) ≤ ρ(X) tr(gᵀg)`: with `gᵀg = [[p, r], [r, q]]`, `pq - r² = 1`, and
`X = [[a, b], [c, -a]]`, `ρ = (c - b)/2`, `ρ² - 1 = a² + ((b + c)/2)²`, Cauchy–Schwarz gives
`(a(p - q) + (b + c) r)² ≤ (ρ² - 1)((p + q)² - 4) ≤ ρ² (p + q)²`. -/
theorem scb_frame_deriv_le {g X : Mat2} (hg : g.det = 1) (hX : IsStarState X) :
    g 0 0 * (g * X) 0 0 + g 0 1 * (g * X) 0 1 + g 1 0 * (g * X) 1 0 + g 1 1 * (g * X) 1 1 ≤
      scb_rho X * frobSq g := by
  have hρ := scb_rho_pos hX
  obtain ⟨htr, hdX, -, -, -⟩ := hX
  have e11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at htr; linarith
  rw [Matrix.det_fin_two] at hg hdX
  rw [e11] at hdX
  rw [scb_rho_eq] at hρ ⊢
  have hD : g 0 0 * (g * X) 0 0 + g 0 1 * (g * X) 0 1 + g 1 0 * (g * X) 1 0 +
      g 1 1 * (g * X) 1 1 = X 0 0 * ((g 0 0 ^ 2 + g 1 0 ^ 2) - (g 0 1 ^ 2 + g 1 1 ^ 2)) +
        (X 0 1 + X 1 0) * (g 0 0 * g 0 1 + g 1 0 * g 1 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, e11]
    ring
  have hf : frobSq g = (g 0 0 ^ 2 + g 1 0 ^ 2) + (g 0 1 ^ 2 + g 1 1 ^ 2) := by
    simp only [frobSq]; ring
  have hpq : (g 0 0 ^ 2 + g 1 0 ^ 2) * (g 0 1 ^ 2 + g 1 1 ^ 2) -
      (g 0 0 * g 0 1 + g 1 0 * g 1 1) ^ 2 = 1 := by
    linear_combination (g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1) * hg
  rw [hD, hf]
  exact scb_cs_aux (by linear_combination hdX) hpq (by positivity) (by positivity) hρ

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}

/-- **Gronwall for the frame**: `‖g(t)‖_F² ≤ 2 exp(2 ∫₀ᵗ ρ)`. -/
theorem scb_frobSq_frame_le_exp (hst : IsStateTrajectory T u g X) (hg0 : g 0 = 1) :
    ∀ t ∈ Icc 0 T, frobSq (g t) ≤ 2 * Real.exp (2 * ∫ s in (0 : ℝ)..t, scb_rho (X s)) := by
  have hT : 0 < T := hst.1
  have hdet : ∀ s ∈ Icc 0 T, (g s).det = 1 := fun s hs ↦ (hst.2.2.2.1 s hs).1
  have hstar : ∀ s ∈ Icc 0 T, IsStarState (X s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  have hgc := scb_continuousOn_frame hst
  have hρc := scb_continuousOn_rho hst
  set P : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, scb_rho (X s) with hP
  have hρi : IntervalIntegrable (fun s ↦ scb_rho (X s)) volume 0 T :=
    (hρc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hPc : ContinuousOn P (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := fun s ↦ scb_rho (X s)) (hρc.integrableOn_Icc.mono_set (by rw [uIcc_of_le hT.le]))
    rwa [uIcc_of_le hT.le] at this
  have hPd : ∀ t ∈ Ioo 0 T, HasDerivAt P (scb_rho (X t)) t := by
    intro t ht
    exact intervalIntegral.integral_hasDerivAt_right
      (hρi.mono_set (by
        rw [uIcc_of_le hT.le, uIcc_of_le ht.1.le]
        exact Icc_subset_Icc_right ht.2.le))
      ((hρc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hρc.continuousAt (Icc_mem_nhds ht.1 ht.2))
  set F : ℝ → ℝ := fun t ↦ frobSq (g t) * Real.exp (-(2 * P t)) with hF
  have hfc : ContinuousOn (fun t ↦ frobSq (g t)) (Icc 0 T) := by
    have hc : Continuous frobSq := by unfold frobSq; fun_prop
    exact hc.comp_continuousOn hgc
  have hFc : ContinuousOn F (Icc 0 T) :=
    hfc.mul (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hPc).neg)
  have hFd : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (2 * (g t 0 0 * (g t * X t) 0 0 + g t 0 1 * (g t * X t) 0 1 + g t 1 0 * (g t * X t) 1 0 +
        g t 1 1 * (g t * X t) 1 1 - scb_rho (X t) * frobSq (g t)) *
        Real.exp (-(2 * P t))) t := by
    intro t ht
    have hd := scb_hasDerivAtEntrywise_frame hst ht
    have hf : HasDerivAt (fun t ↦ frobSq (g t))
        (2 * (g t 0 0 * (g t * X t) 0 0 + g t 0 1 * (g t * X t) 0 1 +
          g t 1 0 * (g t * X t) 1 0 + g t 1 1 * (g t * X t) 1 1)) t := by
      unfold frobSq
      convert ((((hd 0 0).pow 2).add ((hd 0 1).pow 2)).add ((hd 1 0).pow 2)).add
        ((hd 1 1).pow 2) using 1
      simp
      ring
    have he := ((hPd t ht).const_mul 2).neg.exp
    convert hf.mul he using 1
    simp only [Pi.neg_apply]
    ring
  have hanti : AntitoneOn F (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFc ?_ ?_
    · rw [interior_Icc]
      exact fun t ht ↦ (hFd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hFd t ht).deriv]
      have := scb_frame_deriv_le (hdet t (Ioo_subset_Icc_self ht))
        (hstar t (Ioo_subset_Icc_self ht))
      have := Real.exp_pos (-(2 * P t))
      nlinarith
  intro t ht
  have h := hanti (left_mem_Icc.mpr hT.le) ht ht.1
  have hF0 : F 0 = 2 := by
    simp only [hF, hP, hg0, intervalIntegral.integral_same, mul_zero, neg_zero, Real.exp_zero,
      mul_one]
    simp [frobSq]
    norm_num
  rw [hF0] at h
  simp only [hF] at h
  have hE := Real.exp_pos (2 * P t)
  have : frobSq (g t) = frobSq (g t) * Real.exp (-(2 * P t)) * Real.exp (2 * P t) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [this]
  exact mul_le_mul_of_nonneg_right h hE.le

/-- **The frame bound**. For a state trajectory with `g(0) = I` and cost at most `A_oct`,
`‖g(t)‖_F² ≤ 42` on `[0, T]`: the cost is `3∫₀ᵀ ρ`, so `scb_frobSq_frame_le_exp` gives
`‖g(t)‖_F² ≤ 2 e^{2A_oct/3} < 42`. -/
theorem scb_frobSq_frame_le (hst : IsStateTrajectory T u g X) (hg0 : g 0 = 1)
    (hcost : reinhardtCost T X ≤ octagonCost) : ∀ t ∈ Icc 0 T, frobSq (g t) ≤ 42 := by
  intro t ht
  have hT : 0 < T := hst.1
  have hstar : ∀ s ∈ Icc 0 T, IsStarState (X s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  have hρc := scb_continuousOn_rho hst
  have hρi : IntervalIntegrable (fun s ↦ scb_rho (X s)) volume 0 T :=
    (hρc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hmono : ∫ s in (0 : ℝ)..t, scb_rho (X s) ≤ ∫ s in (0 : ℝ)..T, scb_rho (X s) := by
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ hρi
    refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ ?_
    exact (scb_rho_pos (hstar s (Ioc_subset_Icc_self hs))).le
  have hcostI : reinhardtCost T X = 3 * ∫ s in (0 : ℝ)..T, scb_rho (X s) := by
    rw [reinhardtCost, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    congr 1; funext s; simp only [scb_rho]; ring
  have hoc := scb_octagonCost_lt
  have h3 : 2 * ∫ s in (0 : ℝ)..t, scb_rho (X s) ≤ 3 := by linarith
  have he : Real.exp 3 < 21 := by
    have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [e]
    have := Real.exp_one_lt_d9
    have := Real.exp_pos 1
    nlinarith
  have := scb_frobSq_frame_le_exp hst hg0 t ht
  have := Real.exp_le_exp.mpr h3
  linarith

/-- `‖g⁻¹ M g‖_F² ≤ ‖g‖_F⁴ ‖M‖_F²` for `det g = 1`. -/
theorem scb_frobSq_conj_le {g : Mat2} (hg : g.det = 1) (M : Mat2) :
    frobSq (g⁻¹ * M * g) ≤ frobSq g ^ 2 * frobSq M := by
  have hinv : g⁻¹ = g.adjugate := by rw [Matrix.inv_def, hg, Ring.inverse_one, one_smul]
  rw [hinv]
  have h1 := scb_frobSq_mul_le (g.adjugate * M) g
  have h2 := scb_frobSq_mul_le g.adjugate M
  rw [scb_frobSq_adjugate] at h2
  have := scb_frobSq_nonneg g
  have := scb_frobSq_nonneg M
  calc frobSq (g.adjugate * M * g) ≤ frobSq (g.adjugate * M) * frobSq g := h1
    _ ≤ frobSq g * frobSq M * frobSq g := mul_le_mul_of_nonneg_right h2 (by assumption)
    _ = frobSq g ^ 2 * frobSq M := by ring

end SmoothedOctagon.Reduction

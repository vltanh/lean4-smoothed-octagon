module

public import SmoothedOctagon.Reduction.Clearance.Winding
public import SmoothedOctagon.Period.Twist
public import SmoothedOctagon.Period.Hamiltonian
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The complete-period budget inequality

Write `b(c) = (2π-c)/(3(π-c))` and `b_oct = b(A_oct)`. Integrating the equilibrium
inequality against the winding estimate gives `|λ| ≤ b_oct ‖Λ₁(t)-(3/2)λJ‖_F`.
Rebasing the period gives this bound at every time.

Main API: `clr_budgetCoeff`, `clr_budgetOct`, `clr_budget`, `clr_abs_lam_le`,
`clr_lam_sq_le`, and the spatial conservation and twisted equilibrium inequalities.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Real

/-! ### The numerical margin -/

/-- `A_oct < 3.127` (`A_oct = √12 (8 - √32 - log 2)/(√8 - 1) ≈ 3.12605`), from rational
enclosures of `√12`, `√32`, `√8` and `log 2`. -/
theorem clr_octagonCost_lt : octagonCost < 3.127 := by
  have h12 : √12 < 3.46411 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h32 : 5.65685 < √32 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h32' : √32 < 5.6569 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h8 : 2.828427 < √8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have h12p : 0 ≤ √12 := Real.sqrt_nonneg _
  have hD : 0 < √8 - 1 := by linarith
  have hN : 0 ≤ 8 - √32 - Real.log 2 := by linarith
  rw [octagonCost, octagonDensity, mul_div_assoc', div_lt_iff₀ hD]
  have : √12 * (8 - √32 - Real.log 2) ≤ 3.46411 * (8 - √32 - Real.log 2) :=
    mul_le_mul_of_nonneg_right h12.le hN
  nlinarith

/-! ### The budget inequality at the initial time -/

/-- The budget coefficient at cost `c < π`. -/
noncomputable def clr_budgetCoeff (c : ℝ) : ℝ := (2 * π - c) / (3 * (π - c))

/-- The budget coefficient at the octagon cost. -/
noncomputable def clr_budgetOct : ℝ := clr_budgetCoeff octagonCost

theorem clr_budgetCoeff_mono {c C : ℝ} (h : c ≤ C) (hC : C < π) :
    clr_budgetCoeff c ≤ clr_budgetCoeff C := by
  unfold clr_budgetCoeff
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h)]

theorem clr_budgetOct_ge_two_thirds : (2 / 3 : ℝ) ≤ clr_budgetOct := by
  have hgap : 0 < π - octagonCost := sub_pos.mpr octagonCost_lt_pi
  have hcost : 0 ≤ octagonCost := by
    rw [← volume_real_smoothedPolygonDisk_one]
    exact measureReal_nonneg
  unfold clr_budgetOct clr_budgetCoeff
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Integrating the equilibrium inequality against the winding bound gives the exact
budget `μ ≤ b_oct ‖M + (3/2)μJ‖_F`. The only cost gap used is `A_oct < π`. -/
theorem clr_budget {T : ℝ} {u : ℝ → Fin 3 → ℝ} {h Y : ℝ → Mat2}
    (hadm : IsReinhardtAdmissible T u h Y) (hcost : reinhardtCost T Y ≤ octagonCost)
    {M : Mat2} {μ : ℝ}
    (hmax : ∀ s ∈ Icc 0 T, traceForm ((h s)⁻¹ * M * h s + (3 / 2 * μ) • J) (Y s) ≤ 0) :
    μ ≤ clr_budgetOct * √(frobSq (M + (3 / 2 * μ) • J)) := by
  have hwind := clr_winding hadm
  obtain ⟨hst, -, -, -⟩ := hadm
  have hT : 0 < T := hst.1
  have hdet : ∀ s ∈ Icc 0 T, (h s).det = 1 := fun s hs ↦ (hst.2.2.2.1 s hs).1
  have hstar : ∀ s ∈ Icc 0 T, IsStarState (Y s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  set A₀ := M + (3 / 2 * μ) • J with hA₀
  set a₀ := √(frobSq A₀) with ha₀
  have ha₀0 : 0 ≤ a₀ := Real.sqrt_nonneg _
  -- the pointwise inequality `3μρ_R + tr(A₀ V) ≤ 3μρ` with `tr(A₀ V) ≥ -2 a₀ ρ_R`
  have hpt : ∀ s ∈ Icc 0 T,
      (3 * μ - 2 * a₀) * clr_rhoR (h s) (Y s) ≤ 3 * μ * clr_rho (Y s) := by
    intro s hs
    have hm := hmax s hs
    have hinv : (h s)⁻¹ = (h s).adjugate := by
      rw [Matrix.inv_def, hdet s hs, Ring.inverse_one, one_smul]
    set V := h s * Y s * (h s).adjugate with hV
    have e1 : traceForm ((h s)⁻¹ * M * h s + (3 / 2 * μ) • J) (Y s) =
        traceForm A₀ V + 3 * μ * clr_rhoR (h s) (Y s) - 3 * μ * clr_rho (Y s) := by
      have t1 : traceForm ((h s).adjugate * M * h s) (Y s) = traceForm M V := by
        simp only [traceForm, hV, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      have t2 : traceForm A₀ V = traceForm M V + 3 / 2 * μ * traceForm J V := by
        simp only [hA₀, traceForm, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul,
          Matrix.trace_smul, smul_eq_mul]
      have t3 : traceForm ((h s).adjugate * M * h s + (3 / 2 * μ) • J) (Y s) =
          traceForm ((h s).adjugate * M * h s) (Y s) + 3 / 2 * μ * traceForm J (Y s) := by
        simp only [traceForm, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul,
          Matrix.trace_smul, smul_eq_mul]
      rw [hinv, t3, t1, clr_rhoR, clr_rho, clr_rho, ← hV]
      linarith
    rw [e1] at hm
    -- Cauchy–Schwarz and `‖V‖_F² = 4ρ_R² - 2`
    have hR := clr_rhoR_pos (hdet s hs) (hstar s hs)
    have hfV := clr_frobSq_conj (hdet s hs) (hstar s hs)
    have hCS := clr_traceForm_sq_le A₀ V
    rw [← hV] at hfV
    rw [hfV] at hCS
    have hsq : traceForm A₀ V ^ 2 ≤ frobSq A₀ * (2 * clr_rhoR (h s) (Y s)) ^ 2 := by
      have := clr_frobSq_nonneg A₀
      nlinarith
    have habs := Real.abs_le_sqrt hsq
    rw [Real.sqrt_mul (clr_frobSq_nonneg A₀), Real.sqrt_sq (by linarith), ← ha₀] at habs
    have := neg_abs_le (traceForm A₀ V)
    nlinarith
  -- integrate
  have hρc := clr_continuousOn_rho hst
  have hρRc := clr_continuousOn_rhoR hst
  have hsub : uIcc 0 T ⊆ Icc 0 T := by rw [uIcc_of_le hT.le]
  have hρi : IntervalIntegrable (fun s ↦ clr_rho (Y s)) volume 0 T :=
    (hρc.mono hsub).intervalIntegrable
  have hρRi : IntervalIntegrable (fun s ↦ clr_rhoR (h s) (Y s)) volume 0 T :=
    (hρRc.mono hsub).intervalIntegrable
  have hint := intervalIntegral.integral_mono_on hT.le (hρRi.const_mul (3 * μ - 2 * a₀))
    (hρi.const_mul (3 * μ)) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  rw [intervalIntegral.integral_add hρi hρRi] at hwind
  have hcostI : reinhardtCost T Y = 3 * ∫ s in (0 : ℝ)..T, clr_rho (Y s) := by
    rw [reinhardtCost, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1; funext s; simp only [clr_rho]; ring
  set I := ∫ s in (0 : ℝ)..T, clr_rho (Y s)
  set IR := ∫ s in (0 : ℝ)..T, clr_rhoR (h s) (Y s)
  have hgap : 0 < π - octagonCost := sub_pos.mpr octagonCost_lt_pi
  have hcost0 : 0 ≤ 3 * I := by
    have hI0 : 0 ≤ I := by
      apply intervalIntegral.integral_nonneg hT.le
      intro s hs
      exact (clr_rho_pos (hstar s hs)).le
    positivity
  have hI : 3 * I ≤ octagonCost := by rwa [hcostI] at hcost
  by_cases hsmall : 3 * μ ≤ 2 * a₀
  · have hb := clr_budgetOct_ge_two_thirds
    have := mul_le_mul_of_nonneg_right hb ha₀0
    dsimp only [a₀, A₀] at *
    linarith
  · have hK : 0 < 3 * μ - 2 * a₀ := by linarith
    have hwind' : 2 * π / 3 - I ≤ IR := by linarith
    have hmul := mul_le_mul_of_nonneg_left hwind' hK.le
    have hbase : 3 * μ * (π - 3 * I) ≤ a₀ * (2 * π - 3 * I) := by nlinarith
    have hμ : μ ≤ clr_budgetCoeff (3 * I) * a₀ := by
      rw [clr_budgetCoeff, div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < 3 * (π - 3 * I))]
      nlinarith
    exact hμ.trans (mul_le_mul_of_nonneg_right
      (clr_budgetCoeff_mono hI octagonCost_lt_pi) ha₀0)

/-! ### Conservation and the equilibrium inequality along an extremal -/

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}

/-- **Spatial conservation** (Hales–Vajjha, Corollary 6.5.3): `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` on
`[0, T]`. -/
theorem clr_conservation (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t := by
  obtain ⟨hst, hg0, -, -, -, -, -, -, hΛ, -, -⟩ := hext
  obtain ⟨-, -, -, hsd, hgI, hXI⟩ := hst
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hΛc : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛ
  have hg : ∀ t ∈ Icc 0 T, Matrix.HasDerivWithinAtEntrywise g (g t * X t) (Icc 0 T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI ht ((hgc.mul hXc) t ht)
  have hΛ' : ∀ t ∈ Icc 0 T,
      Matrix.HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hΛ ht
      (((hΛc.mul hXc).sub (hXc.mul hΛc)) t ht)
  exact fun t ht ↦ (corollary6_5_3 T g X Λ₁ hg hg0 (fun t ht ↦ (hsd t ht).1) hΛ' t ht).1

/-- **The equilibrium inequality at every time**: `tr((Λ₁ - (3/2)λJ) X) ≤ 0` on `[0, T]`. Every
vertex Hamiltonian is `≤ 0`, and `clr_vertex_bounds` turns this into the inequality. -/
theorem clr_traceForm_le_zero (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) ≤ 0 := by
  intro t ht
  have hH := (IsPontryaginExtremal.vertexHamiltonian_max_eq_zero hext t ht).1
  obtain ⟨-, hWtr, hWX, -⟩ := hext.2.2.2.2.2.2.2.1 t ht
  exact (clr_vertex_bounds (hext.1.2.2.2.1 t ht).2 hWtr hWX hH).1

/-- The equilibrium inequality along the twisted extension `G(τ) = g(τ - nT) Rⁿ`,
`Y(τ) = R⁻ⁿ X(τ - nT) Rⁿ`, with the costate `G(τ)⁻¹ Λ₁(0) G(τ)`, for every `τ ≥ 0`. -/
theorem clr_twisted_traceForm_le (hT : 0 < T) {c : ℝ}
    (hcons : ∀ t ∈ Icc 0 T, Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t)
    (hle : ∀ t ∈ Icc 0 T, traceForm (Λ₁ t + c • J) (X t) ≤ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    traceForm ((twistedFrame T g τ)⁻¹ * Λ₁ 0 * twistedFrame T g τ + c • J)
      (twistedState T X τ) ≤ 0 := by
  have hr : τ - ⌊τ / T⌋₊ * T ∈ Icc 0 T := Ico_subset_Icc_self (sub_floor_mul_mem_Ico hT hτ)
  set r := τ - ⌊τ / T⌋₊ * T
  set n := ⌊τ / T⌋₊
  have e1 : twistedFrame T g τ = g r * R ^ n := rfl
  have e2 : twistedState T X τ = (R ^ n)⁻¹ * X r * R ^ n := rfl
  have e3 : (g r * R ^ n)⁻¹ * Λ₁ 0 * (g r * R ^ n) + c • J =
      (R ^ n)⁻¹ * (Λ₁ r + c • J) * R ^ n := by
    rw [Matrix.mul_inv_rev, hcons r hr, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, conj_R_pow_J]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3, poly_traceForm_conj (R_pow_mul_inv n)]
  exact hle r hr

/-- Rebasing the complete-period budget at each time gives the absolute-value
budget for the Pontryagin multiplier. -/
theorem clr_abs_lam_le (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost) :
    ∀ t ∈ Icc 0 T, |lam| ≤ clr_budgetOct * √(frobSq (Λ₁ t - (3 / 2 * lam) • J)) := by
  intro t₀ ht₀
  have hcons := clr_conservation hext
  have htr := clr_traceForm_le_zero hext
  obtain ⟨hst, hg0, hgT, hXT, -, -, hlam, -⟩ := hext
  have hT : 0 < T := hst.1
  have hadm : IsReinhardtAdmissible T u g X := ⟨hst, hg0, hgT, hXT⟩
  have hdet : ∀ t ∈ Icc 0 T, (g t).det = 1 := fun t ht ↦ (hst.2.2.2.1 t ht).1
  have hadm' := SmoothedOctagon.isReinhardtAdmissible_rebase hadm ht₀.1
  have hcost' : reinhardtCost T (fun s ↦ twistedState T X (t₀ + s)) ≤ octagonCost := by
    rw [reinhardtCost_rebase hT ht₀.1 hXT]; exact hcost
  have hgR : g T = g 0 * R := by rw [hgT, hg0, Matrix.one_mul]
  have hG₀ : twistedFrame T g t₀ = g t₀ := twistedFrame_of_mem_Icc hT hgR ht₀
  have hunit : IsUnit (g t₀).det := by rw [hdet t₀ ht₀]; exact isUnit_one
  have hle : ∀ t ∈ Icc 0 T, traceForm (Λ₁ t + (3 / 2 * -lam) • J) (X t) ≤ 0 := by
    intro t ht
    have := htr t ht
    rwa [sub_eq_add_neg, ← neg_smul, show -(3 / 2 * lam) = 3 / 2 * -lam by ring] at this
  have hmax : ∀ s ∈ Icc 0 T, traceForm ((rebaseFrame T g t₀ s)⁻¹ * Λ₁ t₀ *
      rebaseFrame T g t₀ s + (3 / 2 * -lam) • J) (twistedState T X (t₀ + s)) ≤ 0 := by
    intro s hs
    have hτ : 0 ≤ t₀ + s := add_nonneg ht₀.1 hs.1
    have e : (rebaseFrame T g t₀ s)⁻¹ * Λ₁ t₀ * rebaseFrame T g t₀ s =
        (twistedFrame T g (t₀ + s))⁻¹ * Λ₁ 0 * twistedFrame T g (t₀ + s) := by
      rw [rebaseFrame, hG₀, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hunit,
        hcons t₀ ht₀]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (g t₀) (g t₀)⁻¹, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul,
        ← Matrix.mul_assoc (g t₀) (g t₀)⁻¹, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
    rw [e]
    exact clr_twisted_traceForm_le hT hcons hle hτ
  have hb := clr_budget hadm' hcost' hmax
  have e2 : Λ₁ t₀ + (3 / 2 * -lam) • J = Λ₁ t₀ - (3 / 2 * lam) • J := by
    rw [sub_eq_add_neg, ← neg_smul]; congr 2; ring
  rw [e2] at hb
  rw [abs_of_nonpos hlam]
  exact hb

theorem clr_lam_sq_le (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost) :
    ∀ t ∈ Icc 0 T, lam ^ 2 ≤ clr_budgetOct ^ 2 * frobSq (Λ₁ t - (3 / 2 * lam) • J) := by
  intro t ht
  have hb := clr_abs_lam_le hext hcost t ht
  have hs := pow_le_pow_left₀ (abs_nonneg lam) hb 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (clr_frobSq_nonneg _)] using hs

end SmoothedOctagon.Reduction

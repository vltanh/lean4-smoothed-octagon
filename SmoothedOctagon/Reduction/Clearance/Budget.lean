module

public import SmoothedOctagon.Reduction.Clearance.Winding
public import SmoothedOctagon.Period.Twist
public import SmoothedOctagon.Period.Hamiltonian
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The complete-period budget inequality

For a Pontryagin extremal of cost at most `A_oct`, at every time `t ∈ [0, T]`,
`|λ| ≤ 100 ‖Λ₁(t) - (3/2)λJ‖_F`. The bound is proved at the initial time by integrating the
equilibrium inequality against the winding bound `∫(ρ + ρ_R) ≥ 2π/3`, and moved to every time by
rebasing the period.

Main API:

* `scb_octagonCost_lt`: `A_oct < 3.127` (`A_oct ≈ 3.12605`).
* `scb_budget`: the budget inequality at the initial time of an admissible trajectory with
  `tr((h⁻¹ M h + (3/2)μJ) Y) ≤ 0`: `μ ≤ 100 ‖M + (3/2)μJ‖_F`.
* `scb_conservation`: `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` on `[0, T]` (Corollary 6.5.3).
* `scb_traceForm_le_zero`: `tr((Λ₁ - (3/2)λJ) X) ≤ 0` at every time.
* `scb_twisted_traceForm_le`: the same inequality along the twisted extension, for `t ≥ 0`.
* `scb_lam_sq_le`: `λ² ≤ 10⁴ ‖Λ₁(t) - (3/2)λJ‖_F²` at every `t ∈ [0, T]`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Real

/-! ### The numerical margin -/

/-- `A_oct < 3.127` (`A_oct = √12 (8 - √32 - log 2)/(√8 - 1) ≈ 3.12605`), from rational
enclosures of `√12`, `√32`, `√8` and `log 2`. -/
theorem scb_octagonCost_lt : octagonCost < 3.127 := by
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

/-- **The budget inequality**. Let `(T, u, h, Y)` be admissible with cost at most `A_oct`, `μ`
real, and `M` a matrix with `tr((h⁻¹ M h + (3/2)μJ) Y) ≤ 0` on `[0, T]` (the equilibrium
inequality for the costate `Λ₁ = h⁻¹ M h`). Then `μ ≤ 100 ‖M + (3/2)μJ‖_F`.

Proof: with `A₀ = M + (3/2)μJ` and `V = h Y h⁻¹`, the hypothesis reads
`3μ ρ_R + tr(A₀ V) ≤ 3μ ρ`, and Cauchy–Schwarz with `‖V‖_F² = 4ρ_R² - 2` gives
`tr(A₀ V) ≥ -2‖A₀‖ ρ_R`. Integrating, `(3μ - 2‖A₀‖) ∫ρ_R ≤ 3μ ∫ρ`. If `μ > 100 ‖A₀‖`, then
`3μ - 2‖A₀‖ > (149/50) μ`, and the winding bound `∫ρ_R ≥ 2π/3 - ∫ρ` gives
`(149/50)(2π/3 - ∫ρ) < 3∫ρ`, which fails because the cost `3∫ρ` is below `3.127`. -/
theorem scb_budget {T : ℝ} {u : ℝ → Fin 3 → ℝ} {h Y : ℝ → Mat2}
    (hadm : IsReinhardtAdmissible T u h Y) (hcost : reinhardtCost T Y ≤ octagonCost)
    {M : Mat2} {μ : ℝ}
    (hmax : ∀ s ∈ Icc 0 T, traceForm ((h s)⁻¹ * M * h s + (3 / 2 * μ) • J) (Y s) ≤ 0) :
    μ ≤ 100 * √(frobSq (M + (3 / 2 * μ) • J)) := by
  have hwind := scb_winding hadm
  obtain ⟨hst, -, -, -⟩ := hadm
  have hT : 0 < T := hst.1
  have hdet : ∀ s ∈ Icc 0 T, (h s).det = 1 := fun s hs ↦ (hst.2.2.2.1 s hs).1
  have hstar : ∀ s ∈ Icc 0 T, IsStarState (Y s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  set A₀ := M + (3 / 2 * μ) • J with hA₀
  set a₀ := √(frobSq A₀) with ha₀
  have ha₀0 : 0 ≤ a₀ := Real.sqrt_nonneg _
  -- the pointwise inequality `3μρ_R + tr(A₀ V) ≤ 3μρ` with `tr(A₀ V) ≥ -2 a₀ ρ_R`
  have hpt : ∀ s ∈ Icc 0 T,
      (3 * μ - 2 * a₀) * scb_rhoR (h s) (Y s) ≤ 3 * μ * scb_rho (Y s) := by
    intro s hs
    have hm := hmax s hs
    have hinv : (h s)⁻¹ = (h s).adjugate := by
      rw [Matrix.inv_def, hdet s hs, Ring.inverse_one, one_smul]
    set V := h s * Y s * (h s).adjugate with hV
    have e1 : traceForm ((h s)⁻¹ * M * h s + (3 / 2 * μ) • J) (Y s) =
        traceForm A₀ V + 3 * μ * scb_rhoR (h s) (Y s) - 3 * μ * scb_rho (Y s) := by
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
      rw [hinv, t3, t1, scb_rhoR, scb_rho, scb_rho, ← hV]
      linarith
    rw [e1] at hm
    -- Cauchy–Schwarz and `‖V‖_F² = 4ρ_R² - 2`
    have hR := scb_rhoR_pos (hdet s hs) (hstar s hs)
    have hfV := scb_frobSq_conj (hdet s hs) (hstar s hs)
    have hCS := scb_traceForm_sq_le A₀ V
    rw [← hV] at hfV
    rw [hfV] at hCS
    have hsq : traceForm A₀ V ^ 2 ≤ frobSq A₀ * (2 * scb_rhoR (h s) (Y s)) ^ 2 := by
      have := scb_frobSq_nonneg A₀
      nlinarith
    have habs := Real.abs_le_sqrt hsq
    rw [Real.sqrt_mul (scb_frobSq_nonneg A₀), Real.sqrt_sq (by linarith), ← ha₀] at habs
    have := neg_abs_le (traceForm A₀ V)
    nlinarith
  -- integrate
  have hρc := scb_continuousOn_rho hst
  have hρRc := scb_continuousOn_rhoR hst
  have hsub : uIcc 0 T ⊆ Icc 0 T := by rw [uIcc_of_le hT.le]
  have hρi : IntervalIntegrable (fun s ↦ scb_rho (Y s)) volume 0 T :=
    (hρc.mono hsub).intervalIntegrable
  have hρRi : IntervalIntegrable (fun s ↦ scb_rhoR (h s) (Y s)) volume 0 T :=
    (hρRc.mono hsub).intervalIntegrable
  have hint := intervalIntegral.integral_mono_on hT.le (hρRi.const_mul (3 * μ - 2 * a₀))
    (hρi.const_mul (3 * μ)) hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  rw [intervalIntegral.integral_add hρi hρRi] at hwind
  have hcostI : reinhardtCost T Y = 3 * ∫ s in (0 : ℝ)..T, scb_rho (Y s) := by
    rw [reinhardtCost, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1; funext s; simp only [scb_rho]; ring
  set I := ∫ s in (0 : ℝ)..T, scb_rho (Y s)
  set IR := ∫ s in (0 : ℝ)..T, scb_rhoR (h s) (Y s)
  have hoc := scb_octagonCost_lt
  have hpi := Real.pi_gt_d6
  have hI : I < 3.127 / 3 := by linarith
  by_contra hcon
  push Not at hcon
  have hμpos : 0 < μ := by linarith
  have hK : (149 / 50) * μ < 3 * μ - 2 * a₀ := by linarith
  have hgap : 0 < 2 * π / 3 - I := by linarith
  have h1 : (3 * μ - 2 * a₀) * (2 * π / 3 - I) ≤ (3 * μ - 2 * a₀) * IR :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (149 / 50) * μ * (2 * π / 3 - I) < (3 * μ - 2 * a₀) * (2 * π / 3 - I) :=
    mul_lt_mul_of_pos_right hK hgap
  have h3 : (149 / 50) * (2 * π / 3 - I) < 3 * I := by
    have : μ * ((149 / 50) * (2 * π / 3 - I)) < μ * (3 * I) := by nlinarith
    exact lt_of_mul_lt_mul_left this hμpos.le
  nlinarith

/-! ### Conservation and the equilibrium inequality along an extremal -/

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}

/-- **Spatial conservation** (Hales–Vajjha, Corollary 6.5.3): `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` on
`[0, T]`. -/
theorem scb_conservation (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
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
vertex Hamiltonian is `≤ 0`, and `scb_vertex_bounds` turns this into the inequality. -/
theorem scb_traceForm_le_zero (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) ≤ 0 := by
  intro t ht
  have hH := (IsPontryaginExtremal.vertexHamiltonian_max_eq_zero hext t ht).1
  obtain ⟨-, hWtr, hWX, -⟩ := hext.2.2.2.2.2.2.2.1 t ht
  exact (scb_vertex_bounds (hext.1.2.2.2.1 t ht).2 hWtr hWX hH).1

/-- The equilibrium inequality along the twisted extension `G(τ) = g(τ - nT) Rⁿ`,
`Y(τ) = R⁻ⁿ X(τ - nT) Rⁿ`, with the costate `G(τ)⁻¹ Λ₁(0) G(τ)`, for every `τ ≥ 0`. -/
theorem scb_twisted_traceForm_le (hT : 0 < T) {c : ℝ}
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

/-- **The budget inequality at every time**. For a Pontryagin extremal of cost at most `A_oct`,
`λ² ≤ 10⁴ ‖Λ₁(t) - (3/2)λJ‖_F²` at every `t ∈ [0, T]`: apply `scb_budget` to the period rebased at
`t` (`ĝ(s) = G(t)⁻¹ G(t + s)`, `X̂(s) = Y(t + s)`, initial costate `Λ₁(t)`), which is admissible
with the same cost. -/
theorem scb_lam_sq_le (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost) :
    ∀ t ∈ Icc 0 T, lam ^ 2 ≤ 10 ^ 4 * frobSq (Λ₁ t - (3 / 2 * lam) • J) := by
  intro t₀ ht₀
  have hcons := scb_conservation hext
  have htr := scb_traceForm_le_zero hext
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
    exact scb_twisted_traceForm_le hT hcons hle hτ
  have hb := scb_budget hadm' hcost' hmax
  have e2 : Λ₁ t₀ + (3 / 2 * -lam) • J = Λ₁ t₀ - (3 / 2 * lam) • J := by
    rw [sub_eq_add_neg, ← neg_smul]; congr 2; ring
  rw [e2] at hb
  have hf := scb_frobSq_nonneg (Λ₁ t₀ - (3 / 2 * lam) • J)
  have hs := Real.sq_sqrt hf
  have hl : 0 ≤ -lam := by linarith
  nlinarith [Real.sqrt_nonneg (frobSq (Λ₁ t₀ - (3 / 2 * lam) • J))]

end SmoothedOctagon.Reduction

module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.Clearance.Frame

/-!
# Singular clearance and projective bounds of a competitive Pontryagin lift

For a Pontryagin extremal (normal or abnormal) whose cost is at most `A_oct` and whose state stays
in `𝔥**`:

* (clearance) the costate stays away from the singular locus `Λ₁ = (3/2)λJ`, `Λ_R = 0`
  in proportion to its size: `‖𝒫(t)‖ ≤ 251 Q(t)`, with `‖𝒫‖² = λ² + ‖Λ₁‖² + ‖Λ_R‖²` and
  `Q² = ‖Λ₁ - (3/2)λJ‖² + ‖Λ_R‖²`. Hence for the lift normalized by `‖𝒫(0)‖ = 1`,
  `D(t) ≥ Q(t) > 10⁻⁸/251 > 10⁻¹¹`.
* (projective bounds) `10⁻⁸ ‖𝒫(0)‖ < ‖𝒫(t)‖ < 10⁸ ‖𝒫(0)‖`.

Both are homogeneous in `(λ, Λ₁, Λ_R)`, so no normalization is imposed; they are stated with squared
norms (`covectorNormSq`, `singularGapSq`).

Main API:

* `covectorNormSq_le_singularGapSq`: `‖𝒫(t)‖² ≤ 251² Q(t)²` on `[0, T]`.
* `covectorNormSq_projective_bounds`: `‖𝒫(0)‖² < 10¹⁶ ‖𝒫(t)‖²` and `‖𝒫(t)‖² < 10¹⁶ ‖𝒫(0)‖²`
  on `[0, T]`.

The ingredients are in `Reduction/Clearance/`: `Algebra` (matrix algebra, the equilibrium
inequality and the bound on `Λ_R`), `Winding` (the angular identity and `∫(ρ + ρ_R) ≥ 2π/3`),
`Budget` (the budget inequality at every time) and `Frame` (the frame bound).
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

private theorem frobSq_add_smul_J_eq (M : Mat2) (c : ℝ) :
    frobSq (M + c • J) = frobSq M + 2 * c * (M 1 0 - M 0 1) + 2 * c ^ 2 := by
  simp [frobSq, J]
  ring

private theorem covectorNormSq_pos {lam : ℝ} {Λ₁ ΛR : Mat2} (h : lam ≠ 0 ∨ Λ₁ ≠ 0 ∨ ΛR ≠ 0) :
    0 < covectorNormSq lam Λ₁ ΛR := by
  have h1 := clr_frobSq_nonneg Λ₁
  have h2 := clr_frobSq_nonneg ΛR
  unfold covectorNormSq
  rcases h with h | h | h
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    linarith
  · have := clr_frobSq_pos h
    nlinarith [sq_nonneg lam]
  · have := clr_frobSq_pos h
    nlinarith [sq_nonneg lam]

/-- `‖g M g⁻¹‖_F² ≤ ‖g‖_F⁴ ‖M‖_F²` with `g⁻¹ = adj g`. -/
private theorem frobSq_conj_adjugate_le (g M : Mat2) :
    frobSq (g * M * g.adjugate) ≤ frobSq g ^ 2 * frobSq M := by
  have h1 := clr_frobSq_mul_le (g * M) g.adjugate
  have h2 := clr_frobSq_mul_le g M
  rw [clr_frobSq_adjugate] at h1
  have := clr_frobSq_nonneg g
  calc frobSq (g * M * g.adjugate) ≤ frobSq (g * M) * frobSq g := h1
    _ ≤ frobSq g * frobSq M * frobSq g := mul_le_mul_of_nonneg_right h2 this
    _ = frobSq g ^ 2 * frobSq M := by ring

/-- On `𝔥**`, `‖Λ_R(t)‖_F² ≤ 218700 ‖Λ₁(t) - (3/2)λJ‖_F²` (that is, `‖W‖ ≤ 468 ‖A‖`):
`clr_vertex_bounds` with margins at least `2/15` gives `‖W‖_F² ≤ 2700 tr(AX)²`, and
Cauchy–Schwarz with `‖X‖_F² < 81` gives `tr(AX)² ≤ 81 ‖A‖_F²`. -/
private theorem frobSq_ΛR_le {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    frobSq (ΛR t) ≤ 218700 * frobSq (Λ₁ t - (3 / 2 * lam) • J) := by
  have hH := (IsPontryaginExtremal.vertexHamiltonian_max_eq_zero hext t ht).1
  obtain ⟨-, hWtr, hWX, -⟩ := hext.2.2.2.2.2.2.2.1 t ht
  have hb := (clr_vertex_bounds (hext.1.2.2.2.1 t ht).2 hWtr hWX hH).2
    (two_div_fifteen_le_margin (hK t ht))
  have hCS := clr_traceForm_sq_le (Λ₁ t - (3 / 2 * lam) • J) (X t)
  have hX := frobSq_lt_of_inCompactDomain (hK t ht)
  have hA := clr_frobSq_nonneg (Λ₁ t - (3 / 2 * lam) • J)
  have : frobSq (Λ₁ t - (3 / 2 * lam) • J) * frobSq (X t) ≤
      frobSq (Λ₁ t - (3 / 2 * lam) • J) * 81 := mul_le_mul_of_nonneg_left hX.le hA
  linarith

/-- **Singular clearance**. Let `(T, u, g, X, Λ₁, Λ_R, λ)` be a Pontryagin extremal (any `λ ≤ 0`,
normal or abnormal) with cost `C ≤ A_oct` and state in `𝔥**`. Then at every `t ∈ [0, T]`,
`‖𝒫(t)‖² ≤ 251² Q(t)²`.

Proof outline: write `A = Λ₁ - (3/2)λJ` and `μ = -λ`. The equilibrium control `u*` lies in the
simplex and `P_{u*} = -X/2`, so `tr(A X) = H(u*) ≤ max H = 0` at every time
(`clr_traceForm_le_zero`). With `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Hales–Vajjha, Corollary 6.5.3) and
`V = g X g⁻¹` this reads `3μρ_R + tr(A₀V) ≤ 3μρ`, and `tr(A₀ V) ≥ -2‖A₀‖ρ_R`; integrating against
the winding bound `∫(ρ + ρ_R) ≥ 2π/3` (`clr_winding`: the continuous argument of the `J`-part
`s + it` of the frame turns by at least `π/3`) gives `μ ≤ 100 ‖A₀‖` (`clr_budget`). Rebasing the
twisted extension (`twistedFrame`, `twistedState`, with the costate `G(τ)⁻¹ Λ₁(0) G(τ)`) at `t`
gives `λ² ≤ 10⁴ ‖A(t)‖²` at every time (`clr_lam_sq_le`). Since `Λ₁ = A + (3/2)λJ`, the bound
`‖Λ₁‖² ≤ (1 + ε)‖A‖² + (1 + 1/ε)(9/2)λ²` with `ε = 200` then gives `‖𝒫‖² ≤ 251² Q²`. The compact
domain is not used for this inequality. -/
theorem covectorNormSq_le_singularGapSq {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t)) :
    ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ t) (ΛR t) ≤ 251 ^ 2 * singularGapSq lam (Λ₁ t) (ΛR t) := by
  intro t ht
  have hb := clr_lam_sq_le hext hcost t ht
  set A := Λ₁ t - (3 / 2 * lam) • J with hA
  have hΛ : Λ₁ t = A + (3 / 2 * lam) • J := by rw [hA, sub_add_cancel]
  unfold covectorNormSq singularGapSq
  rw [← hA, hΛ, frobSq_add_smul_J_eq]
  have hW := clr_frobSq_nonneg (ΛR t)
  have hd : (A 1 0 - A 0 1) ^ 2 ≤ 2 * frobSq A := by
    unfold frobSq; nlinarith [sq_nonneg (A 1 0 + A 0 1), sq_nonneg (A 0 0), sq_nonneg (A 1 1)]
  nlinarith [sq_nonneg (10 * (A 1 0 - A 0 1) - 3 / 20 * lam)]

/-- **Projective bounds**. Under the same hypotheses, for every `t ∈ [0, T]`:
`‖𝒫(0)‖² < 10¹⁶ ‖𝒫(t)‖²` and `‖𝒫(t)‖² < 10¹⁶ ‖𝒫(0)‖²`, i.e. `10⁻⁸ ‖𝒫(0)‖ < ‖𝒫(t)‖ < 10⁸ ‖𝒫(0)‖`.

Proof outline, in Frobenius norms throughout. Gronwall for `‖g‖_F²`
(`f' = 2 tr(X gᵀg) ≤ 2ρ f`) gives `‖g(t)‖_F² ≤ 2 e^{2C/3} < 42` (`clr_frobSq_frame_le`), so
`‖Λ₁(t)‖_F² ≤ 1764 ‖Λ₁(0)‖_F²` and conversely (`Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)`). On
`𝔥**`, with `W = Λ_R`, the exact equilibrium weights `ϑ_i = p_i(p_j + p_k)/8` and the margins
`p_i ≥ 2/15` give `‖W‖_F² ≤ 2700 tr(AX)² ≤ 218700 ‖A‖_F²` at every time (`clr_vertex_bounds`);
and `‖A‖ ≤ ‖Λ₁‖ + (3/2)√2|λ|`. Hence `‖𝒫(t)‖² < 8·10⁸ ‖𝒫(0)‖²` and conversely. -/
theorem covectorNormSq_projective_bounds {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t)) :
    ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ 0) (ΛR 0) < 10 ^ 16 * covectorNormSq lam (Λ₁ t) (ΛR t) ∧
        covectorNormSq lam (Λ₁ t) (ΛR t) < 10 ^ 16 * covectorNormSq lam (Λ₁ 0) (ΛR 0) := by
  intro t ht
  have hT : 0 < T := hext.1.1
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hN0 := covectorNormSq_pos (hext.2.2.2.2.2.2.2.1 0 h0).2.2.2
  have hNt := covectorNormSq_pos (hext.2.2.2.2.2.2.2.1 t ht).2.2.2
  -- the frame bound and conservation
  have hg := clr_frobSq_frame_le hext.1 hext.2.1 hcost t ht
  have hg0 := clr_frobSq_nonneg (g t)
  have hg2 : frobSq (g t) ^ 2 ≤ 1764 := by nlinarith
  have hdet : (g t).det = 1 := (hext.1.2.2.2.1 t ht).1
  have hinv : (g t)⁻¹ = (g t).adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have hunit : IsUnit (g t).det := by rw [hdet]; exact isUnit_one
  have hcons := clr_conservation hext t ht
  have hΛt : frobSq (Λ₁ t) ≤ 1764 * frobSq (Λ₁ 0) := by
    have := clr_frobSq_conj_le hdet (Λ₁ 0)
    rw [← hcons] at this
    have := clr_frobSq_nonneg (Λ₁ 0)
    nlinarith
  have hΛ0 : frobSq (Λ₁ 0) ≤ 1764 * frobSq (Λ₁ t) := by
    have e : Λ₁ 0 = g t * Λ₁ t * (g t).adjugate := by
      rw [hcons, ← hinv]
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    have := frobSq_conj_adjugate_le (g t) (Λ₁ t)
    rw [← e] at this
    have := clr_frobSq_nonneg (Λ₁ t)
    nlinarith
  -- `‖Λ_R‖² ≤ 218700 ‖A‖²` and `‖A‖² ≤ 2‖Λ₁‖² + 9λ²`
  have hA : ∀ s ∈ Icc 0 T, frobSq (Λ₁ s - (3 / 2 * lam) • J) ≤ 2 * frobSq (Λ₁ s) + 9 * lam ^ 2 := by
    intro s _
    have := clr_frobSq_add_smul_J_le (Λ₁ s) (-(3 / 2 * lam))
    rw [neg_smul, ← sub_eq_add_neg] at this
    nlinarith
  have hW0 := frobSq_ΛR_le hext hK h0
  have hWt := frobSq_ΛR_le hext hK ht
  have hA0 := hA 0 h0
  have hAt := hA t ht
  have hl := sq_nonneg lam
  have p0 := clr_frobSq_nonneg (Λ₁ 0)
  have pt := clr_frobSq_nonneg (Λ₁ t)
  have q0 := clr_frobSq_nonneg (ΛR 0)
  have qt := clr_frobSq_nonneg (ΛR t)
  unfold covectorNormSq at hN0 hNt ⊢
  constructor <;> nlinarith

end SmoothedOctagon.Reduction

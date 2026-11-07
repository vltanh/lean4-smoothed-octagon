module

public import SmoothedOctagon.Reduction.Defs

/-!
# Singular clearance and projective bounds of a competitive Pontryagin lift

SINGULAR_COST_BUDGET (inventory A2, §2.4: `SCB:(3)/(21)`, `SCB:(24)-(26)`, `SCB:(29)`,
`SCB:(30)-(33)`, `SCB:(28)`, `SCB:(34)` and `Thm(1)`). For a Pontryagin extremal (normal or
abnormal) whose cost is at most `A_oct` and whose state stays in `𝔥**`:

* (clearance, SCB (34)) the costate stays away from the singular locus `Λ₁ = (3/2)λJ`, `Λ_R = 0`
  in proportion to its size: `‖𝒫(t)‖ ≤ 251 Q(t)`, with `‖𝒫‖² = λ² + ‖Λ₁‖² + ‖Λ_R‖²` and
  `Q² = ‖Λ₁ - (3/2)λJ‖² + ‖Λ_R‖²`. Hence for the lift normalized by `‖𝒫(0)‖ = 1`,
  `D(t) ≥ Q(t) > 10⁻⁸/251 > 10⁻¹¹` (SCB, Theorem (1)).
* (projective bounds, SCB (28)) `10⁻⁸ ‖𝒫(0)‖ < ‖𝒫(t)‖ < 10⁸ ‖𝒫(0)‖`.

Both are homogeneous in `(λ, Λ₁, Λ_R)`, so no normalization is imposed; they are stated with squared
norms (`covectorNormSq`, `singularGapSq`).

Main API:

* `covectorNormSq_le_singularGapSq`: `‖𝒫(t)‖² ≤ 251² Q(t)²` on `[0, T]`.
* `covectorNormSq_projective_bounds`: `‖𝒫(0)‖² < 10¹⁶ ‖𝒫(t)‖²` and `‖𝒫(t)‖² < 10¹⁶ ‖𝒫(0)‖²`
  on `[0, T]`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Singular clearance** (SINGULAR_COST_BUDGET (34), with (3), (24)-(27)). Let
`(T, u, g, X, Λ₁, Λ_R, λ)` be a Pontryagin extremal (any `λ ≤ 0`, normal or abnormal) with cost
`C ≤ A_oct` and state in `𝔥**`. Then at every `t ∈ [0, T]`, `‖𝒫(t)‖² ≤ 251² Q(t)²`.

Proof outline: (SCB (3), budget inequality) `‖A(t)‖ ≥ κ|λ|` with `A = Λ₁ - (3/2)λJ` and
`κ = 3(π - C)/(2π - C) > 9/788 > 1/100` (SCB (24)-(26): `A_oct < 391/125 < 157/50 < π`). At
`t = 0`: `tr(A X) ≤ 0` at every time (SCB (10): the equilibrium control `u*` lies in the simplex and
`P_{u*} = -X/2`, so `tr(A X) = H(u*) ≤ max H = 0`, the maximum vanishing everywhere by continuity);
with `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Corollary 6.5.3) and `V = g X g⁻¹` this gives
`3μρ_R + tr(A₀V) ≤ 3μρ` (`μ = -λ`), `tr(A₀ V) ≥ -2‖A₀‖ρ_R` (SCB (13)); integrate and use the
winding bound `∫ρ_R ≥ (2π - C)/3` (SCB (15)-(17), from `ρ + ρ_R = 2(s² + t²)θ'` and
`g(T) = R`). At general `t`: rebase the twisted extension of the lift (`remark6_6_1`) at `t`. Then,
with `d = √(11/2)` the norm of `(λ, (3/2)λJ, 0)`, `‖𝒫‖ ≤ Q + d|λ| ≤ (1 + d/κ) Q < 251 Q`.
(The compact domain is not used for this inequality in the notes' argument.) -/
theorem covectorNormSq_le_singularGapSq {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t)) :
    ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ t) (ΛR t) ≤ 251 ^ 2 * singularGapSq lam (Λ₁ t) (ΛR t) := by
  sorry

/-- **Projective bounds** (SINGULAR_COST_BUDGET (28), with (29)-(33)). Under the same hypotheses,
for every `t ∈ [0, T]`: `‖𝒫(0)‖² < 10¹⁶ ‖𝒫(t)‖²` and `‖𝒫(t)‖² < 10¹⁶ ‖𝒫(0)‖²`, i.e.
`10⁻⁸ ‖𝒫(0)‖ < ‖𝒫(t)‖ < 10⁸ ‖𝒫(0)‖`.

Proof outline: (SCB (29)) `‖g(t)‖_op, ‖g(t)⁻¹‖_op ≤ exp(∫‖X‖_op) < e^{2C/3} < 9`, so
`‖Λ₁(t)‖ ≤ 81 ‖Λ₁(0)‖` and conversely (`Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)`); (SCB (30)-(33)) on `𝔥**`,
`‖W‖ ≤ 607500 ‖A‖ ≤ 10⁶ ‖A‖` at every time (`W = Λ_R`, using the vertex weights of `u*`, at least
`1/135`, `Σ ϑ_i h_i = 0`, `max_i h_i = -tr(A X) ≤ 9‖A‖`, and the width bound
`max h - min h ≥ ω‖W‖`, `ω > 1/500`, of QUANTITATIVE_REGULAR_SWITCH_BOUND (14)); and
`‖A‖ ≤ ‖Λ₁‖ + (3/2)√2|λ|`. Normalizing `‖𝒫(0)‖ = 1`: `‖Λ₁(t)‖ < 81`, `‖A(t)‖ < 84`,
`‖W(t)‖ < 84·10⁶`, so `‖𝒫(t)‖ < 10⁸`; reading the same bounds from `t` back to `0` gives
`1 ≤ 83250082 ‖𝒫(t)‖`. -/
theorem covectorNormSq_projective_bounds {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t)) :
    ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ 0) (ΛR 0) < 10 ^ 16 * covectorNormSq lam (Λ₁ t) (ΛR t) ∧
        covectorNormSq lam (Λ₁ t) (ΛR t) < 10 ^ 16 * covectorNormSq lam (Λ₁ 0) (ΛR 0) := by
  sorry

end SmoothedOctagon.Reduction

module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.Switch.Glue
public import SmoothedOctagon.Reduction.Switch.Local

/-!
# Finitely many switches

A Pontryagin extremal (normal or abnormal) with cost at most `A_oct`, state in `𝔥**`, the singular
clearance of `Reduction/SingularClearance.lean`, and the edge property (E4) has a control that is
a.e. a concatenation of finitely many vertex pieces on `[0, T]`. Only finiteness is proved; the
number of pieces is not bounded explicitly.

Main API:

* `exists_isPiecewiseVertex`: finitely many vertex pieces.

The local analysis is in `Reduction/Switch/Local.lean`, the gluing and the compactness argument in
`Reduction/Switch/Glue.lean`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Finitely many switches**. Let `(T, u, g, X, Λ₁, Λ_R, λ)` be a Pontryagin extremal with cost at
most `A_oct` and state in `𝔥**`, satisfying the clearance `‖𝒫(t)‖² ≤ 251² Q(t)²` on `[0, T]`, whose
control has property (E4). Then on `[0, T]` the control is a.e. a concatenation of finitely many
vertex pieces.

Proof outline. By nontriviality `‖𝒫(t)‖ > 0`, so the clearance gives `Q(t) > 0`: the costate never
meets the singular locus (`switch_singularGapSq_pos`). Around each `t₀ ∈ [0, T]` there are `δ > 0` and
vertices `j`, `k` with `H_j < 0` on `(t₀, t₀ + δ)` and `H_k < 0` on `(t₀ - δ, t₀)`
(`switch_exists_excluded_vertex`): if one vertex Hamiltonian is strictly below the maximum at `t₀`, it
stays so nearby; otherwise the three tie, which forces `Λ_R(t₀) = 0`, and `Q(t₀) > 0` makes
`Λ_R'(t₀) = [X, A] ≠ 0`, whose vertex comparisons are not all equal, so one comparison `H_j - H_k`
changes sign at `t₀`. On each side that coordinate of the control vanishes a.e.
(`maximizing_control_support`) and (E4) gives at most four pieces; gluing at `t₀` and compactness of
`[0, T]` (Lebesgue number) give finitely many pieces in all. The cost bound `hcost` is not used (it
enters through the clearance `hclear`).

At a tie the sign change comes from the first-order expansion
`Λ_R(t) = (t - t₀)[X(t₀), A(t₀)] + o(t - t₀)`. -/
theorem exists_isPiecewiseVertex {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t))
    (hclear : ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ t) (ΛR t) ≤ 251 ^ 2 * singularGapSq lam (Λ₁ t) (ΛR t))
    (hedge : EdgeBound T u) :
    ∃ n, IsPiecewiseVertex u 0 T n := by
  apply switch_isPiecewiseVertex_of_local hext.1.1.le
  intro t₀ ht₀
  have hQ := switch_singularGapSq_pos (hext.2.2.2.2.2.2.2.1 t₀ ht₀).2.2.2 (hclear t₀ ht₀)
  obtain ⟨δ, hδ, j, k, hj, hk⟩ := switch_exists_excluded_vertex hext hK ht₀ hQ
  -- right of `t₀` the coordinate `u_j` vanishes a.e., left of `t₀` the coordinate `u_k`
  have hright : ∀ a b, t₀ ≤ a → a < b → b < t₀ + δ → 0 ≤ a → b ≤ T →
      ∃ n, IsPiecewiseVertex u a b n := by
    intro a b hta hab hbt ha hb
    obtain ⟨n, -, hn⟩ := hedge a b ha hab hb j (switch_ae_coord_eq_zero hext ha hb fun t ht ↦
      hj t ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩ (hta.trans_lt ht.1) (ht.2.trans hbt))
    exact ⟨n, hn⟩
  have hleft : ∀ a b, t₀ - δ < a → a < b → b ≤ t₀ → 0 ≤ a → b ≤ T →
      ∃ n, IsPiecewiseVertex u a b n := by
    intro a b hta hab hbt ha hb
    obtain ⟨n, -, hn⟩ := hedge a b ha hab hb k (switch_ae_coord_eq_zero hext ha hb fun t ht ↦
      hk t ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩ (hta.trans ht.1) (ht.2.trans_le hbt))
    exact ⟨n, hn⟩
  refine ⟨δ, hδ, fun a b ha hab hb hδa hδb ↦ ?_⟩
  rcases le_or_gt t₀ a with h1 | h1
  · exact hright a b h1 hab hδb ha hb
  rcases le_or_gt b t₀ with h2 | h2
  · exact hleft a b hδa hab h2 ha hb
  obtain ⟨n, hn⟩ := hleft a t₀ hδa h1 le_rfl ha ht₀.2
  obtain ⟨m, hm⟩ := hright t₀ b le_rfl h2 hδb ht₀.1 hb
  exact ⟨n + m, switch_isPiecewiseVertex_append hn hm⟩

end SmoothedOctagon.Reduction

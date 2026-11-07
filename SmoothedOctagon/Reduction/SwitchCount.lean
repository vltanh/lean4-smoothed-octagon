module

public import SmoothedOctagon.Reduction.Defs

/-!
# Finitely many switches

QUANTITATIVE_REGULAR_SWITCH_BOUND, Theorem (1), in qualitative form (inventory A2, §2.6 `QRSB:*`).
A Pontryagin extremal (normal or abnormal) with cost at most `A_oct`, state in `𝔥**`, the singular
clearance of `Reduction/SingularClearance.lean`, and the edge property (E4) has a control that is
a.e. a concatenation of finitely many vertex pieces on `[0, T]`. The notes' explicit bound
`N < 10^56` is not needed by the proof of the main theorem.

Main API:

* `exists_isPiecewiseVertex`: finitely many vertex pieces.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Finitely many switches** (QUANTITATIVE_REGULAR_SWITCH_BOUND, Theorem (1), in qualitative
form). Let `(T, u, g, X, Λ₁, Λ_R, λ)` be a Pontryagin extremal with cost at most `A_oct` and state in
`𝔥**`, satisfying the clearance `‖𝒫(t)‖² ≤ 251² Q(t)²` on `[0, T]`, whose control has property (E4).
Then on `[0, T]` the control is a.e. a concatenation of finitely many vertex pieces.

Proof outline (QRSB §§2-6, made qualitative). By nontriviality `‖𝒫(t)‖ > 0`, so the clearance
gives `Q(t) > 0`: the costate never meets the singular locus. Around each `t₀ ∈ [0, T]` there is a
neighbourhood on which the control has finitely many vertex pieces: if one vertex Hamiltonian is
strictly below the maximum at `t₀`, it stays so nearby, that coordinate of the control vanishes
a.e. (`maximizing_control_support`), and (E4) gives at most four pieces; otherwise the
trichotomy of QRSB §5 and its guard lines (15)-(17) apply, the guard projections are strictly
monotone near `t₀` because `Q(t₀) > 0` (QRSB's Case III is empty), so the neighbourhood splits
into at most seven pieces each lying in one rotated sector, and (E4) applies in each. Compactness of
`[0, T]` gives finitely many pieces in all.

Route: the notes bound the number of pieces explicitly (`N < 10^56`), which needs the projective
bounds and the constants of QRSB §1.4; the proof only uses finiteness, so the local argument and
compactness suffice. -/
theorem exists_isPiecewiseVertex {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t))
    (hclear : ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ t) (ΛR t) ≤ 251 ^ 2 * singularGapSq lam (Λ₁ t) (ΛR t))
    (hedge : EdgeBound T u) :
    ∃ n, IsPiecewiseVertex u 0 T n := by
  sorry

end SmoothedOctagon.Reduction

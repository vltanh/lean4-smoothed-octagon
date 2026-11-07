module

public import SmoothedOctagon.Reduction.Defs

/-!
# The quantitative switch count `N < 10^56`

QUANTITATIVE_REGULAR_SWITCH_BOUND, Theorem (1) with (30)-(31), as evaluated in
SINGULAR_COST_BUDGET, Theorem (2) and (36)-(40) (inventory A2, §2.6 `QRSB:*`, §2.4
`SCB:(36)-(40) and Thm(2)`, constants §1.4). A Pontryagin extremal (normal or abnormal) with cost at
most `A_oct`, state in `𝔥**`, the singular clearance and projective bounds of
`Reduction/SingularClearance.lean`, and the edge property (E4) has a control that is a.e. a
concatenation of fewer than `10^56` vertex pieces on `[0, T]`.

Main API:

* `exists_isPiecewiseVertex_lt`: fewer than `10^56` vertex pieces.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Quantitative switch count** (QUANTITATIVE_REGULAR_SWITCH_BOUND, Theorem (1);
SINGULAR_COST_BUDGET, Theorem (2)). Let `(T, u, g, X, Λ₁, Λ_R, λ)` be a Pontryagin extremal with
cost at most `A_oct` and state in `𝔥**`, satisfying the clearance `‖𝒫(t)‖² ≤ 251² Q(t)²` and the
projective bounds `10⁻¹⁶ ‖𝒫(0)‖² < ‖𝒫(t)‖² < 10¹⁶ ‖𝒫(0)‖²` on `[0, T]`, whose control has
property (E4). Then on `[0, T]` the control is a.e. a concatenation of `n < 10^56` vertex pieces.

Proof outline (QRSB §§2-6): normalize `‖𝒫(0)‖ = 1` (all hypotheses are homogeneous), so
`m = 10⁻⁸ < ‖𝒫(t)‖ < M = 10⁸` and `D(t) ≥ Q(t) > 10⁻⁸/251 > ε = 10⁻¹¹`. The compact domain gives
`‖X‖_F ≤ K_X = 9` (`frobSq_lt_of_inCompactDomain`), `γ_i ≥ Γ = 2/(15√3)`
(`two_div_fifteen_le_margin`), and `T ≤ C/3 < π/3`. Cover `[0, T]` by `⌈T_max/h⌉` intervals of
length `h = c·min(ε, 1, m) > 10⁻⁵⁴` (constants of §1.4, `c > 10⁻⁴³`). On each, by the trichotomy
(QRSB §5) and the three guard lines (QRSB (15)-(17)), after deleting at most six zeros of the guard
projections, each of the at most seven components lies in one rotated sector, where one vertex
Hamiltonian is strictly below the maximum, so that coordinate of the control vanishes a.e.
(maximality a.e., `maximizing_control_support`), and (E4) gives at most four pieces: at most
`28` per interval (QRSB (30)), `n ≤ 28⌈T_max/h⌉ ≤ 56·10⁵⁴ < 10⁵⁶`.

Route remark: with the clearance in this homogeneous form, Case III of the trichotomy
(`‖W‖ < re`, `‖A‖ < ae`) is empty, since then `Q < (r + a)e ≤ e/4 < 10⁻⁸/251`; only Cases I
(a vertex strictly excluded) and II (monotone guard projections) remain. -/
theorem exists_isPiecewiseVertex_lt {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ octagonCost)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t))
    (hclear : ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ t) (ΛR t) ≤ 251 ^ 2 * singularGapSq lam (Λ₁ t) (ΛR t))
    (hproj : ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ 0) (ΛR 0) < 10 ^ 16 * covectorNormSq lam (Λ₁ t) (ΛR t) ∧
        covectorNormSq lam (Λ₁ t) (ΛR t) < 10 ^ 16 * covectorNormSq lam (Λ₁ 0) (ΛR 0))
    (hedge : EdgeBound T u) :
    ∃ n < 10 ^ 56, IsPiecewiseVertex u 0 T n := by
  sorry

end SmoothedOctagon.Reduction

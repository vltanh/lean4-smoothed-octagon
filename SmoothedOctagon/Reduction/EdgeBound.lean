module

public import SmoothedOctagon.Reduction.Defs

/-!
# The edge bound (E4)

MEASURABLE_EDGE_PMP_BOUND, Theorem (E4) (inventory A2, §2.5 `MEPB:Thm`, coordinates §1.5, PMP
bridge §5.A "Edge PMP from OC", risks §5.C item 2). On a subinterval of `[0, T]` where one
coordinate `u_j` of the control of a global minimizer vanishes a.e., the control is a.e. a
concatenation of at most four vertex pieces.

Main API:

* `edgeBound_of_isReinhardtMinimizer`: every global minimizer has property (E4) (`EdgeBound`).
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **The edge bound (E4)** (MEASURABLE_EDGE_PMP_BOUND, Theorem). Let `(T, u, g, X)` be a global
minimizer and `0 ≤ t₀ < t₁ ≤ T` with `u_j = 0` a.e. on `(t₀, t₁)` for one `j`. Then on `[t₀, t₁]`
the control is a.e. a concatenation of at most four constant vertex pieces (with labels other than
`j`).

Proof outline (MEPB §§1-6): rotate `j` to `0` (conjugation by `R^j`). On the edge, `x = X₀₀/X₁₀`
is a strictly increasing clock (`x' = y`); in the clock `x ∈ [a, b]` the state is `w = y⁻²`,
`s = ∫ w dx`, the control `v ∈ [0, 1]` (`w' = β_v(x) w`), and the frame and cost are recovered from
`(x, w, s)` (MEPB (8)-(12)); the cost is `(3/2)(b - a + S + M(w))` with `M(w) = ∫ x² w dx`. By
splicing (global minimality, competitors with any terminal time) the restriction minimizes `M`
among edge curves with the same endpoints `w(a), w(b), s(a) = 0, s(b) = S`. The maximum principle
then gives `λ ≤ 0`, `p_s` constant and `F = ρ p_w` with `F' = -ρ(p_s + λx²)`, `ρ > 0`; `v = 1`
where `p_w > 0` and `v = 0` where `p_w < 0`. A nonzero quadratic has at most two zeros, so `F` has
at most three (Rolle), and if `p_s + λx² ≡ 0` then `F` is a nonzero constant: at most four bang
pieces.

PMP to use (inventory A2 §5.A): the free-time `External.pontryagin_maximum_principle` with the
clock adjoined as a state, `E = ℝ³ ∋ (x, w, s)`, `Ω = {|x| < 1/√3, 0 < w < 1/(1/3 - x²)}`,
`U = [0, 1]`, `f = (1, β_v(x) w, w)`, `φ = x² w`, endpoint map `G(z₀, z₁) = (z₀ - (a, w_a, 0),
z₁ - (b, w_b, S))`. Its `H = 0` condition is what yields the nontriviality `(λ, p_s, p_w) ≢ 0`:
with `ν = p_s = 0` and `p_w ≡ 0`, `p_x` is constant and `H = p_x = 0`, against `(ν, p(t)) ≠ 0`.
The fixed-time `theorem12_3` alone admits the useless multiplier `ν = 0`, `p = (c, 0, 0)`. -/
theorem edgeBound_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) : EdgeBound T u := by
  sorry

end SmoothedOctagon.Reduction

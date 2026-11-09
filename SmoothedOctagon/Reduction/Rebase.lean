module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Period.Twist

/-!
# Cyclic rebasing of an admissible trajectory

Extend an admissible trajectory `(T, u, g, X)` by the twist, `G(t + T) = G(t) R`,
`Y(t + T) = R⁻¹ Y(t) R`, `v(t + T) = rot v(t)` (`Z_{v(t+T)} = R⁻¹ Z_{v(t)} R`), and restart it at a
time `s ∈ [0, T)`: `ĝ(t) = G(s)⁻¹ G(s + t)`, `X̂(t) = Y(s + t)`, `û(t) = v(s + t)` on `[0, T]`. The
rebased triple is again admissible with the same terminal time, and has the same cost (`J` commutes
with `R`, so `tr(J Y)` is `T`-periodic). So a rebased global minimizer is again a global minimizer.

Main API:

* `isReinhardtAdmissible_rebase`: the rebased trajectory is admissible, with the same cost.
* `isReinhardtMinimizer_rebase`: the rebased trajectory of a global minimizer is a global
  minimizer, with the same cost.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Cyclic rebasing**. For an admissible trajectory `(T, u, g, X)` and `s ∈ [0, T)`, the rebased
trajectory `(T, û, ĝ, X̂)` with `û(t) = v(s + t)`, `ĝ(t) = G(s)⁻¹ G(s + t)`, `X̂(t) = Y(s + t)`
(twisted extensions `v, G, Y`) is admissible, and its cost equals the cost of `(T, u, g, X)`.

Proof outline: on `[0, T - s]` the rebased pieces are `g(s)⁻¹ g(s + t)`, `X(s + t)`, `u(s + t)`;
on `[T - s, T]` they are `g(s)⁻¹ g(s + t - T) R`, `R⁻¹ X(s + t - T) R` and the rotated control.
Conjugation by `R` preserves the state equations, the star domain and the simplex
(`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`), and the two pieces glue continuously at `t = T - s` because
`g(T) = g(0) R` and `X(T) = R⁻¹ X(0) R`; the Carathéodory equations glue by additivity of the
integral (compare `remark6_6_1` and `exists_cyclic_extension_of_isReinhardtAdmissible`). The
endpoints: `ĝ(0) = I`, `ĝ(T) = G(s)⁻¹ G(s) R = R`, `X̂(T) = R⁻¹ X(s) R = R⁻¹ X̂(0) R`. The cost:
`∫_s^{s+T} tr(J Y) = ∫_s^T tr(J X) + ∫_0^s tr(J R⁻¹ X R) = ∫_0^T tr(J X)`. Measurability of `û`:
`⌊·⌋₊` is measurable. -/
theorem isReinhardtAdmissible_rebase {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {s : ℝ} (hs0 : 0 ≤ s) (_hsT : s < T) :
    IsReinhardtAdmissible T (rebaseControl T u s) (rebaseFrame T g s) (rebaseState T X s) ∧
      reinhardtCost T (rebaseState T X s) = reinhardtCost T X := by
  have hc : rebaseControl T u s = fun t ↦ SmoothedOctagon.twistedControl T u (s + t) := by
    funext t j
    simp [rebaseControl, twistedControl, SmoothedOctagon.twistedControl,
      relabelControl_iterate_apply]
  have hX : rebaseState T X s = fun t ↦ twistedState T X (s + t) := rfl
  rw [hc, hX]
  exact ⟨SmoothedOctagon.isReinhardtAdmissible_rebase h hs0,
    reinhardtCost_rebase h.1.1 hs0 h.2.2.2⟩

/-- **A rebased global minimizer is a global minimizer**, with the same cost: every competitor
costs at least the original cost, which is the rebased cost. -/
theorem isReinhardtMinimizer_rebase {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T) :
    IsReinhardtMinimizer T (rebaseControl T u s) (rebaseFrame T g s) (rebaseState T X s) ∧
      reinhardtCost T (rebaseState T X s) = reinhardtCost T X := by
  obtain ⟨hadm, hcost⟩ := isReinhardtAdmissible_rebase hmin.1 hs0 hsT
  exact ⟨⟨hadm, fun T' u' g' X' h' ↦ hcost ▸ hmin.2 T' u' g' X' h'⟩, hcost⟩

end SmoothedOctagon.Reduction

module

public import SmoothedOctagon.Period.Defs

/-!
# From a global minimizer to a finite normal period

Every global minimizer of the Reinhardt control problem, rebased at a switch, is a normal vertex
period with fewer than `10^56` pieces whose state stays in the compact domain `𝔥**`.

The proof is the chain of the proof notes:

1. the compact domain (`COMPACT_DOMAIN_SOURCE_AUDIT`, from Hales–Vajjha, Theorem 5.0.2, here the
   hypothesis `Cited.HalesVajjha.Theorem5_0_2`): every margin is at least `2/15`;
2. the Pontryagin lift of a global minimizer (`exists_isPontryaginExtremal_of_isReinhardtMinimizer`
   in `SmoothedPolygons`, through the maximum principle of `OptimalControl`);
3. the singular clearance `D > 10⁻¹¹` (`SINGULAR_COST_BUDGET`);
4. the edge bound from the fixed-time edge problem (`MEASURABLE_EDGE_PMP_BOUND`);
5. the three-guard switch count `N < 10^56` (`QUANTITATIVE_REGULAR_SWITCH_BOUND`);
6. merging equal neighbours and deleting zero pieces, also across the twisted seam, and rebasing at
   a genuine switch (`VERTEX_WORD_REDUCTION`, `SWITCHING_WORDS`);
7. normality, `λ ≠ 0`, rescaled to `λ = -1` (`GLOBAL_NORMALITY`).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-- **Finite normal representation of a global minimizer** (the conjunction delivered by
`SINGULAR_COST_BUDGET`, `MEASURABLE_EDGE_PMP_BOUND`, `QUANTITATIVE_REGULAR_SWITCH_BOUND`,
`VERTEX_WORD_REDUCTION` and `GLOBAL_NORMALITY`). A global minimizer `(T, u, g, X)`, rebased at a time
`s ∈ [0, T)`, is a normal vertex period `P` with the same terminal time and cost, still a global
minimizer, with state in `𝔥**` and fewer than `10^56` pieces. -/
theorem finiteNormalRepresentation (h502 : Cited.HalesVajjha.Theorem5_0_2)
    {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    ∃ (P : NormalPeriod) (s : ℝ), P.T = T ∧ 0 ≤ s ∧ s < T ∧
      (∀ t ∈ Icc 0 T, P.g t = rebaseFrame T g s t ∧ P.X t = twistedState T X (s + t)) ∧
      P.cost = reinhardtCost T X ∧ IsReinhardtMinimizer P.T P.u P.g P.X ∧
      P.InCompactDomain ∧ P.N < 10 ^ 56 := by
  sorry

end SmoothedOctagon

module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Reduction.CompactDomain
public import SmoothedOctagon.Reduction.Rebase
public import SmoothedOctagon.Reduction.WordReduction
public import SmoothedOctagon.Reduction.EdgeBound
public import SmoothedOctagon.Reduction.SingularClearance
public import SmoothedOctagon.Reduction.SwitchCount
public import SmoothedOctagon.Reduction.Normality
public import SmoothedPolygons.Ch6.MatrixExtremal

/-!
# From a global minimizer to a finite normal period

Every global minimizer of the Reinhardt control problem, rebased at a switch, is a normal vertex
period with finitely many pieces whose state stays in the compact domain `𝔥**`.

The proof is a chain, each link a module of `SmoothedOctagon/Reduction/`:

1. the compact domain (from Hales–Vajjha, Theorem 5.0.2, proved in `SmoothedPolygons` as
   `theorem5_0_2`): the state of a global minimizer stays in `𝔥**`
   (`Reduction.inCompactDomain_of_isReinhardtMinimizer`, `CompactDomain.lean`);
2. the Pontryagin lift of a global minimizer (`exists_isPontryaginExtremal_of_isReinhardtMinimizer`
   in `SmoothedPolygons`, through the maximum principle of `OptimalControl`);
3. the singular clearance `‖𝒫(t)‖ ≤ 251 Q(t)` (so `D > 10⁻¹¹` for normalized lifts) and the
   projective bounds `10⁻⁸ < ‖𝒫(t)‖/‖𝒫(0)‖ < 10⁸` (`SingularClearance.lean`);
4. the edge bound (E4) (`EdgeBound.lean`);
5. finitely many switches (`SwitchCount.lean`);
6. merging equal neighbours, also across the twisted seam, and rebasing at a genuine switch
   (`WordReduction.lean`); the rebased minimizer is a global minimizer with the same cost
   (`Rebase.lean`);
7. normality, `λ ≠ 0`, rescaled to `λ = -1` (`Normality.lean`).

Steps 2, 7 and 1 are applied to the rebased minimizer, which is itself a global minimizer, so no
costate is transported through the rebasing.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-- **Finite normal representation of a global minimizer**, by the chain of the module description.
A global minimizer `(T, u, g, X)`, rebased at a time `s ∈ [0, T)`, is a normal vertex period `P`
with the same terminal time and cost, still a global minimizer, with state in `𝔥**` and finitely
many pieces. -/
theorem finiteNormalRepresentation {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) :
    ∃ (P : NormalPeriod) (s : ℝ), P.T = T ∧ 0 ≤ s ∧ s < T ∧
      (∀ t ∈ Icc 0 T, P.g t = rebaseFrame T g s t ∧ P.X t = twistedState T X (s + t)) ∧
      P.cost = reinhardtCost T X ∧ IsReinhardtMinimizer P.T P.u P.g P.X ∧
      P.InCompactDomain := by
  -- 1. the compact domain and the cost budget
  have hK := Reduction.inCompactDomain_of_isReinhardtMinimizer hmin
  have hcost := Reduction.cost_le_octagonCost hmin
  -- 2. a Pontryagin lift, normal or abnormal
  obtain ⟨Λ₁, ΛR, lam, hext⟩ := exists_isPontryaginExtremal_of_isReinhardtMinimizer hmin
  -- 3–5. the clearance and (E4) give finitely many vertex pieces
  obtain ⟨n, hpw⟩ := Reduction.exists_isPiecewiseVertex hext hcost hK
    (Reduction.covectorNormSq_le_singularGapSq hext hcost hK)
    (Reduction.edgeBound_of_isReinhardtMinimizer hmin)
  -- 6. merge and rebase at a genuine switch; the rebased trajectory is a global minimizer
  obtain ⟨s, hs0, hsT, ρ, -⟩ := Reduction.exists_rebase_vertexRepresentation hmin.1.1.1 hpw
  obtain ⟨hmin', hcost'⟩ := Reduction.isReinhardtMinimizer_rebase hmin hs0 hsT
  -- 7. a Pontryagin lift of the rebased minimizer is normal; rescale it to `λ = -1`
  obtain ⟨Λ₁', ΛR', lam', hext'⟩ := exists_isPontryaginExtremal_of_isReinhardtMinimizer hmin'
  obtain ⟨Λ₁'', ΛR'', hext''⟩ := Reduction.exists_normal_lift hext'
    (Reduction.lam_lt_zero_of_vertexRepresentation hmin' hext' ρ)
  exact ⟨⟨T, Reduction.rebaseControl T u s, rebaseFrame T g s, Reduction.rebaseState T X s,
    Λ₁'', ΛR'', hext'', ρ⟩, s, rfl, hs0, hsT, fun _ _ ↦ ⟨rfl, rfl⟩, hcost', hmin',
    Reduction.inCompactDomain_of_isReinhardtMinimizer hmin'⟩

end SmoothedOctagon

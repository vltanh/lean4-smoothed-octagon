module

public import SmoothedOctagon.Foundations.ReverseComparison
public import SmoothedOctagon.Period.Partition
public import SmoothedOctagon.Reduction.FiniteNormal
public import SmoothedOctagon.Exclusion.Reverse
public import SmoothedOctagon.Exclusion.MinimumStructure
public import SmoothedOctagon.Exclusion.ShortRuns
public import SmoothedOctagon.Exclusion.Forward
public import SmoothedOctagon.Exclusion.Nonshort
public import SmoothedOctagon.Terminal.Comparison

/-!
# The sharp lower bound

`GLOBAL_COST_EQUALITY_ASSEMBLY` §§2–5.

1. A global minimizer of the control problem, rebased at a switch, is a competitive normal vertex
   period in the compact domain with finitely many pieces (`finiteNormalRepresentation`).
2. If it had six or more pieces, its cyclic sign sequence would be in one of the classes R, F, M3,
   M1, M2 (`VertexRepresentation.partition`), and each is excluded. So it has at most five pieces
   (`period_le_five`).
3. A period with at most five pieces costs at least `A_oct` (`terminal_cost`). So every global
   minimizer costs at least `A_oct` (`minimizer_cost_ge`).
4. Global minimizers exist: the realization of a worst disk is one, by the reverse comparison for
   arbitrary measurable controls (`exists_worstDisk_controlMinimizer`). Every admissible trajectory
   therefore costs at least `A_oct` (`controlLowerBound`), and every centrally symmetric convex disk
   has density at least `δ_oct` (`reinhardtConjecture`).

The hypotheses are Hales–Vajjha's Theorem 5.0.2 (`Cited.HalesVajjha.Theorem5_0_2`) and the interval
covers (`Certificates.IntervalCovers`).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-- The smoothed octagon's area is `A_oct`. -/
theorem volume_real_octagon : volume.real octagon = octagonCost := by
  have h := smoothedOctagon_volume.2
  have h12 : (0 : ℝ) < √12 := by positivity
  rw [div_eq_iff h12.ne'] at h
  rw [measureReal_def, octagon, h, octagonCost, octagonDensity, mul_comm]

/-- A global minimizer is competitive with the smoothed octagon. -/
theorem cost_le_octagonCost_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) : reinhardtCost T X ≤ octagonCost := by
  have h := controlMinimizer_density_eq_minimax hmin
  have h12 : (0 : ℝ) < √12 := by positivity
  rw [div_eq_iff h12.ne'] at h
  rw [h, octagonCost, mul_comm]
  exact mul_le_mul_of_nonneg_left minimaxDensity_le_octagonDensity h12.le

/-- **At most five pieces.** A competitive normal vertex period in the compact domain has at most
five pieces. -/
theorem period_le_five (hcov : Certificates.IntervalCovers) (P : NormalPeriod)
    (hc : P.IsCompetitive) (hK : P.InCompactDomain) : P.N ≤ 5 := by
  by_contra h
  have hN : 6 ≤ P.N := by omega
  rcases P.rep.partition with hR | hF | h3 | h1 | h2
  · exact reverse_exclusion P hR
  · exact forward_exclusion hcov.forward P hc hF hN
  · exact minimumStructure_exclusion P h3
  · exact shortRuns_exclusion P hc h1
  · exact nonshort_exclusion hcov.mixed P hc hK h2 hN

/-- **Every global minimizer costs at least `A_oct`.** -/
theorem minimizer_cost_ge (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) : octagonCost ≤ reinhardtCost T X := by
  obtain ⟨P, -, -, -, -, -, hcost, -, hK⟩ := finiteNormalRepresentation h502 hmin
  have hc : P.IsCompetitive := by
    unfold NormalPeriod.IsCompetitive
    rw [hcost]
    exact cost_le_octagonCost_of_isReinhardtMinimizer hmin
  rw [← hcost]
  exact terminal_cost P (period_le_five hcov P hc hK)

/-- **The control lower bound.** Every admissible trajectory of the Reinhardt control problem, with
any terminal time and any measurable control, costs at least the area `A_oct` of the smoothed
octagon. -/
theorem controlLowerBound (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) : ControlLowerBound := by
  intro T u g X hadm
  obtain ⟨K, S, σ, G, Y, -, -, -, hWmin, -⟩ := exists_worstDisk_controlMinimizer
  rw [volume_real_octagon]
  exact (minimizer_cost_ge h502 hcov hWmin).trans (hWmin.2 T u g X hadm)

/-- **The Reinhardt conjecture.** The smoothed octagon is a worst disk: every centrally symmetric
convex disk has greatest packing density at least `δ_oct`. -/
theorem reinhardtConjecture (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) : ReinhardtConjecture :=
  reinhardtConjecture_iff_controlLowerBound.mpr (controlLowerBound h502 hcov)

end SmoothedOctagon

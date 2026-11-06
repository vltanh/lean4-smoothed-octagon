module

public import SmoothedOctagon.CyclicExtension
public import SmoothedOctagon.ReverseGeometry
public import SmoothedOctagon.ControlBounds

/-!
# Completing the geometric and control comparison

Every low-cost integral-admissible trajectory constructs a balanced circle disk
with exactly the same area as its cost. The global cyclic extension supplies
regularity, dynamics, and curvature; low-cost winding supplies simplicity; the
radial-hull theorem supplies convexity. High costs are handled by the existing
octagon. No geometric reconstruction or comparison hypothesis remains.

Consequently an actual worst disk has a globally cost-minimizing control
realization. The remaining universal control lower bound is equivalent to the
original geometric conjecture. This equivalence does not prove that lower bound
or classify the minimizers. Source draft: compilation and kernel validation have
not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Matrix SmoothedPolygons

/-- Construct an actual balanced circle disk of equal area from any low-cost
admissible trajectory, including arbitrary measurable simplex controls. -/
theorem lowCost_admissible_balanced_realization {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hadm : IsReinhardtAdmissible T u g X)
    (hcost : reinhardtCost T X < π) :
    ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      volume.real K = reinhardtCost T X ∧
      greatestPackingDensity K = reinhardtCost T X / √12 := by
  obtain ⟨G, Y, hagree, hGC, hYC, hYLip, hdet, hstar, hD, hG0,
      hGshift, hYshift, hperiod, hcurv, hcosteq⟩ :=
    exists_cyclic_extension_of_isReinhardtAdmissible hadm
  have hκ : ∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (frameContact G j) t)
      (deriv (deriv (frameContact G j)) t) := by
    intro j
    filter_upwards [hcurv] with t ht
    exact ht j
  have hlow : reinhardtCost T Y < π := by rw [hcosteq]; exact hcost
  obtain ⟨hbal, hcirc⟩ := lowCost_cyclicFrame_isBalancedPair hadm.1.1 hGC hdet hYC
    hD hstar hYLip hG0 hGshift hκ hlow
  have harea : reinhardtCost T Y = volume.real (cyclicFrameDisk G T) :=
    cost_eq_area_of_balanced_cyclic hbal G Y (fun j t _ ↦ rfl)
      (fun t _ ↦ hD t) (frameContact_shift hGshift)
  have hareaX := harea.symm.trans hcosteq
  refine ⟨cyclicFrameDisk G T, frameContact G, hbal, hcirc, hareaX, ?_⟩
  rw [greatestPackingDensity_of_isBalancedPair hbal, hareaX]

/-- The low-cost reverse comparison is supplied by the constructed cyclic
extension and the actual simple convex radial hull. -/
theorem lowCostBalancedComparison : LowCostBalancedComparison := by
  intro T u g X hadm hcost
  obtain ⟨K, σ, hbal, hcirc, harea, _⟩ :=
    lowCost_admissible_balanced_realization hadm hcost
  exact ⟨K, σ, T, hbal, hcirc, harea.le⟩

/-- Every admissible control has a balanced circle competitor of no larger area.
Low costs give equal area; high costs use the concrete octagon. -/
theorem admissibleBalancedComparison : AdmissibleBalancedComparison :=
  admissibleBalancedComparison_iff_lowCost.mpr lowCostBalancedComparison

/-- The constructed control realization of an actual normalized worst disk is
a global minimizer over the entire upstream admissible class. -/
theorem normalized_worstDisk_controlMinimizer {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) (hS : rein_Std K) :
    ∃ (T : ℝ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (g X : ℝ → Mat2),
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      IsReinhardtMinimizer T (boundaryControl X) g X ∧
      reinhardtCost T X = volume.real K ∧
      greatestPackingDensity K = reinhardtCost T X / √12 := by
  obtain ⟨T, σ, g, X, hbal, hcirc, _, _, hadm, hcost, hdensity⟩ :=
    normalized_worstDisk_admissible_realization hK hS
  exact ⟨T, σ, g, X, hbal, hcirc,
    controlMinimizer_of_worstDisk_realization admissibleBalancedComparison
      hK hbal hcirc hadm hcost, hcost, hdensity⟩

/-- Nonvacuous existence of a full control minimizer follows from the actual
geometric worst-disk existence theorem and both proved comparison directions. -/
theorem exists_worstDisk_controlMinimizer :
    ∃ (K : Set (Fin 2 → ℝ)) (T : ℝ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
      (g X : ℝ → Mat2),
      IsWorstDisk K ∧ IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      IsReinhardtMinimizer T (boundaryControl X) g X ∧
      reinhardtCost T X = volume.real K ∧
      greatestPackingDensity K = reinhardtCost T X / √12 ∧
      reinhardtCost T X < π ∧ T < π / 3 := by
  obtain ⟨K, T, σ, g, X, hK, hbal, hcirc, hadm, hcost, hdensity, _, hlt, hT⟩ :=
    exists_worstDisk_lowCost_realization
  exact ⟨K, T, σ, g, X, hK, hbal, hcirc,
    controlMinimizer_of_worstDisk_realization admissibleBalancedComparison
      hK hbal hcirc hadm hcost, hcost, hdensity, hlt, hT⟩

/-- Every full control minimizer has the geometric minimax value after division
by the fixed critical-hexagon area. No classification of minimizers is used. -/
theorem controlMinimizer_density_eq_minimax {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    reinhardtCost T X / √12 = minimaxDensity := by
  obtain ⟨K, S, σ, G, Y, hK, _, _, hWmin, _, hdensity, _, _⟩ :=
    exists_worstDisk_controlMinimizer
  have hcosteq : reinhardtCost T X = reinhardtCost S Y :=
    le_antisymm (hmin.2 S (boundaryControl Y) G Y hWmin.1)
      (hWmin.2 T u g X hmin.1)
  rw [hcosteq, ← hdensity]
  exact hK.2

/-- Every full control minimizer reconstructs an actual geometric worst disk,
with its original terminal time and cost. The low-cost premise is derived. -/
theorem controlMinimizer_balanced_worstDisk {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsWorstDisk K ∧ IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      volume.real K = reinhardtCost T X := by
  obtain ⟨W, S, τ, G, Y, _, _, _, hWmin, _, _, hWcost, _⟩ :=
    exists_worstDisk_controlMinimizer
  have hlow : reinhardtCost T X < π :=
    (hmin.2 S (boundaryControl Y) G Y hWmin.1).trans_lt hWcost
  obtain ⟨K, σ, hbal, hcirc, harea, hdensity⟩ :=
    lowCost_admissible_balanced_realization hmin.1 hlow
  have hK : IsWorstDisk K :=
    ⟨hbal.1, hdensity.trans (controlMinimizer_density_eq_minimax hmin)⟩
  exact ⟨K, σ, hK, hbal, hcirc, harea⟩

/-- The remaining universal control inequality, including all terminal times
and arbitrary measurable simplex controls. It is still an open proposition. -/
def ControlLowerBound : Prop :=
  ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
    IsReinhardtAdmissible T u g X → volume.real octagon ≤ reinhardtCost T X

theorem controlLowerBound_iff_lowCost : ControlLowerBound ↔ LowCostControlLowerBound := by
  constructor
  · intro h T u g X hadm _
    exact h T u g X hadm
  · intro h T u g X hadm
    rcases lt_or_ge (reinhardtCost T X) π with hlt | hge
    · exact h T u g X hadm hlt
    · exact octagon_area_lt_pi.le.trans hge

/-- Exact unconditional transfer of the global conjecture to the unrestricted
control inequality. The reverse reconstruction is proved, not an input. -/
theorem reinhardtConjecture_iff_controlLowerBound :
    ReinhardtConjecture ↔ ControlLowerBound := by
  rw [controlLowerBound_iff_lowCost]
  exact reinhardtConjecture_iff_lowCostControlLowerBound lowCostBalancedComparison

end SmoothedOctagon

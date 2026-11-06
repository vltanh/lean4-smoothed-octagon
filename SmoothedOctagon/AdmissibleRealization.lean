module

public import SmoothedOctagon.CyclicClock
public import SmoothedPolygons.Ch2.BalancedDensity

/-!
# Admissible control realizations with exact geometric cost

The forward construction combines the actual balanced representation, the
determinant clock, its cyclic shift, and the repaired measurable curvature control.
The area identity is an equality of real numbers, with positivity checked before
removing `ENNReal.ofReal` from the upstream area theorem.

This module does not assert control optimality. Comparing an arbitrary admissible
control with a balanced geometric competitor remains a separate reverse-comparison
obligation. Source draft only; compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Matrix SmoothedPolygons

/-- The upstream area formula is a real equality once the positive area of the
actual convex disk rules out a negative or zero cost hidden by `ENNReal.ofReal`. -/
theorem cost_eq_area_of_balanced_cyclic {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ} (hbal : IsBalancedPair K σ T)
    (g X : ℝ → Mat2)
    (hframe : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hg : ∀ t ∈ Ioo 0 T, HasDerivAtEntrywise g (g t * X t) t)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    reinhardtCost T X = volume.real K := by
  have harea := eqn_cost hbal g X hframe hg hshift
  have hvolpos : 0 < volume K :=
    (isOpen_interior.measure_pos volume hbal.1.2.2.1).trans_le
      (measure_mono interior_subset)
  have hcostpos : 0 < reinhardtCost T X := by
    rw [harea] at hvolpos
    exact ENNReal.ofReal_pos.mp hvolpos
  change reinhardtCost T X = (volume K).toReal
  rw [harea, ENNReal.toReal_ofReal hcostpos.le]

/-- Every actual worst disk in normal position has an admissible control
realization whose cost is exactly its area. All boundary, clock, control,
integral-equation, and terminal-condition witnesses are constructed. -/
theorem normalized_worstDisk_admissible_realization {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) (hS : rein_Std K) :
    ∃ (T : ℝ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (g X : ℝ → Mat2),
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧
      (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtAdmissible T (boundaryControl X) g X ∧
      reinhardtCost T X = volume.real K ∧
      greatestPackingDensity K = reinhardtCost T X / √12 := by
  obtain ⟨τ, tf, hbal, hcirc⟩ := normalized_worstDisk_exists_balanced_circle hK hS
  obtain ⟨P, hP, a, ha0, haC, hapos, haper, hτbal, hτcirc, hshift,
      hstar, hLip, hg, hGshift, hXshift, hg0, hgT, hXT⟩ :=
    balanced_exists_cyclic_determinant_clock hK hbal hcirc
  let g : ℝ → Mat2 := fun t ↦ contactFrame τ (a t)
  let X : ℝ → Mat2 := normalizedContactState τ a
  have hframe : ∀ j t, (τ j ∘ a) t = g t *ᵥ sixthRoot j :=
    fun j t ↦ contactFrame_action hbal.2.2.2.1 (a t) j
  have htraj : IsStateTrajectory (P / 6) (boundaryControl X) g X :=
    balanced_determinantClock_isStateTrajectory hbal a haC hapos hstar hLip hg
      (div_pos hP (by norm_num))
  have hadm : IsReinhardtAdmissible (P / 6) (boundaryControl X) g X :=
    ⟨htraj, hg0, hgT, hXT⟩
  have hcost : reinhardtCost (P / 6) X = volume.real K :=
    cost_eq_area_of_balanced_cyclic hτbal g X (fun j t _ ↦ hframe j t)
      (fun t _ ↦ hg t) hshift
  refine ⟨P / 6, fun j ↦ τ j ∘ a, g, X, hτbal, hτcirc, hframe,
    hshift, hadm, hcost, ?_⟩
  rw [greatestPackingDensity_of_isBalancedPair hτbal, hcost]

/-- An arbitrary actual worst disk has a density-preserving linear image with a
complete admissible realization. The final identity connects the original disk's
packing density to the constructed control cost. -/
theorem worstDisk_admissible_realization {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (d T : ℝ)
      (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (g X : ℝ → Mat2),
      rein_PosLin e d ∧ IsWorstDisk (e '' K) ∧
      greatestPackingDensity (e '' K) = greatestPackingDensity K ∧
      IsBalancedPair (e '' K) σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧
      (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtAdmissible T (boundaryControl X) g X ∧
      reinhardtCost T X = volume.real (e '' K) ∧
      greatestPackingDensity K = reinhardtCost T X / √12 := by
  obtain ⟨e, d, he, hK', hS, hdensity⟩ := worstDisk_normalization hK
  obtain ⟨T, σ, g, X, hbal, hcirc, hframe, hshift, hadm, hcost, hdens⟩ :=
    normalized_worstDisk_admissible_realization hK' hS
  exact ⟨e, d, T, σ, g, X, he, hK', hdensity, hbal, hcirc, hframe, hshift,
    hadm, hcost, hdensity.symm.trans hdens⟩

/-- In particular the geometric worst-disk existence theorem produces an actual
inhabitant of the admissible control problem with exact area cost. This is an
existence statement, not a claim of control minimality. -/
theorem exists_worstDisk_admissible_realization :
    ∃ (K : Set (Fin 2 → ℝ)) (T : ℝ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
      (g X : ℝ → Mat2),
      IsWorstDisk K ∧ IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      IsReinhardtAdmissible T (boundaryControl X) g X ∧
      reinhardtCost T X = volume.real K ∧
      greatestPackingDensity K = reinhardtCost T X / √12 := by
  obtain ⟨K, hK, hS⟩ := exists_normalized_worst_disk
  obtain ⟨T, σ, g, X, hbal, hcirc, _, _, hadm, hcost, hdensity⟩ :=
    normalized_worstDisk_admissible_realization hK hS
  exact ⟨K, T, σ, g, X, hK, hbal, hcirc, hadm, hcost, hdensity⟩

end SmoothedOctagon

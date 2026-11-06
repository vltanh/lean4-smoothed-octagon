module

public import SmoothedPolygons.Ch2.Boundary
public import Mathlib.Tactic

/-!
# Continuous boundary traces of an actual worst disk

Select the unique critical hexagon whose first edge midpoint has polar angle `θ`. Its six
midpoints give six continuous, simple, closed curves covering the same boundary. In Reinhardt's
normal position they satisfy the normalized multi-point identities and start at the sixth roots
of unity.

This constructs the global continuous multi-curve. It does not assert differentiability or a
balanced pair. Those require the separate regular parametrization and arclength arguments.
The source has not been compiled or kernel-checked.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real SmoothedPolygons

variable {K : Set (Fin 2 → ℝ)}

/-- The critical hexagon whose edge `0` has midpoint at polar angle `θ`.

Existence is the no-gap theorem underlying upstream Lemma 2.2.7. The indexed hexagon is unique,
so the choice is independent of a choice of witness. -/
noncomputable def criticalHexagonAtAngle (hG : rein_Good K) (θ : ℝ) : ZMod 6 → Fin 2 → ℝ :=
  Classical.choose (rein_mem_Θ hG θ)

lemma criticalHexagonAtAngle_spec (hG : rein_Good K) (θ : ℝ) :
    IsLeastAreaHexagon K (criticalHexagonAtAngle hG θ) ∧
      hexMidpoint (criticalHexagonAtAngle hG θ) 0 = rein_bd K θ :=
  Classical.choose_spec (rein_mem_Θ hG θ)

lemma criticalHexagonAtAngle_unique (hG : rein_Good K) {θ : ℝ}
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (hvm : hexMidpoint v 0 = rein_bd K θ) : v = criticalHexagonAtAngle hG θ :=
  rein_V_unique hG (fun t ↦ (criticalHexagonAtAngle_spec hG t).1)
    (fun t ↦ (criticalHexagonAtAngle_spec hG t).2) hv hvm

/-- The six moving edge midpoints, with the first point parametrized by polar angle. -/
noncomputable def criticalBoundaryTrace (hG : rein_Good K) (j : ZMod 6) (θ : ℝ) : Fin 2 → ℝ :=
  hexMidpoint (criticalHexagonAtAngle hG θ) j

lemma criticalBoundaryTrace_zero (hG : rein_Good K) :
    criticalBoundaryTrace hG 0 = rein_bd K := by
  funext θ
  exact (criticalHexagonAtAngle_spec hG θ).2

lemma criticalBoundaryTrace_continuous (hG : rein_Good K) (j : ZMod 6) :
    Continuous (criticalBoundaryTrace hG j) :=
  (rein_continuous_hexMidpoint j).comp
    (rein_continuous_V hG (fun t ↦ (criticalHexagonAtAngle_spec hG t).1)
      (fun t ↦ (criticalHexagonAtAngle_spec hG t).2))

lemma criticalBoundaryTrace_mem_frontier (hG : rein_Good K) (j : ZMod 6) (θ : ℝ) :
    criticalBoundaryTrace hG j θ ∈ frontier K :=
  rein_hexMidpoint_mem_frontier hG.1 (criticalHexagonAtAngle_spec hG θ).1 j

/-- Normalization of one critical hexagon normalizes the midpoint determinant of all of them. -/
lemma criticalBoundaryTrace_isMultiPoint (hG : rein_Good K) (hS : rein_Std K) (θ : ℝ) :
    IsMultiPoint fun j ↦ criticalBoundaryTrace hG j θ := by
  let v := criticalHexagonAtAngle hG θ
  have hv : IsLeastAreaHexagon K v := (criticalHexagonAtAngle_spec hG θ).1
  intro j
  change hexMidpoint v j + hexMidpoint v (j + 2) + hexMidpoint v (j + 4) = 0 ∧
    hexMidpoint v (j + 3) = -hexMidpoint v j ∧
      det2 (hexMidpoint v j) (hexMidpoint v (j + 1)) = √3 / 2
  have h4 : hexMidpoint v (j + 4) = -hexMidpoint v (j + 1) := by
    simpa only [show j + 1 + 3 = j + 4 by ring] using
      rein_hexMidpoint_add_three hv.1 (j + 1)
  refine ⟨?_, rein_hexMidpoint_add_three hv.1 j, rein_det2_hexMidpoint_std hS hv j⟩
  rw [← rein_hexMidpoint_succ hv.1 j, h4, add_neg_cancel]

/-- The selected critical hexagons, hence all six midpoint curves, have the same full period. -/
lemma criticalBoundaryTrace_periodic (hG : rein_Good K) (j : ZMod 6) (θ : ℝ) :
    criticalBoundaryTrace hG j (θ + 2 * π) = criticalBoundaryTrace hG j θ := by
  have hV : criticalHexagonAtAngle hG (θ + 2 * π) = criticalHexagonAtAngle hG θ :=
    criticalHexagonAtAngle_unique hG (criticalHexagonAtAngle_spec hG (θ + 2 * π)).1
      (by rw [(criticalHexagonAtAngle_spec hG (θ + 2 * π)).2, rein_bd_add_two_pi])
  change hexMidpoint (criticalHexagonAtAngle hG (θ + 2 * π)) j =
    hexMidpoint (criticalHexagonAtAngle hG θ) j
  rw [hV]

/-- No midpoint curve repeats a boundary point during a single full period.

An equality of the `j`-th midpoints determines the entire indexed critical hexagon. Equality of
its first midpoint then determines the polar angle modulo `2π`. -/
lemma criticalBoundaryTrace_injOn (hG : rein_Good K) (j : ZMod 6) (a : ℝ) :
    InjOn (criticalBoundaryTrace hG j) (Ico a (a + 2 * π)) := by
  intro θ hθ ψ hψ heq
  have hV : criticalHexagonAtAngle hG ψ = criticalHexagonAtAngle hG θ := by
    funext k
    have h := rein_unique hG (criticalHexagonAtAngle_spec hG θ).1
      (criticalHexagonAtAngle_spec hG ψ).1 heq (k - j)
    simpa using h
  have hb : rein_bd K θ = rein_bd K ψ := by
    rw [← (criticalHexagonAtAngle_spec hG θ).2,
      ← (criticalHexagonAtAngle_spec hG ψ).2, hV]
  obtain ⟨n, hn⟩ := rein_bd_inj hG.1 hb
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      have hm := mul_le_mul_of_nonneg_right hnle two_pi_pos.le
      linarith [hθ.2, hψ.1]
    · have hnge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have hm := mul_le_mul_of_nonneg_right hnge two_pi_pos.le
      linarith [hθ.1, hψ.2]
  simpa [hn0] using hn.symm

/-- Every midpoint curve covers the boundary within any one full period.

For a specified boundary point, shift the indexing of its critical hexagon so that this point
is midpoint `j`. Choose the polar angle of midpoint `0` in the desired interval and invoke
uniqueness of the indexed critical hexagon. -/
lemma criticalBoundaryTrace_image_Ico (hG : rein_Good K) (j : ZMod 6) (a : ℝ) :
    criticalBoundaryTrace hG j '' Ico a (a + 2 * π) = frontier K := by
  apply Subset.antisymm
  · rintro x ⟨θ, -, rfl⟩
    exact criticalBoundaryTrace_mem_frontier hG j θ
  · intro x hx
    obtain ⟨θ, hxθ⟩ := rein_frontier_eq_bd hG.1 hx
    let v := criticalHexagonAtAngle hG θ
    have hv : IsLeastAreaHexagon K v := (criticalHexagonAtAngle_spec hG θ).1
    have hv0 : hexMidpoint v 0 = x := (criticalHexagonAtAngle_spec hG θ).2.trans hxθ.symm
    let w : ZMod 6 → Fin 2 → ℝ := fun k ↦ v (k + -j)
    have hw : IsLeastAreaHexagon K w := rein_isLeastAreaHexagon_shift hv (-j)
    have hwj : hexMidpoint w j = x := by
      change hexMidpoint (fun k ↦ v (k + -j)) j = x
      rw [rein_hexMidpoint_shift, add_neg_cancel]
      exact hv0
    obtain ⟨ψ, hψlo, hψhi, hw0⟩ :=
      rein_exists_bd_Ico hG.1 (rein_hexMidpoint_mem_frontier hG.1 hw 0) a
    have hwV : w = criticalHexagonAtAngle hG ψ := criticalHexagonAtAngle_unique hG hw hw0
    refine ⟨ψ, ⟨hψlo, hψhi⟩, ?_⟩
    change hexMidpoint (criticalHexagonAtAngle hG ψ) j = x
    rw [← hwV]
    exact hwj

lemma criticalBoundaryTrace_range (hG : rein_Good K) (j : ZMod 6) :
    range (criticalBoundaryTrace hG j) = frontier K := by
  apply Subset.antisymm
  · rintro x ⟨θ, rfl⟩
    exact criticalBoundaryTrace_mem_frontier hG j θ
  · intro x hx
    rw [← criticalBoundaryTrace_image_Ico hG j 0] at hx
    obtain ⟨θ, -, hθ⟩ := hx
    exact ⟨θ, hθ⟩

/-- In normal position the selected trace starts at the given six roots of unity. -/
lemma criticalBoundaryTrace_circleRepresentation (hG : rein_Good K) (hS : rein_Std K) :
    IsCircleRepresentation (criticalBoundaryTrace hG) := by
  obtain ⟨v, hv, hm⟩ := hS
  have hvm : hexMidpoint v 0 = rein_bd K 0 :=
    rein_eq_bd hG.1 (rein_hexMidpoint_mem_frontier hG.1 hv 0)
      (by norm_num : (0 : ℝ) < 1) (by simpa [sixthRoot, rein_dir] using hm 0)
  have hvV : v = criticalHexagonAtAngle hG 0 := criticalHexagonAtAngle_unique hG hv hvm
  intro j
  change hexMidpoint (criticalHexagonAtAngle hG 0) j = sixthRoot j
  rw [← hvV]
  exact hm j

/-- A normalized actual worst disk admits a global continuous normalized multi-curve with
common period `2π`, simple boundary traversal on each period, and the prescribed initial points.

No boundary curve is assumed in the hypotheses. The missing analytic upgrade to a balanced
pair is deliberately separate from this topological construction. -/
theorem exists_continuous_normalized_boundary_trace (hK : IsWorstDisk K) (hS : rein_Std K) :
    ∃ σ : ZMod 6 → ℝ → Fin 2 → ℝ,
      (∀ j, Continuous (σ j)) ∧
      (∀ θ, IsMultiPoint fun j ↦ σ j θ) ∧
      (∀ j θ, σ j θ ∈ frontier K) ∧
      σ 0 = rein_bd K ∧
      (∀ j θ, σ j (θ + 2 * π) = σ j θ) ∧
      (∀ j, InjOn (σ j) (Ico 0 (2 * π))) ∧
      (∀ j, σ j '' Ico 0 (2 * π) = frontier K) ∧
      IsCircleRepresentation σ := by
  let hG := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  refine ⟨criticalBoundaryTrace hG, criticalBoundaryTrace_continuous hG,
    criticalBoundaryTrace_isMultiPoint hG hS, criticalBoundaryTrace_mem_frontier hG,
    criticalBoundaryTrace_zero hG, criticalBoundaryTrace_periodic hG, ?_, ?_,
    criticalBoundaryTrace_circleRepresentation hG hS⟩
  · intro j
    simpa only [zero_add] using criticalBoundaryTrace_injOn hG j 0
  · intro j
    simpa only [zero_add] using criticalBoundaryTrace_image_Ico hG j 0

end SmoothedOctagon

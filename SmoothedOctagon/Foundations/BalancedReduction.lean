module

public import SmoothedOctagon.Foundations.Normalization
public import SmoothedOctagon.Foundations.BoundaryTrace
public import SmoothedOctagon.Foundations.RadialRegularity
public import SmoothedOctagon.Foundations.ArcLength
public import SmoothedPolygons.Ch2.BalancedDensity

/-!
# From an actual worst disk to a balanced circle minimizer

The preceding modules construct the normalized disk, its continuous contact trace, radial
regularity, and a global Euclidean arclength parameter. This module assembles those inputs
with the upstream boundary lemmas. Every parametrization hypothesis is discharged from an
actual worst disk; no smooth curve or arclength change of parameter is assumed to exist.

The result is a reduction of the geometric minimax problem to the balanced area problem.
It does not compare the resulting minimizer with the octagon.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set SmoothedPolygons

/-- A global increasing regular change of parameter preserves a positive boundary curve. -/
theorem positiveBoundaryParam_reparam {K : Set (Fin 2 → ℝ)}
    {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ)
    (a : ℝ ≃o ℝ) (ha : ContDiff ℝ 1 (fun t ↦ a t))
    (hda : ∀ t, 0 < deriv (fun u ↦ a u) t) :
    IsPositiveBoundaryParam K (γ ∘ a) := by
  have hd : ∀ t, deriv (γ ∘ a) t =
      deriv (fun u ↦ a u) t • deriv γ (a t) := by
    intro t
    exact (((hγ.1.differentiable (by norm_num)) (a t)).hasDerivAt.scomp t
      (((ha.differentiable (by norm_num)) t).hasDerivAt)).deriv
  have hpos : ∀ t, 0 < det2 ((γ ∘ a) t) (deriv (γ ∘ a) t) := by
    intro t
    rw [hd, rein_det2_smul_right]
    exact mul_pos (hda t) (hγ.2.2.2 (a t))
  refine ⟨hγ.1.comp ha, ?_, ?_, hpos⟩
  · intro t hz
    have hp := hpos t
    rw [hz] at hp
    simp [det2] at hp
  · rw [a.surjective.range_comp γ]
    exact hγ.2.2.1

/-- An actual worst disk in normal position has a balanced circle representation.

The common parameter is the Euclidean arclength of its zeroth contact curve. Its full
period is the perimeter `P`, and the balanced-pair parameter is `P / 6`. -/
theorem normalized_worstDisk_exists_balanced_circle {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) (hS : rein_Std K) :
    ∃ σ : ZMod 6 → ℝ → Fin 2 → ℝ, ∃ tf : ℝ,
      IsBalancedPair K σ tf ∧ IsCircleRepresentation σ := by
  let hG := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  let σ := criticalBoundaryTrace hG
  have hσ0 : IsPositiveBoundaryParam K (σ 0) := by
    change IsPositiveBoundaryParam K (criticalBoundaryTrace hG 0)
    rw [criticalBoundaryTrace_zero]
    exact rein_bd_isPositiveBoundaryParam_of_isWorstDisk hK
  have hσ : ∀ j, IsPositiveBoundaryParam K (σ j) :=
    lemma2_4_2 hK (criticalBoundaryTrace_continuous hG)
      (criticalBoundaryTrace_isMultiPoint hG hS)
      (criticalBoundaryTrace_mem_frontier hG) hσ0
  obtain ⟨P, hP, a, ha0, hac, had, haper, harc⟩ :=
    exists_unitSpeed_reparam hσ0.1 hσ0.2.1 two_pi_pos
      (criticalBoundaryTrace_periodic hG 0)
  let τ : ZMod 6 → ℝ → Fin 2 → ℝ := fun j ↦ σ j ∘ a
  have hτpar : ∀ j, IsPositiveBoundaryParam K (τ j) :=
    fun j ↦ positiveBoundaryParam_reparam (hσ j) a hac had
  have hτm : ∀ t, IsMultiPoint fun j ↦ τ j t :=
    fun t ↦ criticalBoundaryTrace_isMultiPoint hG hS (a t)
  have hτK : ∀ j t, τ j t ∈ frontier K :=
    fun j t ↦ criticalBoundaryTrace_mem_frontier hG j (a t)
  have hτ : IsBoundaryMultiCurve K τ := ⟨hτpar, hτm⟩
  have hτlip : ∀ j, ∃ C, LipschitzWith C (deriv (τ j)) :=
    lemma2_4_3 hK (fun j ↦ (hτpar j).1) hτm hτK (hτpar 0).2.2.1 harc
  have haP : a P = 2 * π := by
    simpa only [zero_add, ha0] using haper 0
  have hasymm0 : a.symm 0 = 0 := by
    apply a.injective
    simp only [a.apply_symm_apply, ha0]
  have hasymmP : a.symm (2 * π) = P := by
    apply a.injective
    simp only [a.apply_symm_apply, haP]
  have hIco : a '' Ico 0 P = Ico 0 (2 * π) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨by simpa only [ha0] using a.monotone ht.1,
        by simpa only [haP] using a.strictMono ht.2⟩
    · intro t ht
      refine ⟨a.symm t, ⟨?_, ?_⟩, a.apply_symm_apply t⟩
      · simpa only [hasymm0] using a.symm.monotone ht.1
      · simpa only [hasymmP] using a.symm.strictMono ht.2
  have hmem : ∀ t ∈ Ico 0 P, a t ∈ Ico 0 (2 * π) := by
    intro t ht
    rw [← hIco]
    exact mem_image_of_mem a ht
  have hτinj : ∀ j, InjOn (τ j) (Ico 0 P) := by
    intro j s hs t ht heq
    apply a.injective
    have hinj : InjOn (σ j) (Ico 0 (2 * π)) := by
      simpa only [zero_add] using criticalBoundaryTrace_injOn hG j 0
    exact hinj (hmem s hs) (hmem t ht) heq
  have hτimage : ∀ j, τ j '' Ico 0 P = frontier K := by
    intro j
    change (σ j ∘ a) '' Ico 0 P = frontier K
    rw [image_comp, hIco]
    simpa only [zero_add] using criticalBoundaryTrace_image_Ico hG j 0
  have hperiod : 6 * (P / 6) = P := by ring
  refine ⟨τ, P / 6, ⟨hK.1, fun j ↦ ⟨(hτpar j).1, (hτpar j).2.1⟩,
    hτlip, hτm, lemma2_4_6 hK.1 hτ hτlip, lemma2_4_5 hK.1 hτ,
    div_pos hP (by norm_num), ?_, ?_, ?_⟩, ?_⟩
  · intro j t
    change σ j (a (t + 6 * (P / 6))) = σ j (a t)
    rw [hperiod, haper]
    exact criticalBoundaryTrace_periodic hG j (a t)
  · simpa only [hperiod] using hτinj
  · simpa only [hperiod] using hτimage
  · intro j
    change σ j (a 0) = sixthRoot j
    rw [ha0]
    exact criticalBoundaryTrace_circleRepresentation hG hS j

/-- A balanced circle representation of an actual worst disk minimizes normalized area.
The comparison is over every balanced circle competitor, not just a polygon family. -/
theorem isBalancedCircleMinimizer_of_isWorstDisk {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hbal : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) :
    IsBalancedCircleMinimizer K := by
  refine ⟨⟨σ, tf, hbal, hcirc⟩, ?_⟩
  intro K' σ' tf' hbal' _
  have hden : 0 < √12 := by positivity
  have hbound := (ch2_isWorstDisk_iff.mp hK).2 K' hbal'.1
  rw [greatestPackingDensity_of_isBalancedPair hbal,
    greatestPackingDensity_of_isBalancedPair hbal'] at hbound
  have harea : volume.real K ≤ volume.real K' :=
    (div_le_div_iff_of_pos_right hden).mp hbound
  exact (ENNReal.toReal_le_toReal hK.1.2.1.measure_lt_top.ne
    hbal'.1.2.1.measure_lt_top.ne).mp harea

/-- Every actual worst disk has a density-preserving linear image that is an actual
balanced circle minimizer. The regular boundary representation is constructed above. -/
theorem worstDisk_balanced_normalization {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (d : ℝ),
      rein_PosLin e d ∧ IsWorstDisk (e '' K) ∧
      IsBalancedCircleMinimizer (e '' K) ∧
      greatestPackingDensity (e '' K) = greatestPackingDensity K := by
  obtain ⟨e, d, he, hK', hS, hdensity⟩ := worstDisk_normalization hK
  obtain ⟨σ, tf, hbal, hcirc⟩ := normalized_worstDisk_exists_balanced_circle hK' hS
  exact ⟨e, d, he, hK', isBalancedCircleMinimizer_of_isWorstDisk hK' hbal hcirc, hdensity⟩

/-- The balanced area problem is inhabited by a genuine global packing minimizer. -/
theorem exists_balancedCircle_worst_disk :
    ∃ K : Set (Fin 2 → ℝ), IsWorstDisk K ∧ IsBalancedCircleMinimizer K := by
  obtain ⟨K, hK, hS⟩ := exists_normalized_worst_disk
  obtain ⟨σ, tf, hbal, hcirc⟩ := normalized_worstDisk_exists_balanced_circle hK hS
  exact ⟨K, hK, isBalancedCircleMinimizer_of_isWorstDisk hK hbal hcirc⟩

/-- Conversely, a minimizer of the balanced circle area problem is an actual worst disk.
The reverse comparison uses the constructed balanced representative of a global minimizer. -/
theorem balancedCircleMinimizer_isWorstDisk {K : Set (Fin 2 → ℝ)}
    (hK : IsBalancedCircleMinimizer K) : IsWorstDisk K := by
  obtain ⟨σ, tf, hbal, hcirc⟩ := hK.1
  obtain ⟨W, hW, hWbal⟩ := exists_balancedCircle_worst_disk
  obtain ⟨τ, T, hbalW, hcircW⟩ := hWbal.1
  have harea : volume.real K ≤ volume.real W :=
    ENNReal.toReal_mono hW.1.2.1.measure_lt_top.ne (hK.2 W τ T hbalW hcircW)
  have hdensity : greatestPackingDensity K ≤ greatestPackingDensity W := by
    rw [greatestPackingDensity_of_isBalancedPair hbal,
      greatestPackingDensity_of_isBalancedPair hbalW]
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < √12)).mpr harea
  apply ch2_isWorstDisk_iff.mpr
  exact ⟨hbal.1, fun K' hK' ↦ hdensity.trans ((ch2_isWorstDisk_iff.mp hW).2 K' hK')⟩

end SmoothedOctagon

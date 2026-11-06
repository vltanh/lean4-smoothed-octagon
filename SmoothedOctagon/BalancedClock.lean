module

public import SmoothedOctagon.ControlTrajectory
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Balanced geometry after determinant time normalization

The determinant clock preserves the positive regular boundary curves, their common full
period, their simplicity, and their images. The remaining analytic clause in a balanced pair
is the global Lipschitz property of each contact derivative. This module derives it from the
global Lipschitz frame velocity `g X`: a contact derivative is `(g X) s_j*`, a fixed linear
combination of its entries.

The global velocity bound comes from the periodic frame and the Lipschitz normalized state.
Thus no additional smoothness or Lipschitz hypothesis on the inverse clock is introduced.
The resulting balanced pair can be used in the upstream exact area formula once the cyclic
contact shift is supplied by the separate cyclic-clock construction.

Source draft only: compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real SmoothedPolygons Matrix

private lemma exists_lipschitzWith_mul_const {f : ℝ → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (c : ℝ) :
    ∃ D, LipschitzWith D (fun t ↦ f t * c) := by
  refine ⟨_, LipschitzWith.of_dist_le' (K := (C : ℝ) * |c|) fun x y ↦ ?_⟩
  have hxy := hf.dist_le_mul x y
  simp only [Real.dist_eq] at hxy ⊢
  calc
    |f x * c - f y * c| = |f x - f y| * |c| := by rw [← sub_mul, abs_mul]
    _ ≤ ((C : ℝ) * |x - y|) * |c| :=
      mul_le_mul_of_nonneg_right hxy (abs_nonneg c)
    _ = ((C : ℝ) * |c|) * |x - y| := by ring

/-- A fixed vector applied to an entrywise Lipschitz matrix curve is Lipschitz in the
plane's sup norm. The conclusion includes an actual finite Lipschitz constant. -/
theorem lipschitz_mulVec_of_entrywise {v : ℝ → Mat2}
    (hv : LipschitzOnEntrywise v univ) (w : Fin 2 → ℝ) :
    ∃ C, LipschitzWith C (fun t ↦ v t *ᵥ w) := by
  have hcoord : ∀ i : Fin 2, ∃ C, LipschitzWith C (fun t ↦ (v t *ᵥ w) i) := by
    intro i
    obtain ⟨C0, h0⟩ := hv i 0
    obtain ⟨C1, h1⟩ := hv i 1
    obtain ⟨D0, hD0⟩ := exists_lipschitzWith_mul_const (lipschitzOnWith_univ.1 h0) (w 0)
    obtain ⟨D1, hD1⟩ := exists_lipschitzWith_mul_const (lipschitzOnWith_univ.1 h1) (w 1)
    exact ⟨D0 + D1, by
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hD0.add hD1⟩
  obtain ⟨C0, h0⟩ := hcoord 0
  obtain ⟨C1, h1⟩ := hcoord 1
  have hC0 : (C0 : ℝ) ≤ ((C0 + C1 : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add]
    exact le_add_of_nonneg_right (NNReal.coe_nonneg C1)
  have hC1 : (C1 : ℝ) ≤ ((C0 + C1 : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add]
    exact le_add_of_nonneg_left (NNReal.coe_nonneg C0)
  refine ⟨C0 + C1, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  fin_cases i
  · exact (h0.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right hC0 dist_nonneg)
  · exact (h1.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right hC1 dist_nonneg)

/-- Contact derivatives inherit global Lipschitz regularity from the frame velocity. -/
theorem contact_derivatives_lipschitz_of_frame_velocity
    {τ : ZMod 6 → ℝ → Fin 2 → ℝ} {g X : ℝ → Mat2}
    (hframe : ∀ j t, τ j t = g t *ᵥ sixthRoot j)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hvel : LipschitzOnEntrywise (fun t ↦ g t * X t) univ) :
    ∀ j, ∃ C, LipschitzWith C (deriv (τ j)) := by
  intro j
  have hcurve : τ j = fun t ↦ g t *ᵥ sixthRoot j := funext (hframe j)
  have hd : deriv (τ j) = fun t ↦ (g t * X t) *ᵥ sixthRoot j := by
    rw [hcurve]
    funext t
    exact ((hg t).mulVec_const (sixthRoot j)).deriv
  rw [hd]
  exact lipschitz_mulVec_of_entrywise hvel (sixthRoot j)

/-- An increasing global regular change of time with prescribed period drift preserves
the balanced-pair clauses, once global contact-derivative Lipschitz regularity is proved. -/
theorem balancedPair_reparam_of_derivatives_lipschitz {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    (a : ℝ ≃o ℝ) (ha0 : a 0 = 0) (ha : ContDiff ℝ 1 (fun t ↦ a t))
    (hapos : ∀ t, 0 < deriv (fun u ↦ a u) t) {P : ℝ} (hP : 0 < P)
    (haper : ∀ t, a (t + P) = a t + 6 * tf)
    (hτlip : ∀ j, ∃ C, LipschitzWith C (deriv (σ j ∘ a))) :
    IsBalancedPair K (fun j ↦ σ j ∘ a) (P / 6) := by
  let τ : ZMod 6 → ℝ → Fin 2 → ℝ := fun j ↦ σ j ∘ a
  have hτpar : ∀ j, IsPositiveBoundaryParam K (τ j) := fun j ↦
    positiveBoundaryParam_reparam (positiveBoundaryParam_of_balanced hbal j) a ha hapos
  have hτm : ∀ t, IsMultiPoint fun j ↦ τ j t := fun t ↦ hbal.2.2.2.1 (a t)
  have hτ : IsBoundaryMultiCurve K τ := ⟨hτpar, hτm⟩
  have haP : a P = 6 * tf := by
    simpa only [zero_add, ha0] using haper 0
  have hasymm0 : a.symm 0 = 0 := by
    apply a.injective
    simp only [a.apply_symm_apply, ha0]
  have hasymmP : a.symm (6 * tf) = P := by
    apply a.injective
    simp only [a.apply_symm_apply, haP]
  have hIco : a '' Ico 0 P = Ico 0 (6 * tf) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨by simpa only [ha0] using a.monotone ht.1,
        by simpa only [haP] using a.strictMono ht.2⟩
    · intro t ht
      refine ⟨a.symm t, ⟨?_, ?_⟩, a.apply_symm_apply t⟩
      · simpa only [hasymm0] using a.symm.monotone ht.1
      · simpa only [hasymmP] using a.symm.strictMono ht.2
  have hmem : ∀ t ∈ Ico 0 P, a t ∈ Ico 0 (6 * tf) := by
    intro t ht
    rw [← hIco]
    exact mem_image_of_mem a ht
  have hτinj : ∀ j, InjOn (τ j) (Ico 0 P) := by
    intro j s hs t ht heq
    apply a.injective
    exact hbal.2.2.2.2.2.2.2.2.1 j (hmem s hs) (hmem t ht) heq
  have hτimage : ∀ j, τ j '' Ico 0 P = frontier K := by
    intro j
    change (σ j ∘ a) '' Ico 0 P = frontier K
    rw [← image_image, hIco]
    exact hbal.2.2.2.2.2.2.2.2.2 j
  have hperiod : 6 * (P / 6) = P := by ring
  refine ⟨hbal.1, fun j ↦ ⟨(hτpar j).1, (hτpar j).2.1⟩,
    hτlip, hτm, lemma2_4_6 hbal.1 hτ hτlip, lemma2_4_5 hbal.1 hτ,
    div_pos hP (by norm_num), ?_, ?_, ?_⟩
  · intro j t
    change σ j (a (t + 6 * (P / 6))) = σ j (a t)
    rw [hperiod, haper]
    exact hbal.2.2.2.2.2.2.2.1 j (a t)
  · simpa only [hperiod] using hτinj
  · simpa only [hperiod] using hτimage

/-- The constructed determinant clock preserves the entire balanced pair, including the
global Lipschitz derivative clause. Its input regularity is exactly that already exported
by `balanced_exists_determinant_clock`; no extra inverse-clock regularity is assumed. -/
theorem balancedPair_determinantClock_reparam {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    (a : ℝ ≃o ℝ) (ha0 : a 0 = 0) (ha : ContDiff ℝ 1 (fun t ↦ a t))
    (hapos : ∀ t, 0 < deriv (fun u ↦ a u) t) {P : ℝ} (hP : 0 < P)
    (haper : ∀ t, a (t + P) = a t + 6 * tf)
    (hLip : LipschitzOnEntrywise (normalizedContactState σ a) univ)
    (hg : ∀ t, HasDerivAtEntrywise (fun u ↦ contactFrame σ (a u))
      (contactFrame σ (a t) * normalizedContactState σ a t) t) :
    IsBalancedPair K (fun j ↦ σ j ∘ a) (P / 6) := by
  have hperiod : Function.Periodic (fun t ↦ contactFrame σ (a t)) P := by
    intro t
    rw [haper]
    exact contactFrame_periodic hbal.2.2.2.2.2.2.2.1 (a t)
  have hvel := frame_velocity_lipschitz_periodic hg hLip hP hperiod
  have hframe : ∀ j t, (σ j ∘ a) t = contactFrame σ (a t) *ᵥ sixthRoot j :=
    fun j t ↦ contactFrame_action hbal.2.2.2.1 (a t) j
  exact balancedPair_reparam_of_derivatives_lipschitz hbal a ha0 ha hapos hP haper
    (contact_derivatives_lipschitz_of_frame_velocity hframe hg hvel)

end SmoothedOctagon

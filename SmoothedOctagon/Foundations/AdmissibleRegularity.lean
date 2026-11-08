module

public import SmoothedOctagon.Foundations.ControlTrajectory
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.Compact

/-!
# Regularity of arbitrary integral-form state trajectories

The upstream state-trajectory definition only assumes a measurable control and
integral equations. Those equations give continuous states. Compactness of the
control simplex and the compact time interval then bounds the state commutator:
the trace denominator is strictly negative throughout that compact product.
The integral estimate gives a Lipschitz state, and the continuous frame velocity
gives a `C¹` frame, including one-sided derivatives at the endpoints.

All regularity is derived from `IsStateTrajectory`; no continuity or
differentiability of its measurable control is added as a hypothesis.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Filter Matrix SmoothedPolygons
open scoped Topology

/-- The right-hand side of the normalized matrix state equation. -/
noncomputable def controlCommutator (u : Fin 3 → ℝ) (X : Mat2) : Mat2 :=
  controlP u X * X - X * controlP u X

/-- The control simplex is a closed slice of the compact coordinate box `[0,1]³`. -/
theorem isCompact_controlSimplex : IsCompact controlSimplex := by
  have hset : controlSimplex =
      Icc (0 : Fin 3 → ℝ) 1 ∩ {u | u 0 + u 1 + u 2 = 1} := by
    ext u
    change ((∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ u 0 + u 1 + u 2 = 1) ↔
      ((∀ i, 0 ≤ u i) ∧ (∀ i, u i ≤ 1)) ∧ u 0 + u 1 + u 2 = 1
    constructor
    · rintro ⟨hu, hs⟩
      exact ⟨⟨fun i ↦ (hu i).1, fun i ↦ (hu i).2⟩, hs⟩
    · rintro ⟨⟨hl, hu⟩, hs⟩
      exact ⟨fun i ↦ ⟨hl i, hu i⟩, hs⟩
  have hsum : Continuous fun u : Fin 3 → ℝ ↦ u 0 + u 1 + u 2 :=
    ((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2)
  rw [hset]
  exact isCompact_Icc.inter_right (isClosed_eq hsum continuous_const)

theorem continuous_controlMatrix : Continuous (controlMatrix : (Fin 3 → ℝ) → Mat2) := by
  apply Matrix.continuous_iff_entrywise.mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [controlMatrix, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> fun_prop

/-- The commutator is continuous jointly in time and a simplex control along a
continuous star-state curve. The possible zero denominator is excluded explicitly. -/
theorem continuousOn_controlCommutator {X : ℝ → Mat2} {T : ℝ}
    (hX : ContinuousOn X (Icc 0 T))
    (hstar : ∀ t ∈ Icc 0 T, IsStarState (X t)) :
    ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) ↦ controlCommutator p.2 (X p.1))
      (Icc 0 T ×ˢ controlSimplex) := by
  have hXon : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) ↦ X p.1)
      (Icc 0 T ×ˢ controlSimplex) :=
    hX.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hZon : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) ↦ controlMatrix p.2)
      (Icc 0 T ×ˢ controlSimplex) :=
    (continuous_controlMatrix.comp continuous_snd).continuousOn
  have hmul := hZon.fun_mul hXon
  have hden : ContinuousOn
      (fun p : ℝ × (Fin 3 → ℝ) ↦ traceForm (controlMatrix p.2) (X p.1))
      (Icc 0 T ×ˢ controlSimplex) := by
    simpa only [traceForm, Matrix.trace_fin_two] using
      (Matrix.continuousOn_iff_entrywise.mp hmul 0 0).fun_add
        (Matrix.continuousOn_iff_entrywise.mp hmul 1 1)
  have hne : ∀ p ∈ Icc 0 T ×ˢ controlSimplex,
      traceForm (controlMatrix p.2) (X p.1) ≠ 0 := by
    intro p hp
    have hs := hstar p.1 hp.1
    exact (((lemma3_3_4 (X p.1) hs.1).mp hs.2.2) p.2 hp.2).ne
  have hPon : ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) ↦ controlP p.2 (X p.1))
      (Icc 0 T ×ˢ controlSimplex) := (hden.inv₀ hne).smul hZon
  exact (hPon.mul hXon).sub (hXon.mul hPon)

/-- A finite entrywise bound applies uniformly over every simplex control, so no
regularity of the selected measurable control is needed to bound the state velocity. -/
theorem controlCommutator_bounded {X : ℝ → Mat2} {T : ℝ}
    (hX : ContinuousOn X (Icc 0 T))
    (hstar : ∀ t ∈ Icc 0 T, IsStarState (X t)) (i j : Fin 2) :
    ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ u ∈ controlSimplex,
      |controlCommutator u (X t) i j| ≤ C := by
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ controlSimplex) :=
    isCompact_Icc.prod isCompact_controlSimplex
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (Matrix.continuousOn_iff_entrywise.mp (continuousOn_controlCommutator hX hstar) i j)
  exact ⟨C, fun t ht u hu ↦ by simpa only [Real.norm_eq_abs] using hC (t, u) ⟨ht, hu⟩⟩

/-- A bounded integral velocity makes the curve Lipschitz on the closed interval.
The proof uses the integral equation directly, not a pointwise derivative hypothesis. -/
theorem integralCurve_lipschitz_of_bounded {f v : ℝ → Mat2} {T : ℝ}
    (hT : 0 ≤ T) (hf : IsIntegralCurve f v T)
    (hbound : ∀ i j, ∃ C : ℝ, ∀ t ∈ Icc 0 T, |v t i j| ≤ C) :
    LipschitzOnEntrywise f (Icc 0 T) := by
  intro i j
  obtain ⟨C, hC⟩ := hbound i j
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := C) fun x hx y hy ↦ ?_⟩
  have hxy : uIcc x y ⊆ uIcc 0 T :=
    uIcc_subset_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
  have h0x : IntervalIntegrable (fun t ↦ v t i j) volume 0 x :=
    (hf i j).1.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx))
  have hixy : IntervalIntegrable (fun t ↦ v t i j) volume x y :=
    (hf i j).1.mono_set hxy
  have hsum := intervalIntegral.integral_add_adjacent_intervals h0x hixy
  have hdiff : f y i j - f x i j = ∫ t in x..y, v t i j := by
    rw [(hf i j).2 x hx, (hf i j).2 y hy]
    linarith
  have hnorm : ‖∫ t in x..y, v t i j‖ ≤ C * |y - x| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ by
      have htI : t ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using hxy (uIoc_subset_uIcc ht)
      simpa only [Real.norm_eq_abs] using hC t htI
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (f x i j), hdiff]
  simpa only [Real.norm_eq_abs, abs_sub_comm y x] using hnorm

/-- The Lebesgue fundamental theorem of calculus gives the actual state derivative
almost everywhere from its integral equation. -/
theorem integralCurve_ae_hasDerivAt {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hf : IsIntegralCurve f v T) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise f (v t) t := by
  have heach : ∀ i j, ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAt (fun s ↦ f s i j) (v t i j) t := by
    intro i j
    filter_upwards [(hf i j).1.ae_hasDerivAt_integral] with t ht htI
    have hmem : t ∈ uIcc 0 T := Icc_subset_uIcc (Ioo_subset_Icc_self htI)
    have hd := ht hmem 0 left_mem_uIcc
    exact (hd.const_add (f 0 i j)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Icc_mem_nhds htI.1 htI.2) fun s hs ↦ (hf i j).2 s hs)
  have hall : ∀ᵐ t, ∀ i j, t ∈ Ioo 0 T →
      HasDerivAt (fun s ↦ f s i j) (v t i j) t :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 (heach i)
  filter_upwards [hall] with t ht htI
  exact fun i j ↦ ht i j htI

/-! ## Consequences for every actual state trajectory -/

/-- Both states are continuous, directly from their entrywise integral equations. -/
theorem stateTrajectory_continuous {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) :
    ContinuousOn g (Icc 0 T) ∧ ContinuousOn X (Icc 0 T) :=
  ⟨Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.1,
    Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.2⟩

/-- The matrix state of any integral-form trajectory is Lipschitz on the whole
closed interval, including its endpoints. -/
theorem stateTrajectory_state_lipschitz {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) : LipschitzOnEntrywise X (Icc 0 T) := by
  apply integralCurve_lipschitz_of_bounded h.1.le h.2.2.2.2.2
  intro i j
  obtain ⟨C, hC⟩ := controlCommutator_bounded (stateTrajectory_continuous h).2
    (fun t ht ↦ (h.2.2.2.1 t ht).2) i j
  exact ⟨C, fun t ht ↦ hC t ht (u t) (h.2.2.1 t ht)⟩

/-- The frame equation holds classically on the interior and with the appropriate
one-sided derivatives at both endpoints. -/
theorem stateTrajectory_frame_hasDerivWithinAt {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAtEntrywise g (g t * X t) (Icc 0 T) t := by
  obtain ⟨hgc, hXc⟩ := stateTrajectory_continuous h
  exact Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral h.2.2.2.2.1 ht
    ((hgc.mul hXc) t ht)

theorem stateTrajectory_frame_hasDerivAt {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAtEntrywise g (g t * X t) t :=
  (stateTrajectory_frame_hasDerivWithinAt h t (Ioo_subset_Icc_self ht)).hasDerivAtEntrywise
    (Icc_mem_nhds ht.1 ht.2)

/-- The frame is `C¹` on the closed interval, entry by entry. The derivative
within the interval is the continuous product `g X`, including at its endpoints. -/
theorem stateTrajectory_frame_contDiffOn {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) (i j : Fin 2) :
    ContDiffOn ℝ 1 (fun t ↦ g t i j) (Icc 0 T) := by
  have hu : UniqueDiffOn ℝ (Icc 0 T) := uniqueDiffOn_Icc h.1
  have hd : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s ↦ g s i j) ((g t * X t) i j) (Icc 0 T) t :=
    fun t ht ↦ stateTrajectory_frame_hasDerivWithinAt h t ht i j
  have hgc := (stateTrajectory_continuous h).1
  have hXc := (stateTrajectory_continuous h).2
  have hvc : ContinuousOn (fun t ↦ (g t * X t) i j) (Icc 0 T) :=
    Matrix.continuousOn_iff_entrywise.mp (hgc.mul hXc) i j
  apply (contDiffOn_one_iff_derivWithin hu).mpr
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, ?_⟩
  exact hvc.congr fun t ht ↦ (hd t ht).derivWithin (hu t ht)

/-- The state differential equation holds almost everywhere for every admissible
integral-form trajectory, independently of any regularity of the control. -/
theorem stateTrajectory_state_ae_hasDerivAt {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise X
      (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) t :=
  integralCurve_ae_hasDerivAt h.1.le h.2.2.2.2.2

/-- The curvature inequalities needed for reverse geometric reconstruction follow
from the actual simplex-valued control and the a.e. state equation. -/
theorem stateTrajectory_stateCurvature_nonneg {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) :
    ∀ᵐ t, t ∈ Ioo 0 T → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j := by
  filter_upwards [stateTrajectory_state_ae_hasDerivAt h] with t hd ht
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hstar := (h.2.2.2.1 t htI).2
  have hu := h.2.2.1 t htI
  have hden : traceForm (controlMatrix (u t)) (X t) < 0 :=
    ((lemma3_3_4 (X t) hstar.1).mp hstar.2.2) (u t) hu
  intro j
  rw [(hd ht).derivEntrywise, oct_stateCurvature_eq hstar (u t) hden.ne j]
  exact mul_nonneg
    (mul_nonneg_of_nonpos_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0) (inv_neg''.mpr hden).le)
    (hu.1 j).1

/-- The three state curvatures control all six contacts: the other three are
opposite roots, and the quadratic determinant is unchanged by negating a root. -/
theorem sixthRoot_curvature_nonneg_of_stateCurvature {X X' : Mat2}
    (hκ : ∀ k, 0 ≤ stateCurvature X X' k) (j : ZMod 6) :
    0 ≤ det2 (sixthRoot j) ((X + X⁻¹ * X') *ᵥ sixthRoot j) := by
  let q : ZMod 6 → ℝ := fun k ↦
    det2 (sixthRoot k) ((X + X⁻¹ * X') *ᵥ sixthRoot k)
  have h0 : 0 ≤ q 0 := hκ 0
  have h2 : 0 ≤ q 2 := hκ 1
  have h4 : 0 ≤ q 4 := hκ 2
  have hneg (k : ZMod 6) : q (k + 3) = q k := by
    dsimp only [q]
    rw [(bdy_isMultiPoint_sixthRoot k).2.1, Matrix.mulVec_neg, oct_det2_neg]
  change 0 ≤ q j
  fin_cases j
  · exact h0
  · have heq : q 4 = q 1 := hneg 1
    rwa [heq] at h4
  · exact h2
  · have heq : q 0 = q 3 := (hneg 0).symm
    rwa [heq] at h0
  · exact h4
  · have heq : q 2 = q 5 := (hneg 2).symm
    rwa [heq] at h2

/-- Every contact of an arbitrary integral-form state trajectory has nonnegative
signed curvature almost everywhere on the open interval. The proof is local:
outside `[0,T]` the original frame is unconstrained and is never differentiated. -/
theorem stateTrajectory_contactCurvature_nonneg {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) :
    ∀ᵐ t, t ∈ Ioo 0 T → ∀ j : ZMod 6,
      0 ≤ det2 (deriv (fun s ↦ g s *ᵥ sixthRoot j) t)
        (deriv (deriv (fun s ↦ g s *ᵥ sixthRoot j)) t) := by
  filter_upwards [stateTrajectory_state_ae_hasDerivAt h,
    stateTrajectory_stateCurvature_nonneg h] with t hd hκ ht
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hgD := stateTrajectory_frame_hasDerivAt h t ht
  have hXD : HasDerivAtEntrywise X (derivEntrywise X t) t :=
    (hd ht).congr_deriv (hd ht).derivEntrywise.symm
  intro j
  have hfirst : deriv (fun s ↦ g s *ᵥ sixthRoot j) =ᶠ[𝓝 t]
      fun s ↦ (g s * X s) *ᵥ sixthRoot j :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦
      ((stateTrajectory_frame_hasDerivAt h s hs).mulVec_const (sixthRoot j)).deriv
  have hsecond := (hgD.mul hXD).mulVec_const (sixthRoot j)
  have hdf : deriv (fun s ↦ g s *ᵥ sixthRoot j) t = (g t * X t) *ᵥ sixthRoot j :=
    hfirst.eq_of_nhds
  have hddf : deriv (deriv (fun s ↦ g s *ᵥ sixthRoot j)) t =
      (g t * X t * X t + g t * derivEntrywise X t) *ᵥ sixthRoot j :=
    hfirst.deriv_eq.trans hsecond.deriv
  rw [hdf, hddf]
  rw [normalized_curvature_identity (g t) (X t) (derivEntrywise X t)
    (h.2.2.2.1 t htI).1 (h.2.2.2.1 t htI).2.2.1]
  exact sixthRoot_curvature_nonneg_of_stateCurvature (hκ ht) j

/-- A consolidated interface for extending an arbitrary actual admissible segment.
Every hypothesis is obtained from the original integral-form definition. -/
theorem stateTrajectory_regularity {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) :
    ContinuousOn g (Icc 0 T) ∧ ContinuousOn X (Icc 0 T) ∧
      LipschitzOnEntrywise X (Icc 0 T) ∧
      (∀ i j, ContDiffOn ℝ 1 (fun t ↦ g t i j) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAtEntrywise g (g t * X t) (Icc 0 T) t) ∧
      (∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise X
        (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) t) ∧
      (∀ᵐ t, t ∈ Ioo 0 T → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j) ∧
      (∀ᵐ t, t ∈ Ioo 0 T → ∀ j : ZMod 6,
        0 ≤ det2 (deriv (fun s ↦ g s *ᵥ sixthRoot j) t)
          (deriv (deriv (fun s ↦ g s *ᵥ sixthRoot j)) t)) :=
  ⟨(stateTrajectory_continuous h).1, (stateTrajectory_continuous h).2,
    stateTrajectory_state_lipschitz h, stateTrajectory_frame_contDiffOn h,
    stateTrajectory_frame_hasDerivWithinAt h, stateTrajectory_state_ae_hasDerivAt h,
    stateTrajectory_stateCurvature_nonneg h, stateTrajectory_contactCurvature_nonneg h⟩

end SmoothedOctagon

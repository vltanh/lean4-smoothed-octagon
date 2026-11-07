module

public import SmoothedOctagon.Reduction.Edge.Splice

/-!
# The edge segment of a global minimizer

On an interval `[t₀, t₁] ⊆ [0, T]` on which `u₀ = 0` a.e., the coordinates
`q(τ) = (X₀₀, X₁₀, ∫₀^τ X₁₀)(t₀ + τ)` and the control `v(τ) = u₁(t₀ + τ)` of a global minimizer form
an admissible pair of the edge system on `[0, t₁ - t₀]` (`e4_refAdmissible`), whose cost is the
cost of the segment (`e4_refCost`) and whose frame is recovered from `q` (`e4_refFrame`, MEPB (9)).
By the splice (`e4_splice`) it is a strong local (indeed global) minimizer of the edge problem with
fixed end points and free time (`e4_isStrongLocalMinimizer`).

Main API:

* `e4_refQ`, `e4_refV`: the edge coordinates and control of the segment.
* `e4_refAdmissible`, `e4_refCost`, `e4_refFrame`.
* `e4_isStrongLocalMinimizer`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction.Edge

open SmoothedPolygons MeasureTheory Set Filter Pontryagin ControlSystem
open scoped Topology

/-- The edge coordinates `(a, c, s)(τ) = (X₀₀, X₁₀, ∫₀^τ X₁₀)(t₀ + τ)` of a segment. -/
noncomputable def e4_refQ (X : ℝ → Mat2) (t₀ τ : ℝ) : ℝ × ℝ × ℝ :=
  (X (t₀ + τ) 0 0, X (t₀ + τ) 1 0, ∫ r in (0 : ℝ)..τ, X (t₀ + r) 1 0)

/-- The edge control `v(τ) = u₁(t₀ + τ)` of a segment. -/
def e4_refV (u : ℝ → Fin 3 → ℝ) (t₀ τ : ℝ) : ℝ := u (t₀ + τ) 1

private lemma e4_ae_shift {P : ℝ → Prop} {t₀ t₁ : ℝ} (h : ∀ᵐ t, t ∈ Ioo t₀ t₁ → P t) :
    ∀ᵐ τ, τ ∈ Ioo 0 (t₁ - t₀) → P (t₀ + τ) := by
  have := (measurePreserving_add_right volume t₀).quasiMeasurePreserving.ae h
  filter_upwards [this] with τ hτ hmem
  rw [add_comm]
  exact hτ ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

section Segment

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} {t₀ t₁ : ℝ}

/-- The shifted state of an admissible trajectory is an integral curve on `[0, t₁ - t₀]`. -/
private lemma e4_shift_X (h : IsStateTrajectory T u g X) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ ≤ T) :
    IsIntegralCurve (fun τ ↦ X (t₀ + τ)) (fun τ ↦ controlP (u (t₀ + τ)) (X (t₀ + τ)) *
      X (t₀ + τ) - X (t₀ + τ) * controlP (u (t₀ + τ)) (X (t₀ + τ))) (t₁ - t₀) :=
  isIntegralCurve_comp_add_left h.2.2.2.2.2 h0 (by linarith) (by linarith)

private lemma e4_shift_g (h : IsStateTrajectory T u g X) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ ≤ T) :
    IsIntegralCurve (fun τ ↦ g (t₀ + τ)) (fun τ ↦ g (t₀ + τ) * X (t₀ + τ)) (t₁ - t₀) :=
  isIntegralCurve_comp_add_left h.2.2.2.2.1 h0 (by linarith) (by linarith)

private lemma e4_mem_Icc (h0 : 0 ≤ t₀) (h1 : t₁ ≤ T) {τ : ℝ} (hτ : τ ∈ Icc 0 (t₁ - t₀)) :
    t₀ + τ ∈ Icc 0 T := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩

/-- The edge segment of a state trajectory with `u₀ = 0` a.e. is an admissible edge pair. -/
theorem e4_refAdmissible (h : IsStateTrajectory T u g X) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ ≤ T) (hu0 : ∀ᵐ t, t ∈ Ioo t₀ t₁ → u t 0 = 0) :
    IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (e4_refQ X t₀ 0) (t₁ - t₀)
      (e4_refV u t₀) (e4_refQ X t₀) := by
  have hTe : 0 ≤ t₁ - t₀ := by linarith
  have hXs := e4_shift_X h h0 h01 h1
  have hstar : ∀ τ ∈ Icc 0 (t₁ - t₀), IsStarState (X (t₀ + τ)) := fun τ hτ ↦
    (h.2.2.2.1 _ (e4_mem_Icc h0 h1 hτ)).2
  have hsimp : ∀ τ ∈ Icc 0 (t₁ - t₀), u (t₀ + τ) ∈ controlSimplex := fun τ hτ ↦
    h.2.2.1 _ (e4_mem_Icc h0 h1 hτ)
  have hcont : ∀ i j, ContinuousOn (fun τ ↦ X (t₀ + τ) i j) (Icc 0 (t₁ - t₀)) := fun i j ↦ by
    have := (e4_ac_of_isIntegralCurve hTe hXs i j).continuousOn
    rwa [uIcc_of_le hTe] at this
  have hcint : IntervalIntegrable (fun r ↦ X (t₀ + r) 1 0) volume 0 (t₁ - t₀) :=
    (hcont 1 0).intervalIntegrable_of_Icc hTe
  have hu0' := e4_ae_shift hu0
  -- the first two components of the field agree a.e. with entries of the state field
  have hf : ∀ᵐ τ, τ ∈ Ioo 0 (t₁ - t₀) →
      (controlP (u (t₀ + τ)) (X (t₀ + τ)) * X (t₀ + τ) -
        X (t₀ + τ) * controlP (u (t₀ + τ)) (X (t₀ + τ))) 0 0 =
        (e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)).1 ∧
      (controlP (u (t₀ + τ)) (X (t₀ + τ)) * X (t₀ + τ) -
        X (t₀ + τ) * controlP (u (t₀ + τ)) (X (t₀ + τ))) 1 0 =
        (e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)).2.1 := by
    filter_upwards [hu0'] with τ hτ hmem
    exact e4_stateField_edge (hsimp τ (Ioo_subset_Icc_self hmem)) (hτ hmem)
      (hstar τ (Ioo_subset_Icc_self hmem)) _
  have hI1 : IntervalIntegrable (fun τ ↦ (e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)).1)
      volume 0 (t₁ - t₀) := by
    refine (hXs 0 0).1.congr_ae ?_
    rw [uIoc_of_le hTe]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [hf, volume.ae_ne (t₁ - t₀)] with τ hτ hne hmem
    exact (hτ ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩).1
  have hI2 : IntervalIntegrable (fun τ ↦ (e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)).2.1)
      volume 0 (t₁ - t₀) := by
    refine (hXs 1 0).1.congr_ae ?_
    rw [uIoc_of_le hTe]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [hf, volume.ae_ne (t₁ - t₀)] with τ hτ hne hmem
    exact (hτ ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩).2
  have hI : IntervalIntegrable (fun τ ↦ e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)) volume 0
      (t₁ - t₀) :=
    ⟨hI1.1.prodMk (hI2.1.prodMk hcint.1), hI1.2.prodMk (hI2.2.prodMk hcint.2)⟩
  refine ⟨⟨?_, fun τ hτ ↦ ⟨((hsimp τ hτ).1 1).1, ((hsimp τ hτ).1 1).2⟩, ?_, hI, fun τ hτ ↦ ?_⟩,
    fun τ hτ ↦ e4_mem_edgeDomain_of_isStarState (hstar τ hτ) _⟩
  · exact (measurable_pi_apply 1).comp (h.2.1.comp (measurable_const_add t₀))
  · refine ContinuousOn.prodMk (hcont 0 0) (ContinuousOn.prodMk (hcont 1 0) ?_)
    have :=
      (hcint.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc).continuousOn
    rwa [uIcc_of_le hTe] at this
  · have hτI : IntervalIntegrable (fun τ ↦ e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ))
        volume 0 τ :=
      hI.mono_set (by rw [uIcc_of_le hτ.1, uIcc_of_le hTe]; exact Icc_subset_Icc_right hτ.2)
    have hτ1 : IntervalIntegrable (fun τ ↦ (e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)).1)
        volume 0 τ :=
      hI1.mono_set (by rw [uIcc_of_le hτ.1, uIcc_of_le hTe]; exact Icc_subset_Icc_right hτ.2)
    have hτ2 : IntervalIntegrable (fun τ ↦ (e4_edgeField (e4_refQ X t₀ τ) (e4_refV u t₀ τ)).2.1)
        volume 0 τ :=
      hI2.mono_set (by rw [uIcc_of_le hτ.1, uIcc_of_le hTe]; exact Icc_subset_Icc_right hτ.2)
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · have e := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).intervalIntegral_comp_comm hτI
      simp only [ContinuousLinearMap.coe_fst'] at e
      rw [Prod.fst_add, ← e]
      have e2 := (hXs 0 0).2 τ hτ
      simp only [add_zero] at e2
      simp only [e4_refQ, add_zero]
      rw [e2]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hf, volume.ae_ne τ] with s hs hne hmem
      rw [uIoc_of_le hτ.1] at hmem
      exact (hs ⟨hmem.1, lt_of_lt_of_le (lt_of_le_of_ne hmem.2 hne) hτ.2⟩).1
    · have e := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).intervalIntegral_comp_comm hτI
      simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', Function.comp_apply] at e
      rw [Prod.snd_add, Prod.fst_add, ← e]
      have e2 := (hXs 1 0).2 τ hτ
      simp only [add_zero] at e2
      simp only [e4_refQ, add_zero]
      rw [e2]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hf, volume.ae_ne τ] with s hs hne hmem
      rw [uIoc_of_le hτ.1] at hmem
      exact (hs ⟨hmem.1, lt_of_lt_of_le (lt_of_le_of_ne hmem.2 hne) hτ.2⟩).2
    · have e := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).intervalIntegral_comp_comm hτI
      simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_snd',
        Function.comp_apply] at e
      rw [Prod.snd_add, Prod.snd_add, ← e]
      simp [e4_refQ, e4_edgeField]

/-- The cost of the edge segment is the cost `-(3/2) ∫_{t₀}^{t₁} tr(J X)` of the segment. -/
theorem e4_refCost (h : IsStateTrajectory T u g X) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ ≤ T) :
    cost e4_edgeCost (t₁ - t₀) (e4_refV u t₀) (e4_refQ X t₀) =
      -(3 / 2) * ∫ t in t₀..t₁, traceForm J (X t) := by
  have hTe : 0 ≤ t₁ - t₀ := by linarith
  have e1 : ∫ τ in (0 : ℝ)..t₁ - t₀, e4_edgeCost (e4_refQ X t₀ τ) (e4_refV u t₀ τ) =
      ∫ τ in (0 : ℝ)..t₁ - t₀, -(3 / 2) * traceForm J (X (t₀ + τ)) := by
    refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
    rw [uIcc_of_le hTe] at hτ
    rw [e4_edgeCost_eq_traceForm, e4_refQ,
      e4_edgeX_of_isStarState (h.2.2.2.1 _ (e4_mem_Icc h0 h1 hτ)).2]
  have e2 := intervalIntegral.integral_comp_add_left (fun t ↦ traceForm J (X t)) t₀
    (a := 0) (b := t₁ - t₀)
  simp only [add_zero, add_sub_cancel] at e2
  rw [cost, e1, intervalIntegral.integral_const_mul, e2]

/-- **The frame of the edge segment** (MEPB (9)): `g(t₀ + τ) = g(t₀) h(q(0))⁻¹ h(q(τ))`. -/
theorem e4_refFrame (h : IsStateTrajectory T u g X) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ ≤ T) (hu0 : ∀ᵐ t, t ∈ Ioo t₀ t₁ → u t 0 = 0) :
    ∀ τ ∈ Icc 0 (t₁ - t₀), g (t₀ + τ) =
      g t₀ * (e4_edgeFrame (e4_refQ X t₀ 0)).adjugate * e4_edgeFrame (e4_refQ X t₀ τ) := by
  have hTe : 0 ≤ t₁ - t₀ := by linarith
  have hK := (e4_reconstruct hTe (e4_refAdmissible h h0 h01 h1 hu0)).2
  have hG : IsIntegralCurve (fun τ ↦ g (t₀ + τ))
      (fun τ ↦ g (t₀ + τ) * e4_edgeX (e4_refQ X t₀ τ)) (t₁ - t₀) := by
    refine e4_isIntegralCurve_congr hTe (e4_shift_g h h0 h01 h1) (fun _ _ ↦ rfl) ?_
    refine Eventually.of_forall fun τ hτ ↦ ?_
    rw [e4_refQ, e4_edgeX_of_isStarState
      (h.2.2.2.1 _ (e4_mem_Icc h0 h1 (Ioo_subset_Icc_self hτ))).2]
  have := e4_frame_unique hTe hG hK (fun τ _ ↦ by simp [Matrix.trace_fin_two])
    (fun τ _ ↦ e4_det_edgeFrame _)
  intro τ hτ
  rw [this τ hτ, add_zero]

end Segment

/-- **The edge segment of a global minimizer is a strong local minimizer of the edge problem**
(MEPB §3): fixed end points `q(0)`, `q(t₁ - t₀)`, free time. Any admissible edge pair with these
end points is reconstructed (`e4_reconstruct`) and spliced into the trajectory (`e4_splice`);
global minimality compares the costs. -/
theorem e4_isStrongLocalMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} {t₀ t₁ : ℝ}
    (hmin : IsReinhardtMinimizer T u g X) (h0 : 0 ≤ t₀) (h01 : t₀ < t₁) (h1 : t₁ ≤ T)
    (hu0 : ∀ᵐ t, t ∈ Ioo t₀ t₁ → u t 0 = 0) :
    IsStrongLocalMinimizer e4_edgeField e4_edgeCost e4_edgeDomain (Icc 0 1)
      {w | w = (e4_refQ X t₀ 0, e4_refQ X t₀ (t₁ - t₀))} (t₁ - t₀) (e4_refV u t₀)
      (e4_refQ X t₀) := by
  have hst := hmin.1.1
  have hadm := e4_refAdmissible hst h0 h01.le h1 hu0
  refine ⟨by linarith, hadm, rfl, 1, one_pos, fun T' v' q' hT' hadm' hN' _ _ ↦ ?_⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq] at hN'
  obtain ⟨hq0, hq1⟩ := hN'
  set C := g t₀ * (e4_edgeFrame (e4_refQ X t₀ 0)).adjugate with hC
  obtain ⟨hX', hK'⟩ := e4_reconstruct hT'.le hadm'
  have hstar0 : IsStarState (X t₀) := (hst.2.2.2.1 t₀ ⟨h0, by linarith⟩).2
  have hstar1 : IsStarState (X t₁) := (hst.2.2.2.1 t₁ ⟨by linarith, h1⟩).2
  have hdet0 : (g t₀).det = 1 := (hst.2.2.2.1 t₀ ⟨h0, by linarith⟩).1
  have hframe := e4_refFrame hst h0 h01.le h1 hu0
  have hTe : t₁ - t₀ ∈ Icc 0 (t₁ - t₀) := ⟨by linarith, le_rfl⟩
  have hfr1 := hframe (t₁ - t₀) hTe
  rw [add_sub_cancel] at hfr1
  have hCK : C * e4_edgeFrame (e4_refQ X t₀ 0) = g t₀ := by
    rw [hC, Matrix.mul_assoc, Matrix.adjugate_mul, e4_det_edgeFrame, one_smul, Matrix.mul_one]
  obtain ⟨T'', u'', g'', X'', hadm'', hcost''⟩ := e4_splice hmin.1 h0 h01.le h1 hT'
    (u' := fun t ↦ e4_edgeControl (v' t)) (g' := fun t ↦ C * e4_edgeFrame (q' t))
    (X' := fun t ↦ e4_edgeX (q' t)) (e4_measurable_edgeControl.comp hadm'.1.1)
    (fun t ht ↦ e4_edgeControl_mem (hadm'.1.2.1 t ht))
    (fun t ht ↦ ⟨by rw [Matrix.det_mul, hC, Matrix.det_mul, Matrix.det_adjugate, e4_det_edgeFrame,
        e4_det_edgeFrame, hdet0]; norm_num, e4_isStarState_edgeX (hadm'.2 t ht)⟩)
    (isIntegralCurve_congr (isIntegralCurve_mul_mul hK' C 1) (fun t ↦ by simp only [Matrix.mul_one])
      (fun t ↦ by simp only [Matrix.mul_one, Matrix.mul_assoc])) hX'
    (by simp only [hq0, hCK])
    (by simp only [hq0]; rw [e4_refQ, add_zero, e4_edgeX_of_isStarState hstar0])
    (by simp only [hq1]; exact hfr1.symm)
    (by simp only [hq1]; rw [e4_refQ, add_sub_cancel, e4_edgeX_of_isStarState hstar1])
  have hle := hmin.2 T'' u'' g'' X'' hadm''
  rw [hcost''] at hle
  have hc' : cost e4_edgeCost T' v' q' =
      -(3 / 2) * ∫ t in (0 : ℝ)..T', traceForm J (e4_edgeX (q' t)) := by
    simp only [cost, e4_edgeCost_eq_traceForm, intervalIntegral.integral_const_mul]
  rw [e4_refCost hst h0 h01.le h1, hc']
  linarith

end SmoothedOctagon.Reduction.Edge

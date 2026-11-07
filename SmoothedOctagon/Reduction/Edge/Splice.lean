module

public import SmoothedOctagon.Reduction.Edge.BangBang
public import SmoothedOctagon.Period.Twist

/-!
# Edge competitors and the splice

An admissible pair of the edge system (`System.lean`) is an actual Reinhardt segment: its state is
`e4_edgeX (a, c, s)`, its frame `g₀ h(a₀/c₀, 0)⁻¹ h(a/c, s)` (MEPB (9)-(10)), its control
`(0, v, 1 - v)`, and its cost the edge cost (MEPB (12), in physical time). Replacing the segment
`[t₀, t₁]` of an admissible trajectory by any segment with the same end states and end frames, and
translating the rest in time, gives an admissible trajectory whose cost changes by the difference
of the segment costs. Hence the edge segment of a global minimizer is a (global, so strong local)
minimizer of the edge problem with fixed end points and free time.

Main API:

* `e4_reconstruct`: an admissible edge pair gives integral curves `X = e4_edgeX(q)`,
  `K = e4_edgeFrame(q)`
  with `X' = [P, X]`, `K' = K X`.
* `e4_splice`: replacing a segment of an admissible trajectory by a segment with the same end
  states and frames.
* `e4_isStrongLocalMinimizer`: the edge segment of a global minimizer on an edge is a strong local
  minimizer of the edge problem.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction.Edge

open SmoothedPolygons MeasureTheory Set Filter Pontryagin ControlSystem
open scoped Topology

private lemma e4_ac_const (C T : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ C) 0 T :=
  (LipschitzWith.const C).lipschitzOnWith.absolutelyContinuousOnInterval

/-- **Reconstruction.** Along an admissible edge pair, `X = e4_edgeX(q)` solves `X' = [P_u, X]` with
`u = (0, v, 1 - v)` and `K = e4_edgeFrame(q)` solves `K' = K X`. -/
theorem e4_reconstruct {Te : ℝ} (hTe : 0 ≤ Te) {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q) :
    IsIntegralCurve (fun t ↦ e4_edgeX (q t))
      (fun t ↦ controlP (e4_edgeControl (v t)) (e4_edgeX (q t)) * e4_edgeX (q t) -
        e4_edgeX (q t) * controlP (e4_edgeControl (v t)) (e4_edgeX (q t))) Te ∧
    IsIntegralCurve (fun t ↦ e4_edgeFrame (q t)) (fun t ↦ e4_edgeFrame (q t) * e4_edgeX (q t))
      Te := by
  obtain ⟨ha, hc, hd⟩ := e4_ac_ae hTe hadm
  have hs : AbsolutelyContinuousOnInterval (fun t ↦ (q t).2.2) 0 Te :=
    e4_ac_of_eq_add_integral hTe (e4_coord_s hadm).1 (e4_coord_s hadm).2
  have hsd := e4_ae_hasDerivAt (e4_coord_s hadm).1 (e4_coord_s hadm).2
  have hpos : ∀ t ∈ Icc 0 Te, 0 < (q t).2.1 := fun t ht ↦ (hadm.2 t ht).1
  have hci := e4_ac_inv hTe hc hpos
  have hx : AbsolutelyContinuousOnInterval (fun t ↦ (q t).1 / (q t).2.1) 0 Te :=
    (ha.fun_mul hci).congr fun t _ ↦ by simp [div_eq_mul_inv]
  have hall : ∀ᵐ t, t ∈ Ioo 0 Te → HasDerivAt (fun t ↦ (q t).1) (e4_edgeField (q t) (v t)).1 t ∧
      HasDerivAt (fun t ↦ (q t).2.1) (e4_edgeField (q t) (v t)).2.1 t ∧
      HasDerivAt (fun t ↦ (q t).2.2) (q t).2.1 t := by
    filter_upwards [hd, hsd] with t h1 h2 ht
    exact ⟨(h1 ht).1, (h1 ht).2, h2 ht⟩
  constructor
  · refine e4_isIntegralCurve_of_ac hTe (fun i j ↦ ?_) (fun i j ↦ ?_)
    · fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, e4_edgeX_00, e4_edgeX_01, e4_edgeX_10,
          e4_edgeX_11]
      · exact ha
      · exact (((e4_ac_const (-1) Te).fun_sub (ha.fun_mul ha)).fun_mul hci).congr fun t _ ↦ by
          simp only
          ring
      · exact hc
      · exact ha.fun_neg
    · filter_upwards [hall] with t ht htI
      obtain ⟨h1, h2, -⟩ := ht htI
      have htI' := Ioo_subset_Icc_self htI
      have hz := hadm.2 t htI'
      have hv := hadm.1.2.1 t htI'
      have hD := (e4_edgeDenom_pos hz hv).ne'
      have hcne := (hpos t htI').ne'
      rw [e4_stateField_edgeX hz hv]
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, e4_edgeX_00, e4_edgeX_01, e4_edgeX_10,
          e4_edgeX_11,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
      · exact h1
      · convert (((h1.pow 2).const_add 1).neg).div h2 hcne using 1
        simp only [e4_edgeField, Pi.pow_apply, Pi.neg_apply]
        field_simp
        ring
      · exact h2
      · exact h1.neg
  · refine e4_isIntegralCurve_of_ac hTe (fun i j ↦ ?_) (fun i j ↦ ?_)
    · fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, e4_edgeFrame_00, e4_edgeFrame_01,
          e4_edgeFrame_10, e4_edgeFrame_11]
      · exact e4_ac_const 1 Te
      · exact hx.fun_neg
      · exact hs
      · exact (e4_ac_const 1 Te).fun_sub (hs.fun_mul hx)
    · filter_upwards [hall] with t ht htI
      obtain ⟨h1, h2, h3⟩ := ht htI
      have htI' := Ioo_subset_Icc_self htI
      have hz := hadm.2 t htI'
      have hv := hadm.1.2.1 t htI'
      have hD := (e4_edgeDenom_pos hz hv).ne'
      have hcne := (hpos t htI').ne'
      have hxd : HasDerivAt (fun t ↦ (q t).1 / (q t).2.1) (1 / (q t).2.1) t := by
        convert h1.div h2 hcne using 1
        simp only [e4_edgeField]
        field_simp
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, e4_edgeX_00, e4_edgeX_01, e4_edgeX_10,
          e4_edgeX_11,
          e4_edgeFrame_00, e4_edgeFrame_01, e4_edgeFrame_10, e4_edgeFrame_11, Matrix.mul_apply,
          Fin.sum_univ_two]
      · convert hasDerivAt_const t (1 : ℝ) using 1
        field_simp
        ring
      · convert hxd.neg using 1
        field_simp
        ring
      · convert h3 using 1
        field_simp
        ring
      · convert (hasDerivAt_const t (1 : ℝ)).sub (h3.mul hxd) using 1
        field_simp
        ring

/-! ### The splice -/

/-- `F` on `(-∞, t₀]`, `F'(· - t₀)` on `(t₀, L]`, `F(· - L + t₁)` after `L`. -/
noncomputable def e4_spl {α : Type*} (t₀ L t₁ : ℝ) (F F' : ℝ → α) (t : ℝ) : α :=
  if t ≤ t₀ then F t else if t ≤ L then F' (t - t₀) else F (t - L + t₁)

private lemma e4_spl_left {α : Type*} {t₀ L t₁ : ℝ} {F F' : ℝ → α} {t : ℝ} (ht : t ≤ t₀) :
    e4_spl t₀ L t₁ F F' t = F t := by
  simp [e4_spl, ht]

private lemma e4_spl_mid {α : Type*} {t₀ t₁ T' : ℝ} {F F' : ℝ → α} (h0 : F' 0 = F t₀) {τ : ℝ}
    (hτ : τ ∈ Icc 0 T') : e4_spl t₀ (t₀ + T') t₁ F F' (t₀ + τ) = F' τ := by
  rcases hτ.1.eq_or_lt with rfl | hpos
  · simp [e4_spl, h0]
  · have h1 : ¬ t₀ + τ ≤ t₀ := by linarith
    have h2 : t₀ + τ ≤ t₀ + T' := by linarith [hτ.2]
    simp [e4_spl, h1, h2]

private lemma e4_spl_mid' {α : Type*} {t₀ t₁ T' : ℝ} {F F' : ℝ → α} {τ : ℝ}
    (hτ : τ ∈ Ioc 0 T') : e4_spl t₀ (t₀ + T') t₁ F F' (t₀ + τ) = F' τ := by
  have h1 : ¬ t₀ + τ ≤ t₀ := by linarith [hτ.1]
  have h2 : t₀ + τ ≤ t₀ + T' := by linarith [hτ.2]
  simp [e4_spl, h1, h2]

private lemma e4_spl_right {α : Type*} {t₀ t₁ T' : ℝ} (hT' : 0 < T') {F F' : ℝ → α}
    (h1 : F' T' = F t₁) {τ : ℝ} (hτ : 0 ≤ τ) :
    e4_spl t₀ (t₀ + T') t₁ F F' (t₀ + T' + τ) = F (t₁ + τ) := by
  have ha : ¬ t₀ + T' + τ ≤ t₀ := by linarith
  rcases hτ.eq_or_lt with rfl | hpos
  · have hb : t₀ + T' + 0 ≤ t₀ + T' := by linarith
    simp only [e4_spl, ha, hb, ite_false, ite_true]
    rw [show t₀ + T' + 0 - t₀ = T' by ring, add_zero, h1]
  · have hb : ¬ t₀ + T' + τ ≤ t₀ + T' := by linarith
    simp only [e4_spl, ha, hb, ite_false]
    congr 1
    ring

private lemma e4_spl_right' {α : Type*} {t₀ t₁ T' : ℝ} (hT' : 0 < T') {F F' : ℝ → α} {τ : ℝ}
    (hτ : 0 < τ) : e4_spl t₀ (t₀ + T') t₁ F F' (t₀ + T' + τ) = F (t₁ + τ) := by
  have ha : ¬ t₀ + T' + τ ≤ t₀ := by linarith
  have hb : ¬ t₀ + T' + τ ≤ t₀ + T' := by linarith
  simp only [e4_spl, ha, hb, ite_false]
  congr 1
  ring

theorem e4_traceForm_J (M : Mat2) : traceForm J M = M 0 1 - M 1 0 := by
  simp only [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

private lemma e4_traceForm_continuousOn {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) : ContinuousOn (fun t ↦ traceForm J (f t)) (Icc 0 T) := by
  have hc : ∀ i j, ContinuousOn (fun t ↦ f t i j) (Icc 0 T) := fun i j ↦ by
    have := (e4_ac_of_isIntegralCurve hT h i j).continuousOn
    rwa [uIcc_of_le hT] at this
  simp_rw [e4_traceForm_J]
  exact (hc 0 1).sub (hc 1 0)

/-- **Splice.** Replacing the segment `[t₀, t₁]` of an admissible trajectory by a segment on
`[0, T']` with the same end states and end frames gives an admissible trajectory on
`[0, t₀ + T' + (T - t₁)]`, whose cost changes by the difference of the segment costs. -/
theorem e4_splice {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hadm : IsReinhardtAdmissible T u g X) {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ ≤ T) {T' : ℝ} (hT' : 0 < T') {u' : ℝ → Fin 3 → ℝ} {g' X' : ℝ → Mat2}
    (hu' : Measurable u') (hU' : ∀ t ∈ Icc 0 T', u' t ∈ controlSimplex)
    (hdet' : ∀ t ∈ Icc 0 T', (g' t).det = 1 ∧ IsStarState (X' t))
    (hg' : IsIntegralCurve g' (fun t ↦ g' t * X' t) T')
    (hX' : IsIntegralCurve X'
      (fun t ↦ controlP (u' t) (X' t) * X' t - X' t * controlP (u' t) (X' t)) T')
    (hg0 : g' 0 = g t₀) (hX0 : X' 0 = X t₀) (hg1 : g' T' = g t₁) (hX1 : X' T' = X t₁) :
    ∃ (T'' : ℝ) (u'' : ℝ → Fin 3 → ℝ) (g'' X'' : ℝ → Mat2),
      IsReinhardtAdmissible T'' u'' g'' X'' ∧
      reinhardtCost T'' X'' = reinhardtCost T X + 3 / 2 * (∫ t in t₀..t₁, traceForm J (X t)) -
        3 / 2 * ∫ t in (0 : ℝ)..T', traceForm J (X' t) := by
  obtain ⟨⟨hT, hu, hU, hdet, hg, hX⟩, hgi, hgT, hXT⟩ := hadm
  set L := t₀ + T' with hL
  set T'' := t₀ + T' + (T - t₁) with hT''
  set u'' := e4_spl t₀ L t₁ u u'
  set g'' := e4_spl t₀ L t₁ g g'
  set X'' := e4_spl t₀ L t₁ X X'
  have hT1 : 0 ≤ T - t₁ := by linarith
  -- the field along the spliced trajectory, piece by piece
  have hmid : ∀ τ ∈ Ioc 0 T', u'' (t₀ + τ) = u' τ ∧ g'' (t₀ + τ) = g' τ ∧ X'' (t₀ + τ) = X' τ :=
    fun τ hτ ↦ ⟨e4_spl_mid' hτ, e4_spl_mid' hτ, e4_spl_mid' hτ⟩
  have hright : ∀ τ, 0 < τ → u'' (L + τ) = u (t₁ + τ) ∧ g'' (L + τ) = g (t₁ + τ) ∧
      X'' (L + τ) = X (t₁ + τ) :=
    fun τ hτ ↦ ⟨e4_spl_right' hT' hτ, e4_spl_right' hT' hτ, e4_spl_right' hT' hτ⟩
  have hgen : ∀ (F F' : ℝ → Mat2) (V V'' : ℝ → Mat2),
      IsIntegralCurve F V T → IsIntegralCurve F' (fun t ↦ V'' (t₀ + t)) T' →
      F' 0 = F t₀ → F' T' = F t₁ →
      (∀ t, t < t₀ → V'' t = V t) → (∀ τ, 0 < τ → V'' (L + τ) = V (t₁ + τ)) →
      IsIntegralCurve (e4_spl t₀ L t₁ F F') V'' T'' := by
    intro F F' V V'' hF hF' hF0 hF1 hVl hVr
    have p1 : IsIntegralCurve (e4_spl t₀ L t₁ F F') V'' t₀ := by
      have := isIntegralCurve_comp_add_left hF le_rfl h0 (by linarith)
      simp only [zero_add] at this
      refine e4_isIntegralCurve_congr h0 this (fun t ht ↦ (e4_spl_left ht.2).symm) ?_
      exact Eventually.of_forall fun t ht ↦ (hVl t ht.2).symm
    have p2 : IsIntegralCurve (fun τ ↦ e4_spl t₀ L t₁ F F' (t₀ + τ))
        (fun τ ↦ V'' (t₀ + τ)) T' :=
      e4_isIntegralCurve_congr hT'.le hF' (fun τ hτ ↦ (e4_spl_mid hF0 hτ).symm)
        (Eventually.of_forall fun _ _ ↦ rfl)
    have p3 : IsIntegralCurve (fun τ ↦ e4_spl t₀ L t₁ F F' (L + τ))
        (fun τ ↦ V'' (L + τ)) (T - t₁) := by
      have := isIntegralCurve_comp_add_left hF (le_trans h0 h01) hT1 (by linarith)
      refine e4_isIntegralCurve_congr hT1 this (fun τ hτ ↦ (e4_spl_right hT' hF1 hτ.1).symm) ?_
      exact Eventually.of_forall fun τ hτ ↦ (hVr τ hτ.1).symm
    exact e4_isIntegralCurve_glue (by linarith) hT1 (e4_isIntegralCurve_glue h0 hT'.le p1 p2) p3
  have hXc : IsIntegralCurve X'' (fun t ↦ controlP (u'' t) (X'' t) * X'' t -
      X'' t * controlP (u'' t) (X'' t)) T'' := by
    refine hgen X X' _ _ hX ?_ hX0 hX1 (fun t ht ↦ ?_) (fun τ hτ ↦ ?_)
    · refine e4_isIntegralCurve_congr hT'.le hX' (fun _ _ ↦ rfl) ?_
      refine Eventually.of_forall fun τ hτ ↦ ?_
      obtain ⟨e1, -, e3⟩ := hmid τ ⟨hτ.1, hτ.2.le⟩
      simp only [e1, e3]
    · simp only [u'', X'', e4_spl_left ht.le]
    · obtain ⟨e1, -, e3⟩ := hright τ hτ
      simp only [e1, e3]
  have hgc : IsIntegralCurve g'' (fun t ↦ g'' t * X'' t) T'' := by
    refine hgen g g' _ _ hg ?_ hg0 hg1 (fun t ht ↦ ?_) (fun τ hτ ↦ ?_)
    · refine e4_isIntegralCurve_congr hT'.le hg' (fun _ _ ↦ rfl) ?_
      refine Eventually.of_forall fun τ hτ ↦ ?_
      obtain ⟨-, e2, e3⟩ := hmid τ ⟨hτ.1, hτ.2.le⟩
      simp only [e2, e3]
    · simp only [g'', X'', e4_spl_left ht.le]
    · obtain ⟨-, e2, e3⟩ := hright τ hτ
      simp only [e2, e3]
  -- pointwise conditions
  have hcase : ∀ t ∈ Icc 0 T'', (t ≤ t₀ ∧ t ∈ Icc 0 T) ∨ (∃ τ ∈ Ioc 0 T', t = t₀ + τ) ∨
      (∃ τ, 0 < τ ∧ t = L + τ ∧ t₁ + τ ∈ Icc 0 T) := by
    intro t ht
    by_cases h₁ : t ≤ t₀
    · exact Or.inl ⟨h₁, ht.1, by linarith⟩
    · by_cases h₂ : t ≤ L
      · exact Or.inr (Or.inl ⟨t - t₀, ⟨by linarith, by linarith⟩, by ring⟩)
      · exact Or.inr (Or.inr ⟨t - L, by linarith, by ring, by linarith, by linarith [ht.2]⟩)
  refine ⟨T'', u'', g'', X'', ⟨⟨by linarith, ?_, ?_, ?_, hgc, hXc⟩, ?_, ?_, ?_⟩, ?_⟩
  · exact Measurable.ite measurableSet_Iic hu
      (Measurable.ite measurableSet_Iic (hu'.comp (measurable_sub_const _))
        (hu.comp ((measurable_sub_const _).add_const _)))
  · intro t ht
    rcases hcase t ht with ⟨h, hm⟩ | ⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl, hm⟩
    · simp only [u'', e4_spl_left h]
      exact hU t hm
    · rw [(hmid τ hτ).1]
      exact hU' τ ⟨hτ.1.le, hτ.2⟩
    · rw [(hright τ hτ).1]
      exact hU _ hm
  · intro t ht
    rcases hcase t ht with ⟨h, hm⟩ | ⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl, hm⟩
    · simp only [g'', X'', e4_spl_left h]
      exact hdet t hm
    · rw [(hmid τ hτ).2.1, (hmid τ hτ).2.2]
      exact hdet' τ ⟨hτ.1.le, hτ.2⟩
    · rw [(hright τ hτ).2.1, (hright τ hτ).2.2]
      exact hdet _ hm
  · simp only [g'', e4_spl_left h0, hgi]
  · have := e4_spl_right (t₀ := t₀) (t₁ := t₁) (F := g) (F' := g') hT' hg1 hT1
    simp only [g'', T'']
    rw [this, add_sub_cancel, hgT]
  · have hX0'' : X'' 0 = X 0 := e4_spl_left h0
    have := e4_spl_right (t₀ := t₀) (t₁ := t₁) (F := X) (F' := X') hT' hX1 hT1
    simp only [X'', T''] at hX0'' ⊢
    rw [this, add_sub_cancel, hXT, hX0'']
  · -- the cost
    have hXcont := e4_traceForm_continuousOn (by linarith) hXc
    have hX0c := e4_traceForm_continuousOn hT.le hX
    have hX'c := e4_traceForm_continuousOn hT'.le hX'
    have hi : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T'' →
        IntervalIntegrable (fun t ↦ traceForm J (X'' t)) volume a b := fun a b ha hab hb ↦
      (hXcont.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable
    have hi0 : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T →
        IntervalIntegrable (fun t ↦ traceForm J (X t)) volume a b := fun a b ha hab hb ↦
      (hX0c.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable
    have c1 : ∫ t in (0 : ℝ)..t₀, traceForm J (X'' t) = ∫ t in (0 : ℝ)..t₀, traceForm J (X t) := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le h0] at ht
      simp only [X'', e4_spl_left ht.2]
    have c2 : ∫ t in t₀..L, traceForm J (X'' t) = ∫ t in (0 : ℝ)..T', traceForm J (X' t) := by
      have e := intervalIntegral.integral_comp_add_left (fun t ↦ traceForm J (X'' t)) t₀
        (a := 0) (b := T')
      simp only [add_zero] at e
      rw [hL, ← e]
      refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
      rw [uIcc_of_le hT'.le] at hτ
      exact congrArg (traceForm J) (e4_spl_mid hX0 hτ)
    have c3 : ∫ t in L..T'', traceForm J (X'' t) = ∫ t in t₁..T, traceForm J (X t) := by
      have e1 : T'' = L + (T - t₁) := by rw [hT'', hL]
      have e := intervalIntegral.integral_comp_add_left (fun t ↦ traceForm J (X'' t)) L
        (a := 0) (b := T - t₁)
      simp only [add_zero] at e
      have e2 := intervalIntegral.integral_comp_add_left (fun t ↦ traceForm J (X t)) t₁
        (a := 0) (b := T - t₁)
      simp only [add_zero, add_sub_cancel] at e2
      rw [e1, ← e, ← e2]
      refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
      rw [uIcc_of_le hT1] at hτ
      exact congrArg (traceForm J) (e4_spl_right hT' hX1 hτ.1)
    simp only [reinhardtCost]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₀ le_rfl h0 (by linarith))
        (hi t₀ T'' h0 (by linarith) le_rfl),
      ← intervalIntegral.integral_add_adjacent_intervals (hi t₀ L h0 (by linarith) (by linarith))
        (hi L T'' (by linarith) (by linarith) le_rfl),
      ← intervalIntegral.integral_add_adjacent_intervals (hi0 0 t₀ le_rfl h0 (by linarith))
        (hi0 t₀ T h0 (by linarith) le_rfl),
      ← intervalIntegral.integral_add_adjacent_intervals (hi0 t₀ t₁ h0 h01 h1)
        (hi0 t₁ T (by linarith) h1 le_rfl), c1, c2, c3]
    ring

end SmoothedOctagon.Reduction.Edge

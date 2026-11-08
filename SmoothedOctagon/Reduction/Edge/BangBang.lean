module

public import SmoothedOctagon.Reduction.Edge.System
public import SmoothedPolygons.Ch6.MatrixMinimizer

/-!
# Bang-bang structure of an edge extremal

From the conclusions of the free-time maximum principle for the edge system `e4_edgeField`
(`System.lean`) along an admissible pair `(v, q)` on `[0, T]`, the control is a.e. a concatenation
of at most four constant pieces with values in `{0, 1}`.

With `q = (a, c, s)`, `p_a = p(1, 0, 0)`, `p_c = p(0, 1, 0)`, `p_s = p(0, 0, 1)`:

* `p_s` is constant (the system does not depend on `s`);
* the switching function `σ = p(a, c, 0) = a p_a + c p_c` satisfies `σ' = -c (2 p_s + 3ν(1 + x²))`
  with `x = a/c`, using the adjoint equation, the homogeneity of the field in `(a, c)` and `H = 0`
  (the last eliminates the derivative along the clock);
* the maximum condition gives `v = 1` where `σ > 0` and `v = 0` where `σ < 0`;
* `x` is strictly increasing (`x' = 1/c`), so a nonzero quadratic `2p_s + 3ν(1 + x²)` in `x`
  vanishes at most twice, and `σ` has at most three zeros (Rolle). If `ν = p_s = 0`, `σ` is a
  constant, nonzero by the nontriviality `(ν, p(t)) ≠ 0` and `H = 0`.

Main API:

* `e4_bangBang`: the conclusion, at most four pieces with values in `{0, 1}`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction.Edge

open SmoothedPolygons MeasureTheory Set Filter Pontryagin ControlSystem
open scoped Topology

/-- A covector on `ℝ³` in coordinates. -/
theorem e4_dual_apply (ℓ : StrongDual ℝ (ℝ × ℝ × ℝ)) (x y z : ℝ) :
    ℓ (x, y, z) = x * ℓ (1, 0, 0) + y * ℓ (0, 1, 0) + z * ℓ (0, 0, 1) := by
  have : ((x, y, z) : ℝ × ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
      y • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
      z • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- A linear coordinate of an admissible pair is in integral form. -/
theorem e4_coord {Te : ℝ} {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q)
    (L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ) :
    IntervalIntegrable (fun s ↦ L (e4_edgeField (q s) (v s))) volume 0 Te ∧
      ∀ t ∈ Icc 0 Te, L (q t) = L (q 0) + ∫ s in (0 : ℝ)..t, L (e4_edgeField (q s) (v s)) := by
  obtain ⟨⟨-, -, -, hint, heq⟩, -⟩ := hadm
  refine ⟨⟨L.integrable_comp hint.1, L.integrable_comp hint.2⟩, fun t ht ↦ ?_⟩
  have hint' : IntervalIntegrable (fun s ↦ e4_edgeField (q s) (v s)) volume 0 t := hint.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc_right ht.2)
  conv_lhs => rw [heq t ht]
  rw [map_add, L.intervalIntegral_comp_comm hint']

/-- The coordinates `a` and `c` of an admissible pair, in integral form. -/
theorem e4_coord_a {Te : ℝ} {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q) :
    IntervalIntegrable (fun s ↦ (e4_edgeField (q s) (v s)).1) volume 0 Te ∧
      ∀ t ∈ Icc 0 Te, (q t).1 = (q 0).1 + ∫ s in (0 : ℝ)..t, (e4_edgeField (q s) (v s)).1 :=
  e4_coord hadm (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))

theorem e4_coord_c {Te : ℝ} {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q) :
    IntervalIntegrable (fun s ↦ (e4_edgeField (q s) (v s)).2.1) volume 0 Te ∧
      ∀ t ∈ Icc 0 Te, (q t).2.1 = (q 0).2.1 + ∫ s in (0 : ℝ)..t, (e4_edgeField (q s) (v s)).2.1 :=
  e4_coord hadm ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

theorem e4_coord_s {Te : ℝ} {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q) :
    IntervalIntegrable (fun s ↦ (e4_edgeField (q s) (v s)).2.2) volume 0 Te ∧
      ∀ t ∈ Icc 0 Te, (q t).2.2 = (q 0).2.2 + ∫ s in (0 : ℝ)..t, (e4_edgeField (q s) (v s)).2.2 :=
  e4_coord hadm ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

/-- The integrand of the adjoint equation. -/
noncomputable def e4_adj (ν : ℝ) (v : ℝ → ℝ) (q : ℝ → ℝ × ℝ × ℝ) (p : ℝ → StrongDual ℝ (ℝ × ℝ × ℝ))
    (r : ℝ) : StrongDual ℝ (ℝ × ℝ × ℝ) :=
  (p r).comp (linearization e4_edgeField v q r) + ν • fderiv ℝ (e4_edgeCost · (v r)) (q r)

/-- `p_s` is constant. -/
theorem e4_ps_const {Te ν : ℝ} {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ} {p : ℝ → StrongDual ℝ (ℝ × ℝ × ℝ)}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q)
    (hA : IsAdjoint e4_edgeField e4_edgeCost ν v q Te p) :
    ∀ t ∈ Icc 0 Te, p t (0, 0, 1) = p Te (0, 0, 1) := by
  intro t ht
  have hint : IntervalIntegrable (e4_adj ν v q p) volume t Te := hA.1.mono_set (by
    rw [uIcc_of_le ht.2, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc_left ht.1)
  have h0 : ∫ r in t..Te, e4_adj ν v q p r (0, 0, 1) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) ?_]
    · simp
    intro r hr
    rw [uIcc_of_le ht.2] at hr
    have hr' : r ∈ Icc 0 Te := ⟨ht.1.trans hr.1, hr.2⟩
    simp only [e4_adj, linearization, add_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [e4_fderiv_edgeField_s (hadm.2 r hr') (hadm.1.2.1 r hr'),
      e4_fderiv_edgeCost_s (hadm.2 r hr') (hadm.1.2.1 r hr')]
    simp
  have e := hA.2 t ht
  rw [e, add_apply]
  change p Te (0, 0, 1) + (∫ r in t..Te, e4_adj ν v q p r) (0, 0, 1) = p Te (0, 0, 1)
  rw [ContinuousLinearMap.intervalIntegral_apply hint, h0, add_zero]

/-- The costate is differentiable a.e., `p' = -(p ∘ ∂f + ν ∂φ)`. -/
theorem e4_ae_hasDerivAt_p {Te ν : ℝ} (hTe : 0 ≤ Te) {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    {p : ℝ → StrongDual ℝ (ℝ × ℝ × ℝ)} (hA : IsAdjoint e4_edgeField e4_edgeCost ν v q Te p) :
    ∀ᵐ t, t ∈ Ioo 0 Te → HasDerivAt p (-e4_adj ν v q p t) t := by
  refine ae_hasDerivAt_of_eq_add_integral (w := fun r ↦ -e4_adj ν v q p r) hA.1.neg
    ⟨hTe, le_rfl⟩ (x₀ := p Te) fun t ht ↦ ?_
  rw [hA.2 t ht, intervalIntegral.integral_neg, intervalIntegral.integral_symm]
  rfl

/-- `t ↦ 1/c(t)` is absolutely continuous when `c` is, and positive on `[0, T]`. -/
theorem e4_ac_inv {c : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : AbsolutelyContinuousOnInterval c 0 T)
    (hpos : ∀ t ∈ Icc 0 T, 0 < c t) : AbsolutelyContinuousOnInterval (fun t ↦ (c t)⁻¹) 0 T := by
  have hcont : ContinuousOn c (Icc 0 T) := by
    have := hc.continuousOn
    rwa [uIcc_of_le hT] at this
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hcont
  have hm : 0 < c t₀ := hpos t₀ ht₀
  have hL : LipschitzOnWith (Real.toNNReal (1 / c t₀ ^ 2)) (fun y : ℝ ↦ y⁻¹) (Ici (c t₀)) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have hy0 : 0 < y := lt_of_lt_of_le hm hy
    have hy0' : 0 < y' := lt_of_lt_of_le hm hy'
    rw [inv_sub_inv hy0.ne' hy0'.ne', abs_div, abs_mul, abs_of_pos hy0, abs_of_pos hy0',
      abs_sub_comm, div_le_iff₀ (by positivity)]
    have h1 : c t₀ ^ 2 ≤ y * y' := by
      have := mul_le_mul hy hy' hm.le hy0.le
      nlinarith
    calc |y - y'| = 1 / c t₀ ^ 2 * |y - y'| * c t₀ ^ 2 := by field_simp
      _ ≤ 1 / c t₀ ^ 2 * |y - y'| * (y * y') := by gcongr
  refine hL.comp_absolutelyContinuousOnInterval (g := c) (fun t ht ↦ ?_) hc
  rw [uIcc_of_le hT] at ht
  exact hmin ht

/-- `(a, c)` is absolutely continuous and differentiable a.e. with the field as derivative. -/
theorem e4_ac_ae {Te : ℝ} (hTe : 0 ≤ Te) {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q) :
    AbsolutelyContinuousOnInterval (fun t ↦ (q t).1) 0 Te ∧
      AbsolutelyContinuousOnInterval (fun t ↦ (q t).2.1) 0 Te ∧
      ∀ᵐ t, t ∈ Ioo 0 Te → HasDerivAt (fun t ↦ (q t).1) (e4_edgeField (q t) (v t)).1 t ∧
        HasDerivAt (fun t ↦ (q t).2.1) (e4_edgeField (q t) (v t)).2.1 t := by
  refine ⟨e4_ac_of_eq_add_integral hTe (e4_coord_a hadm).1 (e4_coord_a hadm).2,
    e4_ac_of_eq_add_integral hTe (e4_coord_c hadm).1 (e4_coord_c hadm).2, ?_⟩
  filter_upwards [e4_ae_hasDerivAt (e4_coord_a hadm).1 (e4_coord_a hadm).2,
    e4_ae_hasDerivAt (e4_coord_c hadm).1 (e4_coord_c hadm).2] with t h1 h2 ht
  exact ⟨h1 ht, h2 ht⟩

/-- **The clock.** `x = a/c` is strictly increasing on `[0, T]` (`x' = 1/c > 0`). -/
theorem e4_x_strictMonoOn {Te : ℝ} (hTe : 0 ≤ Te) {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q) :
    StrictMonoOn (fun t ↦ (q t).1 / (q t).2.1) (Icc 0 Te) := by
  obtain ⟨ha, hc, hd⟩ := e4_ac_ae hTe hadm
  have hpos : ∀ t ∈ Icc 0 Te, 0 < (q t).2.1 := fun t ht ↦ (hadm.2 t ht).1
  have hqc : ContinuousOn q (Icc 0 Te) := hadm.1.2.2.1
  have hcc : ContinuousOn (fun t ↦ (q t).2.1) (Icc 0 Te) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn hqc
  have hac : ContinuousOn (fun t ↦ (q t).1) (Icc 0 Te) := continuous_fst.comp_continuousOn hqc
  have hxac : AbsolutelyContinuousOnInterval (fun t ↦ (q t).1 / (q t).2.1) 0 Te :=
    (ha.fun_mul (e4_ac_inv hTe hc hpos)).congr fun t _ ↦ by simp [div_eq_mul_inv]
  have hxd : ∀ᵐ t, t ∈ Ioo 0 Te → HasDerivAt (fun t ↦ (q t).1 / (q t).2.1) (1 / (q t).2.1) t := by
    filter_upwards [hd] with t ht htI
    obtain ⟨h1, h2⟩ := ht htI
    have htI' := Ioo_subset_Icc_self htI
    have hcne := (hpos t htI').ne'
    have hD := (e4_edgeDenom_pos (hadm.2 t htI') (hadm.1.2.1 t htI')).ne'
    convert h1.div h2 hcne using 1
    simp only [e4_edgeField]
    field_simp
  have hx := e4_hasDerivAt_of_ac hTe hxac hxd
    (continuousOn_const.div hcc fun t ht ↦ (hpos t ht).ne')
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 Te) (hac.div hcc fun t ht ↦ (hpos t ht).ne')
    fun t ht ↦ ?_
  rw [interior_Icc] at ht
  rw [(hx t ht).deriv]
  exact one_div_pos.2 (hpos t (Ioo_subset_Icc_self ht))

/-- **The switching function.** `σ = p(a, c, 0)` has derivative `-c (2 p_s + 3ν(1 + x²))` at every
interior time. -/
theorem e4_switching_hasDerivAt {Te ν : ℝ} (hTe : 0 ≤ Te) {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    {p : ℝ → StrongDual ℝ (ℝ × ℝ × ℝ)}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q)
    (hlip : ∃ K, LipschitzOnWith K p (Icc 0 Te))
    (hA : IsAdjoint e4_edgeField e4_edgeCost ν v q Te p)
    (hH : ∀ᵐ t ∂(volume.restrict (Icc 0 Te)),
      controlHamiltonian e4_edgeField e4_edgeCost ν (q t) (p t) (v t) = 0) :
    ∀ t ∈ Ioo 0 Te, HasDerivAt (fun t ↦ p t ((q t).1, (q t).2.1, 0))
      (-(q t).2.1 * (2 * p Te (0, 0, 1) + 3 * ν * (1 + ((q t).1 / (q t).2.1) ^ 2))) t := by
  obtain ⟨ha, hc, hd⟩ := e4_ac_ae hTe hadm
  obtain ⟨K, hK⟩ := hlip
  have hpos : ∀ t ∈ Icc 0 Te, 0 < (q t).2.1 := fun t ht ↦ (hadm.2 t ht).1
  have hπ : ∀ e : ℝ × ℝ × ℝ, AbsolutelyContinuousOnInterval (fun t ↦ p t e) 0 Te := by
    intro e
    have := (ContinuousLinearMap.apply ℝ ℝ e).lipschitzWith.comp_lipschitzOnWith hK
    rw [← uIcc_of_le hTe] at this
    exact this.absolutelyContinuousOnInterval
  have hσeq : (fun t ↦ p t ((q t).1, (q t).2.1, 0)) =
      fun t ↦ (q t).1 * p t (1, 0, 0) + (q t).2.1 * p t (0, 1, 0) := by
    funext t
    rw [e4_dual_apply]
    ring
  rw [hσeq]
  have hσac := (ha.fun_mul (hπ ((1 : ℝ), (0 : ℝ), (0 : ℝ)))).fun_add
    (hc.fun_mul (hπ ((0 : ℝ), (1 : ℝ), (0 : ℝ))))
  have hqc : ContinuousOn q (Icc 0 Te) := hadm.1.2.2.1
  have hcc : ContinuousOn (fun t ↦ (q t).2.1) (Icc 0 Te) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn hqc
  have hac : ContinuousOn (fun t ↦ (q t).1) (Icc 0 Te) := continuous_fst.comp_continuousOn hqc
  refine e4_hasDerivAt_of_ac hTe hσac ?_ ?_
  · filter_upwards [hd, e4_ae_hasDerivAt_p hTe hA, (ae_restrict_iff' measurableSet_Icc).1 hH]
      with t ht hp hHt htI
    obtain ⟨h1, h2⟩ := ht htI
    have htI' := Ioo_subset_Icc_self htI
    have hz := hadm.2 t htI'
    have hv := hadm.1.2.1 t htI'
    have hcne := (hpos t htI').ne'
    have hpa : HasDerivAt (fun s ↦ p s (1, 0, 0)) (-e4_adj ν v q p t (1, 0, 0)) t :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt
        t (hp htI)
    have hpc : HasDerivAt (fun s ↦ p s (0, 1, 0)) (-e4_adj ν v q p t (0, 1, 0)) t :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt
        t (hp htI)
    convert (h1.mul hpa).add (h2.mul hpc) using 1
    -- the algebra
    have hAdecomp := e4_dual_apply (e4_adj ν v q p t) (q t).1 (q t).2.1 0
    have hAval : e4_adj ν v q p t ((q t).1, (q t).2.1, 0) =
        (q t).2.1 * p t (0, 0, 1) + ν * (3 / 2 * ((q t).2.1 + ((q t).1 ^ 2 - 1) / (q t).2.1)) := by
      simp only [e4_adj, linearization, add_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [e4_fderiv_edgeField_scale hz hv, e4_fderiv_edgeCost_scale hz hv, e4_dual_apply (p t) 0 0]
      ring
    have hf : p t (e4_edgeField (q t) (v t)) = (e4_edgeField (q t) (v t)).1 * p t (1, 0, 0) +
        (e4_edgeField (q t) (v t)).2.1 * p t (0, 1, 0) + (q t).2.1 * p t (0, 0, 1) :=
      calc p t (e4_edgeField (q t) (v t)) = p t ((e4_edgeField (q t) (v t)).1,
            (e4_edgeField (q t) (v t)).2.1, (q t).2.1) := rfl
        _ = _ := e4_dual_apply _ _ _ _
    have hHval : (e4_edgeField (q t) (v t)).1 * p t (1, 0, 0) +
        (e4_edgeField (q t) (v t)).2.1 * p t (0, 1, 0) + (q t).2.1 * p t (0, 0, 1) +
        ν * (3 / 2 * ((q t).2.1 + (1 + (q t).1 ^ 2) / (q t).2.1)) = 0 := by
      have := hHt htI'
      simp only [controlHamiltonian, e4_edgeCost] at this
      rw [← hf]
      exact this
    have hps := e4_ps_const hadm hA t htI'
    have hE : 3 / 2 * ((q t).2.1 + (1 + (q t).1 ^ 2) / (q t).2.1) +
        3 / 2 * ((q t).2.1 + ((q t).1 ^ 2 - 1) / (q t).2.1) =
        (q t).2.1 * (3 * (1 + ((q t).1 / (q t).2.1) ^ 2)) := by
      field_simp
      ring
    linear_combination (-1) * hHval - hAdecomp + hAval + 2 * (q t).2.1 * hps + ν * hE
  · exact (hcc.neg).mul (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.add
      ((hac.div hcc fun t ht ↦ (hpos t ht).ne').pow 2))))

/-- The Hamiltonian difference between two controls is proportional to the switching function. -/
theorem e4_ham_sub {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {w w' : ℝ} (hw : w ∈ Icc (0 : ℝ) 1)
    (hw' : w' ∈ Icc (0 : ℝ) 1) (ν : ℝ) (ℓ : StrongDual ℝ (ℝ × ℝ × ℝ)) :
    controlHamiltonian e4_edgeField e4_edgeCost ν z ℓ w -
      controlHamiltonian e4_edgeField e4_edgeCost ν z ℓ w' =
      3 * z.2.1 * (e4_edgeAlpha w - e4_edgeAlpha w') /
        ((z.2.1 - 3 * e4_edgeAlpha w * z.1) * (z.2.1 - 3 * e4_edgeAlpha w' * z.1)) *
        ℓ (z.1, z.2.1, 0) := by
  have hD := (e4_edgeDenom_pos hz hw).ne'
  have hD' := (e4_edgeDenom_pos hz hw').ne'
  obtain ⟨A, hA⟩ : ∃ A, ℓ (1, 0, 0) = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, ℓ (0, 1, 0) = B := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, ℓ (0, 0, 1) = C := ⟨_, rfl⟩
  have key : ∀ x y z, ℓ (x, y, z) = x * A + y * B + z * C := fun x y z ↦ by
    rw [e4_dual_apply, hA, hB, hC]
  simp only [controlHamiltonian, e4_edgeCost, e4_edgeField, key]
  have hc : z.2.1 ≠ 0 := hz.1.ne'
  generalize e4_edgeAlpha w = α at hD ⊢
  generalize e4_edgeAlpha w' = α' at hD' ⊢
  generalize z.1 = a at hD hD' ⊢
  generalize z.2.1 = c at hc hD hD' ⊢
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-(c * A + 3 * α * c * B) * (c - 3 * α * a)⁻¹) * mul_inv_cancel₀ hD' +
    ((c * A + 3 * α' * c * B) * (c - 3 * α' * a)⁻¹) * mul_inv_cancel₀ hD

/-- **Bang-bang.** The maximum condition gives `v = 1` where `σ > 0` and `v = 0` where `σ < 0`. -/
theorem e4_bang {Te ν : ℝ} {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ} {p : ℝ → StrongDual ℝ (ℝ × ℝ × ℝ)}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q)
    (hM : IsMaximal e4_edgeField e4_edgeCost ν (Icc 0 1) v q Te p) :
    ∀ᵐ t, t ∈ Icc 0 Te → (0 < p t ((q t).1, (q t).2.1, 0) → v t = 1) ∧
      (p t ((q t).1, (q t).2.1, 0) < 0 → v t = 0) := by
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hM] with t hmax ht
  have hz := hadm.2 t ht
  have hv := hadm.1.2.1 t ht
  have hc := hz.1
  have hD := e4_edgeDenom_pos hz hv
  have h3 : (0 : ℝ) < √3 := by positivity
  refine ⟨fun hσ ↦ ?_, fun hσ ↦ ?_⟩
  · by_contra hne
    have hlt : v t < 1 := lt_of_le_of_ne hv.2 hne
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hle := sub_nonpos.2 (hmax ht 1 h1)
    rw [e4_ham_sub hz h1 hv] at hle
    have hα : 0 < e4_edgeAlpha 1 - e4_edgeAlpha (v t) := by
      simp only [e4_edgeAlpha]
      rw [← sub_div]
      exact div_pos (by linarith) h3
    have hD1 := e4_edgeDenom_pos hz h1
    have : 0 < 3 * (q t).2.1 * (e4_edgeAlpha 1 - e4_edgeAlpha (v t)) /
        (((q t).2.1 - 3 * e4_edgeAlpha 1 * (q t).1) *
          ((q t).2.1 - 3 * e4_edgeAlpha (v t) * (q t).1)) *
        p t ((q t).1, (q t).2.1, 0) := by positivity
    linarith
  · by_contra hne
    have hlt : 0 < v t := lt_of_le_of_ne hv.1 (Ne.symm hne)
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hle := sub_nonpos.2 (hmax ht 0 h0)
    rw [e4_ham_sub hz h0 hv] at hle
    have hα : e4_edgeAlpha 0 - e4_edgeAlpha (v t) < 0 := by
      simp only [e4_edgeAlpha]
      rw [← sub_div]
      exact div_neg_of_neg_of_pos (by linarith) h3
    have hD0 := e4_edgeDenom_pos hz h0
    have : 0 < 3 * (q t).2.1 * (e4_edgeAlpha 0 - e4_edgeAlpha (v t)) /
        (((q t).2.1 - 3 * e4_edgeAlpha 0 * (q t).1) *
          ((q t).2.1 - 3 * e4_edgeAlpha (v t) * (q t).1)) *
        p t ((q t).1, (q t).2.1, 0) := by
      apply mul_pos_of_neg_of_neg _ hσ
      apply div_neg_of_neg_of_pos _ (by positivity)
      nlinarith
    linarith

/-- **Partition by the zeros.** A continuous function on `[0, T]` without four zeros in `(0, T)`
has constant strict sign on each piece of a partition of `[0, T]` into at most four intervals. -/
theorem e4_partition {σ : ℝ → ℝ} {Te : ℝ} (hTe : 0 < Te) (hσ : ContinuousOn σ (Icc 0 Te))
    (h4 : ∀ t₁ t₂ t₃ t₄ : ℝ, 0 < t₁ → t₁ < t₂ → t₂ < t₃ → t₃ < t₄ → t₄ < Te →
      σ t₁ = 0 → σ t₂ = 0 → σ t₃ = 0 → σ t₄ = 0 → False) :
    ∃ n ≤ 4, ∃ τ : ℕ → ℝ, τ 0 = 0 ∧ τ n = Te ∧ (∀ k < n, τ k < τ (k + 1)) ∧
      (∀ k ≤ n, τ k ∈ Icc 0 Te) ∧
      ∀ k < n, (∀ t ∈ Ioo (τ k) (τ (k + 1)), 0 < σ t) ∨ (∀ t ∈ Ioo (τ k) (τ (k + 1)), σ t < 0) := by
  set Z : Set ℝ := {t | t ∈ Ioo 0 Te ∧ σ t = 0} with hZ
  have hcard : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ Z → s.card ≤ 3 := by
    intro s hs
    by_contra h
    obtain ⟨s', hs'sub, hs'card⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    have hmem : ∀ i, s'.orderEmbOfFin hs'card i ∈ Z := fun i ↦
      hs (hs'sub (s'.orderEmbOfFin_mem hs'card i))
    have hm := (s'.orderEmbOfFin hs'card).strictMono
    exact h4 _ _ _ _ (hmem 0).1.1 (hm (by decide : (0 : Fin 4) < 1))
      (hm (by decide : (1 : Fin 4) < 2)) (hm (by decide : (2 : Fin 4) < 3)) (hmem 3).1.2
      (hmem 0).2 (hmem 1).2 (hmem 2).2 (hmem 3).2
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨s, hs, hs4⟩ := Set.Infinite.exists_subset_card_eq hinf 4
    have := hcard s hs
    omega
  set F := hfin.toFinset with hF
  set k := F.card with hk
  have hk3 : k ≤ 3 := hcard F (by simp [hF])
  set e := F.orderEmbOfFin hk.symm with he
  have heZ : ∀ i, e i ∈ Z := fun i ↦ by
    have : e i ∈ F := F.orderEmbOfFin_mem hk.symm i
    exact (Set.Finite.mem_toFinset hfin).1 this
  set E : ℕ → ℝ := fun i ↦ if h : i < k then e ⟨i, h⟩ else Te with hE
  have hE_pos : ∀ i, 0 < E i := fun i ↦ by
    simp only [hE]
    split_ifs with h
    · exact (heZ _).1.1
    · exact hTe
  have hE_le : ∀ i, E i ≤ Te := fun i ↦ by
    simp only [hE]
    split_ifs with h
    · exact (heZ _).1.2.le
    · exact le_rfl
  have hE_lt : ∀ i, i < k → E i < E (i + 1) := fun i hi ↦ by
    simp only [hE, dite_eq_left hi]
    split_ifs with h
    · exact e.strictMono (show (⟨i, hi⟩ : Fin k) < ⟨i + 1, h⟩ from Fin.mk_lt_mk.2 (by omega))
    · exact (heZ _).1.2
  have hE_mono : ∀ i j, i ≤ j → E i ≤ E j := fun i j hij ↦ by
    by_cases hj : j < k
    · simp only [hE, dite_eq_left hj, dite_eq_left (lt_of_le_of_lt hij hj)]
      exact e.monotone (Fin.mk_le_mk.2 hij)
    · have : E j = Te := by simp only [hE, dite_eq_right hj]
      rw [this]
      exact hE_le i
  have hcov : ∀ t ∈ Z, ∃ j < k, E j = t := fun t ht ↦ by
    have htF : t ∈ F := by rwa [hF, Set.Finite.mem_toFinset]
    have hr := F.range_orderEmbOfFin hk.symm
    have : t ∈ Set.range e := by rw [he, hr]; exact htF
    obtain ⟨j, rfl⟩ := this
    exact ⟨j.1, j.2, by simp [hE, j.2]⟩
  set τ : ℕ → ℝ := fun i ↦ if i = 0 then 0 else E (i - 1) with hτ
  have hτs : ∀ i, τ (i + 1) = E i := fun i ↦ by simp [hτ]
  have hτ0 : τ 0 = 0 := by simp [hτ]
  refine ⟨k + 1, by omega, τ, hτ0, ?_, ?_, ?_, ?_⟩
  · rw [hτs]
    simp [hE]
  · intro i hi
    rw [hτs]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hτ0]
      exact hE_pos 0
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [hτs]
      exact hE_lt j (by omega)
  · intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hτ0]
      exact ⟨le_rfl, hTe.le⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [hτs]
      exact ⟨(hE_pos j).le, hE_le j⟩
  · intro i hi
    have hτi : 0 ≤ τ i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hτ0]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [hτs]
        exact (hE_pos j).le
    have hne : ∀ t ∈ Ioo (τ i) (τ (i + 1)), σ t ≠ 0 := by
      intro t ht h0
      rw [hτs] at ht
      have htZ : t ∈ Z := ⟨⟨lt_of_le_of_lt hτi ht.1, lt_of_lt_of_le ht.2 (hE_le i)⟩, h0⟩
      obtain ⟨j, hj, rfl⟩ := hcov t htZ
      rcases lt_or_ge j i with hji | hji
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [hτs] at ht
        exact absurd ht.1 (not_lt.2 (hE_mono j m (by omega)))
      · exact absurd ht.2 (not_lt.2 (hE_mono i j hji))
    have hsub : Ioo (τ i) (τ (i + 1)) ⊆ Icc 0 Te := fun t ht ↦ by
      rw [hτs] at ht
      exact ⟨hτi.trans ht.1.le, ht.2.le.trans (hE_le i)⟩
    by_cases hpos : ∃ t ∈ Ioo (τ i) (τ (i + 1)), 0 < σ t
    · left
      obtain ⟨t₀, ht₀, hσ₀⟩ := hpos
      intro t ht
      by_contra hle
      have hlt : σ t < 0 := lt_of_le_of_ne (not_lt.1 hle) (hne t ht)
      obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value ht ht₀ (hσ.mono hsub)
        ⟨hlt.le, hσ₀.le⟩
      exact hne x hx hx0
    · right
      push Not at hpos
      exact fun t ht ↦ lt_of_le_of_ne (hpos t ht) (hne t ht)

/-- **The edge bound in the edge system.** Under the conclusions of the free-time maximum
principle, the control is a.e. a concatenation of at most four constant pieces with values in
`{0, 1}`. -/
theorem e4_bangBang {Te ν : ℝ} (hTe : 0 < Te) {v : ℝ → ℝ} {q : ℝ → ℝ × ℝ × ℝ}
    {p : ℝ → StrongDual ℝ (ℝ × ℝ × ℝ)}
    (hadm : IsAdmissibleIn e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) (q 0) Te v q)
    (hlip : ∃ K, LipschitzOnWith K p (Icc 0 Te)) (hN : ∀ t ∈ Icc 0 Te, (ν, p t) ≠ 0)
    (hA : IsAdjoint e4_edgeField e4_edgeCost ν v q Te p)
    (hM : IsMaximal e4_edgeField e4_edgeCost ν (Icc 0 1) v q Te p)
    (hH : ∀ᵐ t ∂(volume.restrict (Icc 0 Te)),
      controlHamiltonian e4_edgeField e4_edgeCost ν (q t) (p t) (v t) = 0) :
    ∃ n ≤ 4, ∃ (τ : ℕ → ℝ) (b : ℕ → ℝ), τ 0 = 0 ∧ τ n = Te ∧ (∀ k < n, τ k < τ (k + 1)) ∧
      (∀ k ≤ n, τ k ∈ Icc 0 Te) ∧ (∀ k < n, b k = 0 ∨ b k = 1) ∧
      ∀ k < n, ∀ᵐ t, t ∈ Ioo (τ k) (τ (k + 1)) → v t = b k := by
  classical
  set σ : ℝ → ℝ := fun t ↦ p t ((q t).1, (q t).2.1, 0) with hσdef
  have hpos : ∀ t ∈ Icc 0 Te, 0 < (q t).2.1 := fun t ht ↦ (hadm.2 t ht).1
  have hσd := e4_switching_hasDerivAt hTe.le hadm hlip hA hH
  have hqc : ContinuousOn q (Icc 0 Te) := hadm.1.2.2.1
  have hσc : ContinuousOn σ (Icc 0 Te) := by
    obtain ⟨K, hK⟩ := hlip
    have hw : ContinuousOn (fun t ↦ (((q t).1, (q t).2.1, (0 : ℝ)) : ℝ × ℝ × ℝ)) (Icc 0 Te) :=
      (continuous_fst.comp_continuousOn hqc).prodMk
        (((continuous_fst.comp continuous_snd).comp_continuousOn hqc).prodMk continuousOn_const)
    exact hK.continuousOn.clm_apply hw
  have hx := e4_x_strictMonoOn hTe.le hadm
  -- the zero of the switching function's derivative
  have hQ : ∀ r ∈ Ioo 0 Te,
      -(q r).2.1 * (2 * p Te (0, 0, 1) + 3 * ν * (1 + ((q r).1 / (q r).2.1) ^ 2)) = 0 →
      2 * p Te (0, 0, 1) + 3 * ν * (1 + ((q r).1 / (q r).2.1) ^ 2) = 0 := fun r hr h ↦ by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (neg_ne_zero.2 (hpos r (Ioo_subset_Icc_self hr)).ne')
    · exact h
  have hrolle : ∀ t₁ t₂, 0 < t₁ → t₁ < t₂ → t₂ < Te → σ t₁ = 0 → σ t₂ = 0 →
      ∃ r ∈ Ioo t₁ t₂, 2 * p Te (0, 0, 1) + 3 * ν * (1 + ((q r).1 / (q r).2.1) ^ 2) = 0 := by
    intro t₁ t₂ h0 h12 h2 z1 z2
    obtain ⟨r, hr, hr0⟩ := exists_hasDerivAt_eq_zero h12
      (hσc.mono (Icc_subset_Icc h0.le h2.le)) (z1.trans z2.symm)
      fun x hx ↦ hσd x ⟨h0.trans hx.1, hx.2.trans h2⟩
    exact ⟨r, hr, hQ r ⟨h0.trans hr.1, hr.2.trans h2⟩ hr0⟩
  have h4 : ∀ t₁ t₂ t₃ t₄ : ℝ, 0 < t₁ → t₁ < t₂ → t₂ < t₃ → t₃ < t₄ → t₄ < Te →
      σ t₁ = 0 → σ t₂ = 0 → σ t₃ = 0 → σ t₄ = 0 → False := by
    intro t₁ t₂ t₃ t₄ h0 h12 h23 h34 h4T z1 z2 z3 z4
    obtain ⟨r₁, hr₁, q₁⟩ := hrolle t₁ t₂ h0 h12 (by linarith) z1 z2
    obtain ⟨r₂, hr₂, q₂⟩ := hrolle t₂ t₃ (by linarith) h23 (by linarith) z2 z3
    obtain ⟨r₃, hr₃, q₃⟩ := hrolle t₃ t₄ (by linarith) h34 h4T z3 z4
    by_cases hν : ν = 0
    · -- `σ` is constant, hence zero, and the costate vanishes somewhere
      have hps : p Te (0, 0, 1) = 0 := by rw [hν] at q₁; linarith
      have hd0 : ∀ t ∈ Ioo 0 Te, HasDerivAt σ 0 t := fun t ht ↦ by
        convert hσd t ht using 1
        rw [hν, hps]
        ring
      have hconst : ∀ x ∈ Icc 0 Te, ∀ y ∈ Icc 0 Te, x < y → σ x = σ y := by
        intro x hx y hy hxy
        obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_slope σ (fun _ ↦ (0 : ℝ)) hxy
          (hσc.mono (Icc_subset_Icc hx.1 hy.2))
          fun r hr ↦ hd0 r ⟨hx.1.trans_lt hr.1, hr.2.trans_le hy.2⟩
        have := sub_ne_zero.2 hxy.ne'
        field_simp at hc0
        linarith
      have hσ0 : ∀ t ∈ Icc 0 Te, σ t = 0 := by
        intro t ht
        have ht₁ : t₁ ∈ Icc 0 Te := ⟨h0.le, by linarith⟩
        rcases lt_trichotomy t t₁ with h | h | h
        · rw [hconst t ht t₁ ht₁ h, z1]
        · rw [h, z1]
        · rw [← hconst t₁ ht₁ t ht h, z1]
      have : (ae (volume.restrict (Icc (0 : ℝ) Te))).NeBot :=
        ae_restrict_neBot.2 (by simp; linarith)
      obtain ⟨t, hHt, htI⟩ := (hH.and (ae_restrict_mem measurableSet_Icc)).exists
      have hz := hadm.2 t htI
      have hv := hadm.1.2.1 t htI
      have hD := (e4_edgeDenom_pos hz hv).ne'
      have hc := (hpos t htI).ne'
      have hpst : p t (0, 0, 1) = 0 := (e4_ps_const hadm hA t htI).trans hps
      have hσt := hσ0 t htI
      simp only [hσdef] at hσt
      rw [e4_dual_apply, hpst] at hσt
      simp only [controlHamiltonian, hν, zero_mul, add_zero] at hHt
      have hf : p t (e4_edgeField (q t) (v t)) = (e4_edgeField (q t) (v t)).1 * p t (1, 0, 0) +
          (e4_edgeField (q t) (v t)).2.1 * p t (0, 1, 0) + (q t).2.1 * p t (0, 0, 1) :=
        calc p t (e4_edgeField (q t) (v t)) = p t ((e4_edgeField (q t) (v t)).1,
              (e4_edgeField (q t) (v t)).2.1, (q t).2.1) := rfl
          _ = _ := e4_dual_apply _ _ _ _
      rw [hf, hpst] at hHt
      simp only [e4_edgeField] at hHt
      have hdet : (q t).2.1 / ((q t).2.1 - 3 * e4_edgeAlpha (v t) * (q t).1) * (q t).2.1 -
          3 * e4_edgeAlpha (v t) * (q t).2.1 / ((q t).2.1 - 3 * e4_edgeAlpha (v t) * (q t).1) *
            (q t).1 = (q t).2.1 := by
        field_simp
      have hpa : p t (1, 0, 0) = 0 := by
        have : (q t).2.1 * p t (1, 0, 0) = 0 := by
          rw [← hdet]
          linear_combination (q t).2.1 * hHt -
            3 * e4_edgeAlpha (v t) * (q t).2.1 /
              ((q t).2.1 - 3 * e4_edgeAlpha (v t) * (q t).1) * hσt
        exact (mul_eq_zero.1 this).resolve_left hc
      have hpc : p t (0, 1, 0) = 0 := by
        rw [hpa] at hσt
        have : (q t).2.1 * p t (0, 1, 0) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hc
      apply hN t htI
      rw [hν]
      refine Prod.ext rfl (ContinuousLinearMap.ext fun w ↦ ?_)
      obtain ⟨w₁, w₂, w₃⟩ := w
      simp only [Prod.snd_zero, zero_apply]
      rw [e4_dual_apply, hpa, hpc, hpst]
      ring
    · -- three distinct values of `x` with the same square
      have hr₁' : r₁ ∈ Icc 0 Te := ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩
      have hr₂' : r₂ ∈ Icc 0 Te := ⟨by linarith [hr₂.1], by linarith [hr₂.2]⟩
      have hr₃' : r₃ ∈ Icc 0 Te := ⟨by linarith [hr₃.1], by linarith [hr₃.2]⟩
      have hx12 := hx hr₁' hr₂' (by linarith [hr₁.2, hr₂.1])
      have hx23 := hx hr₂' hr₃' (by linarith [hr₂.2, hr₃.1])
      simp only at hx12 hx23
      set x₁ := (q r₁).1 / (q r₁).2.1
      set x₂ := (q r₂).1 / (q r₂).2.1
      set x₃ := (q r₃).1 / (q r₃).2.1
      have e12 : x₁ ^ 2 = x₂ ^ 2 := by
        have : 3 * ν * (x₁ ^ 2 - x₂ ^ 2) = 0 := by linarith
        have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero (by norm_num) hν)
        linarith
      have e23 : x₂ ^ 2 = x₃ ^ 2 := by
        have : 3 * ν * (x₂ ^ 2 - x₃ ^ 2) = 0 := by linarith
        have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero (by norm_num) hν)
        linarith
      have s12 : x₁ + x₂ = 0 := by
        have : (x₁ - x₂) * (x₁ + x₂) = 0 := by linear_combination e12
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hx12.ne)
      have s23 : x₂ + x₃ = 0 := by
        have : (x₂ - x₃) * (x₂ + x₃) = 0 := by linear_combination e23
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hx23.ne)
      linarith
  obtain ⟨n, hn, τ, hτ0, hτn, hτlt, hτmem, hsign⟩ := e4_partition hTe hσc h4
  have hbang := e4_bang hadm hM
  refine ⟨n, hn, τ, fun k ↦ if ∀ t ∈ Ioo (τ k) (τ (k + 1)), 0 < σ t then 1 else 0, hτ0, hτn,
    hτlt, hτmem, fun k _ ↦ ?_, fun k hk ↦ ?_⟩
  · dsimp only
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have hsub : Ioo (τ k) (τ (k + 1)) ⊆ Icc 0 Te := fun t ht ↦
      ⟨(hτmem k hk.le).1.trans ht.1.le, ht.2.le.trans (hτmem (k + 1) hk).2⟩
    filter_upwards [hbang] with t ht htk
    obtain ⟨h1, h0⟩ := ht (hsub htk)
    split_ifs with hp
    · exact h1 (hp t htk)
    · rcases hsign k hk with h | h
      · exact absurd h hp
      · exact h0 (h t htk)

end SmoothedOctagon.Reduction.Edge

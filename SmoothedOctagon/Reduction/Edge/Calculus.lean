module

public import SmoothedOctagon.Reduction.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Calculus helpers for the edge bound (E4)

Fundamental theorem of calculus for absolutely continuous functions with an almost-everywhere
derivative, and gluing of integral curves.

Main API:

* `e4_eq_add_integral_of_ac`: an absolutely continuous `F` on `[0, T]` with `F' = f` a.e. is
  `F(t) = F(0) + ∫₀ᵗ f`, `f` interval integrable.
* `e4_hasDerivAt_of_ac`: if moreover `f` is continuous on `[0, T]`, then `F' = f` at every
  interior point.
* `e4_ac_of_eq_add_integral`: an integral curve is absolutely continuous.
* `e4_isIntegralCurve_congr`: integral curves under change of the curve on `[0, T]` and of the
  velocity a.e.
* `e4_isIntegralCurve_glue`: two integral curves on `[0, c]` and `[c, c + d]` glue.
* `e4_isIntegralCurve_of_ac`: entrywise absolute continuity and an a.e. derivative give an integral
  curve.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction.Edge

open SmoothedPolygons MeasureTheory Set Filter
open scoped Topology Interval

/-- **FTC for absolutely continuous functions with a known a.e. derivative.** -/
theorem e4_eq_add_integral_of_ac {F f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hF : AbsolutelyContinuousOnInterval F 0 T)
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt F (f t) t) :
    IntervalIntegrable f volume 0 T ∧ ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, f s := by
  have hae : ∀ᵐ t, t ∈ Ioc 0 T → deriv F t = f t := by
    filter_upwards [hd, volume.ae_ne T] with t ht htT hmem
    exact (ht ⟨hmem.1, lt_of_le_of_ne hmem.2 htT⟩).deriv
  have hint : IntervalIntegrable (deriv F) volume 0 T := hF.intervalIntegrable_deriv
  refine ⟨hint.congr_ae ?_, fun t ht ↦ ?_⟩
  · rw [uIoc_of_le hT]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae
  · have hFt : AbsolutelyContinuousOnInterval F 0 t := hF.mono (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc_right ht.2)
    have h1 := hFt.integral_deriv_eq_sub
    have h2 : ∫ s in (0 : ℝ)..t, deriv F s = ∫ s in (0 : ℝ)..t, f s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with s hs hmem
      rw [uIoc_of_le ht.1] at hmem
      exact hs ⟨hmem.1, hmem.2.trans ht.2⟩
    linarith

/-- **FTC, classical form.** An absolutely continuous `F` on `[0, T]` whose a.e. derivative is a
function continuous on `[0, T]` is differentiable at every interior point, with that derivative. -/
theorem e4_hasDerivAt_of_ac {F f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hF : AbsolutelyContinuousOnInterval F 0 T)
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt F (f t) t) (hf : ContinuousOn f (Icc 0 T)) :
    ∀ t ∈ Ioo 0 T, HasDerivAt F (f t) t := by
  obtain ⟨hint, heq⟩ := e4_eq_add_integral_of_ac hT hF hd
  intro t ht
  have hint' : IntervalIntegrable f volume 0 t := hint.mono_set (by
    rw [uIcc_of_le ht.1.le, uIcc_of_le hT]
    exact Icc_subset_Icc_right ht.2.le)
  have hmeas : StronglyMeasurableAtFilter f (𝓝 t) :=
    (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hc : ContinuousAt f t := hf.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have h := (intervalIntegral.integral_hasDerivAt_right hint' hmeas hc).const_add (F 0)
  exact h.congr_of_eventuallyEq (eventually_of_mem (Icc_mem_nhds ht.1 ht.2)
    fun s hs ↦ heq s hs)

/-- A curve in integral form on `[0, T]` is absolutely continuous there. -/
theorem e4_ac_of_eq_add_integral {F f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T)
    (hF : ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, f s) :
    AbsolutelyContinuousOnInterval F 0 T := by
  have h1 := hf.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ F 0) 0 T :=
    (LipschitzWith.const (F 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine (h0.fun_add h1).congr fun t ht ↦ ?_
  rw [uIcc_of_le hT] at ht
  exact (hF t ht).symm

/-- Lebesgue's differentiation theorem for a real curve in integral form. -/
theorem e4_ae_hasDerivAt {F f : ℝ → ℝ} {T : ℝ} (hf : IntervalIntegrable f volume 0 T)
    (hF : ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, f s) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt F (f t) t := by
  filter_upwards [hf.ae_hasDerivAt_integral] with t ht htI
  have hmem : t ∈ uIcc 0 T := Icc_subset_uIcc (Ioo_subset_Icc_self htI)
  exact ((ht hmem 0 left_mem_uIcc).const_add (F 0)).congr_of_eventuallyEq
    (eventually_of_mem (Icc_mem_nhds htI.1 htI.2) fun s hs ↦ hF s hs)

/-- The entries of an integral curve are absolutely continuous. -/
theorem e4_ac_of_isIntegralCurve {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t ↦ f t i j) 0 T :=
  e4_ac_of_eq_add_integral hT (h i j).1 (h i j).2

/-- The entries of an integral curve have the velocity as derivative almost everywhere. -/
theorem e4_ae_hasDerivAt_of_isIntegralCurve {f v : ℝ → Mat2} {T : ℝ}
    (h : IsIntegralCurve f v T) :
    ∀ᵐ t, t ∈ Ioo 0 T → ∀ i j, HasDerivAt (fun s ↦ f s i j) (v t i j) t := by
  have h' : ∀ i j, ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt (fun s ↦ f s i j) (v t i j) t :=
    fun i j ↦ e4_ae_hasDerivAt (h i j).1 (h i j).2
  filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 (h' i)] with t ht htI i j
  exact ht i j htI

/-- Entrywise absolute continuity and an a.e. derivative give an integral curve. -/
theorem e4_isIntegralCurve_of_ac {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hac : ∀ i j, AbsolutelyContinuousOnInterval (fun t ↦ f t i j) 0 T)
    (hd : ∀ i j, ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt (fun s ↦ f s i j) (v t i j) t) :
    IsIntegralCurve f v T :=
  fun i j ↦ e4_eq_add_integral_of_ac hT (hac i j) (hd i j)

/-- An integral curve with the curve changed off `[0, T]` and the velocity changed on a null set. -/
theorem e4_isIntegralCurve_congr {f f' v v' : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) (hf : ∀ t ∈ Icc 0 T, f t = f' t)
    (hv : ∀ᵐ t, t ∈ Ioo 0 T → v t = v' t) : IsIntegralCurve f' v' T := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  have hae : ∀ t ∈ Icc 0 T, ∀ᵐ s, s ∈ Ι 0 t → v s i j = v' s i j := by
    intro t ht
    filter_upwards [hv, volume.ae_ne T] with s hs hsT hmem
    rw [uIoc_of_le ht.1] at hmem
    rw [hs ⟨hmem.1, lt_of_le_of_ne (hmem.2.trans ht.2) hsT⟩]
  refine ⟨hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 (hae T ⟨hT, le_rfl⟩)),
    fun t ht ↦ ?_⟩
  rw [← hf t ht, ← hf 0 ⟨le_rfl, hT⟩, heq t ht, intervalIntegral.integral_congr_ae (hae t ht)]

/-- **Gluing.** An integral curve on `[0, c]` whose continuation `f(c + ·)` is an integral curve on
`[0, d]` is an integral curve on `[0, c + d]`. -/
theorem e4_isIntegralCurve_glue {f v : ℝ → Mat2} {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h₁ : IsIntegralCurve f v c)
    (h₂ : IsIntegralCurve (fun t ↦ f (c + t)) (fun t ↦ v (c + t)) d) :
    IsIntegralCurve f v (c + d) := by
  intro i j
  obtain ⟨hi₁, he₁⟩ := h₁ i j
  obtain ⟨hi₂, he₂⟩ := h₂ i j
  have hi₂' : IntervalIntegrable (fun s ↦ v s i j) volume c (c + d) := by
    have := hi₂.comp_sub_right c
    simp only [add_sub_cancel, zero_add] at this
    rwa [add_comm d c] at this
  refine ⟨hi₁.trans hi₂', fun t ht ↦ ?_⟩
  rcases le_or_gt t c with htc | htc
  · exact he₁ t ⟨ht.1, htc⟩
  · have e1 := he₂ (t - c) ⟨by linarith, by linarith [ht.2]⟩
    simp only [add_sub_cancel, add_zero] at e1
    have e2 : ∫ s in (0 : ℝ)..t - c, v (c + s) i j = ∫ s in c..t, v s i j := by
      rw [intervalIntegral.integral_comp_add_left (fun s ↦ v s i j) c, add_zero,
        add_sub_cancel]
    have hct : IntervalIntegrable (fun s ↦ v s i j) volume c t := hi₂'.mono_set (by
      rw [uIcc_of_le htc.le, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc_right ht.2)
    rw [e1, e2, he₁ c ⟨hc, le_rfl⟩, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals hi₁ hct]

private lemma e4_mul_adj_zero (A B : Mat2) (i : Fin 2) :
    (A * B.adjugate) i 0 = A i 0 * B 1 1 - A i 1 * B 1 0 := by
  rw [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

private lemma e4_mul_adj_one (A B : Mat2) (i : Fin 2) :
    (A * B.adjugate) i 1 = -(A i 0 * B 0 1) + A i 1 * B 0 0 := by
  rw [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

private lemma e4_mul_apply (A B : Mat2) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

/-- An absolutely continuous function with derivative zero a.e. on `(0, T)` is constant. -/
theorem e4_const_of_ae_hasDerivAt_zero {φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hφ : AbsolutelyContinuousOnInterval φ 0 T) (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt φ 0 t) :
    ∀ t ∈ Icc 0 T, φ t = φ 0 := by
  have hd' : ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt φ 0 t := by
    filter_upwards [hd, volume.ae_ne 0, volume.ae_ne T] with t ht h0 hT' hmem
    rw [uIcc_of_le hT] at hmem
    exact ht ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), lt_of_le_of_ne hmem.2 hT'⟩
  obtain ⟨C, hC⟩ := hφ.const_of_ae_hasDerivAt_zero hd'
  intro t ht
  rw [uIcc_of_le hT] at hC
  rw [hC t ht, hC 0 ⟨le_rfl, hT⟩]

/-- **Uniqueness for `g' = g Y`.** If `G' = G Y` and `K' = K Y` with `Y` traceless and
`det K = 1`, then `G(t) = G(0) adj(K(0)) K(t)` (the entries of `G adj K` have derivative zero). -/
theorem e4_frame_unique {G K Y : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hG : IsIntegralCurve G (fun t ↦ G t * Y t) T) (hK : IsIntegralCurve K (fun t ↦ K t * Y t) T)
    (hY : ∀ t ∈ Icc 0 T, (Y t).trace = 0) (hdet : ∀ t ∈ Icc 0 T, (K t).det = 1) :
    ∀ t ∈ Icc 0 T, G t = G 0 * (K 0).adjugate * K t := by
  have hGa := e4_ac_of_isIntegralCurve hT hG
  have hKa := e4_ac_of_isIntegralCurve hT hK
  have hd : ∀ᵐ t, t ∈ Ioo 0 T → (∀ i j, HasDerivAt (fun s ↦ G s i j) ((G t * Y t) i j) t) ∧
      (∀ i j, HasDerivAt (fun s ↦ K s i j) ((K t * Y t) i j) t) := by
    filter_upwards [e4_ae_hasDerivAt_of_isIntegralCurve hG,
      e4_ae_hasDerivAt_of_isIntegralCurve hK] with t hg hk htI
    exact ⟨hg htI, hk htI⟩
  have hM : ∀ i l, ∀ t ∈ Icc 0 T, (G t * (K t).adjugate) i l = (G 0 * (K 0).adjugate) i l := by
    intro i l
    fin_cases l
    · simp only [Fin.zero_eta, e4_mul_adj_zero]
      refine e4_const_of_ae_hasDerivAt_zero hT
        (((hGa i 0).fun_mul (hKa 1 1)).fun_sub ((hGa i 1).fun_mul (hKa 1 0))) ?_
      filter_upwards [hd] with t ht htI
      obtain ⟨hg, hk⟩ := ht htI
      have htr := hY t (Ioo_subset_Icc_self htI)
      rw [Matrix.trace_fin_two] at htr
      convert ((hg i 0).mul (hk 1 1)).sub ((hg i 1).mul (hk 1 0)) using 1
      simp only [e4_mul_apply]
      linear_combination (-(G t i 0 * K t 1 1) + G t i 1 * K t 1 0) * htr
    · simp only [Fin.mk_one, e4_mul_adj_one]
      refine e4_const_of_ae_hasDerivAt_zero hT
        (((hGa i 0).fun_mul (hKa 0 1)).fun_neg.fun_add ((hGa i 1).fun_mul (hKa 0 0))) ?_
      filter_upwards [hd] with t ht htI
      obtain ⟨hg, hk⟩ := ht htI
      have htr := hY t (Ioo_subset_Icc_self htI)
      rw [Matrix.trace_fin_two] at htr
      convert ((hg i 0).mul (hk 0 1)).neg.add ((hg i 1).mul (hk 0 0)) using 1
      simp only [e4_mul_apply]
      linear_combination (G t i 0 * K t 0 1 - G t i 1 * K t 0 0) * htr
  intro t ht
  have hMt : G t * (K t).adjugate = G 0 * (K 0).adjugate := by
    ext i l
    exact hM i l t ht
  calc G t = G t * ((K t).adjugate * K t) := by
        rw [Matrix.adjugate_mul, hdet t ht, one_smul, Matrix.mul_one]
    _ = G 0 * (K 0).adjugate * K t := by rw [← Matrix.mul_assoc, hMt]

end SmoothedOctagon.Reduction.Edge

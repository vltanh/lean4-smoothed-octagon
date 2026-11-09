module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.IntermediateValue
public import Basic.Analysis.Convex.StarCurve

/-!
# Continuous angles without covering spaces

Elementary tools for the projective winding of case M1 (`Exclusion/ShortRuns/Winding.lean`): a real
`θ` is *an angle of* a nonzero complex number `z` (`wind_IsAng θ z`) when `z = r e^{iθ}` with
`r > 0`; angles add under products and are unique modulo `2π`. A continuous real function on an
interval whose increments are multiples of `2π` is constant (`wind_eq_of_int`); this gives the
uniqueness of continuous angles. Plane vectors are complex numbers through `sc_toC v = v₀ + v₁ i`.

## Main API

* `wind_IsAng`, `wind_isAng_arg`, `wind_IsAng.mul`, `wind_IsAng.pos_mul`, `wind_IsAng.unique`,
  `wind_isAng_exp`.
* `wind_eq_of_int`: constancy of a continuous function with `2πℤ` increments.
* `wind_continuousOn_arg`: `arg ∘ f` is continuous where `f` stays in the slit plane.
* `wind_toC_add`, `wind_toC_neg`, `wind_toC_mulVec_ne`, `wind_cOn_mulVec`, `wind_cOn_toC`.
-/

@[expose] public section

namespace SmoothedOctagon

open Complex Set PlaneCurve
open scoped Matrix

/-- `θ` is an angle of `z`: `z = r e^{iθ}` with `r > 0`. -/
def wind_IsAng (θ : ℝ) (z : ℂ) : Prop := ∃ r : ℝ, 0 < r ∧ z = r * exp (θ * I)

theorem wind_isAng_arg {z : ℂ} (hz : z ≠ 0) : wind_IsAng (arg z) z :=
  ⟨‖z‖, norm_pos_iff.2 hz, (norm_mul_exp_arg_mul_I z).symm⟩

theorem wind_isAng_exp (θ : ℝ) : wind_IsAng θ (exp (θ * I)) := ⟨1, one_pos, by simp⟩

theorem wind_IsAng.mul {a b : ℝ} {z w : ℂ} (h1 : wind_IsAng a z) (h2 : wind_IsAng b w) :
    wind_IsAng (a + b) (z * w) := by
  obtain ⟨r, hr, rfl⟩ := h1
  obtain ⟨s, hs, rfl⟩ := h2
  refine ⟨r * s, mul_pos hr hs, ?_⟩
  push_cast
  rw [show ((a : ℂ) + b) * I = a * I + b * I by ring, exp_add]
  ring

theorem wind_IsAng.pos_mul {a c : ℝ} {z : ℂ} (h : wind_IsAng a z) (hc : 0 < c) :
    wind_IsAng a (c * z) := by
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨c * r, mul_pos hc hr, by push_cast; ring⟩

theorem wind_IsAng.ne_zero {a : ℝ} {z : ℂ} (h : wind_IsAng a z) : z ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := h
  exact mul_ne_zero (by exact_mod_cast hr.ne') (exp_ne_zero _)

/-- Angles are unique modulo `2π`. -/
theorem wind_IsAng.unique {a b : ℝ} {z : ℂ} (h1 : wind_IsAng a z) (h2 : wind_IsAng b z) :
    ∃ n : ℤ, b = a + n * (2 * Real.pi) := by
  obtain ⟨r, hr, rfl⟩ := h1
  obtain ⟨s, hs, hsz⟩ := h2
  have hn : ‖(r : ℂ) * exp (a * I)‖ = ‖(s : ℂ) * exp (b * I)‖ := by rw [hsz]
  simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs,
    norm_exp_ofReal_mul_I, mul_one] at hn
  subst hn
  have he : exp (b * I) = exp (a * I) := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact (mul_left_cancel₀ hr0 hsz).symm
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- **Constancy of a continuous function with increments in `2πℤ`.** -/
theorem wind_eq_of_int {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hint : ∀ t ∈ Icc a b, ∃ n : ℤ, f t = f a + n * (2 * Real.pi)) : f b = f a := by
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := hint b ⟨hab, le_rfl⟩
  have hhalf : ∀ t ∈ Icc a b, f t ≠ f a + Real.pi ∧ f t ≠ f a - Real.pi := by
    intro t ht
    obtain ⟨k, hk⟩ := hint t ht
    constructor <;> intro h <;> rw [h] at hk
    · have : (1 : ℝ) = 2 * k := by nlinarith
      have : (1 : ℤ) = 2 * k := by exact_mod_cast this
      omega
    · have : (-1 : ℝ) = 2 * k := by nlinarith
      have : (-1 : ℤ) = 2 * k := by exact_mod_cast this
      omega
  rcases lt_trichotomy n 0 with h | h | h
  · exfalso
    have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hmem : f a - Real.pi ∈ Icc (f b) (f a) := ⟨by rw [hn]; nlinarith, by linarith⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hab hf hmem
    exact (hhalf t ht).2 hft
  · rw [hn, h]; simp
  · exfalso
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hmem : f a + Real.pi ∈ Icc (f a) (f b) := ⟨by linarith, by rw [hn]; nlinarith⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf hmem
    exact (hhalf t ht).1 hft

/-- Two continuous angle functions of the same complex function differ by a constant. -/
theorem wind_angle_const {f : ℝ → ℝ} {a b : ℝ} {z : ℂ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hz : ∀ t ∈ Icc a b, ∃ c : ℝ, 0 < c ∧ wind_IsAng (f t) (c * z))
    (ha : wind_IsAng (f a) z) : f b = f a := by
  refine wind_eq_of_int hab hf fun t ht ↦ ?_
  obtain ⟨c, hc, hct⟩ := hz t ht
  obtain ⟨r, hr, hr'⟩ := hct
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hz' : z = ((r / c : ℝ) : ℂ) * exp (f t * I) := by
    have : z = (c : ℂ)⁻¹ * (c * z) := by field_simp
    rw [this, hr']; push_cast; field_simp
  obtain ⟨n, hn⟩ := ha.unique (b := f t) ⟨r / c, div_pos hr hc, hz'⟩
  exact ⟨n, hn⟩

theorem wind_continuousOn_arg {f : ℝ → ℂ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hs : ∀ t ∈ s, f t ∈ slitPlane) : ContinuousOn (fun t ↦ arg (f t)) s :=
  fun t ht ↦ (continuousAt_arg (hs t ht)).comp_continuousWithinAt (hf t ht)

/-! ### Plane vectors as complex numbers -/

theorem wind_toC_add (v w : Fin 2 → ℝ) : sc_toC (v + w) = sc_toC v + sc_toC w := by
  apply Complex.ext <;> simp

theorem wind_toC_neg (v : Fin 2 → ℝ) : sc_toC (-v) = -sc_toC v := by
  apply Complex.ext <;> simp

theorem wind_toC_ne {v : Fin 2 → ℝ} (hv : v ≠ 0) : sc_toC v ≠ 0 :=
  fun h ↦ hv (sc_toC_eq_zero.1 h)

theorem wind_toC_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    sc_toC (M *ᵥ v) = ((M 0 0 * v 0 + M 0 1 * v 1 : ℝ) : ℂ) + ((M 1 0 * v 0 + M 1 1 * v 1 : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- An invertible matrix maps nonzero vectors to nonzero vectors. -/
theorem wind_mulVec_ne {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) {v : Fin 2 → ℝ}
    (hv : v ≠ 0) : M *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (M.adjugate *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero] at this
  exact (smul_eq_zero.1 this).resolve_left hM

theorem wind_toC_mulVec_ne {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) {v : Fin 2 → ℝ}
    (hv : v ≠ 0) : sc_toC (M *ᵥ v) ≠ 0 := wind_toC_ne (wind_mulVec_ne hM hv)

theorem wind_cOn_mulVec {s : Set ℝ} {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Fin 2 → ℝ}
    (hM : ContinuousOn M s) (hv : ContinuousOn v s) : ContinuousOn (fun t ↦ M t *ᵥ v t) s :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_continuousOn (hM.prodMk hv)

theorem wind_cOn_toC {s : Set ℝ} {v : ℝ → Fin 2 → ℝ} (hv : ContinuousOn v s) :
    ContinuousOn (fun t ↦ sc_toC (v t)) s :=
  sc_continuous_toC.comp_continuousOn hv

/-- `Im(w z̄) = det(z, w)` and `Re(w z̄) = z · w`. -/
theorem wind_toC_mul_conj (v w : Fin 2 → ℝ) :
    (sc_toC w * (starRingEnd ℂ) (sc_toC v)).im = v 0 * w 1 - v 1 * w 0 ∧
      (sc_toC w * (starRingEnd ℂ) (sc_toC v)).re = v 0 * w 0 + v 1 * w 1 := by
  constructor <;> simp [sc_toC] <;> ring

/-- A quotient lies in the slit plane iff `w z̄` does. -/
theorem wind_div_mem_slit {z w : ℂ} (hz : z ≠ 0) (h : w * (starRingEnd ℂ) z ∈ slitPlane) :
    w / z ∈ slitPlane := by
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.2 hz
  have e : w / z = ((Complex.normSq z)⁻¹ : ℝ) * (w * (starRingEnd ℂ) z) := by
    rw [div_eq_mul_inv, Complex.inv_def]; push_cast; ring
  rw [e]
  rw [mem_slitPlane_iff] at h ⊢
  have hinv : 0 < (Complex.normSq z)⁻¹ := inv_pos.2 hn
  rcases h with h | h
  · left; simp only [re_ofReal_mul]; positivity
  · right; simp only [im_ofReal_mul]; exact mul_ne_zero hinv.ne' h

end SmoothedOctagon

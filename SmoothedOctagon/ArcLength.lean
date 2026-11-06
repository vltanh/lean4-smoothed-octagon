module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Tactic

/-!
# Explicit Euclidean arclength reparametrization

For a regular `C¹` periodic plane curve, integrate its positive Euclidean speed and
construct the inverse of that integral as an order isomorphism of `ℝ`. The inverse is
`C¹`, has positive derivative, and transports one period to the curve's Euclidean
length over that period. Composition with the inverse gives Euclidean unit speed.

The Euclidean speed is written in coordinates: the norm instance on `Fin 2 → ℝ` is
not used to define length. Surjectivity and differentiability of the inverse are
proved from the stated regularity and periodicity assumptions, not assumed.

Status: source-level Lean draft; compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Filter
open scoped Topology

/-- Euclidean speed of a plane curve, independent of the norm instance on the Pi type. -/
noncomputable def euclideanSpeed (γ : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  √((deriv γ t 0) ^ 2 + (deriv γ t 1) ^ 2)

/-- A nonzero plane tangent has strictly positive Euclidean speed. -/
theorem euclideanSpeed_pos {γ : ℝ → Fin 2 → ℝ}
    (hreg : ∀ t, deriv γ t ≠ 0) (t : ℝ) : 0 < euclideanSpeed γ t := by
  unfold euclideanSpeed
  apply Real.sqrt_pos.2
  by_cases h0 : deriv γ t 0 = 0
  · have h1 : deriv γ t 1 ≠ 0 := by
      intro h1
      apply hreg t
      ext i
      fin_cases i <;> simp [h0, h1]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h1)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (sq_nonneg _)

/-- The square of the Euclidean speed is the sum of the squared tangent coordinates. -/
theorem euclideanSpeed_sq (γ : ℝ → Fin 2 → ℝ) (t : ℝ) :
    euclideanSpeed γ t ^ 2 = (deriv γ t 0) ^ 2 + (deriv γ t 1) ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- `C¹` regularity gives continuity of the Euclidean speed; nonvanishing is not needed here. -/
theorem continuous_euclideanSpeed {γ : ℝ → Fin 2 → ℝ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (euclideanSpeed γ) := by
  have hd : Continuous (deriv γ) := (contDiff_one_iff_deriv.mp hγ).2
  exact Real.continuous_sqrt.comp
    ((((continuous_apply (0 : Fin 2)).comp hd).pow 2).add
      (((continuous_apply (1 : Fin 2)).comp hd).pow 2))

/-- The speed has every period of the `C¹` curve. Differentiate the translated-curve
identity to obtain the corresponding period of its tangent. -/
theorem periodic_euclideanSpeed {γ : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hperiod : Function.Periodic γ T) :
    Function.Periodic (euclideanSpeed γ) T := by
  have hd : Differentiable ℝ γ := (contDiff_one_iff_deriv.mp hγ).1
  have hshift : γ ∘ (fun u : ℝ ↦ u + T) = γ := funext fun u ↦ hperiod u
  have hdperiod : Function.Periodic (deriv γ) T := by
    intro t
    have hcomp : HasDerivAt (γ ∘ (fun u : ℝ ↦ u + T)) (deriv γ (t + T)) t := by
      simpa only [one_smul] using
        (hd (t + T)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const T)
    rw [hshift] at hcomp
    exact hcomp.deriv.symm
  intro t
  simp only [euclideanSpeed, hdperiod t]

/-- The inverse of the integral of a continuous positive periodic function is a `C¹`
order isomorphism. The period in its domain is the positive integral over one period.
This constructs the inverse from surjectivity of the integral. -/
theorem exists_inverse_integral_reparam {v : ℝ → ℝ} {T : ℝ}
    (hvc : Continuous v) (hvpos : ∀ t, 0 < v t) (hT : 0 < T)
    (hvperiod : Function.Periodic v T) :
    0 < (∫ u in (0 : ℝ)..T, v u) ∧
      ∃ a : ℝ ≃o ℝ, a 0 = 0 ∧ ContDiff ℝ 1 (fun t ↦ a t) ∧
        (∀ t, HasDerivAt (fun u ↦ a u) (v (a t))⁻¹ t) ∧
        (∀ t, a (t + ∫ u in (0 : ℝ)..T, v u) = a t + T) := by
  classical
  let S : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t, v u
  have hSder : ∀ t, HasDerivAt S (v t) t := fun t ↦
    (hvc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hSmono : StrictMono S := strictMono_of_hasDerivAt_pos hSder hvpos
  have hScont : Continuous S :=
    continuous_iff_continuousAt.mpr fun t ↦ (hSder t).continuousAt
  have hSzero : S 0 = 0 := by simp [S]
  have hP : 0 < S T := by
    simpa only [hSzero] using hSmono hT
  have hint : ∀ a b : ℝ, IntervalIntegrable v volume a b :=
    fun a b ↦ hvc.intervalIntegrable a b
  have htop : Tendsto S atTop atTop :=
    hvperiod.tendsto_atTop_intervalIntegral_of_pos' (hint 0 T) hvpos hT
  have hbot : Tendsto S atBot atBot :=
    hvperiod.tendsto_atBot_intervalIntegral_of_pos' (hint 0 T) hvpos hT
  have hsurj : Function.Surjective S := hScont.surjective htop hbot
  choose r hr using hsurj
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse S hSmono r hr
  let a : ℝ ≃o ℝ := e.symm
  have hSa : ∀ t, S (a t) = t := fun t ↦ e.apply_symm_apply t
  have hac : Continuous (fun t ↦ a t) := a.continuous
  have had : ∀ t, HasDerivAt (fun u ↦ a u) (v (a t))⁻¹ t := by
    intro t
    exact HasDerivAt.of_local_left_inverse hac.continuousAt (hSder (a t))
      (hvpos (a t)).ne' (Filter.Eventually.of_forall hSa)
  have hadeq : deriv (fun u ↦ a u) = fun t ↦ (v (a t))⁻¹ :=
    funext fun t ↦ (had t).deriv
  have haC1 : ContDiff ℝ 1 (fun t ↦ a t) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t ↦ (had t).differentiableAt, ?_⟩
    rw [hadeq]
    exact (hvc.comp hac).inv₀ fun t ↦ (hvpos (a t)).ne'
  have hSperiod : ∀ t, S (t + T) = S t + S T := by
    intro t
    simpa only [S, zero_add] using hvperiod.intervalIntegral_add_eq_add 0 t hint
  refine ⟨hP, a, ?_, haC1, had, ?_⟩
  · apply hSmono.injective
    rw [hSa, hSzero]
  · intro t
    change a (t + S T) = a t + T
    apply hSmono.injective
    rw [hSa, hSperiod, hSa]

/-- Every regular `C¹` periodic plane curve admits an explicitly constructed increasing
`C¹` Euclidean arclength reparametrization fixing zero. The new positive period is
its Euclidean length over the given old period; no minimal-period hypothesis is needed. -/
theorem exists_unitSpeed_reparam {γ : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t, deriv γ t ≠ 0) (hT : 0 < T)
    (hperiod : Function.Periodic γ T) :
    ∃ P : ℝ, 0 < P ∧ ∃ a : ℝ ≃o ℝ,
      a 0 = 0 ∧ ContDiff ℝ 1 (fun t ↦ a t) ∧
      (∀ t, 0 < deriv (fun u ↦ a u) t) ∧
      (∀ t, a (t + P) = a t + T) ∧
      (∀ t, (deriv (γ ∘ a) t 0) ^ 2 + (deriv (γ ∘ a) t 1) ^ 2 = 1) := by
  obtain ⟨hP, a, ha0, haC1, had, haperiod⟩ :=
    exists_inverse_integral_reparam (continuous_euclideanSpeed hγ)
      (euclideanSpeed_pos hreg) hT (periodic_euclideanSpeed hγ hperiod)
  refine ⟨∫ u in (0 : ℝ)..T, euclideanSpeed γ u, hP, a, ha0, haC1, ?_, haperiod, ?_⟩
  · intro t
    rw [(had t).deriv]
    exact inv_pos.mpr (euclideanSpeed_pos hreg (a t))
  · intro t
    have hd : Differentiable ℝ γ := (contDiff_one_iff_deriv.mp hγ).1
    have hcomp : deriv (γ ∘ a) t =
        (euclideanSpeed γ (a t))⁻¹ • deriv γ (a t) :=
      ((hd (a t)).hasDerivAt.scomp t (had t)).deriv
    have hvne : euclideanSpeed γ (a t) ≠ 0 := (euclideanSpeed_pos hreg (a t)).ne'
    rw [hcomp]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      ((euclideanSpeed γ (a t))⁻¹ * deriv γ (a t) 0) ^ 2 +
          ((euclideanSpeed γ (a t))⁻¹ * deriv γ (a t) 1) ^ 2 =
          ((euclideanSpeed γ (a t))⁻¹) ^ 2 *
            ((deriv γ (a t) 0) ^ 2 + (deriv γ (a t) 1) ^ 2) := by ring
      _ = ((euclideanSpeed γ (a t))⁻¹) ^ 2 * euclideanSpeed γ (a t) ^ 2 := by
        rw [euclideanSpeed_sq]
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hvne, one_pow]

end SmoothedOctagon

module

public import SmoothedOctagon.Foundations.SupportNormal
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-!
# A regular positive radial parametrization of an actual worst disk

A continuous family of supporting covectors differentiates the gauge along the unit circle.
The proof squeezes scalar difference quotients between the two supporting covectors at their
endpoints. It does not differentiate the supporting covectors.

For a centrally symmetric convex disk with a unique support line at every boundary point,
`rein_bd K θ = (gauge K (rein_dir θ))⁻¹ • rein_dir θ` is therefore a regular positive `C¹`
parametrization. Its orientation is certified by the exact identity
`det2 (rein_bd K θ) (deriv (rein_bd K) θ) = 1 / (gauge K (rein_dir θ)) ^ 2`.

Upstream Lemma 2.2.5 supplies the unique-support hypothesis for every actual worst disk.
This closes the initial regular-parametrization hypothesis in upstream Lemma 2.4.2; arclength
reparametrization and the resulting Lipschitz derivatives are handled in `ArcLength` and
`BalancedReduction`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Filter Topology Real SmoothedPolygons

private lemma planeDot_slope (n : Fin 2 → ℝ) (u : ℝ → Fin 2 → ℝ) (x t : ℝ) :
    planeDot n (slope u x t) =
      (planeDot n (u t) - planeDot n (u x)) / (t - x) := by
  rw [slope_def_module, planeDot_smul_right, planeDot_sub_right, div_eq_inv_mul]

/-- A continuous family of supporting covectors differentiates its contact value along a
differentiable curve.

The two support inequalities bound `f t - f x` between `n x · (u t - u x)` and
`n t · (u t - u x)`. Dividing reverses the order on the left of `x`; taking the minimum and
maximum gives bounds valid on both sides, and both bounds have the same limit. -/
theorem hasDerivAt_of_continuous_supporting_family
    {u n : ℝ → Fin 2 → ℝ} {f : ℝ → ℝ} {x : ℝ} {u' : Fin 2 → ℝ}
    (hu : HasDerivAt u u' x) (hn : ContinuousAt n x)
    (hcontact : ∀ t, planeDot (n t) (u t) = f t)
    (hbelow : ∀ s t, planeDot (n s) (u t) ≤ f t) :
    HasDerivAt f (planeDot (n x) u') x := by
  apply hasDerivAt_iff_tendsto_slope.2
  let A : ℝ → ℝ := fun t ↦ planeDot (n x) (slope u x t)
  let B : ℝ → ℝ := fun t ↦ planeDot (n t) (slope u x t)
  have hdu := hu.tendsto_slope
  have hdu0 := (tendsto_pi_nhds.1 hdu) 0
  have hdu1 := (tendsto_pi_nhds.1 hdu) 1
  have hnt : Tendsto n (𝓝[≠] x) (𝓝 (n x)) :=
    (show Tendsto n (𝓝 x) (𝓝 (n x)) from hn).mono_left nhdsWithin_le_nhds
  have hn0 := (tendsto_pi_nhds.1 hnt) 0
  have hn1 := (tendsto_pi_nhds.1 hnt) 1
  have hA : Tendsto A (𝓝[≠] x) (𝓝 (planeDot (n x) u')) := by
    dsimp only [A, planeDot]
    exact (tendsto_const_nhds.mul hdu0).add (tendsto_const_nhds.mul hdu1)
  have hB : Tendsto B (𝓝[≠] x) (𝓝 (planeDot (n x) u')) := by
    dsimp only [B, planeDot]
    exact (hn0.mul hdu0).add (hn1.mul hdu1)
  have hbounds (t : ℝ) :
      min (A t) (B t) ≤ slope f x t ∧ slope f x t ≤ max (A t) (B t) := by
    have hlo : planeDot (n x) (u t) - planeDot (n x) (u x) ≤ f t - f x := by
      rw [hcontact x]
      linarith [hbelow x t]
    have hhi : f t - f x ≤ planeDot (n t) (u t) - planeDot (n t) (u x) := by
      rw [hcontact t]
      linarith [hbelow t x]
    dsimp only [A, B]
    simp only [planeDot_slope, slope_def_field]
    rcases le_total 0 (t - x) with ht | ht
    · have hl : (planeDot (n x) (u t) - planeDot (n x) (u x)) / (t - x) ≤
          (f t - f x) / (t - x) := by
        simpa only [div_eq_inv_mul] using
          mul_le_mul_of_nonneg_left hlo (inv_nonneg.2 ht)
      have hh : (f t - f x) / (t - x) ≤
          (planeDot (n t) (u t) - planeDot (n t) (u x)) / (t - x) := by
        simpa only [div_eq_inv_mul] using
          mul_le_mul_of_nonneg_left hhi (inv_nonneg.2 ht)
      exact ⟨(min_le_left _ _).trans hl, hh.trans (le_max_right _ _)⟩
    · have hl : (planeDot (n t) (u t) - planeDot (n t) (u x)) / (t - x) ≤
          (f t - f x) / (t - x) := by
        simpa only [div_eq_inv_mul] using
          mul_le_mul_of_nonpos_left hhi (inv_nonpos.2 ht)
      have hh : (f t - f x) / (t - x) ≤
          (planeDot (n x) (u t) - planeDot (n x) (u x)) / (t - x) := by
        simpa only [div_eq_inv_mul] using
          mul_le_mul_of_nonpos_left hlo (inv_nonpos.2 ht)
      exact ⟨(min_le_right _ _).trans hl, hh.trans (le_max_left _ _)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [min_self] using hA.min hB)
    (by simpa only [max_self] using hA.max hB)
    (fun t ↦ (hbounds t).1) (fun t ↦ (hbounds t).2)

/-- The derivative of the unit direction vector at polar angle `θ`. -/
noncomputable def radialDirectionDerivative (θ : ℝ) : Fin 2 → ℝ :=
  ![-sin θ, cos θ]

lemma hasDerivAt_rein_dir (θ : ℝ) :
    HasDerivAt rein_dir (radialDirectionDerivative θ) θ := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [rein_dir, radialDirectionDerivative] using Real.hasDerivAt_cos θ
  · simpa [rein_dir, radialDirectionDerivative] using Real.hasDerivAt_sin θ

lemma contDiff_rein_dir : ContDiff ℝ 1 rein_dir := by
  refine contDiff_pi.2 fun i ↦ ?_
  fin_cases i
  · simpa [rein_dir] using Real.contDiff_cos
  · simpa [rein_dir] using Real.contDiff_sin

lemma continuous_radialDirectionDerivative : Continuous radialDirectionDerivative := by
  unfold radialDirectionDerivative
  fun_prop

lemma det2_rein_dir_radialDirectionDerivative (θ : ℝ) :
    det2 (rein_dir θ) (radialDirectionDerivative θ) = 1 := by
  simp only [rein_dir, radialDirectionDerivative, det2,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

variable {K : Set (Fin 2 → ℝ)}

/-- Normalization at the radial boundary point determines the covector's value on the unit
direction: it is exactly the gauge in that direction. -/
lemma radial_support_contact (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ)) (θ : ℝ) :
    planeDot (n θ) (rein_dir θ) = gauge K (rein_dir θ) := by
  have h := (hsupport θ).1
  rw [rein_bd, planeDot_smul_right] at h
  have hg : gauge K (rein_dir θ) ≠ 0 := (rein_gauge_pos hK (rein_dir_ne_zero θ)).ne'
  have hm := congrArg (fun z : ℝ ↦ gauge K (rein_dir θ) * z) h
  simpa only [← mul_assoc, mul_inv_cancel₀ hg, one_mul, mul_one] using hm

/-- The angular gauge derivative uses the supporting covector, with no derivative of that
covector required. -/
lemma hasDerivAt_radialGauge_of_support (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hn : Continuous n) (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ))
    (hdom : ∀ θ y, planeDot (n θ) y ≤ gauge K y) (θ : ℝ) :
    HasDerivAt (fun t ↦ gauge K (rein_dir t))
      (planeDot (n θ) (radialDirectionDerivative θ)) θ :=
  hasDerivAt_of_continuous_supporting_family (hasDerivAt_rein_dir θ) hn.continuousAt
    (radial_support_contact hK hsupport) (fun s t ↦ hdom s (rein_dir t))

lemma radialGauge_contDiff_of_support (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hn : Continuous n) (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ))
    (hdom : ∀ θ y, planeDot (n θ) y ≤ gauge K y) :
    ContDiff ℝ 1 (fun θ ↦ gauge K (rein_dir θ)) := by
  have hd := hasDerivAt_radialGauge_of_support hK hn hsupport hdom
  refine contDiff_one_iff_deriv.2 ⟨fun θ ↦ (hd θ).differentiableAt, ?_⟩
  have hderiv : deriv (fun θ ↦ gauge K (rein_dir θ)) =
      fun θ ↦ planeDot (n θ) (radialDirectionDerivative θ) :=
    funext fun θ ↦ (hd θ).deriv
  rw [hderiv]
  unfold planeDot
  exact (((continuous_apply 0).comp hn).mul
      ((continuous_apply 0).comp continuous_radialDirectionDerivative)).add
    (((continuous_apply 1).comp hn).mul
      ((continuous_apply 1).comp continuous_radialDirectionDerivative))

lemma rein_bd_contDiff_of_support (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hn : Continuous n) (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ))
    (hdom : ∀ θ y, planeDot (n θ) y ≤ gauge K y) :
    ContDiff ℝ 1 (rein_bd K) :=
  ((radialGauge_contDiff_of_support hK hn hsupport hdom).inv
    (fun θ ↦ (rein_gauge_pos hK (rein_dir_ne_zero θ)).ne')).smul contDiff_rein_dir

lemma hasDerivAt_rein_bd_of_support (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hn : Continuous n) (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ))
    (hdom : ∀ θ y, planeDot (n θ) y ≤ gauge K y) (θ : ℝ) :
    HasDerivAt (rein_bd K)
      ((gauge K (rein_dir θ))⁻¹ • radialDirectionDerivative θ +
        (-planeDot (n θ) (radialDirectionDerivative θ) / (gauge K (rein_dir θ)) ^ 2) •
          rein_dir θ) θ :=
  ((hasDerivAt_radialGauge_of_support hK hn hsupport hdom θ).inv
    (rein_gauge_pos hK (rein_dir_ne_zero θ)).ne').smul (hasDerivAt_rein_dir θ)

/-- The radial curve's orientation depends only on its positive radius. The derivative of the
gauge contributes a radial vector, whose determinant with the boundary point vanishes. -/
lemma rein_bd_det2_deriv_of_support (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hn : Continuous n) (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ))
    (hdom : ∀ θ y, planeDot (n θ) y ≤ gauge K y) (θ : ℝ) :
    det2 (rein_bd K θ) (deriv (rein_bd K) θ) = 1 / (gauge K (rein_dir θ)) ^ 2 := by
  rw [(hasDerivAt_rein_bd_of_support hK hn hsupport hdom θ).deriv]
  simp only [rein_bd, rein_det2_add_right, rein_det2_smul_left, rein_det2_smul_right,
    det2_rein_dir_radialDirectionDerivative, rein_det2_self,
    mul_zero, add_zero, mul_one, one_div, pow_two, mul_inv_rev]

lemma rein_bd_isPositiveBoundaryParam_of_support (hK : IsCCSDisk K) {n : ℝ → Fin 2 → ℝ}
    (hn : Continuous n) (hsupport : ∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ))
    (hdom : ∀ θ y, planeDot (n θ) y ≤ gauge K y) :
    IsPositiveBoundaryParam K (rein_bd K) := by
  have hpos : ∀ θ, 0 < det2 (rein_bd K θ) (deriv (rein_bd K) θ) := by
    intro θ
    rw [rein_bd_det2_deriv_of_support hK hn hsupport hdom θ]
    exact one_div_pos.2 (sq_pos_of_pos (rein_gauge_pos hK (rein_dir_ne_zero θ)))
  refine ⟨rein_bd_contDiff_of_support hK hn hsupport hdom, ?_, ?_, hpos⟩
  · intro θ hzero
    have hp := hpos θ
    rw [hzero] at hp
    simp [det2] at hp
  · ext x
    constructor
    · rintro ⟨θ, rfl⟩
      exact rein_bd_mem_frontier hK θ
    · intro hx
      obtain ⟨θ, hθ⟩ := rein_frontier_eq_bd hK hx
      exact ⟨θ, hθ.symm⟩

/-- A centrally symmetric convex disk with unique supporting lines has a global regular
positive `C¹` radial parametrization. This theorem constructs the initial parametrization
needed by the boundary regularity lemmas. -/
theorem rein_bd_isPositiveBoundaryParam_of_unique_support (hK : IsCCSDisk K)
    (huniq : ∀ x ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ x ∈ ℓ) :
    IsPositiveBoundaryParam K (rein_bd K) := by
  obtain ⟨n, hn, hsupport, hdom⟩ :=
    exists_continuous_radial_support_of_unique_support hK huniq
  exact rein_bd_isPositiveBoundaryParam_of_support hK hn hsupport hdom

theorem rein_bd_det2_deriv_of_unique_support (hK : IsCCSDisk K)
    (huniq : ∀ x ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ x ∈ ℓ) (θ : ℝ) :
    det2 (rein_bd K θ) (deriv (rein_bd K) θ) = 1 / (gauge K (rein_dir θ)) ^ 2 := by
  obtain ⟨n, hn, hsupport, hdom⟩ :=
    exists_continuous_radial_support_of_unique_support hK huniq
  exact rein_bd_det2_deriv_of_support hK hn hsupport hdom θ

/-- Every actual worst disk supplies its initial regular positive boundary parametrization;
the parametrization is not an additional hypothesis. -/
theorem rein_bd_isPositiveBoundaryParam_of_isWorstDisk (hK : IsWorstDisk K) :
    IsPositiveBoundaryParam K (rein_bd K) := by
  have hG := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  exact rein_bd_isPositiveBoundaryParam_of_unique_support hK.1 hG.2.1

theorem rein_bd_det2_deriv_of_isWorstDisk (hK : IsWorstDisk K) (θ : ℝ) :
    det2 (rein_bd K θ) (deriv (rein_bd K) θ) = 1 / (gauge K (rein_dir θ)) ^ 2 := by
  have hG := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  exact rein_bd_det2_deriv_of_unique_support hK.1 hG.2.1 θ

end SmoothedOctagon

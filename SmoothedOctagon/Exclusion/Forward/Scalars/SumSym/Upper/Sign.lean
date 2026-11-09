module

public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Upper.Curvature

/-!
# The upper factor endpoint of the forward sum comparison

A fixed tangent controls the left factor interval. A reciprocal curvature
bound controls the short right chord, and monotonicity handles the lower ceiling.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real Polynomial Filter

local syntax "upper_shape_deriv" : tactic
macro_rules
| `(tactic| upper_shape_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> upper_shape_deriv
  | apply HasDerivAt.sub <;> upper_shape_deriv
  | apply HasDerivAt.pow <;> upper_shape_deriv
  | apply HasDerivAt.mul <;> upper_shape_deriv
  | apply HasDerivAt.div <;> first | upper_shape_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> upper_shape_deriv)

noncomputable def fwdSumGShapeFirst (a k : ℝ) : ℝ :=
  fwdPole0 fwdSumGQ1Poly k+2*a*fwdPole0 fwdSumGQ2Poly k+
    3*a^2*fwdPole0 fwdSumGQ3Poly k+4*a^3*fwdPole0 fwdSumGQ4Poly k+
    fwdPole0 fwdSumGAPoly k/(1-a)^2-2*fwdPole0 fwdSumGDPolePoly k/(1-a)^3
noncomputable def fwdSumGFirstA (a k : ℝ) : ℝ :=
  fwdPole1 fwdSumGQ1Poly k+2*a*fwdPole1 fwdSumGQ2Poly k+
    3*a^2*fwdPole1 fwdSumGQ3Poly k+4*a^3*fwdPole1 fwdSumGQ4Poly k+
    fwdPole1 fwdSumGAPoly k/(1-a)^2-2*fwdPole1 fwdSumGDPolePoly k/(1-a)^3

private theorem fse_Gmodel_a_hasDerivAt {a k : ℝ} (ha : a < 1/2) :
    HasDerivAt (fun x : ℝ => fwdSumGModel x k) (fwdSumGShapeFirst a k) a := by
  have hb : 0 < 1-a := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumGModel
    upper_shape_deriv
  · unfold fwdSumGShapeFirst
    norm_num [npowRec]
    field_simp
    ring

theorem fwdSumG_hasDerivAt_a {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    HasDerivAt (fun x : ℝ => fwdSumUpper x k (fwdSumLinearTop k)) (fwdSumGShapeFirst a k) a := by
  have heq : (fun x : ℝ => fwdSumUpper x k (fwdSumLinearTop k)) =ᶠ[nhds a]
      (fun x : ℝ => fwdSumGModel x k) := by
    filter_upwards [eventually_lt_nhds ha] with x hx
    exact fse_G_model hx hk
  exact (fse_Gmodel_a_hasDerivAt ha).congr_of_eventuallyEq heq

theorem fwdSumGFirst_hasDerivAt_a {a k : ℝ} (ha : a < 1/2) :
    HasDerivAt (fun x : ℝ => fwdSumGFirst x k) (fwdSumGFirstA a k) a := by
  have hb : 0 < 1-a := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumGFirst
    upper_shape_deriv
  · unfold fwdSumGFirstA
    norm_num [npowRec]
    field_simp
    ring

/-- These are the small fixed row weights displayed in the paper at k=1/6. -/
theorem fwdSumG_fixed_weights :
    (37/12:ℝ) < fwdPole0 fwdSumGAPoly (1/6) ∧
    0 < fwdPole0 fwdSumGQ4Poly (1/6) ∧
    -7 < 3*fwdPole0 fwdSumGQ3Poly (1/6) ∧
    -4 < 2*fwdPole0 fwdSumGQ2Poly (1/6) ∧
    -9/4 < fwdPole0 fwdSumGQ1Poly (1/6) ∧
    fwdPole1 fwdSumGAPoly (1/6) < 33/2 ∧
    4*fwdPole1 fwdSumGQ4Poly (1/6) < 72 ∧
    3*fwdPole1 fwdSumGQ3Poly (1/6) < -36 ∧
    2*fwdPole1 fwdSumGQ2Poly (1/6) < -37 ∧
    fwdPole1 fwdSumGQ1Poly (1/6) < -23/2 ∧
    fwdPole0 fwdSumGDPolePoly (1/6) = 3/8 ∧
    2*fwdPole1 fwdSumGDPolePoly (1/6) = 27/5 := by
  norm_num [fwdPole0,fwdPole1,fwdSumGAPoly,fwdSumSimplePoleCleared,
    fwdSumGQ1Poly,fwdSumGQ2Poly,fwdSumGQ3Poly,fwdSumGQ4Poly,fwdSumT1Prod,
    fwdSumT2Prod,fwdSumT3Prod,fwdSumTauPoly,fwdSumGDPolePoly,
    Polynomial.derivative_mul,Polynomial.derivative_pow]

noncomputable def fwdSumFixedShapeLower (a : ℝ) : ℝ :=
  -7*a^2-4*a-9/4+(37/12)/(1-a)^2-(3/4)/(1-a)^3

private theorem fse_fixed_shape_lower_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 ≤ fwdSumFixedShapeLower a := by
  have hb : 0 < 1-a := by linarith
  have hid : (1-a)^3*fwdSumFixedShapeLower a =
      (7/4)*(1/7-a)*(a+1/3)+a^3*(45/4-17*a+7*a^2) := by
    unfold fwdSumFixedShapeLower
    field_simp [ne_of_gt hb]
    ring
  have hfirst : 0 ≤ (7/4:ℝ)*(1/7-a)*(a+1/3) := by positivity
  have hsecond : 0 ≤ a^3*(45/4-17*a+7*a^2) :=
    mul_nonneg (pow_nonneg ha 3) (by nlinarith only [ha1,sq_nonneg a])
  have hp : 0 ≤ (1-a)^3*fwdSumFixedShapeLower a := by linarith only [hid,hfirst,hsecond]
  exact nonneg_of_mul_nonneg_right hp (pow_pos hb 3)

theorem fwdSumG_fixed_shape_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 < fwdSumGShapeFirst a (1/6) := by
  obtain ⟨hA,h4,h3,h2,h1,_,_,_,_,_,hD,_⟩ := fwdSumG_fixed_weights
  have hb : 0 < 1-a := by linarith
  have hq4 : 0 ≤ 4*a^3*fwdPole0 fwdSumGQ4Poly (1/6) := by positivity
  have hq3 := mul_le_mul_of_nonneg_right h3.le (sq_nonneg a)
  have hq2 := mul_le_mul_of_nonneg_right h2.le ha
  have hAdiv := div_le_div_of_nonneg_right hA.le (sq_nonneg (1-a))
  have hbase : fwdSumFixedShapeLower a < fwdSumGShapeFirst a (1/6) := by
    unfold fwdSumFixedShapeLower fwdSumGShapeFirst
    rw [hD]
    nlinarith only [hq4,hq3,hq2,h1,hAdiv]
  exact lt_of_le_of_lt (fse_fixed_shape_lower_nonneg ha ha1) hbase

noncomputable def fwdSumFixedReciprocal (a : ℝ) : ℝ :=
  33/(2*(1-a)^2)-27/(5*(1-a)^3)
noncomputable def fwdSumFixedReciprocalFirst (a : ℝ) : ℝ :=
  33/(1-a)^3-81/(5*(1-a)^4)

private theorem fse_fixed_reciprocal_deriv {a : ℝ} (ha : a < 1/2) :
    HasDerivAt fwdSumFixedReciprocal (fwdSumFixedReciprocalFirst a) a := by
  have hb : 0 < 1-a := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumFixedReciprocal
    upper_shape_deriv
  · unfold fwdSumFixedReciprocalFirst
    norm_num [npowRec]
    field_simp
    ring

private theorem fse_fixed_reciprocal_first_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumFixedReciprocalFirst a ≤ 27 := by
  have hb : 0 < 1-a := by linarith
  have hb3 : (6/7:ℝ)^3 ≤ (1-a)^3 := by gcongr; linarith only [ha1]
  have hgap : (84/5)/(1-a)^3-fwdSumFixedReciprocalFirst a = 81*a/(5*(1-a)^4) := by
    unfold fwdSumFixedReciprocalFirst
    field_simp [ne_of_gt hb]
    ring
  have hp : 0 ≤ 81*a/(5*(1-a)^4) := by positivity
  have hupper : (84/5:ℝ)/(1-a)^3 ≤ 27 := by
    apply (div_le_iff₀ (pow_pos hb 3)).mpr
    nlinarith only [hb3]
  linarith only [hgap,hp,hupper]

private theorem fse_fixed_reciprocal_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumFixedReciprocal a ≤ 111/10+27*a := by
  have hh := ff_le_of_deriv (f := fun x : ℝ => 27*x-fwdSumFixedReciprocal x)
    (f' := fun x : ℝ => 27-fwdSumFixedReciprocalFirst x) ha (fun x hx => ?_) (fun x hx => ?_)
  · have h0 : fwdSumFixedReciprocal 0 = 111/10 := by norm_num [fwdSumFixedReciprocal]
    simp only [h0,mul_zero] at hh
    linarith only [hh]
  · convert (((hasDerivAt_id x).const_mul 27).sub
      (fse_fixed_reciprocal_deriv (by linarith only [hx.2,ha1]))) using 1
    · rfl
    · ring
  · have hp := fse_fixed_reciprocal_first_le hx.1 (le_trans hx.2 ha1)
    linarith only [hp]

theorem fwdSumG_fixed_mixed_neg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumGFirstA a (1/6) < 0 := by
  obtain ⟨_,_,_,_,_,hA,h4,h3,h2,h1,_,hD⟩ := fwdSumG_fixed_weights
  have hb : 0 < 1-a := by linarith
  have hq4 := mul_le_mul_of_nonneg_right h4.le (pow_nonneg ha 3)
  have hq3 := mul_le_mul_of_nonneg_right h3.le (sq_nonneg a)
  have hq2 := mul_le_mul_of_nonneg_right h2.le ha
  have hAdiv := div_le_div_of_nonneg_right hA.le (sq_nonneg (1-a))
  have hbase : fwdSumGFirstA a (1/6) <
      72*a^3-36*a^2-37*a-23/2+fwdSumFixedReciprocal a := by
    unfold fwdSumGFirstA fwdSumFixedReciprocal
    rw [show 2*fwdPole1 fwdSumGDPolePoly (1/6)/(1-a)^3 = (27/5)/(1-a)^3 by rw [hD]]
    have hAform : (33/2:ℝ)/(1-a)^2 = 33/(2*(1-a)^2) := by field_simp [ne_of_gt hb]
    have hDform : (27/5:ℝ)/(1-a)^3 = 27/(5*(1-a)^3) := by field_simp [ne_of_gt hb]
    rw [hAform] at hAdiv
    rw [hDform]
    nlinarith only [hq4,hq3,hq2,h1,hAdiv]
  have hrec := fse_fixed_reciprocal_le ha ha1
  have hp : 0 ≥ a^2*(72*a-36) := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (by linarith only [ha1])
  nlinarith only [hbase,hrec,hp,ha]

noncomputable def fwdSumGLeftTangent (a : ℝ) : ℝ :=
  fwdSumUpper a (1/6) (fwdSumLinearTop (1/6))-(13/150)*fwdSumGFirst a (1/6)

private theorem fse_GLeftTangent_deriv {a : ℝ} (ha : a < 1/2) :
    HasDerivAt fwdSumGLeftTangent
      (fwdSumGShapeFirst a (1/6)-(13/150)*fwdSumGFirstA a (1/6)) a := by
  exact (fwdSumG_hasDerivAt_a ha (by norm_num)).sub
    ((fwdSumGFirst_hasDerivAt_a ha).const_mul (13/150))

theorem fwdSumG_fixed_endpoint :
    fwdSumUpper (1/7) (1/6) (fwdSumLinearTop (1/6)) < -1/900 ∧
      fwdSumGLeftTangent (1/7) < 0 := by
  rw [fwdSumUpper_cleared (by norm_num) (by norm_num)]
  norm_num [fwdSumGLeftTangent,fwdSumUpper,fwdSumR0,fwdSumR1,fwdSumAR,fwdSumB1,
    fwdSumN1,fwdSumNd,fwdSumFR,fwdSumPairedLogUpper,fwdSumGFirst,fwdPole1,
    fwdSumG0Poly,fwdSumClearedRow,fwdSumGAPoly,fwdSumSimplePoleCleared,
    fwdSumGQ1Poly,fwdSumGQ2Poly,fwdSumGQ3Poly,fwdSumGQ4Poly,fwdSumT1Prod,
    fwdSumT2Prod,fwdSumT3Prod,fwdSumTauPoly,fwdSumGDPolePoly,fwdSumLinearTop,
    Polynomial.derivative_mul,Polynomial.derivative_pow]

theorem fwdSumG_fixed_lt {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumUpper a (1/6) (fwdSumLinearTop (1/6)) < -1/900 ∧ fwdSumGLeftTangent a < 0 := by
  have hF := ff_le_of_deriv
    (f := fun x : ℝ => fwdSumUpper x (1/6) (fwdSumLinearTop (1/6)))
    (f' := fun x : ℝ => fwdSumGShapeFirst x (1/6)) ha1
    (fun x hx => fwdSumG_hasDerivAt_a (by linarith only [hx.2]) (by norm_num))
    (fun x hx => (fwdSumG_fixed_shape_pos (le_trans ha hx.1) hx.2).le)
  have hB := ff_le_of_deriv (f := fwdSumGLeftTangent)
    (f' := fun x : ℝ => fwdSumGShapeFirst x (1/6)-(13/150)*fwdSumGFirstA x (1/6)) ha1
    (fun x hx => fse_GLeftTangent_deriv (by linarith only [hx.2])) (fun x hx => ?_)
  · exact ⟨lt_of_le_of_lt hF fwdSumG_fixed_endpoint.1,lt_of_le_of_lt hB fwdSumG_fixed_endpoint.2⟩
  · have hp := fwdSumG_fixed_shape_pos (le_trans ha hx.1) hx.2
    have hn := fwdSumG_fixed_mixed_neg (le_trans ha hx.1) hx.2
    nlinarith only [hp,hn]

theorem fwdSumG_left_neg {a k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7)
    (hk : 2/25 ≤ k) (hk1 : k ≤ 1/6) :
    fwdSumUpper a k (fwdSumLinearTop k) < 0 := by
  have ht := fse_concave_tangent (fwdSumG_concaveOn ha ha1)
    (show (1/6:ℝ) ∈ Icc (2/25:ℝ) (1/5) by constructor <;> norm_num)
    (show k ∈ Icc (2/25:ℝ) (1/5) by constructor; exact hk; linarith only [hk1])
    (fwdSumG_hasDerivAt (by linarith only [ha1]) (by norm_num : (1/6:ℝ) < 1/2))
  obtain ⟨hF,hB⟩ := fwdSumG_fixed_lt ha ha1
  by_cases hs : 0 ≤ fwdSumGFirst a (1/6)
  · have hp := mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hk1)
    linarith only [ht,hF,hp]
  · have hp := mul_le_mul_of_nonpos_left
      (show (2/25:ℝ)-1/6 ≤ k-1/6 by linarith only [hk]) (lt_of_not_ge hs).le
    unfold fwdSumGLeftTangent at hB
    nlinarith only [ht,hB,hp]


/-- Actual Laurent residues, evaluated from the original row's displayed factors. -/
noncomputable def fwdSumLaurentF (a : ℝ) : ℝ :=
  let b := 1-a
  let p := 1+a
  let M : ℝ := 112/3
  let Ap := 1+2*a-(1+2*M)*a^2
  p^3/2*(M*a/b-1)+p*Ap/(3*b)
noncomputable def fwdSumLaurentERat (a : ℝ) : ℝ :=
  (1+a)/(1-a)^2*(119/240-3*a+(17/30)*a^2+a^3)
noncomputable def fwdSumLaurentEM (a : ℝ) : ℝ :=
  -a*(1+a)*((125/3)*(1+a)^2+(112/3)*(a+5))/(2*(1-a))
noncomputable def fwdSumLaurentEEll (a : ℝ) : ℝ :=
  let b := 1-a
  let p := 1+a
  let M : ℝ := 112/3
  let N : ℝ := 125/3
  let Ap := 1+2*a-(1+2*M)*a^2
  let Bp := -b+2*a*(M+N*a)
  ((5*p-2)*Ap+2*p*Bp)/(6*b)
noncomputable def fwdSumLaurentEJ (a : ℝ) : ℝ :=
  a^2*(1+a)*((112/3)*(1-a)+2)*(7+2*a)/(6*(1-a))
noncomputable def fwdSumLaurentE (a : ℝ) : ℝ :=
  fwdSumLaurentERat a+fwdSumLaurentEM a+fwdSumLaurentEEll a+fwdSumLaurentEJ a
noncomputable def fwdSumLaurentAlpha : ℝ := -2*fwdSumLaurentE (1/7)
noncomputable def fwdSumLaurentBeta : ℝ := 6*fwdSumLaurentF (1/7)
noncomputable def fwdSumLaurentKappa : ℝ :=
  fwdSumGSecond (1/7) 0+fwdSumLaurentAlpha-fwdSumLaurentBeta

/-- The deliberately coarse residue budget comes only from the original factored row. -/
theorem fwdSumLaurent_bounds :
    (21/2:ℝ) < fwdSumLaurentKappa ∧ fwdSumLaurentAlpha < 35 ∧
      (45/2:ℝ) < fwdSumLaurentBeta := by
  have hF : (15/4:ℝ) < fwdSumLaurentF (1/7) := by norm_num [fwdSumLaurentF]
  have hER : 0 < fwdSumLaurentERat (1/7) := by norm_num [fwdSumLaurentERat]
  have hEM : (-47/2:ℝ) < fwdSumLaurentEM (1/7) := by norm_num [fwdSumLaurentEM]
  have hEL : (44/9:ℝ) < fwdSumLaurentEEll (1/7) := by norm_num [fwdSumLaurentEEll]
  have hEJ : (10/9:ℝ) < fwdSumLaurentEJ (1/7) := by norm_num [fwdSumLaurentEJ]
  have hAlpha : fwdSumLaurentAlpha < 35 := by
    unfold fwdSumLaurentAlpha fwdSumLaurentE
    linarith only [hER,hEM,hEL,hEJ]
  have hBeta : (45/2:ℝ) < fwdSumLaurentBeta := by
    unfold fwdSumLaurentBeta
    linarith only [hF]
  refine ⟨?_,hAlpha,hBeta⟩
  norm_num [fwdSumLaurentKappa,fwdSumGSecond,fwdPole2,fwdSumLaurentAlpha,fwdSumLaurentBeta,
    fwdSumLaurentE,fwdSumLaurentERat,fwdSumLaurentEM,fwdSumLaurentEEll,fwdSumLaurentEJ,
    fwdSumLaurentF,fwdSumG0Poly,fwdSumClearedRow,fwdSumGAPoly,fwdSumSimplePoleCleared,
    fwdSumGQ1Poly,fwdSumGQ2Poly,fwdSumGQ3Poly,fwdSumGQ4Poly,fwdSumT1Prod,
    fwdSumT2Prod,fwdSumT3Prod,fwdSumTauPoly,fwdSumGDPolePoly,
    Polynomial.derivative_mul,Polynomial.derivative_pow]

/-- Exact Laurent identity for the actual upper-shape second derivative. -/
theorem fwdSumG_right_curvature_identity {k : ℝ} (hk : k ≠ 1) :
    fwdSumGSecond (1/7) k = -(625/63)*k+fwdSumLaurentKappa-
      fwdSumLaurentAlpha/(1-k)^3+fwdSumLaurentBeta/(1-k)^4 := by
  unfold fwdSumLaurentKappa fwdSumGSecond fwdPole2 fwdSumLaurentAlpha fwdSumLaurentBeta
    fwdSumLaurentE fwdSumLaurentERat fwdSumLaurentEM fwdSumLaurentEEll fwdSumLaurentEJ
    fwdSumLaurentF fwdSumG0Poly fwdSumClearedRow fwdSumGAPoly fwdSumSimplePoleCleared
    fwdSumGQ1Poly fwdSumGQ2Poly fwdSumGQ3Poly fwdSumGQ4Poly fwdSumT1Prod
    fwdSumT2Prod fwdSumT3Prod fwdSumTauPoly fwdSumGDPolePoly
  norm_num [Polynomial.derivative_mul,Polynomial.derivative_pow]
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring

noncomputable def fwdSumRightKernel (r : ℝ) : ℝ := (45/2-35*r)/r^4
noncomputable def fwdSumRightKernelFirst (r : ℝ) : ℝ := (105*r-90)/r^5

private theorem fse_right_kernel_deriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt fwdSumRightKernel (fwdSumRightKernelFirst r) r := by
  apply HasDerivAt.congr_deriv
  · unfold fwdSumRightKernel
    upper_shape_deriv
  · unfold fwdSumRightKernelFirst
    norm_num [npowRec]
    field_simp
    ring

private theorem fse_right_kernel_lower {r : ℝ} (hr : r ∈ Icc (4/5:ℝ) (5/6)) :
    fwdSumRightKernel (5/6) ≤ fwdSumRightKernel r := by
  have hh := ff_le_of_deriv (f := fun x : ℝ => -fwdSumRightKernel x)
    (f' := fun x : ℝ => -fwdSumRightKernelFirst x) hr.2
    (fun x hx => (fse_right_kernel_deriv (by linarith only [hx.1,hr.1])).neg) (fun x hx => ?_)
  · exact neg_le_neg_iff.mp hh
  · have hx0 : 0 < x := by linarith only [hx.1,hr.1]
    unfold fwdSumRightKernelFirst
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith only [hx.2]) (by positivity))

theorem fwdSumG_right_top_curvature_gt {k : ℝ} (hk : 1/6 ≤ k) (hk1 : k ≤ 1/5) :
    -6 < fwdSumGSecond (1/7) k := by
  have hr : 0 < 1-k := by linarith only [hk1]
  have hrbox : 1-k ∈ Icc (4/5:ℝ) (5/6) := by constructor <;> linarith
  obtain ⟨hK,hA,hB⟩ := fwdSumLaurent_bounds
  have hAdiv := div_lt_div_of_pos_right hA (pow_pos hr 3)
  have hBdiv := div_lt_div_of_pos_right hB (pow_pos hr 4)
  have hlinear : -(625/63:ℝ)*k > -2 := by linarith only [hk1]
  have hkernel := fse_right_kernel_lower hrbox
  have hid : fwdSumRightKernel (1-k) = (45/2)/(1-k)^4-35/(1-k)^3 := by
    unfold fwdSumRightKernel
    field_simp [ne_of_gt hr]
  have hconstant : -6 < -2+(21/2:ℝ)+fwdSumRightKernel (5/6) := by
    norm_num [fwdSumRightKernel]
  rw [fwdSumG_right_curvature_identity (by linarith only [hk1])]
  nlinarith only [hK,hAdiv,hBdiv,hlinear,hkernel,hid,hconstant]

theorem fwdSumG_right_curvature_gt {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 1/6 ≤ k) (hk1 : k ≤ 1/5) :
    -6 < fwdSumGSecond a k := by
  have hmono := ff_le_of_deriv (f := fun x : ℝ => -fwdSumGSecond x k)
    (f' := fun x : ℝ => -fwdSumGSecondA x k) ha1
    (fun x hx => (fwdSumGSecond_hasDerivAt_a (by linarith only [hx.2])).neg) (fun x hx => ?_)
  · exact lt_of_lt_of_le (fwdSumG_right_top_curvature_gt hk hk1) (neg_le_neg_iff.mp hmono)
  · exact (neg_pos.mpr (fwdSumGSecondA_neg (le_trans ha hx.1) hx.2
      (by linarith only [hk]) hk1)).le

noncomputable def fwdSumGRightAdjusted (a k : ℝ) : ℝ :=
  fwdSumUpper a k (fwdSumLinearTop k)+3*k^2-3*(1/6+1/5)*k+3*(1/6)*(1/5)
noncomputable def fwdSumGRightAdjustedFirst (a k : ℝ) : ℝ :=
  fwdSumGFirst a k+6*k-3*(1/6+1/5)

private theorem fse_right_adjusted_deriv {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    HasDerivAt (fwdSumGRightAdjusted a) (fwdSumGRightAdjustedFirst a k) k := by
  have hG := fwdSumG_hasDerivAt ha hk
  apply HasDerivAt.congr_deriv
  · unfold fwdSumGRightAdjusted
    upper_shape_deriv
  · unfold fwdSumGRightAdjustedFirst
    norm_num [npowRec]
    ring

private theorem fse_right_adjustedFirst_deriv {a k : ℝ} (hk : k ≠ 1) :
    HasDerivAt (fwdSumGRightAdjustedFirst a) (fwdSumGSecond a k+6) k := by
  have hG := fwdSumGFirst_hasDerivAt (a := a) hk
  apply HasDerivAt.congr_deriv
  · unfold fwdSumGRightAdjustedFirst
    upper_shape_deriv
  · norm_num [npowRec]

theorem fwdSumG_right_neg {a k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7)
    (hk : 1/6 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumUpper a k (fwdSumLinearTop k) < 0 := by
  have hc : ConvexOn ℝ (Icc (1/6:ℝ) (1/5)) (fwdSumGRightAdjusted a) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (1/6) (1/5))
      (f' := fwdSumGRightAdjustedFirst a) (f'' := fun k : ℝ => fwdSumGSecond a k+6)
    · intro x hx
      exact (fse_right_adjusted_deriv (by linarith only [ha1])
        (by linarith only [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      exact (fse_right_adjusted_deriv (by linarith only [ha1])
        (by have := (interior_subset hx).2; linarith)).hasDerivWithinAt
    · intro x hx
      exact (fse_right_adjustedFirst_deriv
        (by have := (interior_subset hx).2; linarith)).hasDerivWithinAt
    · intro x hx
      have hp := fwdSumG_right_curvature_gt ha ha1 (interior_subset hx).1 (interior_subset hx).2
      linarith only [hp]
  have hmax := fse_convex_le_max hc (show k ∈ Icc (1/6:ℝ) (1/5) from ⟨hk,hk1⟩)
  have hlo : fwdSumGRightAdjusted a (1/6) = fwdSumUpper a (1/6) (fwdSumLinearTop (1/6)) := by
    unfold fwdSumGRightAdjusted
    ring
  have hhi : fwdSumGRightAdjusted a (1/5) = fwdSumUpper a (1/5) (1/5) := by
    norm_num [fwdSumGRightAdjusted,fwdSumLinearTop]
    ring
  rw [hlo,hhi] at hmax
  have hbound : fwdSumGRightAdjusted a k < -1/900 :=
    lt_of_le_of_lt hmax (max_lt (fwdSumG_fixed_lt ha ha1).1 (fwdSumY_lt ha ha1))
  have hgap : 3*(k-1/6)*(1/5-k) ≤ (1/1200:ℝ) := by nlinarith only [sq_nonneg (k-11/60)]
  unfold fwdSumGRightAdjusted at hbound
  nlinarith only [hbound,hgap]

theorem fwdSumG_neg {a k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7)
    (hk : 2/25 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumUpper a k (fwdSumLinearTop k) < 0 := by
  rcases le_total k (1/6) with hleft | hright
  · exact fwdSumG_left_neg ha ha1 hk hleft
  · exact fwdSumG_right_neg ha ha1 hright hk1


noncomputable def fwdSumHA2 (a : ℝ) : ℝ := -(4*a^2+5*a+1)/(6*(1-a))
noncomputable def fwdSumHA1 (a : ℝ) : ℝ := -(10*a^3+15*a^2+10*a+5)/(6*(1-a))
noncomputable def fwdSumHF (a : ℝ) : ℝ := (1+a)^3/(6*(1-a))
/-- The simple pole is defined by the paper's positive difference, without a coefficient expansion. -/
noncomputable def fwdSumHE (a : ℝ) : ℝ :=
  (15/2)*fwdSumHF a+(1+a)/(240*(1-a)^2)*
    (43-220*a+12*a^2+20*a^3*(15-14*a-4*a^2))
noncomputable def fwdSumHFirst (a k : ℝ) : ℝ :=
  2*fwdSumHA2 a*k+fwdSumHA1 a+fwdSumHE a/(1-k)^2-2*fwdSumHF a/(1-k)^3
noncomputable def fwdSumHSecond (a k : ℝ) : ℝ :=
  2*fwdSumHA2 a+2*fwdSumHE a/(1-k)^3-6*fwdSumHF a/(1-k)^4
noncomputable def fwdSumHNum (a : ℝ) : Polynomial ℝ := fwdSumClearedRow (C a) X (C (2/5))

private theorem fse_H_derivative_identity {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    fwdPole1 (fwdSumHNum a) k/(1-a)^2 = fwdSumHFirst a k := by
  unfold fwdPole1 fwdSumHNum fwdSumClearedRow fwdSumHFirst fwdSumHA2 fwdSumHA1 fwdSumHE fwdSumHF
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

theorem fwdSumH_hasDerivAt {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    HasDerivAt (fun v : ℝ => fwdSumUpper a v (2/5)) (fwdSumHFirst a k) k := by
  have heq : (fun v : ℝ => fwdSumUpper a v (2/5)) =ᶠ[nhds k]
      (fun v : ℝ => fwdPole0 (fwdSumHNum a) v/(1-a)^2) := by
    filter_upwards [eventually_lt_nhds hk] with v hv
    rw [fwdSumUpper_cleared ha hv]
    unfold fwdPole0 fwdSumHNum fwdSumClearedRow
    simp
    rw [div_div]
    congr 1
    ring
  have hh := ((fwdPole0_hasDerivAt (fwdSumHNum a) (by linarith : k ≠ 1)).div_const
    ((1-a)^2)).congr_of_eventuallyEq heq
  exact hh.congr_deriv (fse_H_derivative_identity ha hk)

theorem fwdSumHFirst_hasDerivAt {a k : ℝ} (hk : k < 1/2) :
    HasDerivAt (fwdSumHFirst a) (fwdSumHSecond a k) k := by
  have hr : 0 < 1-k := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumHFirst
    upper_shape_deriv
  · unfold fwdSumHSecond
    norm_num [npowRec]
    field_simp
    ring

theorem fwdSumHE_gt {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    (15/2)*fwdSumHF a < fwdSumHE a := by
  have hb : 0 < 1-a := by linarith
  have hp : 0 < 1+a := by linarith
  have hsq : a^2 ≤ (1/7:ℝ)^2 := by gcongr
  have hbracket : 0 < 15-14*a-4*a^2 := by nlinarith only [ha1,hsq]
  have hprod : 0 ≤ 20*a^3*(15-14*a-4*a^2) := mul_nonneg (by positivity) hbracket.le
  have hsum : 0 < 43-220*a+12*a^2+20*a^3*(15-14*a-4*a^2) := by
    nlinarith only [ha1,sq_nonneg a,hprod]
  have hgain : 0 < (1+a)/(240*(1-a)^2)*
      (43-220*a+12*a^2+20*a^3*(15-14*a-4*a^2)) := mul_pos (div_pos hp (by positivity)) hsum
  unfold fwdSumHE
  linarith only [hgain]

private theorem fse_HF_ge {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    (1/6:ℝ) ≤ fwdSumHF a := by
  have hb : 0 < 1-a := by linarith
  unfold fwdSumHF
  apply (le_div_iff₀ (by positivity : 0 < 6*(1-a))).mpr
  nlinarith only [ha,sq_nonneg a,pow_nonneg ha 3]
private theorem fse_HA2_ge {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    (-44/63:ℝ) ≤ 2*fwdSumHA2 a := by
  have hb : 0 < 1-a := by linarith
  have hsq : a^2 ≤ (1/7:ℝ)^2 := by gcongr
  unfold fwdSumHA2
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 6*(1-a))).mpr
  nlinarith only [ha1,hsq]

theorem fwdSumHSecond_pos {a k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7)
    (hk : 0 ≤ k) (hk1 : k ≤ 2/25) : 0 < fwdSumHSecond a k := by
  have hr : 0 < 1-k := by linarith
  have hr1 : 1-k ≤ 1 := by linarith only [hk]
  have hr4 : (1-k)^4 ≤ 1 := pow_le_one₀ hr.le hr1
  have hF := fse_HF_ge ha ha1
  have hA := fse_HA2_ge ha ha1
  have hE := fwdSumHE_gt ha ha1
  have hid : fwdSumHSecond a k-
      (2*fwdSumHA2 a+(15*(1-k)-6)*fwdSumHF a/(1-k)^4) =
      2*(fwdSumHE a-(15/2)*fwdSumHF a)/(1-k)^3 := by
    unfold fwdSumHSecond
    field_simp [ne_of_gt hr]
    ring
  have hgain : 0 < 2*(fwdSumHE a-(15/2)*fwdSumHF a)/(1-k)^3 := by
    apply div_pos
    · linarith only [hE]
    · positivity
  have hcoef : (39/5:ℝ) ≤ 15*(1-k)-6 := by linarith only [hk1]
  have hprod := mul_le_mul hcoef hF (by norm_num : (0:ℝ) ≤ 1/6)
    (by linarith only [hcoef] : (0:ℝ) ≤ 15*(1-k)-6)
  have hlower : (39/5:ℝ)*(1/6) ≤ (15*(1-k)-6)*fwdSumHF a/(1-k)^4 := by
    apply (le_div_iff₀ (pow_pos hr 4)).mpr
    nlinarith only [hprod,hr4]
  linarith only [hid,hgain,hlower,hA]

theorem fwdSumHFirst_zero_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 < fwdSumHFirst a 0 := by
  have hb : 0 < 1-a := by linarith
  have hE := fwdSumHE_gt ha ha1
  have hid : fwdSumHA1 a+(11/2)*fwdSumHF a =
      (1+13*a+3*a^2-9*a^3)/(12*(1-a)) := by
    unfold fwdSumHA1 fwdSumHF
    field_simp [ne_of_gt hb]
    ring
  have hsq : a^2 ≤ (1/7:ℝ)^2 := by gcongr
  have hprod : 0 ≤ a*(13-9*a^2) := mul_nonneg ha (by nlinarith only [hsq])
  have hpos : 0 < (1+13*a+3*a^2-9*a^3)/(12*(1-a)) := by
    apply div_pos
    · nlinarith only [hprod,sq_nonneg a]
    · positivity
  unfold fwdSumHFirst
  norm_num only [mul_zero,sub_zero,one_pow,div_one]
  linarith only [hE,hid,hpos]

theorem fwdSumHFirst_pos {a k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7)
    (hk : 0 ≤ k) (hk1 : k ≤ 2/25) : 0 < fwdSumHFirst a k := by
  have hh := ff_le_of_deriv (f := fwdSumHFirst a) (f' := fwdSumHSecond a) hk
    (fun x hx => fwdSumHFirst_hasDerivAt (by linarith only [hx.2,hk1]))
    (fun x hx => (fwdSumHSecond_pos ha ha1 hx.1 (le_trans hx.2 hk1)).le)
  exact lt_of_lt_of_le (fwdSumHFirst_zero_pos ha ha1) hh

theorem fwdSumH_neg {a k : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7)
    (hk : 0 ≤ k) (hk1 : k ≤ 2/25) : fwdSumUpper a k (2/5) < 0 := by
  have hh := ff_le_of_deriv (f := fun x : ℝ => fwdSumUpper a x (2/5))
    (f' := fwdSumHFirst a) hk1
    (fun x hx => fwdSumH_hasDerivAt (by linarith only [ha1]) (by linarith only [hx.2]))
    (fun x hx => (fwdSumHFirst_pos ha ha1 (le_trans hk hx.1) hx.2).le)
  have hG := fwdSumG_neg ha ha1 (le_refl (2/25:ℝ)) (by norm_num)
  norm_num [fwdSumLinearTop] at hG
  exact lt_of_le_of_lt hh hG

/-- Complete upper factor endpoint, with its two ceilings split exactly at k=2/25. -/
theorem fwdSum_upper_endpoint_neg {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumUpper a k (min (2/5) (fwdSumLinearTop k)) < 0 := by
  rcases le_total k (2/25) with hlow | hhigh
  · have hT : (2/5:ℝ) ≤ fwdSumLinearTop k := by unfold fwdSumLinearTop; linarith only [hlow]
    rw [min_eq_left hT]
    exact fwdSumH_neg ha ha1 hk hlow
  · have hT : fwdSumLinearTop k ≤ (2/5:ℝ) := by unfold fwdSumLinearTop; linarith only [hhigh]
    rw [min_eq_right hT]
    exact fwdSumG_neg ha ha1 hhigh hk1

/-- The complete original symmetric sum residual sign, with the paper's 1/32 threshold. -/
theorem fwdSumResidual32_original_neg {U z h : ℝ}
    (hz : 1 ≤ z) (hz4 : z ≤ 4/3) (hbud : 1+6*z/5 ≤ U) (hU3 : U < 3)
    (hfloor : (1+z)^2/(z^2+U) ≤ h)
    (hcap : h ≤ (1+z)*(5*U-2-3*z)/(3*(z^2+U))) :
    fwdSumResidual32 U z h < 0 := by
  obtain ⟨ha,ha1,hk,_,hkbudget,_,_⟩ := fwdSum_physical_coordinates hz hz4 hbud hU3
  have hk1 : (2*z+1-U)/(1+z)^2 ≤ (1/5:ℝ) := by
    nlinarith only [hkbudget,sq_nonneg ((z-1)/(z+1))]
  exact fwdSumResidual32_original_neg_of_upper_endpoints hz hz4 hbud hU3 hfloor hcap
    (fwdSum_lower_endpoint_neg ha ha1 hk.le hk1)
    (fwdSum_upper_endpoint_neg ha ha1 hk.le hk1)

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Forward.Casimir.Kernels

/-!
# Curvature in the forward Casimir comparison

The base curve has positive curvature. The retained logarithmic correction
preserves it, with a quantitative bound near the natural midpoint.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set
noncomputable def fcBaseD : ℝ := 75/32-(25/32)*(361/192)
noncomputable def fcBaseF : ℝ := (361/192)^2-75/32
noncomputable def fcBaseCurve (U : ℝ) : ℝ := fcScale U*(75/32-(fcBranchM0 U)^2)
noncomputable def fcBaseSlope (U : ℝ) : ℝ :=
  (-(19/192:ℝ)^2*U+(19/192)*(25/32)-fcBaseD/U^2+fcBaseF/U^3)/8
noncomputable def fcBaseCurvature (U : ℝ) : ℝ :=
  (-(19/192:ℝ)^2+2*fcBaseD/U^3-3*fcBaseF/U^4)/8
noncomputable def fcBaseThird (U : ℝ) : ℝ := 3*(2*fcBaseF-fcBaseD*U)/(4*U^5)

/-- The paper's natural three-term normalization of the original base pairing. -/
theorem fc_basePairing_resolvent {U : ℝ} (hU : 0 < U) :
    (1+U)*fcBranchM0 U/U=-(19/192:ℝ)*U+25/32+(361/192)/U := by
  have hK : 1+U ≠ 0 := by linarith only [hU]
  unfold fcBranchM0 ff_e0
  field_simp [hU.ne',hK]
  ring

theorem fc_baseCurve_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcBaseCurve (fcBaseSlope U) U := by
  have h := (fc_scale_hasDerivAt hU).mul
    (((fc_branchM0_hasDerivAt hU).pow 2).const_sub (75/32:ℝ))
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply]
    unfold fcBaseSlope fcBaseD fcBaseF fcScale fcScale' fcBranchM0 fcBranchM0' ff_e0
    ring_nf
    have hK : 1+U ≠ 0 := by linarith only [hU]
    field_simp [hU.ne',hK]
    ring

theorem fc_baseSlope_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcBaseSlope (fcBaseCurvature U) U := by
  have h2 := (hasDerivAt_pow 2 U).inv (pow_ne_zero 2 hU.ne')
  have h3 := (hasDerivAt_pow 3 U).inv (pow_ne_zero 3 hU.ne')
  have h := (((((hasDerivAt_id U).const_mul (-(19/192:ℝ)^2)).add_const
    ((19/192)*(25/32))).sub (h2.const_mul fcBaseD)).add (h3.const_mul fcBaseF)).div_const 8
  convert h using 1
  · ext x; simp [fcBaseSlope,div_eq_mul_inv]
  · unfold fcBaseCurvature
    field_simp [hU.ne']
    ring

theorem fc_baseCurvature_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcBaseCurvature (fcBaseThird U) U := by
  have h3 := (hasDerivAt_pow 3 U).inv (pow_ne_zero 3 hU.ne')
  have h4 := (hasDerivAt_pow 4 U).inv (pow_ne_zero 4 hU.ne')
  have h := (((h3.const_mul (2*fcBaseD)).const_add (-(19/192:ℝ)^2)).sub
    (h4.const_mul (3*fcBaseF))).div_const 8
  convert h using 1
  · ext x; simp [fcBaseCurvature,div_eq_mul_inv]
  · unfold fcBaseThird
    field_simp [hU.ne']
    ring

theorem fc_baseThird_pos {U : ℝ} (hU : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    0 < fcBaseThird U := by
  have hU0 : 0 < U := by linarith only [hU]
  have hD : 0 < fcBaseD := by norm_num [fcBaseD]
  have hgap : fcBaseD*(13/5) < 2*fcBaseF := by norm_num [fcBaseD,fcBaseF]
  have hmul := mul_le_mul_of_nonneg_left hhi hD.le
  unfold fcBaseThird
  exact div_pos (mul_pos (by norm_num) (by linarith only [hgap,hmul])) (by positivity)

theorem fc_baseCurvature_monotone : MonotoneOn fcBaseCurvature (Icc (11/5) (13/5)) := by
  apply ff_monotoneOn_Icc (f' := fcBaseThird)
  · intro U hU; exact fc_baseCurvature_hasDerivAt (by linarith only [hU.1])
  · intro U hU; exact (fc_baseThird_pos hU.1 hU.2).le

theorem fc_baseCurvature_pos {U : ℝ} (hU : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    0 < fcBaseCurvature U := by
  have hm := fc_baseCurvature_monotone (show (11/5:ℝ) ∈ Icc (11/5) (13/5) by norm_num) ⟨hU,hhi⟩ hU
  have he : 0 < fcBaseCurvature (11/5) := by norm_num [fcBaseCurvature,fcBaseD,fcBaseF]
  exact he.trans_le hm

theorem fc_baseCurvature_near {U : ℝ} (hU : 5/2 ≤ U) (hhi : U ≤ 13/5) :
    (1/768:ℝ) < fcBaseCurvature U := by
  have hm := fc_baseCurvature_monotone (show (5/2:ℝ) ∈ Icc (11/5) (13/5) by norm_num)
    ⟨by linarith only [hU],hhi⟩ hU
  have he : (1/768:ℝ) < fcBaseCurvature (5/2) := by norm_num [fcBaseCurvature,fcBaseD,fcBaseF]
  exact he.trans_le hm

end SmoothedOctagon

namespace SmoothedOctagon

/-- The potentially negative part of the second derivative of the positive
logarithmic correction. The hypotheses are the paper's intrinsic kernel bounds. -/
theorem fc_correction_core_nonneg {B Bp M M0p Lp Lpp d : ℝ}
    (hBlo : (7/60:ℝ) ≤ B) (hBhi : B ≤ 2/15)
    (hBplo : -(1/24:ℝ) ≤ Bp) (hM0plo : -(1/5:ℝ) ≤ M0p)
    (hMlo : (8/9:ℝ) ≤ M) (hMhi : M ≤ 1)
    (hLp0 : 0 ≤ Lp) (hLp1 : Lp ≤ 1/100) (hLpp : 0 ≤ Lpp)
    (hd : d ≤ 2/5) (haccum : Lp ≤ d*Lpp) :
    0 ≤ 2*B*M*Lpp-2*B*Lp^2+4*(B*M0p+Bp*M)*Lp := by
  have hB0 : 0 ≤ B := by linarith only [hBlo]
  have hM0 : 0 ≤ M := by linarith only [hMlo]
  have hprod : (7/60:ℝ)*(8/9) ≤ B*M :=
    mul_le_mul hBlo hMlo (by norm_num) hB0
  have hsmall1 := mul_nonneg hB0 (by linarith only [hM0plo] : 0 ≤ M0p+1/5)
  have hsmall2 := mul_nonneg (by linarith only [hBplo] : 0 ≤ Bp+1/24) hM0
  have hsum : -((2/15:ℝ)*(1/5)+1/24) ≤ B*M0p+Bp*M := by
    nlinarith only [hsmall1,hsmall2,hBhi,hMhi]
  have hLp : Lp ≤ (2/5)*Lpp := haccum.trans (mul_le_mul_of_nonneg_right hd hLpp)
  have hcross := mul_le_mul_of_nonneg_right hsum hLp0
  have hcross' : -4*((2/15:ℝ)*(1/5)+1/24)*(2/5)*Lpp ≤ 4*(B*M0p+Bp*M)*Lp := by
    nlinarith only [hcross,hLp]
  have hsq := mul_le_mul_of_nonneg_right hLp1 hLp0
  have hsq' : Lp^2 ≤ (1/100:ℝ)*(2/5)*Lpp := by nlinarith only [hsq,hLp]
  have hbSq := mul_le_mul_of_nonneg_left hsq' hB0
  have hcap := mul_le_mul_of_nonneg_right hBhi (by positivity : 0 ≤ (1/100:ℝ)*(2/5)*Lpp)
  have hnegative : -2*(2/15:ℝ)*(1/100)*(2/5)*Lpp ≤ -2*B*Lp^2 := by
    nlinarith only [hbSq,hcap]
  have hpositive := mul_le_mul_of_nonneg_right hprod hLpp
  have hgap : (0:ℝ) < 2*(7/60)*(8/9)-4*((2/15)*(1/5)+1/24)*(2/5)-2*(2/15)*(1/100)*(2/5) := by norm_num
  have hmargin := mul_nonneg hgap.le hLpp
  nlinarith only [hcross',hnegative,hpositive,hmargin]

/-- The same original second derivative has the quantitative curvature
needed near the natural midpoint U=5/2. -/
theorem fc_correction_quantitative {B Bp M M0p Lp Lpp Base Pos : ℝ}
    (hBlo : (7/60:ℝ) ≤ B) (hBhi : B ≤ 1/8)
    (hBplo : -(1/32:ℝ) ≤ Bp) (hM0plo : -(3/16:ℝ) ≤ M0p)
    (hMlo : (8/9:ℝ) ≤ M) (hMhi : M ≤ 1)
    (hLp0 : 0 ≤ Lp) (hLp1 : Lp ≤ 1/100) (hLpp : (3/100:ℝ) ≤ Lpp)
    (hBase : (1/768:ℝ) ≤ Base) (hPos : 0 ≤ Pos) :
    (1/192:ℝ) < Base+2*B*M*Lpp-2*B*Lp^2+4*(B*M0p+Bp*M)*Lp+Pos := by
  have hB0 : 0 ≤ B := by linarith only [hBlo]
  have hM0 : 0 ≤ M := by linarith only [hMlo]
  have hprod : (7/60:ℝ)*(8/9) ≤ B*M :=
    mul_le_mul hBlo hMlo (by norm_num) hB0
  have hpositive := mul_le_mul hprod hLpp (by norm_num) (mul_nonneg hB0 hM0)
  have hsmall1 := mul_nonneg hB0 (by linarith only [hM0plo] : 0 ≤ M0p+3/16)
  have hsmall2 := mul_nonneg (by linarith only [hBplo] : 0 ≤ Bp+1/32) hM0
  have hsum : -((1/8:ℝ)*(3/16)+1/32) ≤ B*M0p+Bp*M := by
    nlinarith only [hsmall1,hsmall2,hBhi,hMhi]
  have hcross := mul_le_mul_of_nonneg_right hsum hLp0
  have hcross' : -4*((1/8:ℝ)*(3/16)+1/32)*(1/100) ≤ 4*(B*M0p+Bp*M)*Lp := by
    nlinarith only [hcross,hLp1]
  have hsq : Lp^2 ≤ (1/100:ℝ)^2 := (sq_le_sq₀ hLp0 (by norm_num)).2 hLp1
  have hbSq := mul_le_mul_of_nonneg_left hsq hB0
  have hcap := mul_le_mul_of_nonneg_right hBhi (by norm_num : 0 ≤ (1/100:ℝ)^2)
  have hnegative : -2*(1/8:ℝ)*(1/100)^2 ≤ -2*B*Lp^2 := by
    nlinarith only [hbSq,hcap]
  have hgap : (1/192:ℝ) < 1/768+2*(7/60)*(8/9)*(3/100)-4*((1/8)*(3/16)+1/32)*(1/100)-2*(1/8)*(1/100)^2 := by norm_num
  nlinarith only [hBase,hPos,hpositive,hcross',hnegative,hgap]

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

/-- Integrating a second-derivative floor twice on a closed interval.
The zero-width interval is included without division by its width. -/
theorem fc_second_order_lower {f f1 f2 : ℝ → ℝ} {v x k : ℝ} (hvx : v ≤ x)
    (hd : ∀ t ∈ Icc v x, HasDerivAt f (f1 t) t)
    (hd1 : ∀ t ∈ Icc v x, HasDerivAt f1 (f2 t) t)
    (hfloor : ∀ t ∈ Icc v x, k ≤ f2 t) :
    f v+f1 v*(x-v)+(k/2)*(x-v)^2 ≤ f x := by
  have hfirst : ∀ t ∈ Icc v x, f1 v+k*(t-v) ≤ f1 t := by
    intro t ht
    have h := ff_le_of_deriv ht.1
      (f := fun s => f1 s-k*(s-v)) (f' := fun s => f2 s-k)
      (fun s hs => by
        have hds := (hd1 s ⟨hs.1,hs.2.trans ht.2⟩).sub
          (((hasDerivAt_id s).sub_const v).const_mul k)
        convert hds using 1
        · rfl
        · ring)
      (fun s hs => by have hh := hfloor s ⟨hs.1,hs.2.trans ht.2⟩; linarith only [hh])
    simp only [sub_self,mul_zero,sub_zero] at h
    linarith only [h]
  have h := ff_le_of_deriv hvx
    (f := fun s => f s-f1 v*(s-v)-(k/2)*(s-v)^2)
    (f' := fun s => f1 s-f1 v-k*(s-v))
    (fun s hs => by
      have hds := ((hd s hs).sub (((hasDerivAt_id s).sub_const v).const_mul (f1 v))).sub
        ((((hasDerivAt_id s).sub_const v).pow 2).const_mul (k/2))
      convert hds using 1
      · rfl
      · simp only [id_eq]
        ring)
    (fun s hs => by have hh := hfirst s hs; linarith only [hh])
  simp only [sub_self,mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero] at h
  linarith only [h]

/-- The natural completed square after the curvature1/192 estimate. -/
theorem fc_midpoint_square (value slope displacement : ℝ) :
    value-96*slope^2 ≤ value+slope*displacement+displacement^2/384 := by
  nlinarith only [sq_nonneg (displacement+192*slope)]

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set Filter
open scoped Topology

theorem fc_baseSlope_eq_raw {U : ℝ} (hU : 0 < U) :
    fcBaseSlope U=fcScale' U*(75/32-(fcBranchM0 U)^2)-2*fcScale U*fcBranchM0 U*fcBranchM0' U := by
  have h := (fc_scale_hasDerivAt hU).mul (((fc_branchM0_hasDerivAt hU).pow 2).const_sub (75/32:ℝ))
  have hraw : HasDerivAt fcBaseCurve
      (fcScale' U*(75/32-(fcBranchM0 U)^2)-2*fcScale U*fcBranchM0 U*fcBranchM0' U) U := by
    convert h using 1
    · rfl
    · simp only [Pi.pow_apply]; ring
  exact (fc_baseCurve_hasDerivAt hU).unique hraw

/-- Derivative uniqueness links the natural resolvent curvature with the
original product-rule second derivative. -/
theorem fc_baseCurvature_eq_raw {U : ℝ} (hU : 0 < U) :
    fcBaseCurvature U=fcScale'' U*(75/32-(fcBranchM0 U)^2)
      -4*fcScale' U*fcBranchM0 U*fcBranchM0' U
      -2*fcScale U*((fcBranchM0' U)^2+fcBranchM0 U*fcBranchM0'' U) := by
  have hB := fc_scale_hasDerivAt hU
  have hBp := fc_scale'_hasDerivAt hU
  have hM := fc_branchM0_hasDerivAt hU
  have hMp := fc_branchM0'_hasDerivAt hU
  have h := (hBp.mul ((hM.pow 2).const_sub (75/32:ℝ))).sub
    ((((hB.const_mul 2).mul hM).mul hMp))
  have hr : HasDerivAt
      (fun x => fcScale' x*(75/32-(fcBranchM0 x)^2)-2*fcScale x*fcBranchM0 x*fcBranchM0' x)
      (fcScale'' U*(75/32-(fcBranchM0 U)^2)-4*fcScale' U*fcBranchM0 U*fcBranchM0' U
        -2*fcScale U*((fcBranchM0' U)^2+fcBranchM0 U*fcBranchM0'' U)) U := by
    convert h using 1
    simp only [Pi.pow_apply,Pi.mul_apply]
    ring
  have heq : fcBaseSlope =ᶠ[𝓝 U]
      (fun x => fcScale' x*(75/32-(fcBranchM0 x)^2)-2*fcScale x*fcBranchM0 x*fcBranchM0' x) := by
    filter_upwards [Ioi_mem_nhds hU] with x hx
    exact fc_baseSlope_eq_raw hx
  exact (fc_baseSlope_hasDerivAt hU).unique (hr.congr_of_eventuallyEq heq)


end SmoothedOctagon

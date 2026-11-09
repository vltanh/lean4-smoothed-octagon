module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# S6: the genuine reciprocal-variance norm floor
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

/-- The reciprocal-variance norm floor. -/
noncomputable def s6VarianceFloor (R d : ℝ) : ℝ :=
  3/4+(1+R)*R^3/(6*(2*R+(1+R)*d))*
    (1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4))
noncomputable def s6MomentPlus (R : ℝ) : ℝ := ∫ t in (0:ℝ)..R, t^2/(1+t)^2
noncomputable def s6MomentMinus (q : ℝ) : ℝ := ∫ t in (0:ℝ)..q, t^2/(1-t)^2
noncomputable def s6VarianceTangent (R t : ℝ) : ℝ :=
  t^2/(1+3*R/4)^2-2*t^2*(t-3*R/4)/(1+3*R/4)^3+
    3*t^2*(t-3*R/4)^2/(1+R)^4

private theorem s6_recip_cont {R : ℝ} (_hR : 0 ≤ R) :
    ContinuousOn (fun t : ℝ => t^2/(1+t)^2) (Icc 0 R) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (by linarith only [ht.1] : 0 < 1+t))

/-- The adjusted reciprocal tangent has the original positive square remainder. -/
theorem s6_variance_tangent_le {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) (htR : t ≤ R) :
    s6VarianceTangent R t ≤ t^2/(1+t)^2 := by
  let m := 3*R/4
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hmR : m < R := by dsimp [m]; linarith only [hR]
  have hp : 0 < 1+m := by positivity
  have ht1 : 0 < 1+t := by positivity
  have hR1 : 0 < 1+R := by positivity
  have hm2 : (1+m)^2 ≤ (1+R)^2 := by nlinarith only [hmR,hR,hm]
  have ht2 : (1+t)^2 ≤ (1+R)^2 := by nlinarith only [htR,ht,hR]
  have hm3 : (1+m)^3 ≤ (1+R)^3 := by gcongr
  have hd1 : (1+m)^2*(1+t)^2 ≤ (1+R)^4 := by
    have h := mul_le_mul hm2 ht2 (sq_nonneg _) (sq_nonneg _)
    nlinarith only [h]
  have hd2 : (1+m)^3*(1+t) ≤ (1+R)^4 := by
    have h := mul_le_mul hm3 (show 1+t ≤ 1+R by linarith only [htR]) ht1.le (pow_nonneg hR1.le 3)
    nlinarith only [h]
  have hv1 := one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos ht1)) hd1
  have hv2 := one_div_le_one_div_of_le (mul_pos (pow_pos hp 3) ht1) hd2
  have hid : t^2/(1+t)^2-s6VarianceTangent R t =
      t^2*(t-m)^2*(1/((1+m)^2*(1+t)^2)+2/((1+m)^3*(1+t))-3/(1+R)^4) := by
    unfold s6VarianceTangent
    dsimp [m]
    field_simp
    ring
  have hcoef : 0 ≤ 1/((1+m)^2*(1+t)^2)+2/((1+m)^3*(1+t))-3/(1+R)^4 := by
    simp only [div_eq_mul_inv] at hv1 hv2 ⊢
    linarith only [hv1,hv2]
  have hnon : 0 ≤ t^2*(t-m)^2*(1/((1+m)^2*(1+t)^2)+2/((1+m)^3*(1+t))-3/(1+R)^4) := by positivity
  linarith only [hid,hnon]

private theorem s6_variance_tangent_mid_strict {R : ℝ} (hR : 0 < R) :
    s6VarianceTangent R (R/2) < (R/2)^2/(1+R/2)^2 := by
  let m := 3*R/4
  have hm : 0 < m := by dsimp [m]; positivity
  have hmR : m < R := by dsimp [m]; linarith only [hR]
  have hp : 0 < 1+m := by positivity
  have ht1 : 0 < 1+R/2 := by positivity
  have hR1 : 0 < 1+R := by positivity
  have hm2 : (1+m)^2 < (1+R)^2 := by nlinarith only [hmR,hR,hm]
  have ht2 : (1+R/2)^2 ≤ (1+R)^2 := by nlinarith only [hR]
  have hm3 : (1+m)^3 ≤ (1+R)^3 := by gcongr
  have hd1 : (1+m)^2*(1+R/2)^2 < (1+R)^4 := by
    have h := mul_lt_mul_of_pos_right hm2 (sq_pos_of_pos ht1)
    have hh := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (1+R))
    nlinarith only [h,hh]
  have hd2 : (1+m)^3*(1+R/2) ≤ (1+R)^4 := by
    have h := mul_le_mul hm3 (show 1+R/2 ≤ 1+R by linarith only [hR]) ht1.le (pow_nonneg hR1.le 3)
    nlinarith only [h]
  have hv1 := one_div_lt_one_div_of_lt (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos ht1)) hd1
  have hv2 := one_div_le_one_div_of_le (mul_pos (pow_pos hp 3) ht1) hd2
  have hid : (R/2)^2/(1+R/2)^2-s6VarianceTangent R (R/2) =
      (R/2)^2*(R/2-m)^2*(1/((1+m)^2*(1+R/2)^2)+2/((1+m)^3*(1+R/2))-3/(1+R)^4) := by
    unfold s6VarianceTangent
    dsimp [m]
    field_simp
    ring
  have hcoef : 0 < 1/((1+m)^2*(1+R/2)^2)+2/((1+m)^3*(1+R/2))-3/(1+R)^4 := by
    simp only [div_eq_mul_inv] at hv1 hv2 ⊢
    linarith only [hv1,hv2]
  have hsq : 0 < (R/2-m)^2 := by dsimp [m]; exact sq_pos_of_ne_zero (by linarith only [hR])
  have hnon : 0 < (R/2)^2*(R/2-m)^2*(1/((1+m)^2*(1+R/2)^2)+2/((1+m)^3*(1+R/2))-3/(1+R)^4) := by positivity
  linarith only [hid,hnon]

/-- Weighted Jensen with its variance correction, proved by integrating the adjusted tangent. -/
theorem s6MomentPlus_gt_variance {R : ℝ} (hR : 0 < R) :
    R^3/3*(1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4)) < s6MomentPlus R := by
  have hm : 0 < 1+3*R/4 := by positivity
  have hRp : 0 < 1+R := by positivity
  have ht : Continuous (s6VarianceTangent R) := by unfold s6VarianceTangent; fun_prop
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hR
    ht.continuousOn (s6_recip_cont hR.le)
    (fun t ht => s6_variance_tangent_le hR (le_of_lt ht.1) ht.2)
    ⟨R/2,⟨by linarith only [hR],by linarith only [hR]⟩,s6_variance_tangent_mid_strict hR⟩
  let P : ℝ → ℝ := fun t => t^3/(3*(1+3*R/4)^2)-
    2/(1+3*R/4)^3*(t^4/4-(3*R/4)*t^3/3)+
    3/(1+R)^4*(t^5/5-(3*R/4)*t^4/2+(3*R/4)^2*t^3/3)
  have hd (t : ℝ) : HasDerivAt P (s6VarianceTangent R t) t := by
    have hh := (((hasDerivAt_pow 3 t).div_const (3*(1+3*R/4)^2)).sub
      ((((hasDerivAt_pow 4 t).div_const 4).sub
        (((hasDerivAt_pow 3 t).const_mul (3*R/4)).div_const 3)).const_mul (2/(1+3*R/4)^3))).add
      (((((hasDerivAt_pow 5 t).div_const 5).sub
        (((hasDerivAt_pow 4 t).const_mul (3*R/4)).div_const 2)).add
        (((hasDerivAt_pow 3 t).const_mul ((3*R/4)^2)).div_const 3)).const_mul (3/(1+R)^4))
    refine hh.congr_deriv ?_
    unfold s6VarianceTangent
    norm_num
    field_simp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (ht.intervalIntegrable 0 R)
  have hv : P R - P 0 = R^3/3*(1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4)) := by
    dsimp [P]
    field_simp
    ring
  rw [he,hv] at hi
  exact hi

/-- Exact reciprocal moment primitive, prior to any norm comparison. -/
theorem s6MomentPlus_eq {R : ℝ} (hR : 0 ≤ R) :
    s6MomentPlus R=R+1-1/(1+R)-2*log (1+R) := by
  let P : ℝ → ℝ := fun t => t+1-1/(1+t)-2*log (1+t)
  have hd {t : ℝ} (ht : 0 ≤ t) : HasDerivAt P (t^2/(1+t)^2) t := by
    have ht1 : 0 < 1+t := by positivity
    have hh := ((((hasDerivAt_id t).add_const 1).sub
      ((hasDerivAt_const t 1).div ((hasDerivAt_id t).const_add 1) ht1.ne')).sub
      ((((hasDerivAt_id t).const_add 1).log ht1.ne').const_mul 2))
    refine hh.congr_deriv ?_
    norm_num
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd (by rw [uIcc_of_le hR] at ht; exact ht.1))
    ((s6_recip_cont hR).intervalIntegrable_of_Icc hR)
  simpa [s6MomentPlus,P] using hi

/-- The other transformed reciprocal moment, including q=0. -/
theorem s6MomentMinus_eq {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    s6MomentMinus q = q-1+1/(1-q)+2*log (1-q) := by
  let P : ℝ → ℝ := fun t => t-1+1/(1-t)+2*log (1-t)
  have hc : ContinuousOn (fun t : ℝ => t^2/(1-t)^2) (Icc 0 q) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (by linarith only [ht.2,hq1] : 0 < 1-t))
  have hd {t : ℝ} (ht : t < 1) : HasDerivAt P (t^2/(1-t)^2) t := by
    have ht1 : 0 < 1-t := by linarith only [ht]
    have hh := ((((hasDerivAt_id t).sub_const 1).add
      ((hasDerivAt_const t 1).div ((hasDerivAt_id t).const_sub 1) ht1.ne')).add
      ((((hasDerivAt_id t).const_sub 1).log ht1.ne').const_mul 2))
    refine hh.congr_deriv ?_
    norm_num
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd (by rw [uIcc_of_le hq] at ht; linarith only [ht.2,hq1]))
    (hc.intervalIntegrable_of_Icc hq)
  simpa [s6MomentMinus,P] using hi

/-- Exact original secant as the two transformed reciprocal moments. -/
theorem s6_norm_moment_identity {x d : ℝ} (hx : 1 < x) (hd : 0 ≤ d) :
    m2Sec 1 x (x*(1+d))-3/4 = x/(2*(x*(1+d)-1))*
      (s6MomentPlus ((x-1)/(x+1))+s6MomentMinus (d/(2+d))) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hD : 0 < 2+d := by positivity
  have hbe : 1 < x*(1+d) := by nlinarith only [hx,hd,hx0]
  let R := (x-1)/(x+1)
  let q := d/(2+d)
  have hR : 0 < R := div_pos (by linarith only [hx]) hS
  have hq : 0 ≤ q := div_nonneg hd hD.le
  have hq1 : q < 1 := by dsimp [q]; rw [div_lt_one hD]; linarith
  have hRq : 0 < 1-q := by linarith only [hq1]
  have hRp : 0 < 1+R := by positivity
  have harg : (x*(1+d)+x)/(1+x)=(1+R)/(1-q) := by
    dsimp [R,q]
    field_simp
    ring
  change m2Sec 1 x (x*(1+d))-3/4 = x/(2*(x*(1+d)-1))*(s6MomentPlus R+s6MomentMinus q)
  rw [s6MomentPlus_eq hR.le,s6MomentMinus_eq hq hq1,m2Sec_of_ne (by linarith only [hbe]),harg,
    log_div hRp.ne' hRq.ne']
  generalize log (1+R)=lp
  generalize log (1-q)=lm
  dsimp [R,q]
  have hxm : x*(1+d)-1 ≠ 0 := ne_of_gt (by linarith only [hbe])
  field_simp [hxm]
  ring

/-- The paper's variance floor is strict for every nonnegative displacement,
including zero. No quadratic displacement relaxation is used. -/
theorem s6_norm_gt_variance_floor {x d : ℝ} (hx : 1 < x) (hd : 0 ≤ d) :
    s6VarianceFloor ((x-1)/(x+1)) d < m2Sec 1 x (x*(1+d)) := by
  let R := (x-1)/(x+1)
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hR : 0 < R := div_pos (by linarith only [hx]) hS
  have hbe : 1 < x*(1+d) := by nlinarith only [hx,hd,hx0]
  have hfac : 0 < x/(2*(x*(1+d)-1)) := div_pos hx0 (by linarith only [hbe])
  have hmain := s6MomentPlus_gt_variance hR
  have hq : 0 ≤ d/(2+d) := by positivity
  have htail : 0 ≤ s6MomentMinus (d/(2+d)) := by
    exact intervalIntegral.integral_nonneg_of_forall hq (fun t => by positivity)
  have hsum : R^3/3*(1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4)) <
      s6MomentPlus R+s6MomentMinus (d/(2+d)) := by linarith only [hmain,htail]
  have hmul := mul_lt_mul_of_pos_left hsum hfac
  have hM : 0 < 2*R+(1+R)*d := by positivity
  have hcoeff : x/(2*(x*(1+d)-1)) = (1+R)/(2*(2*R+(1+R)*d)) := by
    dsimp [R]
    field_simp
    ring
  have hi := s6_norm_moment_identity hx hd
  change m2Sec 1 x (x*(1+d))-3/4 =
    x/(2*(x*(1+d)-1))*(s6MomentPlus R+s6MomentMinus (d/(2+d))) at hi
  have he : s6VarianceFloor R d-3/4 = x/(2*(x*(1+d)-1))*
      (R^3/3*(1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4))) := by
    rw [hcoeff]
    unfold s6VarianceFloor
    field_simp
    ring
  rw [← hi,← he] at hmul
  linarith only [hmul]

/-- The variance correction is nonnegative on the physical domain. -/
theorem s6_variance_floor_ge_three_quarters {R d : ℝ} (hR : 0 < R) (hd : 0 ≤ d) :
    3/4 ≤ s6VarianceFloor R d := by
  unfold s6VarianceFloor
  have h : 0 ≤ (1+R)*R^3/(6*(2*R+(1+R)*d))*
      (1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4)) := by positivity
  linarith only [h]

end SmoothedOctagon

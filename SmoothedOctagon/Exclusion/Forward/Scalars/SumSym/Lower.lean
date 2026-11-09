module

public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Tangent
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Convex.Deriv

/-!
# The lower factor endpoint of the forward sum comparison

Positive reciprocal kernels prove factor convexity. The two factor edges
are controlled by a positive product and a quadratic midpoint tangent.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real MeasureTheory

/-- The positive reciprocal weight in the lower-endpoint third derivative. -/
noncomputable def fwdSumLowerF (a : ℝ) : ℝ :=
  (1+a)/(6*(1-a))*((1+30*a)*(1+a)^2+15*a*(1-a)^2)
/-- The reciprocal remainder after pairing the negative pole with its endpoint loss. -/
noncomputable def fwdSumLowerQ (a : ℝ) : ℝ :=
  43/48+a*(39/2-177/(16*(1-a))-15*(2-a)/(8*(1-a)^2))+
    a^2*(37/3+a/3-16*a^2/3)
noncomputable def fwdSumLowerThird (a k : ℝ) : ℝ :=
  50*a*(1-2*a)/(1-a)+6*fwdSumLowerQ a/(1-k)^4+
    6*(1-5*k)*fwdSumLowerF a/(1-k)^5

theorem fwdSumLowerF_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 < fwdSumLowerF a := by
  unfold fwdSumLowerF
  have hb : 0 < 1-a := by linarith
  have hp : 0 < 1+a := by linarith
  have hf : 0 < (1+30*a)*(1+a)^2 := mul_pos (by linarith) (sq_pos_of_pos hp)
  have hg : 0 ≤ 15*a*(1-a)^2 := by positivity
  exact mul_pos (div_pos hp (by positivity)) (by linarith only [hf,hg])

theorem fwdSumLowerQ_ge {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    43/48 ≤ fwdSumLowerQ a := by
  have hb : 0 < 1-a := by linarith
  have hbge : (6/7:ℝ) ≤ 1-a := by linarith
  have hrec : 1/(1-a) ≤ 7/6 := (div_le_iff₀ hb).mpr (by linarith)
  have hb2 : (6/7:ℝ)^2 ≤ (1-a)^2 := by gcongr
  have hrec2 : 1/(1-a)^2 ≤ 49/36 :=
    (div_le_iff₀ (sq_pos_of_pos hb)).mpr (by nlinarith only [hb2])
  have hfirst : 177/(16*(1-a)) < 13 := by
    apply (div_lt_iff₀ (by positivity : 0 < 16*(1-a))).mpr
    linarith only [hbge]
  have hsecond : 15*(2-a)/(8*(1-a)^2) < 19/4 := by
    have hid : 15*(2-a)/(8*(1-a)^2) = (15/8:ℝ)*(1/(1-a)+1/(1-a)^2) := by
      field_simp [ne_of_gt hb]
      ring
    rw [hid]
    nlinarith only [hrec,hrec2]
  have hsq : a^2 ≤ (1/7:ℝ)^2 := by gcongr
  have hbracket : 12 < 37/3+a/3-16*a^2/3 := by nlinarith only [hsq,ha]
  have hp : 0 ≤ a*(39/2-177/(16*(1-a))-15*(2-a)/(8*(1-a)^2)) :=
    mul_nonneg ha (by linarith only [hfirst,hsecond])
  have hq : 0 ≤ a^2*(37/3+a/3-16*a^2/3) := mul_nonneg (sq_nonneg a) (by linarith)
  unfold fwdSumLowerQ
  linarith only [hp,hq]

theorem fwdSumLowerThird_pos {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    0 < fwdSumLowerThird a k := by
  have hb : 0 < 1-a := by linarith
  have hr : 0 < 1-k := by linarith
  have hfirst : 0 ≤ 50*a*(1-2*a)/(1-a) := by
    apply div_nonneg
    · exact mul_nonneg (by positivity) (by linarith)
    · exact hb.le
  have hsecond : 0 < 6*fwdSumLowerQ a/(1-k)^4 :=
    div_pos (mul_pos (by norm_num) (by have := fwdSumLowerQ_ge ha ha1; linarith))
      (pow_pos hr _)
  have hthird : 0 ≤ 6*(1-5*k)*fwdSumLowerF a/(1-k)^5 :=
    div_nonneg (mul_nonneg (by linarith) (fwdSumLowerF_pos ha ha1).le) (pow_nonneg hr.le _)
  unfold fwdSumLowerThird
  linarith only [hfirst,hsecond,hthird]

/-- Exact positive-product lower k edge of the unexpanded original row. -/
theorem fwdSumLower_zero_identity {a : ℝ} (ha1 : a ≤ 1/7) :
    (1-a)*fwdSumUpper a 0 0 = -1/16+2*(1+a)/243+a^2/2-
      a^3/6*((2-a)*(11-18*a)+4*a) := by
  unfold fwdSumUpper fwdSumPairedLogUpper fwdSumR0 fwdSumR1 fwdSumAR
    fwdSumB1 fwdSumN1 fwdSumNd fwdSumFR
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  norm_num only [mul_zero,sub_zero,zero_pow,zero_div,zero_mul,add_zero,one_pow]
  field_simp [hb]
  ring

theorem fwdSumLower_zero_neg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumUpper a 0 0 < 0 := by
  have hb : 0 < 1-a := by linarith
  have hbracket : 0 < (2-a)*(11-18*a)+4*a := by
    have hp : 0 < (2-a)*(11-18*a) := mul_pos (by linarith) (by linarith)
    linarith only [hp,ha]
  have hprod : 0 ≤ a^3/6*((2-a)*(11-18*a)+4*a) :=
    mul_nonneg (by positivity) hbracket.le
  have hsmall : 2*(1+a)/243 < 1/72 := by linarith only [ha1]
  have hsq : a^2/2 < 1/72 := by
    have ha6 : a < 1/6 := by linarith only [ha1]
    nlinarith only [ha,ha6]
  have hid := fwdSumLower_zero_identity ha1
  have hneg : (1-a)*fwdSumUpper a 0 0 < 0 := by
    linarith only [hid,hprod,hsmall,hsq]
  exact neg_of_mul_neg_right hneg hb.le

end SmoothedOctagon

namespace SmoothedOctagon
open Set Real Polynomial

/-- Elementary rational differentiation, used only to certify the paper's kernel identities. -/
noncomputable def fwdPole0 (P : Polynomial ℝ) (x : ℝ) : ℝ := P.eval x/(1-x)^2
noncomputable def fwdPole1 (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.derivative.eval x/(1-x)^2+2*P.eval x/(1-x)^3
noncomputable def fwdPole2 (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.derivative.derivative.eval x/(1-x)^2+4*P.derivative.eval x/(1-x)^3+
    6*P.eval x/(1-x)^4
noncomputable def fwdPole3 (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.derivative.derivative.derivative.eval x/(1-x)^2+
    6*P.derivative.derivative.eval x/(1-x)^3+18*P.derivative.eval x/(1-x)^4+
    24*P.eval x/(1-x)^5

private theorem fp_power {x : ℝ} (_hx : x ≠ 1) (n : ℕ) :
    HasDerivAt (fun y : ℝ => (1-y)^n) (-(n:ℝ)*(1-x)^(n-1)) x := by
  convert (((hasDerivAt_id x).const_sub 1).pow n) using 1
  · rfl
  · simp only [id_eq]; ring

private theorem fp_div_power (P : Polynomial ℝ) {x : ℝ} (hx : x ≠ 1) (n : ℕ) :
    HasDerivAt (fun y : ℝ => P.eval y/(1-y)^n)
      ((P.derivative.eval x*(1-x)^n+P.eval x*(n:ℝ)*(1-x)^(n-1))/(1-x)^(2*n)) x := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert (P.hasDerivAt x).div (fp_power hx n) (pow_ne_zero n hd) using 1
  simp only [← pow_mul,Nat.mul_comm n 2]; ring

theorem fwdPole0_hasDerivAt (P : Polynomial ℝ) {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fwdPole0 P) (fwdPole1 P x) x := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert fp_div_power P hx 2 using 1
  · rfl
  · unfold fwdPole1
    norm_num only [Nat.cast_ofNat,Nat.reduceMul,Nat.reduceSub]
    field_simp [hd]

theorem fwdPole1_hasDerivAt (P : Polynomial ℝ) {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fwdPole1 P) (fwdPole2 P x) x := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert (fp_div_power P.derivative hx 2).add ((fp_div_power P hx 3).const_mul 2) using 1
  · ext y; dsimp [fwdPole1]; ring
  · unfold fwdPole2
    norm_num only [Nat.cast_ofNat,Nat.reduceMul,Nat.reduceSub]
    field_simp [hd]
    ring

theorem fwdPole2_hasDerivAt (P : Polynomial ℝ) {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt (fwdPole2 P) (fwdPole3 P x) x := by
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  convert ((fp_div_power P.derivative.derivative hx 2).add
    ((fp_div_power P.derivative hx 3).const_mul 4)).add
      ((fp_div_power P hx 4).const_mul 6) using 1
  · ext y; dsimp [fwdPole2]; ring
  · unfold fwdPole3
    norm_num only [Nat.cast_ofNat,Nat.reduceMul,Nat.reduceSub]
    field_simp [hd]
    ring

/-- The row numerator is assembled from its original factors, without coefficient expansion. -/
noncomputable def fwdSumClearedRow {A : Type*} [CommRing A] [Algebra ℝ A] (a k τ : A) : A :=
  let b := 1-a
  let r := 1-k
  let p := 1+a
  let c := a+k
  let cb := 1-a-k
  let m := 9-25*τ
  let ℓn := 1-algebraMap ℝ A (1/2)*k-algebraMap ℝ A (1/6)*k^2
  let j0 := algebraMap ℝ A (1/2)+algebraMap ℝ A (1/3)*(a+2*k)
  2*cb*r*(a*b+2*p)+algebraMap ℝ A (1/2)*b^3*r-
    b*r*(2*r^2-p*r+algebraMap ℝ A (1/2)*p^2)-
    algebraMap ℝ A (49/16)*(b-2*k)*r-2*b*c*(2-c)*(r+algebraMap ℝ A (1/4)*p^2)+
    algebraMap ℝ A (1/2)*m*a*b*c*(p^2+4*k-4)+
    p*b*r*(algebraMap ℝ A (1/2)*c*τ+r*(algebraMap ℝ A (2/243)-algebraMap ℝ A (19/243)*τ))+
    b*c*((b*c+2*a*(1+m*cb))*ℓn-r*a*cb*(m*b+2)*j0)

/-- Three derivatives of the factored row. -/
noncomputable def fwdSumLowerNumerator (a : ℝ) : Polynomial ℝ :=
  fwdSumClearedRow (C a) X X

end SmoothedOctagon


namespace SmoothedOctagon
open Set Real Polynomial Filter

private theorem fse_R1_pole_cancel {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    fwdSumR1 a k =
      2*(1-a-k)/((1-a)*(1-k))*(1+2*((1+a)/(1-a))-(1-a))+
        (1-a)/(2*(1-k))-fwdSumB1 a k-(49/32)*fwdSumN1 a k-
        fwdSumNd a k*fwdSumFR a k := by
  unfold fwdSumR1 fwdSumAR
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  have hc : 1-a-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-a-k)
  field_simp [hb,hr,hc]
  ring

/-- Clearing only the two geometric denominator factors preserves the original product row. -/
theorem fwdSumUpper_cleared {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) (τ : ℝ) :
    fwdSumUpper a k τ = fwdSumClearedRow a k τ/((1-a)^2*(1-k)^2) := by
  unfold fwdSumUpper
  rw [fse_R1_pole_cancel ha hk]
  unfold fwdSumClearedRow fwdSumPairedLogUpper fwdSumB1 fwdSumN1 fwdSumNd
    fwdSumFR fwdSumR0
  simp only [Algebra.algebraMap_self_apply]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

private theorem fse_lower_num_eval (a k : ℝ) :
    (fwdSumLowerNumerator a).eval k = fwdSumClearedRow a k k := by
  simp [fwdSumLowerNumerator,fwdSumClearedRow]

noncomputable def fwdSumLowerFirst (a k : ℝ) : ℝ :=
  fwdPole1 (fwdSumLowerNumerator a) k/(1-a)^2
noncomputable def fwdSumLowerSecond (a k : ℝ) : ℝ :=
  fwdPole2 (fwdSumLowerNumerator a) k/(1-a)^2

/-- First derivative of the lower-endpoint function on an open neighbourhood of its domain. -/
theorem fwdSumLower_hasDerivAt {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    HasDerivAt (fun v : ℝ => fwdSumUpper a v v) (fwdSumLowerFirst a k) k := by
  have heq : (fun v : ℝ => fwdSumUpper a v v) =ᶠ[nhds k]
      (fun v : ℝ => fwdPole0 (fwdSumLowerNumerator a) v/(1-a)^2) := by
    filter_upwards [eventually_lt_nhds hk] with v hv
    rw [fwdSumUpper_cleared ha hv v,← fse_lower_num_eval a v]
    unfold fwdPole0
    rw [div_div]
    congr 1
    ring
  exact ((fwdPole0_hasDerivAt (fwdSumLowerNumerator a) (by linarith : k ≠ 1)).div_const
    ((1-a)^2)).congr_of_eventuallyEq heq

theorem fwdSumLowerFirst_hasDerivAt {a k : ℝ} (hk : k ≠ 1) :
    HasDerivAt (fwdSumLowerFirst a) (fwdSumLowerSecond a k) k :=
  (fwdPole1_hasDerivAt (fwdSumLowerNumerator a) hk).div_const ((1-a)^2)

/-- The third derivative simplifies to the paper's two positive reciprocal weights. -/
theorem fwdSumLower_third_identity {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    fwdPole3 (fwdSumLowerNumerator a) k/(1-a)^2 = fwdSumLowerThird a k := by
  unfold fwdPole3 fwdSumLowerNumerator fwdSumClearedRow fwdSumLowerThird
    fwdSumLowerF fwdSumLowerQ
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

theorem fwdSumLowerSecond_hasDerivAt {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    HasDerivAt (fwdSumLowerSecond a) (fwdSumLowerThird a k) k := by
  have hh := (fwdPole2_hasDerivAt (fwdSumLowerNumerator a) (by linarith : k ≠ 1)).div_const
    ((1-a)^2)
  exact hh.congr_deriv (fwdSumLower_third_identity ha hk)

end SmoothedOctagon

namespace SmoothedOctagon
open Set Real Polynomial Filter

local syntax "sum_endpoint_deriv" : tactic
macro_rules
| `(tactic| sum_endpoint_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> sum_endpoint_deriv
  | apply HasDerivAt.sub <;> sum_endpoint_deriv
  | apply HasDerivAt.pow <;> sum_endpoint_deriv
  | apply HasDerivAt.mul <;> sum_endpoint_deriv
  | apply HasDerivAt.div <;> first | sum_endpoint_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> sum_endpoint_deriv)

/-- Initial curvature reconstructed by twice integrating the paper's reciprocal kernels. -/
noncomputable def fwdSumInitial (a : ℝ) : ℝ :=
  17/8-199*a/24+(4/3)*(41*a^2/2-22*a^3-8*a^4)+
    (8/3)*((35/2)*(1/(1-a)-1-a)-(3/2)*(1/(1-a)^2-1-2*a))+
    (1/4)*((1/(1-a)^2-1-2*a)-(1/(1-a)-1-a)/2)
noncomputable def fwdSumInitialFirst (a : ℝ) : ℝ :=
  -199/24+(4/3)*(41*a-66*a^2-32*a^3)+
    (8/3)*((35/2)*(1/(1-a)^2-1)-(3/2)*(2/(1-a)^3-2))+
    (1/4)*((2/(1-a)^3-2)-(1/(1-a)^2-1)/2)
noncomputable def fwdSumInitialSecond (a : ℝ) : ℝ :=
  (4/3)*(41-12*a*(11+8*a))+8*(35*(1-a)-9)/(3*(1-a)^4)+
    (6-(1-a))/(4*(1-a)^4)

/-- The model is exactly the original row's initial second derivative. -/
theorem fwdSumLower_initial_identity {a : ℝ} (ha : a < 1/2) :
    fwdSumLowerSecond a 0 = fwdSumInitial a := by
  unfold fwdSumLowerSecond fwdPole2 fwdSumLowerNumerator fwdSumClearedRow fwdSumInitial
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  field_simp [hb]
  ring

theorem fwdSumInitial_hasDerivAt {a : ℝ} (ha : a < 1/2) :
    HasDerivAt fwdSumInitial (fwdSumInitialFirst a) a := by
  have hb : 0 < 1-a := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumInitial
    sum_endpoint_deriv
  · unfold fwdSumInitialFirst
    norm_num [npowRec]
    field_simp
    ring

theorem fwdSumInitialFirst_hasDerivAt {a : ℝ} (ha : a < 1/2) :
    HasDerivAt fwdSumInitialFirst (fwdSumInitialSecond a) a := by
  have hb : 0 < 1-a := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumInitialFirst
    sum_endpoint_deriv
  · unfold fwdSumInitialSecond
    norm_num [npowRec]
    field_simp
    ring

theorem fwdSumInitialSecond_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 < fwdSumInitialSecond a := by
  have hb : 0 < 1-a := by linarith
  have hsq : a^2 ≤ (1/7:ℝ)^2 := by gcongr
  have hfirst : 0 < (4/3:ℝ)*(41-12*a*(11+8*a)) := by
    nlinarith only [ha1,hsq]
  have hsecond : 0 < 8*(35*(1-a)-9)/(3*(1-a)^4) :=
    div_pos (by linarith only [ha1]) (by positivity)
  have hthird : 0 < (6-(1-a))/(4*(1-a)^4) :=
    div_pos (by linarith only [ha]) (by positivity)
  unfold fwdSumInitialSecond
  linarith only [hfirst,hsecond,hthird]

private theorem fse_initialFirst_lower {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    -199/24 ≤ fwdSumInitialFirst a := by
  have hh := ff_le_of_deriv (f := fwdSumInitialFirst) (f' := fwdSumInitialSecond) ha
    (fun x hx => fwdSumInitialFirst_hasDerivAt (by linarith only [hx.2,ha1]))
    (fun x hx => (fwdSumInitialSecond_pos hx.1 (le_trans hx.2 ha1)).le)
  simpa [fwdSumInitialFirst] using hh

theorem fwdSumInitial_pos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 < fwdSumInitial a := by
  have hh := ff_le_of_deriv (f := fun x : ℝ => fwdSumInitial x+199*x/24)
    (f' := fun x : ℝ => fwdSumInitialFirst x+199/24) ha (fun x hx => ?_) (fun x hx => ?_)
  · have hbase : fwdSumInitial 0 = 17/8 := by norm_num [fwdSumInitial]
    simp only [mul_zero,zero_div,add_zero,hbase] at hh
    linarith only [hh,ha1]
  · convert (fwdSumInitial_hasDerivAt (by linarith only [hx.2,ha1])).add
      (((hasDerivAt_id x).const_mul 199).div_const 24) using 1
    · ext y; simp only [Pi.add_apply,id_eq]
    · ring
  · have hp := fse_initialFirst_lower hx.1 (le_trans hx.2 ha1)
    linarith only [hp]

theorem fwdSumLowerSecond_pos {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) :
    0 < fwdSumLowerSecond a k := by
  have hh := ff_le_of_deriv (f := fwdSumLowerSecond a) (f' := fwdSumLowerThird a) hk
    (fun x hx => fwdSumLowerSecond_hasDerivAt (by linarith only [ha1])
      (by linarith only [hx.2,hk1]))
    (fun x hx => (fwdSumLowerThird_pos ha ha1 (le_trans hx.2 hk1)).le)
  rw [fwdSumLower_initial_identity (by linarith only [ha1])] at hh
  exact lt_of_lt_of_le (fwdSumInitial_pos ha ha1) hh

/-- The original lower endpoint is convex in k on the whole independent rectangle. -/
theorem fwdSumLower_convexOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    ConvexOn ℝ (Icc (0:ℝ) (1/5)) (fun k : ℝ => fwdSumUpper a k k) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (1/5))
    (f' := fwdSumLowerFirst a) (f'' := fwdSumLowerSecond a)
  · intro k hk
    exact (fwdSumLower_hasDerivAt (by linarith only [ha1])
      (by linarith only [hk.2])).continuousAt.continuousWithinAt
  · intro k hk
    have hbox := interior_subset hk
    exact (fwdSumLower_hasDerivAt (by linarith only [ha1])
      (by linarith only [hbox.2])).hasDerivWithinAt
  · intro k hk
    have hbox := interior_subset hk
    exact (fwdSumLowerFirst_hasDerivAt (by linarith only [hbox.2])).hasDerivWithinAt
  · intro k hk
    exact (fwdSumLowerSecond_pos ha ha1 (interior_subset hk).1 (interior_subset hk).2).le

noncomputable def fwdSumYNum : Polynomial ℝ := fwdSumClearedRow X (C (1/5)) (C (1/5))
noncomputable def fwdSumYFirst (a : ℝ) : ℝ := fwdPole1 fwdSumYNum a/(4/5)^2
noncomputable def fwdSumYSecond (a : ℝ) : ℝ := fwdPole2 fwdSumYNum a/(4/5)^2

private theorem fse_Y_num_eval (a : ℝ) :
    fwdSumYNum.eval a = fwdSumClearedRow a (1/5) (1/5) := by
  simp [fwdSumYNum,fwdSumClearedRow]

theorem fwdSumY_hasDerivAt {a : ℝ} (ha : a < 1/2) :
    HasDerivAt (fun v : ℝ => fwdSumUpper v (1/5) (1/5)) (fwdSumYFirst a) a := by
  have heq : (fun v : ℝ => fwdSumUpper v (1/5) (1/5)) =ᶠ[nhds a]
      (fun v : ℝ => fwdPole0 fwdSumYNum v/(4/5)^2) := by
    filter_upwards [eventually_lt_nhds ha] with v hv
    rw [fwdSumUpper_cleared hv (by norm_num) (1/5),← fse_Y_num_eval]
    unfold fwdPole0
    norm_num only [show (1:ℝ)-1/5 = 4/5 by norm_num]
    rw [div_div]
  exact ((fwdPole0_hasDerivAt fwdSumYNum (by linarith : a ≠ 1)).div_const
    ((4/5)^2)).congr_of_eventuallyEq heq

theorem fwdSumYFirst_hasDerivAt {a : ℝ} (ha : a ≠ 1) :
    HasDerivAt fwdSumYFirst (fwdSumYSecond a) a :=
  (fwdPole1_hasDerivAt fwdSumYNum ha).div_const ((4/5)^2)

noncomputable def fwdSumYCurvatureBound (b : ℝ) : ℝ :=
  20*b^2-(393/16)*b-2/3+119/(16*b^3)-45/(16*b^4)
noncomputable def fwdSumYCurvatureFirst (b : ℝ) : ℝ :=
  40*b-393/16-357/(16*b^4)+45/(4*b^5)
noncomputable def fwdSumYCurvatureSecond (b : ℝ) : ℝ :=
  40+(357*b-225)/(4*b^6)

theorem fwdSumY_curvature_identity {a : ℝ} (ha : a < 1/2) :
    fwdSumYCurvatureBound (1-a)-fwdSumYSecond a = 101/(4320*(1-a)^3) := by
  unfold fwdSumYCurvatureBound fwdSumYSecond fwdPole2 fwdSumYNum fwdSumClearedRow
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  field_simp [hb]
  ring

theorem fwdSumYCurvature_hasDerivAt {b : ℝ} (hb : 0 < b) :
    HasDerivAt fwdSumYCurvatureBound (fwdSumYCurvatureFirst b) b := by
  apply HasDerivAt.congr_deriv
  · unfold fwdSumYCurvatureBound
    sum_endpoint_deriv
  · unfold fwdSumYCurvatureFirst
    norm_num [npowRec]
    field_simp
    ring

theorem fwdSumYCurvatureFirst_hasDerivAt {b : ℝ} (hb : 0 < b) :
    HasDerivAt fwdSumYCurvatureFirst (fwdSumYCurvatureSecond b) b := by
  apply HasDerivAt.congr_deriv
  · unfold fwdSumYCurvatureFirst
    sum_endpoint_deriv
  · unfold fwdSumYCurvatureSecond
    norm_num [npowRec]
    field_simp
    ring

/-- An interval version of the usual maximum-at-an-endpoint bound for a convex function. -/
theorem fse_convex_le_max {f : ℝ → ℝ} {lo hi x : ℝ}
    (hc : ConvexOn ℝ (Icc lo hi) f) (hx : x ∈ Icc lo hi) :
    f x ≤ max (f lo) (f hi) := by
  have hle : lo ≤ hi := le_trans hx.1 hx.2
  apply hc.le_on_segment ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩
  simpa only [segment_eq_Icc hle] using hx

theorem fwdSumYCurvature_convexOn :
    ConvexOn ℝ (Icc (6/7:ℝ) 1) fwdSumYCurvatureBound := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (6/7) 1)
    (f' := fwdSumYCurvatureFirst) (f'' := fwdSumYCurvatureSecond)
  · intro b hb
    exact (fwdSumYCurvature_hasDerivAt (by linarith only [hb.1])).continuousAt.continuousWithinAt
  · intro b hb
    exact (fwdSumYCurvature_hasDerivAt (by have := (interior_subset hb).1; linarith)).hasDerivWithinAt
  · intro b hb
    exact (fwdSumYCurvatureFirst_hasDerivAt
      (by have := (interior_subset hb).1; linarith)).hasDerivWithinAt
  · intro b hb
    have hb6 := (interior_subset hb).1
    have hb0 : 0 < b := by linarith only [hb6]
    unfold fwdSumYCurvatureSecond
    have hp : 0 ≤ (357*b-225)/(4*b^6) := div_nonneg (by linarith only [hb6]) (by positivity)
    linarith only [hp]

theorem fwdSumYSecond_lt {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumYSecond a < -2/5 := by
  have hmax := fse_convex_le_max fwdSumYCurvature_convexOn
    (show 1-a ∈ Icc (6/7:ℝ) 1 by constructor <;> linarith)
  have hleft : fwdSumYCurvatureBound (6/7) < -2/5 := by norm_num [fwdSumYCurvatureBound]
  have hright : fwdSumYCurvatureBound 1 < -2/5 := by norm_num [fwdSumYCurvatureBound]
  have hbound : fwdSumYCurvatureBound (1-a) < -2/5 := lt_of_le_of_lt hmax (max_lt hleft hright)
  have hid := fwdSumY_curvature_identity (a := a) (by linarith only [ha1])
  have hgap : 0 < 101/(4320*(1-a)^3) := by
    have hb : 0 < 1-a := by linarith
    positivity
  linarith only [hid,hgap,hbound]

end SmoothedOctagon

namespace SmoothedOctagon
open Set Real Polynomial Filter

private theorem fse_Yadjust_hasDerivAt {a : ℝ} (ha : a < 1/2) :
    HasDerivAt (fun x : ℝ => fwdSumUpper x (1/5) (1/5)+x^2/5)
      (fwdSumYFirst a+2*a/5) a := by
  convert (fwdSumY_hasDerivAt ha).add ((hasDerivAt_pow 2 a).div_const 5) using 1
  norm_num

private theorem fse_YadjustFirst_hasDerivAt {a : ℝ} (ha : a ≠ 1) :
    HasDerivAt (fun x : ℝ => fwdSumYFirst x+2*x/5) (fwdSumYSecond a+2/5) a := by
  convert (fwdSumYFirst_hasDerivAt ha).add
    (((hasDerivAt_id a).const_mul 2).div_const 5) using 1
  · rfl
  · ring

/-- Strong concavity is expressed as ordinary concavity after adding the exact quadratic budget. -/
theorem fwdSumY_adjusted_concaveOn :
    ConcaveOn ℝ (Icc (0:ℝ) (1/7)) (fun a : ℝ => fwdSumUpper a (1/5) (1/5)+a^2/5) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (1/7))
    (f' := fun a : ℝ => fwdSumYFirst a+2*a/5) (f'' := fun a : ℝ => fwdSumYSecond a+2/5)
  · intro a ha
    exact (fse_Yadjust_hasDerivAt (by linarith only [ha.2])).continuousAt.continuousWithinAt
  · intro a ha
    exact (fse_Yadjust_hasDerivAt
      (by have := (interior_subset ha).2; linarith)).hasDerivWithinAt
  · intro a ha
    exact (fse_YadjustFirst_hasDerivAt
      (by have := (interior_subset ha).2; linarith)).hasDerivWithinAt
  · intro a ha
    have hp := fwdSumYSecond_lt (interior_subset ha).1 (interior_subset ha).2
    linarith only [hp]

/-- A differentiable concave function lies below its tangent, including both ends of a closed domain. -/
theorem fse_concave_tangent {S : Set ℝ} {f : ℝ → ℝ} {m x d : ℝ}
    (hc : ConcaveOn ℝ S f) (hm : m ∈ S) (hx : x ∈ S) (hd : HasDerivAt f d m) :
    f x ≤ f m+d*(x-m) := by
  rcases lt_trichotomy x m with hxm | hxm | hmx
  · have hs := hc.le_slope_of_hasDerivAt hx hm hxm hd
    rw [slope_def_field] at hs
    have hp := (le_div_iff₀ (sub_pos.mpr hxm)).mp hs
    linarith only [hp]
  · subst x; simp
  · have hs := hc.slope_le_of_hasDerivAt hm hx hmx hd
    rw [slope_def_field] at hs
    have hp := (div_le_iff₀ (sub_pos.mpr hmx)).mp hs
    linarith only [hp]

/-- The only fixed shape evaluation needed by the lower endpoint's quadratic tangent. -/
theorem fwdSumY_midpoint :
    fwdSumUpper (1/14) (1/5) (1/5)+(5/4)*(fwdSumYFirst (1/14))^2 < -1/900 := by
  rw [fwdSumUpper_cleared (by norm_num) (by norm_num) (1/5)]
  norm_num [fwdSumClearedRow,fwdSumYFirst,fwdPole1,fwdSumYNum,
    Polynomial.derivative_mul,Polynomial.derivative_pow]

/-- The top k edge has the full margin required later by the short upper interval. -/
theorem fwdSumY_lt {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    fwdSumUpper a (1/5) (1/5) < -1/900 := by
  have htan := fse_concave_tangent fwdSumY_adjusted_concaveOn
    (show (1/14:ℝ) ∈ Icc (0:ℝ) (1/7) by constructor <;> norm_num)
    (show a ∈ Icc (0:ℝ) (1/7) from ⟨ha,ha1⟩)
    (fse_Yadjust_hasDerivAt (by norm_num : (1/14:ℝ) < 1/2))
  have hquad : fwdSumUpper a (1/5) (1/5) ≤
      fwdSumUpper (1/14) (1/5) (1/5)+fwdSumYFirst (1/14)*(a-1/14)-(a-1/14)^2/5 := by
    nlinarith only [htan]
  have hsquare := sq_nonneg (a-1/14-(5/2)*fwdSumYFirst (1/14))
  have hmax : fwdSumUpper (1/14) (1/5) (1/5)+
      fwdSumYFirst (1/14)*(a-1/14)-(a-1/14)^2/5 ≤
      fwdSumUpper (1/14) (1/5) (1/5)+(5/4)*(fwdSumYFirst (1/14))^2 := by
    nlinarith only [hsquare]
  exact lt_of_le_of_lt (le_trans hquad hmax) fwdSumY_midpoint

/-- Full lower sum endpoint: convexity in k and the two actual negative k edges. -/
theorem fwdSum_lower_endpoint_neg {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumUpper a k k < 0 := by
  have hmax := fse_convex_le_max (fwdSumLower_convexOn ha ha1)
    (show k ∈ Icc (0:ℝ) (1/5) from ⟨hk,hk1⟩)
  have hleft := fwdSumLower_zero_neg ha ha1
  have hright : fwdSumUpper a (1/5) (1/5) < 0 := lt_trans (fwdSumY_lt ha ha1) (by norm_num)
  exact lt_of_le_of_lt hmax (max_lt hleft hright)

end SmoothedOctagon

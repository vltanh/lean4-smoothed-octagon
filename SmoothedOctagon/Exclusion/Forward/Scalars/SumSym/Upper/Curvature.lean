module

public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Lower

/-!
# Curvature at the upper factor ceiling

The original unexpanded row gives simple reciprocal poles. Their curvature
bounds make the upper-ceiling comparison concave in the factor.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real Polynomial Filter

/-- The simple-pole weight of the original row in the a direction. -/
noncomputable def fwdSumSimplePole (k τ : ℝ) : ℝ :=
  let r := 1-k
  let m := 9-25*τ
  let lp := 1+k/2+k^2/(3*r)
  (2*k-1-1/16)/r+2*m*k*(1+k)/r^2+τ*(1+k)/r+
    2*(2/243-(19/243)*τ)+2*(1+k)*(1-m*k)/r*lp+
    2*k*(1+k)/r*(5/6+2*k/3)
noncomputable def fwdSumT1Prod {A : Type*} [CommRing A] (k τ : A) : A :=
  (9-25*τ)*k^2*(4*k^2-k+10)+6+10*k+11*k^2-18*k^3+3*(1-k)*τ
noncomputable def fwdSumT2Prod {A : Type*} [CommRing A] (k τ : A) : A :=
  2*(9-25*τ)*k*(5*k^2-4*k+3)+3+19*k-15*k^2
noncomputable def fwdSumT3Prod {A : Type*} [CommRing A] (k τ : A) : A :=
  (9-25*τ)*(8*k^2-7*k+2)+7-4*k
noncomputable def fwdSumQ1 (k τ : ℝ) : ℝ := -fwdSumT1Prod k τ/(6*(1-k)^2)
noncomputable def fwdSumQ2 (k τ : ℝ) : ℝ := -fwdSumT2Prod k τ/(6*(1-k)^2)
noncomputable def fwdSumQ3 (k τ : ℝ) : ℝ := -fwdSumT3Prod k τ/(6*(1-k)^2)
noncomputable def fwdSumQ4 (k τ : ℝ) : ℝ := (9-25*τ)/(3*(1-k))

/-- Exact original-row pole decomposition; the constant quotient is retained as U(0,k,τ). -/
theorem fwdSumUpper_a_poles {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) (τ : ℝ) :
    fwdSumUpper a k τ = fwdSumUpper 0 k τ+
      fwdSumQ1 k τ*a+fwdSumQ2 k τ*a^2+fwdSumQ3 k τ*a^3+fwdSumQ4 k τ*a^4+
      fwdSumSimplePole k τ*(1/(1-a)-1)-(15*k/(8*(1-k)))*(1/(1-a)^2-1) := by
  rw [fwdSumUpper_cleared ha hk τ,fwdSumUpper_cleared (by norm_num) hk τ]
  unfold fwdSumClearedRow fwdSumSimplePole fwdSumQ1 fwdSumQ2 fwdSumQ3 fwdSumQ4
    fwdSumT1Prod fwdSumT2Prod fwdSumT3Prod
  simp only [Algebra.algebraMap_self_apply]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

noncomputable def fwdSumSimplePoleCleared {A : Type*} [CommRing A] [Algebra ℝ A] (k τ : A) : A :=
  let r := 1-k
  let m := 9-25*τ
  let lpnum := 1-algebraMap ℝ A (1/2)*k-algebraMap ℝ A (1/6)*k^2
  (2*k-1-algebraMap ℝ A (1/16))*r+2*m*k*(1+k)+τ*(1+k)*r+
    2*(algebraMap ℝ A (2/243)-algebraMap ℝ A (19/243)*τ)*r^2+
    2*(1+k)*(1-m*k)*lpnum+
    2*k*(1+k)*r*(algebraMap ℝ A (5/6)+algebraMap ℝ A (2/3)*k)

private theorem fse_simplePole_cleared {k : ℝ} (hk : k ≠ 1) (τ : ℝ) :
    fwdSumSimplePole k τ = fwdSumSimplePoleCleared k τ/(1-k)^2 := by
  unfold fwdSumSimplePole fwdSumSimplePoleCleared
  simp only [Algebra.algebraMap_self_apply]
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring

noncomputable def fwdSumTauPoly : Polynomial ℝ := C (8/15)-C (5/3)*X
noncomputable def fwdSumG0Poly : Polynomial ℝ := fwdSumClearedRow (C 0) X fwdSumTauPoly
noncomputable def fwdSumGQ1Poly : Polynomial ℝ := -C (1/6)*fwdSumT1Prod X fwdSumTauPoly
noncomputable def fwdSumGQ2Poly : Polynomial ℝ := -C (1/6)*fwdSumT2Prod X fwdSumTauPoly
noncomputable def fwdSumGQ3Poly : Polynomial ℝ := -C (1/6)*fwdSumT3Prod X fwdSumTauPoly
noncomputable def fwdSumGQ4Poly : Polynomial ℝ := C (1/3)*(9-25*fwdSumTauPoly)*(1-X)
noncomputable def fwdSumGAPoly : Polynomial ℝ := fwdSumSimplePoleCleared X fwdSumTauPoly
noncomputable def fwdSumGDPolePoly : Polynomial ℝ := C (15/8)*X*(1-X)

private theorem fse_G0_bridge {k : ℝ} (hk : k < 1/2) :
    fwdPole0 fwdSumG0Poly k = fwdSumUpper 0 k (fwdSumLinearTop k) := by
  rw [fwdSumUpper_cleared (by norm_num) hk]
  unfold fwdPole0 fwdSumG0Poly fwdSumClearedRow fwdSumTauPoly fwdSumLinearTop
  simp
  ring

private theorem fse_GQ1_bridge {k : ℝ} (hk : k ≠ 1) :
    fwdPole0 fwdSumGQ1Poly k = fwdSumQ1 k (fwdSumLinearTop k) := by
  unfold fwdPole0 fwdSumGQ1Poly fwdSumQ1 fwdSumT1Prod fwdSumTauPoly fwdSumLinearTop
  simp
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring
private theorem fse_GQ2_bridge {k : ℝ} (hk : k ≠ 1) :
    fwdPole0 fwdSumGQ2Poly k = fwdSumQ2 k (fwdSumLinearTop k) := by
  unfold fwdPole0 fwdSumGQ2Poly fwdSumQ2 fwdSumT2Prod fwdSumTauPoly fwdSumLinearTop
  simp
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring
private theorem fse_GQ3_bridge {k : ℝ} (hk : k ≠ 1) :
    fwdPole0 fwdSumGQ3Poly k = fwdSumQ3 k (fwdSumLinearTop k) := by
  unfold fwdPole0 fwdSumGQ3Poly fwdSumQ3 fwdSumT3Prod fwdSumTauPoly fwdSumLinearTop
  simp
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring
private theorem fse_GQ4_bridge {k : ℝ} (hk : k ≠ 1) :
    fwdPole0 fwdSumGQ4Poly k = fwdSumQ4 k (fwdSumLinearTop k) := by
  unfold fwdPole0 fwdSumGQ4Poly fwdSumQ4 fwdSumTauPoly fwdSumLinearTop
  simp
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
private theorem fse_GA_bridge {k : ℝ} (hk : k ≠ 1) :
    fwdPole0 fwdSumGAPoly k = fwdSumSimplePole k (fwdSumLinearTop k) := by
  rw [fse_simplePole_cleared hk]
  simp [fwdPole0,fwdSumGAPoly,fwdSumSimplePoleCleared,fwdSumTauPoly,fwdSumLinearTop]
  ring
private theorem fse_GD_bridge {k : ℝ} (hk : k ≠ 1) :
    fwdPole0 fwdSumGDPolePoly k = 15*k/(8*(1-k)) := by
  unfold fwdPole0 fwdSumGDPolePoly
  simp
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]

noncomputable def fwdSumGModel (a k : ℝ) : ℝ :=
  fwdPole0 fwdSumG0Poly k+a*fwdPole0 fwdSumGQ1Poly k+a^2*fwdPole0 fwdSumGQ2Poly k+
    a^3*fwdPole0 fwdSumGQ3Poly k+a^4*fwdPole0 fwdSumGQ4Poly k+
    (1/(1-a)-1)*fwdPole0 fwdSumGAPoly k-(1/(1-a)^2-1)*fwdPole0 fwdSumGDPolePoly k
noncomputable def fwdSumGFirst (a k : ℝ) : ℝ :=
  fwdPole1 fwdSumG0Poly k+a*fwdPole1 fwdSumGQ1Poly k+a^2*fwdPole1 fwdSumGQ2Poly k+
    a^3*fwdPole1 fwdSumGQ3Poly k+a^4*fwdPole1 fwdSumGQ4Poly k+
    (1/(1-a)-1)*fwdPole1 fwdSumGAPoly k-(1/(1-a)^2-1)*fwdPole1 fwdSumGDPolePoly k
noncomputable def fwdSumGSecond (a k : ℝ) : ℝ :=
  fwdPole2 fwdSumG0Poly k+a*fwdPole2 fwdSumGQ1Poly k+a^2*fwdPole2 fwdSumGQ2Poly k+
    a^3*fwdPole2 fwdSumGQ3Poly k+a^4*fwdPole2 fwdSumGQ4Poly k+
    (1/(1-a)-1)*fwdPole2 fwdSumGAPoly k-(1/(1-a)^2-1)*fwdPole2 fwdSumGDPolePoly k

theorem fse_G_model {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    fwdSumUpper a k (fwdSumLinearTop k) = fwdSumGModel a k := by
  have hk1 : k ≠ 1 := by linarith
  unfold fwdSumGModel
  rw [fse_G0_bridge hk,fse_GQ1_bridge hk1,fse_GQ2_bridge hk1,fse_GQ3_bridge hk1,fse_GQ4_bridge hk1,
    fse_GA_bridge hk1,fse_GD_bridge hk1]
  rw [fwdSumUpper_a_poles ha hk]
  ring

theorem fse_G_model_hasDerivAt {a k : ℝ} (hk : k ≠ 1) :
    HasDerivAt (fwdSumGModel a) (fwdSumGFirst a k) k := by
  convert
    ((((((fwdPole0_hasDerivAt fwdSumG0Poly hk).add
      ((fwdPole0_hasDerivAt fwdSumGQ1Poly hk).const_mul a)).add
      ((fwdPole0_hasDerivAt fwdSumGQ2Poly hk).const_mul (a^2))).add
      ((fwdPole0_hasDerivAt fwdSumGQ3Poly hk).const_mul (a^3))).add
      ((fwdPole0_hasDerivAt fwdSumGQ4Poly hk).const_mul (a^4))).add
      ((fwdPole0_hasDerivAt fwdSumGAPoly hk).const_mul (1/(1-a)-1))).sub
      ((fwdPole0_hasDerivAt fwdSumGDPolePoly hk).const_mul (1/(1-a)^2-1)) using 1 <;> rfl

theorem fwdSumG_hasDerivAt {a k : ℝ} (ha : a < 1/2) (hk : k < 1/2) :
    HasDerivAt (fun v : ℝ => fwdSumUpper a v (fwdSumLinearTop v)) (fwdSumGFirst a k) k := by
  have heq : (fun v : ℝ => fwdSumUpper a v (fwdSumLinearTop v)) =ᶠ[nhds k] fwdSumGModel a := by
    filter_upwards [eventually_lt_nhds hk] with v hv
    exact fse_G_model ha hv
  exact (fse_G_model_hasDerivAt (by linarith : k ≠ 1)).congr_of_eventuallyEq heq

theorem fwdSumGFirst_hasDerivAt {a k : ℝ} (hk : k ≠ 1) :
    HasDerivAt (fwdSumGFirst a) (fwdSumGSecond a k) k := by
  convert
    ((((((fwdPole1_hasDerivAt fwdSumG0Poly hk).add
      ((fwdPole1_hasDerivAt fwdSumGQ1Poly hk).const_mul a)).add
      ((fwdPole1_hasDerivAt fwdSumGQ2Poly hk).const_mul (a^2))).add
      ((fwdPole1_hasDerivAt fwdSumGQ3Poly hk).const_mul (a^3))).add
      ((fwdPole1_hasDerivAt fwdSumGQ4Poly hk).const_mul (a^4))).add
      ((fwdPole1_hasDerivAt fwdSumGAPoly hk).const_mul (1/(1-a)-1))).sub
      ((fwdPole1_hasDerivAt fwdSumGDPolePoly hk).const_mul (1/(1-a)^2-1)) using 1 <;> rfl

end SmoothedOctagon

namespace SmoothedOctagon
open Set Real Polynomial Filter

/-- Clearing the fourth reciprocal denominator in the second derivative, with factors unexpanded. -/
noncomputable def fwdSumPoleSecondNum (P : Polynomial ℝ) : Polynomial ℝ :=
  (1-X)^2*P.derivative.derivative+4*(1-X)*P.derivative+6*P
noncomputable def fwdSumUpperPPoly : Polynomial ℝ :=
  (fwdSumPoleSecondNum fwdSumGAPoly).comp (1-X)
noncomputable def fwdSumUpperDPoly : Polynomial ℝ :=
  (fwdSumPoleSecondNum fwdSumGQ1Poly).comp (1-X)+fwdSumUpperPPoly-C (15/2)*X
noncomputable def fwdSumUpperCPoly : Polynomial ℝ :=
  -2*((fwdSumPoleSecondNum fwdSumGQ2Poly).comp (1-X))
noncomputable def fwdSumUpperP (r : ℝ) : ℝ := fwdSumUpperPPoly.eval r
noncomputable def fwdSumUpperD (r : ℝ) : ℝ := fwdSumUpperDPoly.eval r
noncomputable def fwdSumUpperC (r : ℝ) : ℝ := fwdSumUpperCPoly.eval r

private theorem fse_secondNum_eval (P : Polynomial ℝ) {k : ℝ} (hk : k ≠ 1) :
    (fwdSumPoleSecondNum P).eval k = (1-k)^4*fwdPole2 P k := by
  unfold fwdSumPoleSecondNum fwdPole2
  simp
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]

private theorem fse_secondNum_reversed (P : Polynomial ℝ) {k : ℝ} (hk : k ≠ 1) :
    ((fwdSumPoleSecondNum P).comp (1-X)).eval (1-k) = (1-k)^4*fwdPole2 P k := by
  rw [Polynomial.eval_comp]
  have hh : ((1-X:Polynomial ℝ).eval (1-k)) = k := by simp
  rw [hh]
  exact fse_secondNum_eval P hk

theorem fwdSumUpperP_bridge {k : ℝ} (hk : k ≠ 1) :
    (1-k)^4*fwdPole2 fwdSumGAPoly k = fwdSumUpperP (1-k) := by
  unfold fwdSumUpperP fwdSumUpperPPoly
  exact (fse_secondNum_reversed fwdSumGAPoly hk).symm

theorem fwdSumUpperD_bridge {k : ℝ} (hk : k ≠ 1) :
    (1-k)^4*fwdPole2 fwdSumGQ1Poly k+fwdSumUpperP (1-k)-(15/2)*(1-k) =
      fwdSumUpperD (1-k) := by
  unfold fwdSumUpperD fwdSumUpperDPoly
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  rw [fse_secondNum_reversed fwdSumGQ1Poly hk]
  rfl

theorem fwdSumUpperC_bridge {k : ℝ} (hk : k ≠ 1) :
    -2*(1-k)^4*fwdPole2 fwdSumGQ2Poly k = fwdSumUpperC (1-k) := by
  unfold fwdSumUpperC fwdSumUpperCPoly
  simp only [Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_ofNat]
  rw [fse_secondNum_reversed fwdSumGQ2Poly hk]
  ring

/-- The three derivative identities are those of the actual pole and central-row functions. -/
theorem fwdSumUpperP_second_identity (r : ℝ) :
    fwdSumUpperPPoly.derivative.derivative.eval r = (200/3)*r^2*(44-25*r) := by
  unfold fwdSumUpperPPoly fwdSumPoleSecondNum fwdSumGAPoly
    fwdSumSimplePoleCleared fwdSumTauPoly
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

theorem fwdSumUpperD_second_identity (r : ℝ) :
    fwdSumUpperDPoly.derivative.derivative.eval r = r^2*((5000/3)*r-164) := by
  unfold fwdSumUpperDPoly fwdSumUpperPPoly fwdSumPoleSecondNum fwdSumGAPoly
    fwdSumSimplePoleCleared fwdSumGQ1Poly fwdSumT1Prod fwdSumTauPoly
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

theorem fwdSumUpperC_second_identity (r : ℝ) :
    fwdSumUpperCPoly.derivative.derivative.eval r = (10000/3)*r^2 := by
  unfold fwdSumUpperCPoly fwdSumPoleSecondNum fwdSumGQ2Poly fwdSumT2Prod fwdSumTauPoly
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

private theorem fse_poly_convex (P : Polynomial ℝ) {lo hi : ℝ}
    (hsecond : ∀ r ∈ Icc lo hi, 0 ≤ P.derivative.derivative.eval r) :
    ConvexOn ℝ (Icc lo hi) (fun r : ℝ => P.eval r) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc lo hi)
    (f' := fun r : ℝ => P.derivative.eval r) (f'' := fun r : ℝ => P.derivative.derivative.eval r)
  · intro r _; exact (P.hasDerivAt r).continuousAt.continuousWithinAt
  · intro r _; exact (P.hasDerivAt r).hasDerivWithinAt
  · intro r _; exact (P.derivative.hasDerivAt r).hasDerivWithinAt
  · intro r hr; exact hsecond r (interior_subset hr)

theorem fwdSumUpperP_lt {r : ℝ} (hr : r ∈ Icc (4/5:ℝ) (23/25)) : fwdSumUpperP r < 75 := by
  have hc := fse_poly_convex fwdSumUpperPPoly (lo := (4/5:ℝ)) (hi := 23/25) (by
    intro x hx
    rw [fwdSumUpperP_second_identity]
    exact mul_nonneg (by positivity) (by linarith only [hx.2]))
  have hmax := fse_convex_le_max hc hr
  have hleft : fwdSumUpperPPoly.eval (4/5) < 75 := by
    norm_num [fwdSumUpperPPoly,fwdSumPoleSecondNum,fwdSumGAPoly,fwdSumSimplePoleCleared,
      fwdSumTauPoly,Polynomial.derivative_comp,Polynomial.derivative_mul,Polynomial.derivative_pow]
  have hright : fwdSumUpperPPoly.eval (23/25) < 75 := by
    norm_num [fwdSumUpperPPoly,fwdSumPoleSecondNum,fwdSumGAPoly,fwdSumSimplePoleCleared,
      fwdSumTauPoly,Polynomial.derivative_comp,Polynomial.derivative_mul,Polynomial.derivative_pow]
  exact lt_of_le_of_lt hmax (max_lt hleft hright)

theorem fwdSumUpperD_lt {r : ℝ} (hr : r ∈ Icc (4/5:ℝ) (23/25)) : fwdSumUpperD r < -7 := by
  have hc := fse_poly_convex fwdSumUpperDPoly (lo := (4/5:ℝ)) (hi := 23/25) (by
    intro x hx
    rw [fwdSumUpperD_second_identity]
    exact mul_nonneg (sq_nonneg _) (by linarith only [hx.1]))
  have hmax := fse_convex_le_max hc hr
  have hleft : fwdSumUpperDPoly.eval (4/5) < -7 := by
    norm_num [fwdSumUpperDPoly,fwdSumUpperPPoly,fwdSumPoleSecondNum,fwdSumGAPoly,
      fwdSumSimplePoleCleared,fwdSumGQ1Poly,fwdSumT1Prod,fwdSumTauPoly,
      Polynomial.derivative_comp,Polynomial.derivative_mul,Polynomial.derivative_pow]
  have hright : fwdSumUpperDPoly.eval (23/25) < -7 := by
    norm_num [fwdSumUpperDPoly,fwdSumUpperPPoly,fwdSumPoleSecondNum,fwdSumGAPoly,
      fwdSumSimplePoleCleared,fwdSumGQ1Poly,fwdSumT1Prod,fwdSumTauPoly,
      Polynomial.derivative_comp,Polynomial.derivative_mul,Polynomial.derivative_pow]
  exact lt_of_le_of_lt hmax (max_lt hleft hright)

noncomputable def fwdSumUpperCAdjustedPoly : Polynomial ℝ := fwdSumUpperCPoly-C 1000*X^2

theorem fwdSumUpperC_gt {r : ℝ} (hr : r ∈ Icc (4/5:ℝ) (23/25)) : 149 < fwdSumUpperC r := by
  have hc := fse_poly_convex fwdSumUpperCAdjustedPoly (lo := (4/5:ℝ)) (hi := 23/25) (by
    intro x hx
    have hid : fwdSumUpperCAdjustedPoly.derivative.derivative.eval x =
        fwdSumUpperCPoly.derivative.derivative.eval x-2000 := by
      norm_num [fwdSumUpperCAdjustedPoly,Polynomial.derivative_mul,Polynomial.derivative_pow]
    rw [hid,fwdSumUpperC_second_identity]
    have hsq : (4/5:ℝ)^2 ≤ x^2 := by gcongr; exact hx.1
    nlinarith only [hsq])
  have htan := fse_concave_tangent hc.neg
    (show (6/7:ℝ) ∈ Icc (4/5:ℝ) (23/25) by constructor <;> norm_num) hr
    (fwdSumUpperCAdjustedPoly.hasDerivAt (6/7)).neg
  simp [fwdSumUpperCAdjustedPoly,Polynomial.derivative_mul,Polynomial.derivative_pow] at htan
  have hquad : fwdSumUpperCPoly.eval (6/7)-
      (fwdSumUpperCPoly.derivative.eval (6/7))^2/4000 ≤ fwdSumUpperCPoly.eval r := by
    nlinarith only [htan,sq_nonneg (r-6/7+fwdSumUpperCPoly.derivative.eval (6/7)/2000)]
  have hmid : 149 < fwdSumUpperCPoly.eval (6/7)-
      (fwdSumUpperCPoly.derivative.eval (6/7))^2/4000 := by
    norm_num [fwdSumUpperCPoly,fwdSumPoleSecondNum,fwdSumGQ2Poly,fwdSumT2Prod,fwdSumTauPoly,
      Polynomial.derivative_comp,Polynomial.derivative_mul,Polynomial.derivative_pow]
  exact lt_of_lt_of_le hmid hquad

end SmoothedOctagon

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

noncomputable def fwdSumGSecondA (a k : ℝ) : ℝ :=
  fwdPole2 fwdSumGQ1Poly k+2*a*fwdPole2 fwdSumGQ2Poly k+
    3*a^2*fwdPole2 fwdSumGQ3Poly k+4*a^3*fwdPole2 fwdSumGQ4Poly k+
    fwdPole2 fwdSumGAPoly k/(1-a)^2-2*fwdPole2 fwdSumGDPolePoly k/(1-a)^3

theorem fwdSumGSecond_hasDerivAt_a {a k : ℝ} (ha : a < 1/2) :
    HasDerivAt (fun x : ℝ => fwdSumGSecond x k) (fwdSumGSecondA a k) a := by
  have hb : 0 < 1-a := by linarith
  apply HasDerivAt.congr_deriv
  · unfold fwdSumGSecond
    upper_shape_deriv
  · unfold fwdSumGSecondA
    norm_num [npowRec]
    field_simp
    ring

private theorem fse_GQ3_second {k : ℝ} (hk : k ≠ 1) :
    3*(1-k)^4*fwdPole2 fwdSumGQ3Poly k = 112-457*k := by
  unfold fwdPole2 fwdSumGQ3Poly fwdSumT3Prod fwdSumTauPoly
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring
private theorem fse_GQ4_second {k : ℝ} (hk : k ≠ 1) :
    4*(1-k)^4*fwdPole2 fwdSumGQ4Poly k = (896/9)*(1-k) := by
  unfold fwdPole2 fwdSumGQ4Poly fwdSumTauPoly
  simp [Polynomial.derivative_mul]
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring
private theorem fse_GD_second {k : ℝ} (hk : k ≠ 1) :
    2*(1-k)^4*fwdPole2 fwdSumGDPolePoly k = (15/2)*(1-k) := by
  unfold fwdPole2 fwdSumGDPolePoly
  simp [Polynomial.derivative_mul]
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring

/-- The mixed derivative combines its poles into the paper's natural P,D,C losses. -/
theorem fwdSumG_mixed_identity {k : ℝ} (hk : k ≠ 1) (a : ℝ) :
    (1-k)^4*fwdSumGSecondA a k = fwdSumUpperD (1-k)+
      (896/9)*(1-k)*a^3+(112-457*k)*a^2-fwdSumUpperC (1-k)*a+
      fwdSumUpperP (1-k)*(1/(1-a)^2-1)-(15/2)*(1-k)*(1/(1-a)^3-1) := by
  have hP := fwdSumUpperP_bridge hk
  have hD := fwdSumUpperD_bridge hk
  have hC := fwdSumUpperC_bridge hk
  have h3 := fse_GQ3_second hk
  have h4 := fse_GQ4_second hk
  have hd := fse_GD_second hk
  unfold fwdSumGSecondA
  linear_combination hD-a*hC+a^2*h3+a^3*h4+(1/(1-a)^2)*hP-(1/(1-a)^3)*hd

private theorem fse_inverse2_bound {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    0 ≤ 1/(1-a)^2-1 ∧ 1/(1-a)^2-1 ≤ (8/3)*a := by
  have hb : 0 < 1-a := by linarith
  have hb2 : (1-a)^2 ≤ 1 := by nlinarith only [ha,ha1]
  constructor
  · have hp : (1:ℝ) ≤ 1/(1-a)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hb)).mpr (by simpa only [one_mul] using hb2)
    linarith only [hp]
  · have hp : 0 ≤ a*(2-13*a+8*a^2)/3 :=
      div_nonneg (mul_nonneg ha (by nlinarith only [ha1,sq_nonneg a])) (by norm_num)
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith only [hp]

private theorem fse_inverse3_bound {a : ℝ} (_ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    3*a ≤ 1/(1-a)^3-1 := by
  have hb : 0 < 1-a := by linarith
  have hp : 0 ≤ a^2*(6-8*a+3*a^2) :=
    mul_nonneg (sq_nonneg a) (by nlinarith only [ha1,sq_nonneg a])
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ (pow_pos hb 3)).mpr
  nlinarith only [hp]

theorem fwdSumGSecondA_neg {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 2/25 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumGSecondA a k < 0 := by
  have hrbox : 1-k ∈ Icc (4/5:ℝ) (23/25) := by constructor <;> linarith
  have hP := fwdSumUpperP_lt hrbox
  have hD := fwdSumUpperD_lt hrbox
  have hC := fwdSumUpperC_gt hrbox
  obtain ⟨hinv0,hinv2⟩ := fse_inverse2_bound ha ha1
  have hinv3 := fse_inverse3_bound ha ha1
  have hPterm : fwdSumUpperP (1-k)*(1/(1-a)^2-1) ≤ 200*a := by
    have h1 := mul_le_mul_of_nonneg_right hP.le hinv0
    have h2 := mul_le_mul_of_nonneg_left hinv2 (by norm_num : (0:ℝ) ≤ 75)
    nlinarith only [h1,h2]
  have hCterm : -fwdSumUpperC (1-k)*a ≤ -149*a := by
    have hp := mul_le_mul_of_nonneg_right hC.le ha
    linarith only [hp]
  have hcube : a^3 ≤ a/49 := by
    have hsq : a^2 ≤ (1/7:ℝ)^2 := by gcongr
    have hp := mul_le_mul_of_nonneg_left hsq ha
    nlinarith only [hp]
  have hquad : a^2 ≤ a/7 := by nlinarith only [ha,ha1]
  have haterm : (896/9)*(1-k)*a^3 ≤ (100/49)*a := by
    have hcoef : (896/9:ℝ)*(1-k) ≤ 100 := by linarith only [hk]
    have hp := mul_le_mul_of_nonneg_right hcoef (pow_nonneg ha 3)
    nlinarith only [hp,hcube]
  have hbterm : (112-457*k)*a^2 ≤ (76/7)*a := by
    have hcoef : 112-457*k ≤ 76 := by linarith only [hk]
    have hp := mul_le_mul_of_nonneg_right hcoef (sq_nonneg a)
    nlinarith only [hp,hquad]
  have hnegterm : 18*a ≤ (15/2)*(1-k)*(1/(1-a)^3-1) := by
    have hcoef : (6:ℝ) ≤ (15/2)*(1-k) := by linarith only [hk1]
    have hp := mul_le_mul hcoef hinv3 (by positivity : (0:ℝ) ≤ 3*a)
      (by linarith only [hcoef] : (0:ℝ) ≤ (15/2)*(1-k))
    nlinarith only [hp]
  have hid := fwdSumG_mixed_identity (by linarith only [hk1] : k ≠ 1) a
  have htotal : (1-k)^4*fwdSumGSecondA a k < 0 := by
    nlinarith only [hid,hPterm,hD,hCterm,haterm,hbterm,hnegterm,ha,ha1]
  exact neg_of_mul_neg_right htotal (pow_nonneg (by linarith : 0 ≤ 1-k) 4)

theorem fwdSumG_center_second {k : ℝ} (hk : k ≠ 1) :
    fwdSumGSecond 0 k =
      -(40*k^4+80*k^2*(3-2*k)+(1-k))/(120*(1-k)^4) := by
  unfold fwdSumGSecond
  simp only [zero_mul,one_div_one,sub_zero,sub_self,add_zero]
  unfold fwdPole2 fwdSumG0Poly fwdSumClearedRow fwdSumTauPoly
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
  field_simp [sub_ne_zero.mpr (Ne.symm hk)]
  ring

theorem fwdSumGSecond_neg {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 2/25 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumGSecond a k < 0 := by
  have hmono := ff_le_of_deriv (f := fun x : ℝ => -fwdSumGSecond x k)
    (f' := fun x : ℝ => -fwdSumGSecondA x k) ha
    (fun x hx => (fwdSumGSecond_hasDerivAt_a (by linarith only [hx.2,ha1])).neg)
    (fun x hx => (neg_pos.mpr (fwdSumGSecondA_neg hx.1 (le_trans hx.2 ha1) hk hk1)).le)
  have hbound : fwdSumGSecond a k ≤ fwdSumGSecond 0 k := neg_le_neg_iff.mp hmono
  rw [fwdSumG_center_second (by linarith only [hk1])] at hbound
  have hnum : 0 < 40*k^4+80*k^2*(3-2*k)+(1-k) := by
    have hr : 0 < 1-k := by linarith only [hk1]
    have hp : 0 ≤ 80*k^2*(3-2*k) := mul_nonneg (by positivity) (by linarith only [hk1])
    nlinarith only [hr,hp,pow_nonneg (by linarith : 0 ≤ k) 4]
  have hr : 0 < 1-k := by linarith only [hk1]
  exact lt_of_le_of_lt hbound (div_neg_of_neg_of_pos (neg_neg_of_pos hnum) (by positivity))

theorem fwdSumG_concaveOn {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/7) :
    ConcaveOn ℝ (Icc (2/25:ℝ) (1/5)) (fun k : ℝ => fwdSumUpper a k (fwdSumLinearTop k)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (2/25) (1/5))
    (f' := fwdSumGFirst a) (f'' := fwdSumGSecond a)
  · intro k hk
    exact (fwdSumG_hasDerivAt (by linarith only [ha1])
      (by linarith only [hk.2])).continuousAt.continuousWithinAt
  · intro k hk
    exact (fwdSumG_hasDerivAt (by linarith only [ha1])
      (by have := (interior_subset hk).2; linarith)).hasDerivWithinAt
  · intro k hk
    exact (fwdSumGFirst_hasDerivAt
      (by have := (interior_subset hk).2; linarith)).hasDerivWithinAt
  · intro k hk
    exact (fwdSumGSecond_neg ha ha1 (interior_subset hk).1 (interior_subset hk).2).le


end SmoothedOctagon

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# S6 exact score and shape concavity

The score retains the fixed-row arctangents. Its three rational second-derivative
terms give strict concavity on the correlated interval `27R/31 ≤ T ≤ R`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The exact fixed-row angle contribution, with `c = 161/54`. -/
noncomputable def costLExact (z : ℝ) : ℝ :=
  z-((161/54)/sqrt 3)*arctan (z/sqrt 3)

/-- Exact-angle scalar score, with the two central-shear envelopes as parameters. -/
noncomputable def costBExact (R T u ZU ZL : ℝ) : ℝ :=
  costLExact R+costLExact T-
    ((1-4*u/(3+R^2))*R+(1-4*u/(3+T^2))*T)/2-
    ((1-4*u/(3+R^2))+(1-4*u/(3+T^2)))*ZU/8-
    (161/54)*((R^2-T^2)/(3+T^2))^2/(8*ZL)

/-- The derivative is taken from the original arctangent, with no angular approximation. -/
theorem costLExact_hasDerivAt (z : ℝ) :
    HasDerivAt costLExact (1-(161/54)/(3+z^2)) z := by
  have hs : 0 < sqrt (3:ℝ) := sqrt_pos.2 (by norm_num)
  have hs2 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have h := (hasDerivAt_id z).sub
    ((((hasDerivAt_id z).div_const (sqrt 3)).arctan).const_mul ((161/54)/sqrt 3))
  convert h using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [hs.ne']
    nlinarith only [hs2]

private lemma s6_frac1_d (T : ℝ) :
    HasDerivAt (fun T : ℝ => T/(3+T^2)) ((3-T^2)/(3+T^2)^2) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := (hasDerivAt_id' T).div ((hasDerivAt_pow 2 T).const_add 3) hd
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring
private lemma s6_frac1_dd (T : ℝ) :
    HasDerivAt (fun T : ℝ => (3-T^2)/(3+T^2)^2)
      (2*T*(T^2-9)/(3+T^2)^3) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hasDerivAt_pow 2 T).const_sub 3).div
    (((hasDerivAt_pow 2 T).const_add 3).pow 2) (pow_ne_zero 2 hd)
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring
private lemma s6_frac2_d (T : ℝ) :
    HasDerivAt (fun T : ℝ => 1/(3+T^2)) (-(2*T)/(3+T^2)^2) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := (hasDerivAt_const T (1:ℝ)).div ((hasDerivAt_pow 2 T).const_add 3) hd
  refine h.congr_deriv ?_
  norm_num
private lemma s6_frac2_dd (T : ℝ) :
    HasDerivAt (fun T : ℝ => -(2*T)/(3+T^2)^2)
      ((6*T^2-6)/(3+T^2)^3) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := (((hasDerivAt_id' T).const_mul 2).neg).div
    (((hasDerivAt_pow 2 T).const_add 3).pow 2) (pow_ne_zero 2 hd)
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring
private lemma s6_sq_d (R T : ℝ) :
    HasDerivAt (fun T : ℝ => ((R^2-T^2)/(3+T^2))^2)
      (-(4*T*(3+R^2)*(R^2-T^2))/(3+T^2)^3) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((((hasDerivAt_pow 2 T).const_sub (R^2)).div
    ((hasDerivAt_pow 2 T).const_add 3) hd).pow 2)
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring
private lemma s6_sq_dd (R T : ℝ) :
    HasDerivAt (fun T : ℝ => -(4*T*(3+R^2)*(R^2-T^2))/(3+T^2)^3)
      (4*(3+R^2)*(9*T^2-3*R^2+T^2*(5*R^2-3*T^2))/(3+T^2)^4) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have hn := ((((hasDerivAt_id' T).const_mul 4).mul_const (3+R^2)).mul
    ((hasDerivAt_pow 2 T).const_sub (R^2))).neg
  have h := hn.div (((hasDerivAt_pow 2 T).const_add 3).pow 3) (pow_ne_zero 3 hd)
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring

noncomputable def ssS6First (R u ZU ZL T : ℝ) : ℝ :=
  1-(161/54)/(3+T^2)-1/2+2*u*((3-T^2)/(3+T^2)^2)+
    (u*ZU/2)*(-(2*T)/(3+T^2)^2)-
    ((161/54)/(8*ZL))*(-(4*T*(3+R^2)*(R^2-T^2))/(3+T^2)^3)
noncomputable def ssS6Second (R u ZU ZL T : ℝ) : ℝ :=
  2*T*((161/54)*(3+T^2)+2*u*(T^2-9))/(3+T^2)^3+
    3*u*ZU*(T^2-1)/(3+T^2)^3-
    ((161/54)/(8*ZL))*(4*(3+R^2)*(9*T^2-3*R^2+T^2*(5*R^2-3*T^2))/(3+T^2)^4)

/-- Exact score derivative, for every `T`, since `3 + T²` is positive. -/
theorem costBExact_hasDerivAt (R u ZU ZL T : ℝ) :
    HasDerivAt ((fun T => costBExact R T u ZU ZL)) (ssS6First R u ZU ZL T) T := by
  let C := costLExact R-(1-4*u/(3+R^2))*R/2-(1-4*u/(3+R^2))*ZU/8-ZU/8
  have hf : (fun T => costBExact R T u ZU ZL) = fun T => C+
      (costLExact T-T/2+2*u*(T/(3+T^2))+(u*ZU/2)*(1/(3+T^2))-
        ((161/54)/(8*ZL))*((R^2-T^2)/(3+T^2))^2) := by
    funext T
    unfold costBExact
    dsimp [C]
    ring
  rw [hf]
  have h := (((((costLExact_hasDerivAt T).sub ((hasDerivAt_id' T).div_const 2)).add
    ((s6_frac1_d T).const_mul (2*u))).add ((s6_frac2_d T).const_mul (u*ZU/2))).sub
    ((s6_sq_d R T).const_mul ((161/54)/(8*ZL)))).const_add C
  exact h

theorem ssS6First_hasDerivAt (R u ZU ZL T : ℝ) :
    HasDerivAt (ssS6First R u ZU ZL) (ssS6Second R u ZU ZL T) T := by
  have he := (((s6_frac2_d T).const_mul (161/54)).const_sub 1).sub_const (1/2)
  have h := ((he.add ((s6_frac1_dd T).const_mul (2*u))).add
    ((s6_frac2_dd T).const_mul (u*ZU/2))).sub
    ((s6_sq_dd R T).const_mul ((161/54)/(8*ZL)))
  convert h using 1
  · funext z
    unfold ssS6First
    dsimp only [Pi.add_apply,Pi.sub_apply]
    ring
  · unfold ssS6Second
    field_simp
    ring


/-- The three displayed exact second derivatives have the required signs on
    the correlated interval; the reciprocal-envelope contribution may vanish. -/
theorem ssS6Second_neg {R T u ZU ZL : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hu : 3/4 ≤ u) (hZU : 0 ≤ ZU) (hZL : 0 < ZL)
    (hT : 27*R/31 ≤ T) (hT1 : T ≤ R) : ssS6Second R u ZU ZL T < 0 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hT0 : 0 < T := by linarith only [hR,hT]
  have hTlt : T < 1 := by linarith only [hT1,hR1]
  have hTq : T^2 < 1 := by nlinarith only [hT0,hTlt]
  have hTqR : T^2 ≤ R^2 := (sq_le_sq₀ hT0.le hR0.le).2 hT1
  have hTlow : (27*R/31)^2 ≤ T^2 := (sq_le_sq₀ (by positivity) hT0.le).2 hT
  have hTthird : R^2/3 < T^2 := by nlinarith only [hTlow,sq_pos_of_pos hR0]
  have hd : 0 < 3+T^2 := by positivity
  have hf : 2*T*((161/54)*(3+T^2)+2*u*(T^2-9))/(3+T^2)^3 < 0 := by
    have hup := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu)
      (show T^2-9 ≤ 0 by linarith only [hTq])
    have hn : (161/54)*(3+T^2)+2*u*(T^2-9) < 0 := by nlinarith only [hup,hTq]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hn) (by positivity)
  have hg : 3*u*ZU*(T^2-1)/(3+T^2)^3 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (by linarith only [hTq])) (by positivity)
  have hν : 0 < 4*(3+R^2)*(9*T^2-3*R^2+T^2*(5*R^2-3*T^2))/(3+T^2)^4 := by
    have hp := mul_nonneg (sq_nonneg T) (show 0 ≤ 5*R^2-3*T^2 by nlinarith only [hTqR,sq_nonneg R])
    have hn : 0 < 9*T^2-3*R^2+T^2*(5*R^2-3*T^2) := by nlinarith only [hp,hTthird]
    exact div_pos (mul_pos (by positivity) hn) (by positivity)
  have hlast := mul_pos (show 0 < (161/54:ℝ)/(8*ZL) by positivity) hν
  unfold ssS6Second
  linarith only [hf,hg,hlast]

/-- The exact score's second derivative is the sum of the three rational kernels. -/
theorem costBExact_deriv2 (R T u ZU ZL : ℝ) :
    (deriv^[2] (fun T => costBExact R T u ZU ZL)) T = ssS6Second R u ZU ZL T := by
  have hf : deriv (fun T => costBExact R T u ZU ZL) = ssS6First R u ZU ZL := by
    funext T
    exact (costBExact_hasDerivAt R u ZU ZL T).deriv
  change deriv (deriv (fun T => costBExact R T u ZU ZL)) T = _
  rw [hf]
  exact (ssS6First_hasDerivAt R u ZU ZL T).deriv

/-- Strict concavity of the exact-angle score on the correlated physical
    interval. No upper norm cap or switch ceiling is needed for this calculus. -/
theorem costBExact_strictConcaveOn {R u ZU ZL : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hu : 3/4 ≤ u) (hZU : 0 ≤ ZU) (hZL : 0 < ZL) :
    StrictConcaveOn ℝ (Icc (27*R/31) R) (fun T => costBExact R T u ZU ZL) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Icc _ _)
    (fun T _ => (costBExact_hasDerivAt R u ZU ZL T).continuousAt.continuousWithinAt)
  intro T hT
  rw [costBExact_deriv2]
  exact ssS6Second_neg hR hR1 hu hZU hZL hT.1 hT.2

end SmoothedOctagon

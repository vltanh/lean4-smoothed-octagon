module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Gate S6 helper: concavity of the polynomial bound in the angle coordinate

At fixed `R`, `d` and incoming norm `u ≥ 3/4`, the polynomial bound `𝓑(u; R, T, d)` is concave in
the angle coordinate `T` on `[9/31, 7/19]`: it is
`f(T) + Z_U g(T) - (c/(8Z_L))((R² - T²)/(3 + T²))²` plus a constant, with `f'' < 0`, `g'' < 0`
and the last square convex.

## Main API

* `hs6_B_concaveOn`: concavity on `[9/31, 7/19]`, for the bound written out with parameters
  `R, u, Z_U, Z_L`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- The derivative of `T/(3 + T²)`. -/
theorem hs6_d_frac1 (T : ℝ) :
    HasDerivAt (fun T : ℝ => T / (3 + T ^ 2)) ((3 - T ^ 2) / (3 + T ^ 2) ^ 2) T := by
  have h3 : (3 + T ^ 2) ≠ 0 := by positivity
  have := (hasDerivAt_id' T).fun_div ((hasDerivAt_pow 2 T).const_add 3) h3
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The derivative of `(3 - T²)/(3 + T²)²`. -/
theorem hs6_d_frac1' (T : ℝ) :
    HasDerivAt (fun T : ℝ => (3 - T ^ 2) / (3 + T ^ 2) ^ 2) (2 * T * (T ^ 2 - 9) / (3 + T ^ 2) ^ 3) T := by
  have h3 : (3 + T ^ 2) ≠ 0 := by positivity
  have := ((hasDerivAt_pow 2 T).const_sub 3).fun_div (((hasDerivAt_pow 2 T).const_add 3).fun_pow 2)
    (pow_ne_zero 2 h3)
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The derivative of `1/(3 + T²)`. -/
theorem hs6_d_frac2 (T : ℝ) :
    HasDerivAt (fun T : ℝ => 1 / (3 + T ^ 2)) (-(2 * T) / (3 + T ^ 2) ^ 2) T := by
  have h3 : (3 + T ^ 2) ≠ 0 := by positivity
  have := (hasDerivAt_const T (1 : ℝ)).fun_div ((hasDerivAt_pow 2 T).const_add 3) h3
  refine this.congr_deriv ?_
  norm_num

/-- The derivative of `-2T/(3 + T²)²`. -/
theorem hs6_d_frac2' (T : ℝ) :
    HasDerivAt (fun T : ℝ => -(2 * T) / (3 + T ^ 2) ^ 2) ((6 * T ^ 2 - 6) / (3 + T ^ 2) ^ 3) T := by
  have h3 : (3 + T ^ 2) ≠ 0 := by positivity
  have := ((hasDerivAt_id' T).const_mul 2).fun_neg.fun_div (((hasDerivAt_pow 2 T).const_add 3).fun_pow 2)
    (pow_ne_zero 2 h3)
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The derivative of `((R² - T²)/(3 + T²))²`. -/
theorem hs6_d_sq (R T : ℝ) :
    HasDerivAt (fun T : ℝ => ((R ^ 2 - T ^ 2) / (3 + T ^ 2)) ^ 2)
      (-(4 * T * (3 + R ^ 2) * (R ^ 2 - T ^ 2)) / (3 + T ^ 2) ^ 3) T := by
  have h3 : (3 + T ^ 2) ≠ 0 := by positivity
  have := (((hasDerivAt_pow 2 T).const_sub (R ^ 2)).fun_div ((hasDerivAt_pow 2 T).const_add 3) h3).fun_pow 2
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The derivative of `-4T(3 + R²)(R² - T²)/(3 + T²)³`. -/
theorem hs6_d_sq' (R T : ℝ) :
    HasDerivAt (fun T : ℝ => -(4 * T * (3 + R ^ 2) * (R ^ 2 - T ^ 2)) / (3 + T ^ 2) ^ 3)
      (4 * (3 + R ^ 2) * (9 * T ^ 2 + 5 * R ^ 2 * T ^ 2 - 3 * R ^ 2 - 3 * T ^ 4) /
        (3 + T ^ 2) ^ 4) T := by
  have h3 : (3 + T ^ 2) ≠ 0 := by positivity
  have hn : HasDerivAt (fun T : ℝ => -(4 * T * (3 + R ^ 2) * (R ^ 2 - T ^ 2)))
      (-(4 * (3 + R ^ 2) * (R ^ 2 - 3 * T ^ 2))) T := by
    have := (((hasDerivAt_id' T).const_mul (4 : ℝ)).mul_const (3 + R ^ 2)).mul
      ((hasDerivAt_pow 2 T).const_sub (R ^ 2))
    refine this.fun_neg.congr_deriv ?_
    push_cast; ring
  have := hn.fun_div (((hasDerivAt_pow 2 T).const_add 3).fun_pow 3) (pow_ne_zero 3 h3)
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

/-- **Concavity of the polynomial bound in `T`**: for
`1/3 ≤ R ≤ 7/19`, `u ≥ 3/4`, `Z_U ≥ 0`, `Z_L > 0`, the bound
`𝓑(T) = L(R) + L(T) - (b₁R + b₂T)/2 - (b₁ + b₂)Z_U/8 - c((3 + R²)/(3 + T²) - 1)²/(8Z_L)`,
`b₁ = 1 - u/((3 + R²)/4)`, `b₂ = 1 - u/((3 + T²)/4)`, is concave on `[9/31, 7/19]`. -/
theorem hs6_B_concaveOn {R u ZU ZL : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hu : 3 / 4 ≤ u)
    (hZU : 0 ≤ ZU) (hZL : 0 < ZL) :
    ConcaveOn ℝ (Icc (9 / 31) (7 / 19)) (fun T : ℝ =>
      (R / 162 + 161 * R ^ 3 / 1458 - 161 * R ^ 5 / 7290) +
        (T / 162 + 161 * T ^ 3 / 1458 - 161 * T ^ 5 / 7290) -
        ((1 - u / ((3 + R ^ 2) / 4)) * R + (1 - u / ((3 + T ^ 2) / 4)) * T) / 2 -
        ((1 - u / ((3 + R ^ 2) / 4)) + (1 - u / ((3 + T ^ 2) / 4))) * ZU / 8 -
        161 / 54 * ((3 + R ^ 2) / (3 + T ^ 2) - 1) ^ 2 / (8 * ZL)) := by
  set K0 := (R / 162 + 161 * R ^ 3 / 1458 - 161 * R ^ 5 / 7290) -
    (1 - u / ((3 + R ^ 2) / 4)) * R / 2 - (1 - u / ((3 + R ^ 2) / 4)) * ZU / 8 - ZU / 8 with hK0
  set γ := 161 / 54 / (8 * ZL) with hγ
  have hfun : (fun T : ℝ =>
      (R / 162 + 161 * R ^ 3 / 1458 - 161 * R ^ 5 / 7290) +
        (T / 162 + 161 * T ^ 3 / 1458 - 161 * T ^ 5 / 7290) -
        ((1 - u / ((3 + R ^ 2) / 4)) * R + (1 - u / ((3 + T ^ 2) / 4)) * T) / 2 -
        ((1 - u / ((3 + R ^ 2) / 4)) + (1 - u / ((3 + T ^ 2) / 4))) * ZU / 8 -
        161 / 54 * ((3 + R ^ 2) / (3 + T ^ 2) - 1) ^ 2 / (8 * ZL)) =
      fun T : ℝ => K0 + ((T / 162 + 161 * T ^ 3 / 1458 - 161 * T ^ 5 / 7290 - T / 2) +
        2 * u * (T / (3 + T ^ 2)) + u * ZU / 2 * (1 / (3 + T ^ 2)) -
        γ * ((R ^ 2 - T ^ 2) / (3 + T ^ 2)) ^ 2) := by
    funext T
    have : (0 : ℝ) < 3 + T ^ 2 := by positivity
    rw [hK0, hγ]
    field_simp
    ring
  rw [hfun]
  have hp : ∀ T : ℝ, HasDerivAt (fun T : ℝ => T / 162 + 161 * T ^ 3 / 1458 - 161 * T ^ 5 / 7290 - T / 2)
      (1 / 162 + 161 * T ^ 2 / 486 - 161 * T ^ 4 / 1458 - 1 / 2) T := fun T => by
    have := ((((hasDerivAt_id' T).div_const 162).add (((hasDerivAt_pow 3 T).const_mul 161).div_const
      1458)).sub (((hasDerivAt_pow 5 T).const_mul 161).div_const 7290)).sub
      ((hasDerivAt_id' T).div_const 2)
    refine this.congr_deriv ?_
    push_cast; ring
  have hp' : ∀ T : ℝ, HasDerivAt (fun T : ℝ => 1 / 162 + 161 * T ^ 2 / 486 - 161 * T ^ 4 / 1458 - 1 / 2)
      (161 * T / 243 - 322 * T ^ 3 / 729) T := fun T => by
    have := (((((hasDerivAt_pow 2 T).const_mul 161).div_const 486).const_add (1 / 162)).sub
      (((hasDerivAt_pow 4 T).const_mul 161).div_const 1458)).sub_const (1 / 2)
    refine this.congr_deriv ?_
    push_cast; ring
  have hg : ∀ T : ℝ, HasDerivAt (fun T : ℝ => K0 + ((T / 162 + 161 * T ^ 3 / 1458 -
      161 * T ^ 5 / 7290 - T / 2) + 2 * u * (T / (3 + T ^ 2)) + u * ZU / 2 * (1 / (3 + T ^ 2)) -
        γ * ((R ^ 2 - T ^ 2) / (3 + T ^ 2)) ^ 2))
      ((1 / 162 + 161 * T ^ 2 / 486 - 161 * T ^ 4 / 1458 - 1 / 2) +
        2 * u * ((3 - T ^ 2) / (3 + T ^ 2) ^ 2) + u * ZU / 2 * (-(2 * T) / (3 + T ^ 2) ^ 2) -
        γ * (-(4 * T * (3 + R ^ 2) * (R ^ 2 - T ^ 2)) / (3 + T ^ 2) ^ 3)) T := fun T =>
    ((((hp T).add ((hs6_d_frac1 T).const_mul (2 * u))).add ((hs6_d_frac2 T).const_mul
      (u * ZU / 2))).sub ((hs6_d_sq R T).const_mul γ)).const_add K0
  have hg' : ∀ T : ℝ, HasDerivAt (fun T : ℝ => (1 / 162 + 161 * T ^ 2 / 486 - 161 * T ^ 4 / 1458 - 1 / 2) +
        2 * u * ((3 - T ^ 2) / (3 + T ^ 2) ^ 2) + u * ZU / 2 * (-(2 * T) / (3 + T ^ 2) ^ 2) -
        γ * (-(4 * T * (3 + R ^ 2) * (R ^ 2 - T ^ 2)) / (3 + T ^ 2) ^ 3))
      ((161 * T / 243 - 322 * T ^ 3 / 729) + 2 * u * (2 * T * (T ^ 2 - 9) / (3 + T ^ 2) ^ 3) +
        u * ZU / 2 * ((6 * T ^ 2 - 6) / (3 + T ^ 2) ^ 3) -
        γ * (4 * (3 + R ^ 2) * (9 * T ^ 2 + 5 * R ^ 2 * T ^ 2 - 3 * R ^ 2 - 3 * T ^ 4) /
          (3 + T ^ 2) ^ 4)) T := fun T =>
    (((hp' T).add ((hs6_d_frac1' T).const_mul (2 * u))).add ((hs6_d_frac2' T).const_mul
      (u * ZU / 2))).sub ((hs6_d_sq' R T).const_mul γ)
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun T _ => (hg T).continuousAt.continuousWithinAt)
    (fun T _ => (hg T).hasDerivWithinAt) (fun T _ => (hg' T).hasDerivWithinAt) ?_
  intro T hT
  rw [interior_Icc] at hT
  obtain ⟨hT1, hT2⟩ := hT
  have hT0 : 0 < T := by linarith
  have hs1 : (9 / 31) ^ 2 < T ^ 2 := pow_lt_pow_left₀ hT1 (by norm_num) (by norm_num)
  have hs2 : T ^ 2 < (7 / 19) ^ 2 := pow_lt_pow_left₀ hT2 hT0.le (by norm_num)
  have hR2 : R ^ 2 ≤ (7 / 19) ^ 2 := pow_le_pow_left₀ (by linarith) hR' 2
  have h3 : 0 < 3 + T ^ 2 := by positivity
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  -- the cubic and secant part: `T(161/243 - 322T²/729 - 4u(9 - T²)/(3 + T²)³) < 0`
  have hA : 161 * T / 243 - 322 * T ^ 3 / 729 + 2 * u * (2 * T * (T ^ 2 - 9) / (3 + T ^ 2) ^ 3) < 0 := by
    have hc3 : (3 + T ^ 2) ^ 3 ≤ (3 + (7 / 19) ^ 2) ^ 3 := pow_le_pow_left₀ h3.le (by linarith) 3
    have hnum : 26 ≤ 4 * u * (9 - T ^ 2) := by nlinarith
    have hq : 161 / 243 < 4 * u * (9 - T ^ 2) / (3 + T ^ 2) ^ 3 := by
      rw [lt_div_iff₀ (by positivity)]; norm_num at hc3; nlinarith
    have e : 161 * T / 243 - 322 * T ^ 3 / 729 + 2 * u * (2 * T * (T ^ 2 - 9) / (3 + T ^ 2) ^ 3) =
        T * (161 / 243 - 322 * T ^ 2 / 729 - 4 * u * (9 - T ^ 2) / (3 + T ^ 2) ^ 3) := by
      field_simp; ring
    rw [e]
    apply mul_neg_of_pos_of_neg hT0
    nlinarith [sq_nonneg T]
  -- the `g` part is nonpositive, the convex square enters with a minus sign
  have hB : u * ZU / 2 * ((6 * T ^ 2 - 6) / (3 + T ^ 2) ^ 3) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith
  have hC : 0 ≤ γ * (4 * (3 + R ^ 2) * (9 * T ^ 2 + 5 * R ^ 2 * T ^ 2 - 3 * R ^ 2 - 3 * T ^ 4) /
      (3 + T ^ 2) ^ 4) := by
    apply mul_nonneg hγ0.le
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    have : T ^ 4 ≤ (7 / 19) ^ 2 * T ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg T)]
  linarith

end SmoothedOctagon

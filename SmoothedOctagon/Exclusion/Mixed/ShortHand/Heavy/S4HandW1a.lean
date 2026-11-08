module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandDefs

/-!
# W1, part a: the three partial derivatives of `Φ`

In the variables `x, b = β, a = α, u` (Lean order `x be al u`), with `S = 1 + x`, `X = x(x + 2)`,
`K = X + a²`, `B = a + b`, `D = hsDg x b a`, `E = hh46S4P x u`, `M = S²(S² - S + 1)`, `η = x - a`,
`F = E + u(K - 2D)`, the partial derivatives of `Φ = hh46S4PhiC x b a u` are

* `Φ_b = -(R₀)_b/7`, `(R₀)_b = (u - 1)/a + b/B² + 4ηF/K²`,
* `Φ_a = -(2w_a + (R - log)_a + (log y)_a)/7` with
  `w_a = ((2Du - E)·2B·K - 4a(M + uD² - DE))/K³`,
  `(R - log)_a = -(u - 1)b/a² + b/B² - 2aX/K² - (4uBK - 2a(2Du - E))/K²`,
  `(log y)_a = (X(2a + b) - a²b)/(aBK)`,
* `Φ_u = Γ_u - (R₀)_u/7`, `Γ_u = (4M - 2ES³)/(16X²)`,
  `(R₀)_u = 2(D² - DS³)/K² + B/a - (2D - S³)/K`,

and the `b`-derivative of `Φ_a` is `-(R₀)_{ab}/7`,
`(R₀)_{ab} = (1 - u)/a² - 2b/B³ - 4F/K² - 8uη(a + 2b)/K² - 16aηF/K³`.

## Main API

* `hl46W1Pb`, `hl46W1Wa`, `hl46W1Ra`, `hl46W1La`, `hl46W1Pa`, `hl46W1Pu`, `hl46W1Pab`.
* `hl46_w1_dg_be`, `hl46_w1_dg_al`: the partial derivatives of `D`.
* `hl46_w1_hasDerivAt_be`, `hl46_w1_hasDerivAt_al`, `hl46_w1_hasDerivAt_u`,
  `hl46_w1_hasDerivAt_Pa_be`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `Φ_b = -(R₀)_b/7`. -/
noncomputable def hl46W1Pb (x be al u : ℝ) : ℝ :=
  -((u - 1) / al + be / (al + be) ^ 2 +
    4 * (x - al) * (hh46S4P x u + u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al)) /
      (x * (x + 2) + al ^ 2) ^ 2) / 7

/-- `w_a`. -/
noncomputable def hl46W1Wa (x be al u : ℝ) : ℝ :=
  ((2 * hsDg x be al * u - hh46S4P x u) * (2 * (al + be)) * (x * (x + 2) + al ^ 2) -
    4 * al * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + hsDg x be al ^ 2 * u -
      hsDg x be al * hh46S4P x u)) / (x * (x + 2) + al ^ 2) ^ 3

/-- The `a`-derivative of the rational part of the residual other than `2w`. -/
noncomputable def hl46W1Ra (x be al u : ℝ) : ℝ :=
  -(u - 1) * be / al ^ 2 + be / (al + be) ^ 2 -
    2 * al * (x * (x + 2)) / (x * (x + 2) + al ^ 2) ^ 2 -
    (2 * u * (2 * (al + be)) * (x * (x + 2) + al ^ 2) -
      (2 * hsDg x be al * u - hh46S4P x u) * (2 * al)) / (x * (x + 2) + al ^ 2) ^ 2

/-- `(log y)_a = (X(2a + b) - a²b)/(aBK)`. -/
noncomputable def hl46W1La (x be al : ℝ) : ℝ :=
  (x * (x + 2) * (2 * al + be) - al ^ 2 * be) / (al * (al + be) * (x * (x + 2) + al ^ 2))

/-- `Φ_a`. -/
noncomputable def hl46W1Pa (x be al u : ℝ) : ℝ :=
  -(2 * hl46W1Wa x be al u + hl46W1Ra x be al u + hl46W1La x be al) / 7

/-- `Φ_u = Γ_u - (R₀)_u/7`. -/
noncomputable def hl46W1Pu (x be al u : ℝ) : ℝ :=
  (4 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - 2 * hh46S4P x u * (1 + x) ^ 3) /
      (16 * x ^ 2 * (x + 2) ^ 2) -
    (2 * (hsDg x be al ^ 2 - hsDg x be al * (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 +
      (al + be) / al - (2 * hsDg x be al - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2)) / 7

/-- `Φ_{ab} = -(R₀)_{ab}/7`. -/
noncomputable def hl46W1Pab (x be al u : ℝ) : ℝ :=
  -((1 - u) / al ^ 2 - 2 * be / (al + be) ^ 3 -
    4 * (hh46S4P x u + u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al)) / (x * (x + 2) + al ^ 2) ^ 2 -
    8 * u * (x - al) * (al + 2 * be) / (x * (x + 2) + al ^ 2) ^ 2 -
    16 * al * (x - al) * (hh46S4P x u + u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al)) /
      (x * (x + 2) + al ^ 2) ^ 3) / 7

/-! ### Derivatives in `b` -/

theorem hl46_w1_dg_be (x be al : ℝ) :
    HasDerivAt (fun be => hsDg x be al) (2 * al - 2 * x) be := by
  have := (((((hasDerivAt_id' be).const_mul (2 * al)).const_add (al ^ 2)).add_const 1).add_const
    (2 * x)).fun_sub (((hasDerivAt_id' be).const_mul 2).mul_const x)
  refine this.congr_deriv ?_
  ring

theorem hl46_w1_hasDerivAt_be {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    HasDerivAt (fun be => hh46S4PhiC x be al u) (hl46W1Pb x be al u) be := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB : 0 < al + be := by positivity
  have hD := hl46_w1_dg_be x be al
  have hW : HasDerivAt (fun be => hh46S4Wc x be al u)
      ((2 * hsDg x be al * u - hh46S4P x u) * (2 * al - 2 * x) / (x * (x + 2) + al ^ 2) ^ 2)
      be := by
    have := ((((hD.fun_pow 2).mul_const u).const_add
      ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))).fun_sub (hD.mul_const (hh46S4P x u))).div_const
      ((x * (x + 2) + al ^ 2) ^ 2)
    refine this.congr_deriv ?_
    push_cast
    ring
  have hlin : HasDerivAt (fun be : ℝ => al + be) 1 be := (hasDerivAt_id' be).const_add al
  have hR : HasDerivAt (fun be => hh46S4Rest x be al u)
      ((u - 1) / al - al / (al + be) ^ 2 - 2 * u * (2 * al - 2 * x) / (x * (x + 2) + al ^ 2))
      be := by
    have := ((((hlin.const_mul (u - 1)).div_const al).fun_add
      ((hasDerivAt_const be al).fun_div hlin hB.ne')).sub_const
      (al ^ 2 / (x * (x + 2) + al ^ 2))).fun_sub
      ((((hD.const_mul 2).mul_const u).sub_const (hh46S4P x u)).div_const (x * (x + 2) + al ^ 2))
    refine this.congr_deriv ?_
    field_simp
    ring
  have hy : 0 < 2 * al * (al + be) / (x * (x + 2) + al ^ 2) := by positivity
  have hL : HasDerivAt (fun be => log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)))
      (1 / (al + be)) be := by
    have := ((hlin.const_mul (2 * al)).div_const (x * (x + 2) + al ^ 2)).log hy.ne'
    refine this.congr_deriv ?_
    field_simp
  have := ((((hW.const_mul 2).sub_const (1 / 2)).fun_add hR).fun_add hL).div_const 7 |>.const_sub
    (hh46S4G x u)
  refine this.congr_deriv ?_
  unfold hl46W1Pb hh46S4P hsDg
  field_simp
  ring

/-! ### Derivatives in `a` -/

theorem hl46_w1_dg_al (x be al : ℝ) :
    HasDerivAt (fun al => hsDg x be al) (2 * al + 2 * be) al := by
  have := ((((hasDerivAt_pow 2 al).fun_add
    (((hasDerivAt_id' al).const_mul 2).mul_const be)).add_const 1).add_const (2 * x)).sub_const
    (2 * be * x)
  refine this.congr_deriv ?_
  push_cast
  ring

theorem hl46_w1_hasDerivAt_al {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    HasDerivAt (fun al => hh46S4PhiC x be al u) (hl46W1Pa x be al u) al := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB : 0 < al + be := by positivity
  have hD := hl46_w1_dg_al x be al
  have hKd : HasDerivAt (fun al => x * (x + 2) + al ^ 2) (2 * al) al := by
    have := (hasDerivAt_pow 2 al).const_add (x * (x + 2))
    refine this.congr_deriv ?_
    push_cast
    ring
  have hW : HasDerivAt (fun al => hh46S4Wc x be al u) (hl46W1Wa x be al u) al := by
    have := ((((hD.fun_pow 2).mul_const u).const_add
      ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))).fun_sub (hD.mul_const (hh46S4P x u))).fun_div
      (hKd.fun_pow 2) (by positivity)
    refine this.congr_deriv ?_
    unfold hl46W1Wa
    push_cast
    field_simp
    ring
  have hlin : HasDerivAt (fun al : ℝ => al + be) 1 al := (hasDerivAt_id' al).add_const be
  have hR : HasDerivAt (fun al => hh46S4Rest x be al u) (hl46W1Ra x be al u) al := by
    have := ((((hlin.const_mul (u - 1)).fun_div (hasDerivAt_id' al) hal.ne').fun_add
      ((hasDerivAt_id' al).fun_div hlin hB.ne')).fun_sub
      ((hasDerivAt_pow 2 al).fun_div hKd hK.ne')).fun_sub
      ((((hD.const_mul 2).mul_const u).sub_const (hh46S4P x u)).fun_div hKd hK.ne')
    refine this.congr_deriv ?_
    unfold hl46W1Ra
    push_cast
    field_simp
    ring
  have hy : 0 < 2 * al * (al + be) / (x * (x + 2) + al ^ 2) := by positivity
  have hL : HasDerivAt (fun al => log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)))
      (hl46W1La x be al) al := by
    have := ((((hasDerivAt_id' al).const_mul 2).fun_mul hlin).fun_div hKd hK.ne').log hy.ne'
    refine this.congr_deriv ?_
    unfold hl46W1La
    field_simp
    ring
  have := ((((hW.const_mul 2).sub_const (1 / 2)).fun_add hR).fun_add hL).div_const 7 |>.const_sub
    (hh46S4G x u)
  refine this.congr_deriv ?_
  unfold hl46W1Pa
  ring

/-! ### Derivative in `u` -/

theorem hl46_w1_hasDerivAt_u {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    HasDerivAt (fun u => hh46S4PhiC x be al u) (hl46W1Pu x be al u) u := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hP : HasDerivAt (fun u => hh46S4P x u) ((1 + x) ^ 3) u := by
    have := ((((hasDerivAt_id' u).sub_const 1).const_mul ((1 + x) ^ 3)).add_const
      (3 * (1 + x))).sub_const 1
    refine this.congr_deriv ?_
    ring
  have hG : HasDerivAt (fun u => hh46S4G x u)
      ((4 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - 2 * hh46S4P x u * (1 + x) ^ 3) /
        (16 * x ^ 2 * (x + 2) ^ 2)) u := by
    have := (((((hasDerivAt_id' u).const_mul 4).mul_const ((1 + x) ^ 2)).mul_const
      ((1 + x) ^ 2 - (1 + x) + 1)).fun_sub (hP.fun_pow 2)).div_const
      (16 * x ^ 2 * (x + 2) ^ 2)
    refine this.congr_deriv ?_
    push_cast
    ring
  have hW : HasDerivAt (fun u => hh46S4Wc x be al u)
      ((hsDg x be al ^ 2 - hsDg x be al * (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2) u := by
    have := ((((hasDerivAt_id' u).const_mul (hsDg x be al ^ 2)).const_add
      ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))).fun_sub (hP.const_mul (hsDg x be al))).div_const
      ((x * (x + 2) + al ^ 2) ^ 2)
    refine this.congr_deriv ?_
    ring
  have hR : HasDerivAt (fun u => hh46S4Rest x be al u)
      ((al + be) / al - (2 * hsDg x be al - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2)) u := by
    have := ((((((hasDerivAt_id' u).sub_const 1).mul_const (al + be)).div_const al).add_const
      (al / (al + be))).sub_const (al ^ 2 / (x * (x + 2) + al ^ 2))).fun_sub
      ((((hasDerivAt_id' u).const_mul (2 * hsDg x be al)).fun_sub hP).div_const
        (x * (x + 2) + al ^ 2))
    refine this.congr_deriv ?_
    ring
  have := hG.fun_sub (((((hW.const_mul 2).sub_const (1 / 2)).fun_add hR).add_const
    (log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)))).div_const 7)
  refine this.congr_deriv ?_
  unfold hl46W1Pu
  ring

/-! ### The `b`-derivative of `Φ_a` -/

theorem hl46_w1_hasDerivAt_Pa_be {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    HasDerivAt (fun be => hl46W1Pa x be al u) (hl46W1Pab x be al u) be := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB : 0 < al + be := by positivity
  have hD := hl46_w1_dg_be x be al
  have hlin : HasDerivAt (fun be : ℝ => al + be) 1 be := (hasDerivAt_id' be).const_add al
  have hW : HasDerivAt (fun be => hl46W1Wa x be al u)
      ((2 * (2 * al - 2 * x) * u * (2 * (al + be)) * (x * (x + 2) + al ^ 2) +
        (2 * hsDg x be al * u - hh46S4P x u) * 2 * (x * (x + 2) + al ^ 2) -
        4 * al * (2 * hsDg x be al * (2 * al - 2 * x) * u - (2 * al - 2 * x) * hh46S4P x u)) /
          (x * (x + 2) + al ^ 2) ^ 3) be := by
    have := (((((hD.const_mul 2).mul_const u).sub_const (hh46S4P x u)).fun_mul
      (hlin.const_mul 2)).mul_const (x * (x + 2) + al ^ 2)).fun_sub
      (((((hD.fun_pow 2).mul_const u).const_add
        ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))).fun_sub
        (hD.mul_const (hh46S4P x u))).const_mul (4 * al))
    have := this.div_const ((x * (x + 2) + al ^ 2) ^ 3)
    refine this.congr_deriv ?_
    push_cast
    ring
  have hR : HasDerivAt (fun be => hl46W1Ra x be al u)
      (-(u - 1) / al ^ 2 + (al - be) / (al + be) ^ 3 -
        (4 * u * (x * (x + 2) + al ^ 2) - (2 * al - 2 * x) * 2 * u * (2 * al)) /
          (x * (x + 2) + al ^ 2) ^ 2) be := by
    have h1 := (((hasDerivAt_id' be).const_mul (-(u - 1))).div_const (al ^ 2)).fun_add
      ((hasDerivAt_id' be).fun_div (hlin.fun_pow 2) (by positivity))
    have h2 := (((hlin.const_mul 2).const_mul (2 * u)).mul_const (x * (x + 2) + al ^ 2)).fun_sub
      ((((hD.const_mul 2).mul_const u).sub_const (hh46S4P x u)).mul_const (2 * al))
    have := (h1.sub_const (2 * al * (x * (x + 2)) / (x * (x + 2) + al ^ 2) ^ 2)).fun_sub
      (h2.div_const ((x * (x + 2) + al ^ 2) ^ 2))
    refine this.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hL : HasDerivAt (fun be => hl46W1La x be al) (-1 / (al + be) ^ 2) be := by
    have := (((hasDerivAt_id' be).const_add (2 * al)).const_mul (x * (x + 2))).fun_sub
      ((hasDerivAt_id' be).const_mul (al ^ 2)) |>.fun_div
      ((hlin.const_mul al).mul_const (x * (x + 2) + al ^ 2)) (by positivity)
    refine this.congr_deriv ?_
    field_simp
    ring
  have := (((hW.const_mul 2).fun_add hR).fun_add hL).fun_neg.div_const 7
  refine this.congr_deriv ?_
  unfold hl46W1Pab hh46S4P hsDg
  field_simp
  ring

end SmoothedOctagon

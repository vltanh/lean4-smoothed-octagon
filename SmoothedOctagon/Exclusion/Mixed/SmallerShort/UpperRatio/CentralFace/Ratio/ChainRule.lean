module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Defs

/-!
# Smaller-short window, upper ratio: the central x comparison, the chain rule

The chain rule along the central curve: for differentiable `b(x)`, `u(x)`
(slopes `ℓ`, `u_x`), with `a` fixed, the total x-derivatives of the pieces of the duration-tangent
tests `F₀`, `F₁` (`urcF0`, `urcF1`), in the atoms `S = 1 + x`, `K`, `B = a + b`, `D`,
`D_x = 2 + 2ℓ(a - x) - 2b`: with `h = w - 3/4 = H₀/K²` and `k = aB/K`,

* `w_x = H₁/K² - 4SH₀/K³` (`urcx_d_w`),
* `(ℛ + log(tk))_x = P_a/a + P_b/B² - P₁/K + P₂/K²` (`urcx_d_Rlog`),
* `((4 - 7k/2)h)_x = G₀H₁/K³ + C₀H₀/K⁴` (`urcx_d_gh0`),
* `((1/k + 1/4)h)_x = G₁H₁/(aBK²) + C₁H₀/(aB²K³)` (`urcx_d_gh1`),
* `(1/k)_x = Z/(aB²)`, `Z = 2SB - ℓK` (`urcx_d_T`).

Here `H₀, H₁, P_a, …` are the primitives of `Ratio/Defs` with the norm `u(x)` and the speed
`u_x` in place of the majorants `U`, `V`; every identity is checked in the abstract atoms.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

theorem urcx_d_K (a y : ℝ) : HasDerivAt (fun z => urcK z a) (2 * (1 + y)) y := by
  have h : HasDerivAt (fun z => urcK z a) _ y :=
    ((hasDerivAt_id' y).fun_mul ((hasDerivAt_id' y).add_const (2 : ℝ))).add_const (a ^ 2)
  refine h.congr_deriv ?_
  ring

theorem urcx_d_D {a y l : ℝ} {b : ℝ → ℝ} (hb : HasDerivAt b l y) :
    HasDerivAt (fun z => ssDg z (b z) a) (2 + 2 * l * (a - y) - 2 * b y) y := by
  have h := ((((hb.const_mul (2 * a)).const_add (a ^ 2)).add_const 1).fun_add
    ((hasDerivAt_id' y).const_mul (2 : ℝ))).fun_sub
      ((hb.const_mul (2 : ℝ)).fun_mul (hasDerivAt_id' y))
  convert h using 1
  · funext z
    unfold ssDg
    ring
  · ring

theorem urcx_d_E {y up : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u up y) :
    HasDerivAt (fun z => (1 + z) ^ 3 * (u z - 1) + 3 * (1 + z) - 1)
      (urcxE1 (1 + y) (u y) up) y := by
  have hS : HasDerivAt (fun z => 1 + z) 1 y := (hasDerivAt_id' y).const_add 1
  have h := (((hS.fun_pow 3).fun_mul (hu.sub_const 1)).fun_add (hS.const_mul (3 : ℝ))).sub_const 1
  convert h using 1
  unfold urcxE1
  push_cast
  ring

/-- **`w_x = H₁/K² - 4SH₀/K³`**. -/
theorem urcx_d_w {a y Dx up : ℝ} {b u : ℝ → ℝ} (hD : HasDerivAt (fun z => ssDg z (b z) a) Dx y)
    (hu : HasDerivAt u up y) (hK0 : urcK y a ≠ 0) :
    HasDerivAt (fun z => urcw z a (b z) (u z))
      (urcxH1 (1 + y) (urcK y a) (ssDg y (b y) a) Dx (u y) up / urcK y a ^ 2 -
        4 * (1 + y) * urcxH0 (1 + y) (urcK y a) (ssDg y (b y) a) (u y) / urcK y a ^ 3) y := by
  have hS : HasDerivAt (fun z => 1 + z) 1 y := (hasDerivAt_id' y).const_add 1
  have hM := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
  have hN := (hM.fun_add ((hD.fun_pow 2).fun_mul hu)).fun_sub (hD.fun_mul (urcx_d_E hu))
  have h : HasDerivAt (fun z => urcw z a (b z) (u z)) _ y :=
    hN.fun_div ((urcx_d_K a y).fun_pow 2) (pow_ne_zero 2 hK0)
  refine h.congr_deriv ?_
  generalize ssDg y (b y) a = D
  generalize urcK y a = K at hK0 ⊢
  generalize u y = w
  unfold urcxH0 urcxH1 urcxE0 urcxE1
  push_cast
  field_simp
  ring

theorem urcx_d_k {a y l : ℝ} {b : ℝ → ℝ} (hb : HasDerivAt b l y) (hK0 : urcK y a ≠ 0) :
    HasDerivAt (fun z => urck z a (b z))
      ((a * l * urcK y a - a * (a + b y) * (2 * (1 + y))) / urcK y a ^ 2) y := by
  have h : HasDerivAt (fun z => urck z a (b z)) _ y :=
    ((hb.const_add a).const_mul a).fun_div (urcx_d_K a y) hK0
  exact h

/-- **`(ℛ + log(tk))_x = P_a/a + P_b/B² - P₁/K + P₂/K²`**. -/
theorem urcx_d_Rlog {t a y l up : ℝ} {b u : ℝ → ℝ} (hb : HasDerivAt b l y)
    (hu : HasDerivAt u up y) (ha : a ≠ 0) (hB : a + b y ≠ 0) (hK0 : urcK y a ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun z => urcR z a (b z) (u z) + log (t * urck z a (b z)))
      (urcxQ a l (1 + y) (urcK y a) (a + b y) (ssDg y (b y) a) (2 + 2 * l * (a - y) - 2 * b y)
        (u y) up) y := by
  have hK := urcx_d_K a y
  have hD := urcx_d_D (a := a) hb
  have hBd : HasDerivAt (fun z => a + b z) l y := hb.const_add a
  have hk0 : t * urck y a (b y) ≠ 0 := by
    unfold urck
    exact mul_ne_zero ht (div_ne_zero (mul_ne_zero ha hB) hK0)
  have hlog := ((urcx_d_k (a := a) hb hK0).const_mul t).log hk0
  have hEL := (((hD.const_mul 2).fun_mul hu).fun_sub (urcx_d_E hu)).fun_div hK hK0
  have hR := (((((hu.sub_const 1).fun_mul hBd).div_const a).fun_add
    ((hasDerivAt_const y a).fun_div hBd hB)).add_const 1 |>.fun_sub
    ((hasDerivAt_const y (a ^ 2)).fun_div hK hK0)).fun_sub hEL
  have h : HasDerivAt (fun z => urcR z a (b z) (u z) + log (t * urck z a (b z))) _ y :=
    hR.fun_add hlog
  refine h.congr_deriv ?_
  unfold urck at hk0 ⊢
  generalize ssDg y (b y) a = D
  generalize urcK y a = K at hK0 hk0 ⊢
  generalize b y = c at hB hk0 ⊢
  generalize u y = w
  unfold urcxQ urcxPa urcxP1 urcxP2 urcxE0 urcxE1
  field_simp
  ring

/-- **`((4 - 7k/2)h)_x = G₀H₁/K³ + C₀H₀/K⁴`**. -/
theorem urcx_d_gh0 {a y l up : ℝ} {b u : ℝ → ℝ} (hb : HasDerivAt b l y)
    (hu : HasDerivAt u up y) (hK0 : urcK y a ≠ 0) :
    HasDerivAt (fun z => (4 - 7 * urck z a (b z) / 2) * (urcw z a (b z) (u z) - 3 / 4))
      (urcxG0 a (urcK y a) (a + b y) *
          urcxH1 (1 + y) (urcK y a) (ssDg y (b y) a) (2 + 2 * l * (a - y) - 2 * b y) (u y) up /
            urcK y a ^ 3 +
        urcxC0 a l (1 + y) (urcK y a) (a + b y) *
          urcxH0 (1 + y) (urcK y a) (ssDg y (b y) a) (u y) / urcK y a ^ 4) y := by
  have hw := urcx_d_w (urcx_d_D (a := a) hb) hu hK0
  have h := ((((urcx_d_k (a := a) hb hK0).const_mul 7).div_const 2).const_sub 4).fun_mul
    (hw.sub_const (3 / 4))
  refine h.congr_deriv ?_
  unfold urck urcw
  generalize ssDg y (b y) a = D
  generalize urcK y a = K at hK0 ⊢
  generalize b y = c
  generalize u y = w
  generalize 2 + 2 * l * (a - y) - 2 * c = Dx
  unfold urcxG0 urcxC0 urcxH0 urcxH1 urcxE0 urcxE1
  field_simp
  ring

/-- **`((1/k + 1/4)h)_x = G₁H₁/(aBK²) + C₁H₀/(aB²K³)`**. -/
theorem urcx_d_gh1 {a y l up : ℝ} {b u : ℝ → ℝ} (hb : HasDerivAt b l y)
    (hu : HasDerivAt u up y) (ha : a ≠ 0) (hB : a + b y ≠ 0) (hK0 : urcK y a ≠ 0) :
    HasDerivAt (fun z => (1 / urck z a (b z) + 1 / 4) * (urcw z a (b z) (u z) - 3 / 4))
      (urcxG1 a (urcK y a) (a + b y) *
          urcxH1 (1 + y) (urcK y a) (ssDg y (b y) a) (2 + 2 * l * (a - y) - 2 * b y) (u y) up /
            (a * (a + b y) * urcK y a ^ 2) +
        urcxC1 a l (1 + y) (urcK y a) (a + b y) *
          urcxH0 (1 + y) (urcK y a) (ssDg y (b y) a) (u y) /
            (a * (a + b y) ^ 2 * urcK y a ^ 3)) y := by
  have hw := urcx_d_w (urcx_d_D (a := a) hb) hu hK0
  have hk0 : urck y a (b y) ≠ 0 := by
    unfold urck
    exact div_ne_zero (mul_ne_zero ha hB) hK0
  have h := ((((hasDerivAt_const y (1 : ℝ)).fun_div (urcx_d_k (a := a) hb hK0) hk0).add_const
    (1 / 4)).fun_mul (hw.sub_const (3 / 4)))
  refine h.congr_deriv ?_
  unfold urck urcw at *
  generalize ssDg y (b y) a = D
  generalize urcK y a = K at hK0 hk0 ⊢
  generalize b y = c at hB hk0 ⊢
  generalize u y = w
  generalize 2 + 2 * l * (a - y) - 2 * c = Dx
  unfold urcxG1 urcxC1 urcxH0 urcxH1 urcxE0 urcxE1
  field_simp
  ring

/-- **`(Tφ)_x = φZ/(aB²)`**, `T = 1/k`, `Z = 2SB - ℓK`. -/
theorem urcx_d_T {a y l φ : ℝ} {b : ℝ → ℝ} (hb : HasDerivAt b l y) (ha : a ≠ 0)
    (hB : a + b y ≠ 0) (hK0 : urcK y a ≠ 0) :
    HasDerivAt (fun z => 1 / urck z a (b z) * φ)
      (φ * (urcxZ l (1 + y) (urcK y a) (a + b y) / (a * (a + b y) ^ 2))) y := by
  have hk0 : urck y a (b y) ≠ 0 := by
    unfold urck
    exact div_ne_zero (mul_ne_zero ha hB) hK0
  have h := ((hasDerivAt_const y (1 : ℝ)).fun_div (urcx_d_k (a := a) hb hK0) hk0).mul_const φ
  refine h.congr_deriv ?_
  unfold urck at *
  generalize urcK y a = K at hK0 hk0 ⊢
  generalize b y = c at hB hk0 ⊢
  unfold urcxZ
  field_simp
  ring

end SmoothedOctagon

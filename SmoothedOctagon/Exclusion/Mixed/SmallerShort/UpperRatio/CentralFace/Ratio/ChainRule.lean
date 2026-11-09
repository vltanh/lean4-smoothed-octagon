module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXDefs

/-!
# S2 hand signs: the central x comparison, the chain rule

The chain rule along the central curve: for differentiable `b(x)`, `u(x)`
(slopes `ℓ`, `u_x`), with `a` fixed, the total x-derivatives of the pieces of the duration-tangent
tests `F₀`, `F₁` (`hl2cF0`, `hl2cF1`), in the atoms `S = 1 + x`, `K`, `B = a + b`, `D`,
`D_x = 2 + 2ℓ(a - x) - 2b`: with `h = w - 3/4 = H₀/K²` and `k = aB/K`,

* `w_x = H₁/K² - 4SH₀/K³` (`hl2cx_d_w`),
* `(ℛ + log(tk))_x = P_a/a + P_b/B² - P₁/K + P₂/K²` (`hl2cx_d_Rlog`),
* `((4 - 7k/2)h)_x = G₀H₁/K³ + C₀H₀/K⁴` (`hl2cx_d_gh0`),
* `((1/k + 1/4)h)_x = G₁H₁/(aBK²) + C₁H₀/(aB²K³)` (`hl2cx_d_gh1`),
* `(1/k)_x = Z/(aB²)`, `Z = 2SB - ℓK` (`hl2cx_d_T`).

Here `H₀, H₁, P_a, …` are the primitives of `S2HandCenXDefs` with the norm `u(x)` and the speed
`u_x` in place of the majorants `U`, `V`; every identity is checked in the abstract atoms.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

theorem hl2cx_d_K (a y : ℝ) : HasDerivAt (fun z => hl2cK z a) (2 * (1 + y)) y := by
  have h : HasDerivAt (fun z => hl2cK z a) _ y :=
    ((hasDerivAt_id' y).fun_mul ((hasDerivAt_id' y).add_const (2 : ℝ))).add_const (a ^ 2)
  refine h.congr_deriv ?_
  ring

theorem hl2cx_d_D {a y l : ℝ} {b : ℝ → ℝ} (hb : HasDerivAt b l y) :
    HasDerivAt (fun z => hsDg z (b z) a) (2 + 2 * l * (a - y) - 2 * b y) y := by
  have h := ((((hb.const_mul (2 * a)).const_add (a ^ 2)).add_const 1).fun_add
    ((hasDerivAt_id' y).const_mul (2 : ℝ))).fun_sub
      ((hb.const_mul (2 : ℝ)).fun_mul (hasDerivAt_id' y))
  convert h using 1
  · funext z
    unfold hsDg
    ring
  · ring

theorem hl2cx_d_E {y up : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u up y) :
    HasDerivAt (fun z => (1 + z) ^ 3 * (u z - 1) + 3 * (1 + z) - 1)
      (hl2cxE1 (1 + y) (u y) up) y := by
  have hS : HasDerivAt (fun z => 1 + z) 1 y := (hasDerivAt_id' y).const_add 1
  have h := (((hS.fun_pow 3).fun_mul (hu.sub_const 1)).fun_add (hS.const_mul (3 : ℝ))).sub_const 1
  convert h using 1
  unfold hl2cxE1
  push_cast
  ring

/-- **`w_x = H₁/K² - 4SH₀/K³`**. -/
theorem hl2cx_d_w {a y Dx up : ℝ} {b u : ℝ → ℝ} (hD : HasDerivAt (fun z => hsDg z (b z) a) Dx y)
    (hu : HasDerivAt u up y) (hK0 : hl2cK y a ≠ 0) :
    HasDerivAt (fun z => hl2cw z a (b z) (u z))
      (hl2cxH1 (1 + y) (hl2cK y a) (hsDg y (b y) a) Dx (u y) up / hl2cK y a ^ 2 -
        4 * (1 + y) * hl2cxH0 (1 + y) (hl2cK y a) (hsDg y (b y) a) (u y) / hl2cK y a ^ 3) y := by
  have hS : HasDerivAt (fun z => 1 + z) 1 y := (hasDerivAt_id' y).const_add 1
  have hM := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
  have hN := (hM.fun_add ((hD.fun_pow 2).fun_mul hu)).fun_sub (hD.fun_mul (hl2cx_d_E hu))
  have h : HasDerivAt (fun z => hl2cw z a (b z) (u z)) _ y :=
    hN.fun_div ((hl2cx_d_K a y).fun_pow 2) (pow_ne_zero 2 hK0)
  refine h.congr_deriv ?_
  generalize hsDg y (b y) a = D
  generalize hl2cK y a = K at hK0 ⊢
  generalize u y = w
  unfold hl2cxH0 hl2cxH1 hl2cxE0 hl2cxE1
  push_cast
  field_simp
  ring

theorem hl2cx_d_k {a y l : ℝ} {b : ℝ → ℝ} (hb : HasDerivAt b l y) (hK0 : hl2cK y a ≠ 0) :
    HasDerivAt (fun z => hl2ck z a (b z))
      ((a * l * hl2cK y a - a * (a + b y) * (2 * (1 + y))) / hl2cK y a ^ 2) y := by
  have h : HasDerivAt (fun z => hl2ck z a (b z)) _ y :=
    ((hb.const_add a).const_mul a).fun_div (hl2cx_d_K a y) hK0
  exact h

/-- **`(ℛ + log(tk))_x = P_a/a + P_b/B² - P₁/K + P₂/K²`**. -/
theorem hl2cx_d_Rlog {t a y l up : ℝ} {b u : ℝ → ℝ} (hb : HasDerivAt b l y)
    (hu : HasDerivAt u up y) (ha : a ≠ 0) (hB : a + b y ≠ 0) (hK0 : hl2cK y a ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun z => hl2cR z a (b z) (u z) + log (t * hl2ck z a (b z)))
      (hl2cxQ a l (1 + y) (hl2cK y a) (a + b y) (hsDg y (b y) a) (2 + 2 * l * (a - y) - 2 * b y)
        (u y) up) y := by
  have hK := hl2cx_d_K a y
  have hD := hl2cx_d_D (a := a) hb
  have hBd : HasDerivAt (fun z => a + b z) l y := hb.const_add a
  have hk0 : t * hl2ck y a (b y) ≠ 0 := by
    unfold hl2ck
    exact mul_ne_zero ht (div_ne_zero (mul_ne_zero ha hB) hK0)
  have hlog := ((hl2cx_d_k (a := a) hb hK0).const_mul t).log hk0
  have hEL := (((hD.const_mul 2).fun_mul hu).fun_sub (hl2cx_d_E hu)).fun_div hK hK0
  have hR := (((((hu.sub_const 1).fun_mul hBd).div_const a).fun_add
    ((hasDerivAt_const y a).fun_div hBd hB)).add_const 1 |>.fun_sub
    ((hasDerivAt_const y (a ^ 2)).fun_div hK hK0)).fun_sub hEL
  have h : HasDerivAt (fun z => hl2cR z a (b z) (u z) + log (t * hl2ck z a (b z))) _ y :=
    hR.fun_add hlog
  refine h.congr_deriv ?_
  unfold hl2ck at hk0 ⊢
  generalize hsDg y (b y) a = D
  generalize hl2cK y a = K at hK0 hk0 ⊢
  generalize b y = c at hB hk0 ⊢
  generalize u y = w
  unfold hl2cxQ hl2cxPa hl2cxP1 hl2cxP2 hl2cxE0 hl2cxE1
  field_simp
  ring

/-- **`((4 - 7k/2)h)_x = G₀H₁/K³ + C₀H₀/K⁴`**. -/
theorem hl2cx_d_gh0 {a y l up : ℝ} {b u : ℝ → ℝ} (hb : HasDerivAt b l y)
    (hu : HasDerivAt u up y) (hK0 : hl2cK y a ≠ 0) :
    HasDerivAt (fun z => (4 - 7 * hl2ck z a (b z) / 2) * (hl2cw z a (b z) (u z) - 3 / 4))
      (hl2cxG0 a (hl2cK y a) (a + b y) *
          hl2cxH1 (1 + y) (hl2cK y a) (hsDg y (b y) a) (2 + 2 * l * (a - y) - 2 * b y) (u y) up /
            hl2cK y a ^ 3 +
        hl2cxC0 a l (1 + y) (hl2cK y a) (a + b y) *
          hl2cxH0 (1 + y) (hl2cK y a) (hsDg y (b y) a) (u y) / hl2cK y a ^ 4) y := by
  have hw := hl2cx_d_w (hl2cx_d_D (a := a) hb) hu hK0
  have h := ((((hl2cx_d_k (a := a) hb hK0).const_mul 7).div_const 2).const_sub 4).fun_mul
    (hw.sub_const (3 / 4))
  refine h.congr_deriv ?_
  unfold hl2ck hl2cw
  generalize hsDg y (b y) a = D
  generalize hl2cK y a = K at hK0 ⊢
  generalize b y = c
  generalize u y = w
  generalize 2 + 2 * l * (a - y) - 2 * c = Dx
  unfold hl2cxG0 hl2cxC0 hl2cxH0 hl2cxH1 hl2cxE0 hl2cxE1
  field_simp
  ring

/-- **`((1/k + 1/4)h)_x = G₁H₁/(aBK²) + C₁H₀/(aB²K³)`**. -/
theorem hl2cx_d_gh1 {a y l up : ℝ} {b u : ℝ → ℝ} (hb : HasDerivAt b l y)
    (hu : HasDerivAt u up y) (ha : a ≠ 0) (hB : a + b y ≠ 0) (hK0 : hl2cK y a ≠ 0) :
    HasDerivAt (fun z => (1 / hl2ck z a (b z) + 1 / 4) * (hl2cw z a (b z) (u z) - 3 / 4))
      (hl2cxG1 a (hl2cK y a) (a + b y) *
          hl2cxH1 (1 + y) (hl2cK y a) (hsDg y (b y) a) (2 + 2 * l * (a - y) - 2 * b y) (u y) up /
            (a * (a + b y) * hl2cK y a ^ 2) +
        hl2cxC1 a l (1 + y) (hl2cK y a) (a + b y) *
          hl2cxH0 (1 + y) (hl2cK y a) (hsDg y (b y) a) (u y) /
            (a * (a + b y) ^ 2 * hl2cK y a ^ 3)) y := by
  have hw := hl2cx_d_w (hl2cx_d_D (a := a) hb) hu hK0
  have hk0 : hl2ck y a (b y) ≠ 0 := by
    unfold hl2ck
    exact div_ne_zero (mul_ne_zero ha hB) hK0
  have h := ((((hasDerivAt_const y (1 : ℝ)).fun_div (hl2cx_d_k (a := a) hb hK0) hk0).add_const
    (1 / 4)).fun_mul (hw.sub_const (3 / 4)))
  refine h.congr_deriv ?_
  unfold hl2ck hl2cw at *
  generalize hsDg y (b y) a = D
  generalize hl2cK y a = K at hK0 hk0 ⊢
  generalize b y = c at hB hk0 ⊢
  generalize u y = w
  generalize 2 + 2 * l * (a - y) - 2 * c = Dx
  unfold hl2cxG1 hl2cxC1 hl2cxH0 hl2cxH1 hl2cxE0 hl2cxE1
  field_simp
  ring

/-- **`(Tφ)_x = φZ/(aB²)`**, `T = 1/k`, `Z = 2SB - ℓK`. -/
theorem hl2cx_d_T {a y l φ : ℝ} {b : ℝ → ℝ} (hb : HasDerivAt b l y) (ha : a ≠ 0)
    (hB : a + b y ≠ 0) (hK0 : hl2cK y a ≠ 0) :
    HasDerivAt (fun z => 1 / hl2ck z a (b z) * φ)
      (φ * (hl2cxZ l (1 + y) (hl2cK y a) (a + b y) / (a * (a + b y) ^ 2))) y := by
  have hk0 : hl2ck y a (b y) ≠ 0 := by
    unfold hl2ck
    exact div_ne_zero (mul_ne_zero ha hB) hK0
  have h := ((hasDerivAt_const y (1 : ℝ)).fun_div (hl2cx_d_k (a := a) hb hK0) hk0).mul_const φ
  refine h.congr_deriv ?_
  unfold hl2ck at *
  generalize hl2cK y a = K at hK0 hk0 ⊢
  generalize b y = c at hB hk0 ⊢
  unfold hl2cxZ
  field_simp
  ring

end SmoothedOctagon

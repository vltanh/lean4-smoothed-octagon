module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.CasimirPart

/-!
# Smaller-short window, Casimir floor: the norm coefficient of the cost and its `x`-slope

On the shape curve at `e = 13/5` (`a = 1 + 13d/5`, `B = a + x(1 + d)`, `K = x(x + 2) + a²`,
`D = a² + 2ab + 1 + 2x - 2bx`, `b = x(1 + d)`), the cost `r₁` is affine in the norm with
coefficient `ρ = (r₁)_u = T_u/(aBK)`,

`T_u = B²K + aB(S³ - 2D) + D(D - S³) = B((B - a)K + a(K - 2D)) + S³(aB - D) + D² > 0`

(by `D < aB`, `2D < K`). Its `x`-derivative along `b = x(1 + d)` is
`ρ_x = q/(aB²K²)` with `q = (T_u)_x BK - T_u(B_x K + BK_x)` (`Q = 78125q`); the
first and second `x`-derivatives of `T_u` are taken by the chain rule in the atoms
`B, K, D, S³` before any expansion (`cas_w3_Tu_deriv`, `cas_w3_Tu1_deriv`). Then
`78125q_x = J(d, x - 2)` and `78125q(2) = Q(2, d)` are explicit polynomials, both
positive by the monomial rule (discard positive `d`-terms, `d ≤ 1/19` in the negative ones), so
`q > 0` and `ρ_x > 0`.

## Main API

* Curve atoms `casW3B`, `casW3K`, `casW3D`, `casW3Dx`; `cas_w3_curve`.
* `casW3Tu`, `casW3Tu1`, `casW3Tu2` (atom level), `casW3TuC`, `casW3Tu1C`, `casW3Tu2C`,
  `casW3rho`, `casW3q`, `casW3J`, `casW3Q2`.
* `cas_w3_rho_pos`, `cas_w3_rho_deriv`, `cas_w3_q_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### The shape curve at `e = 13/5` -/

/-- `B = a + b = 1 + 13d/5 + x(1 + d)`. -/
noncomputable def casW3B (x d : ℝ) : ℝ := 1 + 13 / 5 * d + x * (1 + d)

/-- `K = x(x + 2) + a²`. -/
noncomputable def casW3K (x d : ℝ) : ℝ := x * (x + 2) + (1 + 13 / 5 * d) ^ 2

/-- `D = a² + 2ab + 1 + 2x - 2bx`. -/
noncomputable def casW3D (x d : ℝ) : ℝ := ssDg x (x * (1 + d)) (1 + 13 / 5 * d)

/-- `D_x = 2a(1 + d) + 2 - 4x(1 + d)`. -/
noncomputable def casW3Dx (x d : ℝ) : ℝ := 2 * (1 + 13 / 5 * d) * (1 + d) + 2 - 4 * x * (1 + d)

theorem cas_w3_B_dx (x d : ℝ) : HasDerivAt (fun x => casW3B x d) (1 + d) x := by
  have := ((hasDerivAt_id' x).mul_const (1 + d)).const_add (1 + 13 / 5 * d)
  refine this.congr_deriv ?_
  ring

theorem cas_w3_K_dx (x d : ℝ) : HasDerivAt (fun x => casW3K x d) (2 * x + 2) x := by
  have := ((hasDerivAt_id' x).fun_mul ((hasDerivAt_id' x).add_const 2)).add_const
    ((1 + 13 / 5 * d) ^ 2)
  refine this.congr_deriv ?_
  ring

theorem cas_w3_D_dx (x d : ℝ) : HasDerivAt (fun x => casW3D x d) (casW3Dx x d) x := by
  have hb : HasDerivAt (fun x : ℝ => x * (1 + d)) (1 + d) x := by
    simpa using (hasDerivAt_id' x).mul_const (1 + d)
  have := ((((hb.const_mul (2 * (1 + 13 / 5 * d))).const_add ((1 + 13 / 5 * d) ^ 2)).add_const
    1).fun_add ((hasDerivAt_id' x).const_mul 2)).fun_sub ((hb.const_mul 2).fun_mul (hasDerivAt_id' x))
  refine this.congr_deriv ?_
  unfold casW3Dx
  ring

theorem cas_w3_K1_dx (x : ℝ) : HasDerivAt (fun x : ℝ => 2 * x + 2) 2 x := by
  simpa using ((hasDerivAt_id' x).const_mul 2).add_const 2

theorem cas_w3_Dx_dx (x d : ℝ) : HasDerivAt (fun x => casW3Dx x d) (-4 * (1 + d)) x := by
  have := (((hasDerivAt_id' x).const_mul 4).mul_const (1 + d)).const_sub
    (2 * (1 + 13 / 5 * d) * (1 + d) + 2)
  refine this.congr_deriv ?_
  ring

theorem cas_w3_S3_dx (x : ℝ) : HasDerivAt (fun x : ℝ => (1 + x) ^ 3) (3 * (1 + x) ^ 2) x := by
  have := ((hasDerivAt_id' x).const_add 1).fun_pow 3
  refine this.congr_deriv ?_
  push_cast
  ring

theorem cas_w3_S1_dx (x : ℝ) : HasDerivAt (fun x : ℝ => 3 * (1 + x) ^ 2) (6 * (1 + x)) x := by
  have := (((hasDerivAt_id' x).const_add 1).fun_pow 2).const_mul 3
  refine this.congr_deriv ?_
  push_cast
  ring

/-- Elementary bounds on the curve: `1 ≤ a ≤ B`, `0 < K`, `2D < K`, `D ≤ aB`. -/
theorem cas_w3_curve {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    1 ≤ 1 + 13 / 5 * d ∧ 1 + 13 / 5 * d ≤ casW3B x d ∧ 0 < casW3K x d ∧
      2 * casW3D x d < casW3K x d ∧ casW3D x d ≤ (1 + 13 / 5 * d) * casW3B x d := by
  have hxd : 0 ≤ x * d := mul_nonneg (by linarith) hd
  unfold casW3B casW3K casW3D ssDg
  refine ⟨by linarith, by nlinarith, by positivity, ?_, ?_⟩
  · nlinarith [mul_nonneg hxd (by linarith : (0 : ℝ) ≤ x - (1 + 13 / 5 * d)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 108 / 95 - (1 + 13 / 5 * d)),
      mul_nonneg hd (by linarith : (0 : ℝ) ≤ 1 / 19 - d), mul_nonneg hd hd]
  · nlinarith [mul_nonneg hxd (by linarith : (0 : ℝ) ≤ 2 * x - 1 - 13 / 5 * d), mul_nonneg hd hd]

/-! ### The norm coefficient `T_u` and its chain-rule derivatives -/

/-- `T_u = B²K + aB(S³ - 2D) + D(D - S³)`, in the atoms `a, B, K, D, S³`. -/
noncomputable def casW3Tu (a B K D S3 : ℝ) : ℝ := B ^ 2 * K + a * B * (S3 - 2 * D) + D * (D - S3)

/-- The chain-rule derivative of `T_u` (`a` constant). -/
noncomputable def casW3Tu1 (a B K D S3 B1 K1 D1 S1 : ℝ) : ℝ :=
  (2 * B * K + a * (S3 - 2 * D)) * B1 + B ^ 2 * K1 + (-(2 * a * B) + 2 * D - S3) * D1 +
    (a * B - D) * S1

/-- The chain-rule second derivative of `T_u` (`a` constant). -/
noncomputable def casW3Tu2 (a B K D S3 B1 K1 D1 S1 B2 K2 D2 S2 : ℝ) : ℝ :=
  (2 * B1 * K + 2 * B * K1 + a * (S1 - 2 * D1)) * B1 + (2 * B * K + a * (S3 - 2 * D)) * B2 +
    2 * B * B1 * K1 + B ^ 2 * K2 + (-(2 * a * B1) + 2 * D1 - S1) * D1 +
    (-(2 * a * B) + 2 * D - S3) * D2 + (a * B1 - D1) * S1 + (a * B - D) * S2

theorem cas_w3_Tu_deriv {fB fK fD fS : ℝ → ℝ} {a B1 K1 D1 S1 x : ℝ} (hB : HasDerivAt fB B1 x)
    (hK : HasDerivAt fK K1 x) (hD : HasDerivAt fD D1 x) (hS : HasDerivAt fS S1 x) :
    HasDerivAt (fun x => casW3Tu a (fB x) (fK x) (fD x) (fS x))
      (casW3Tu1 a (fB x) (fK x) (fD x) (fS x) B1 K1 D1 S1) x := by
  have := (((hB.fun_pow 2).fun_mul hK).fun_add ((hB.const_mul a).fun_mul
    (hS.fun_sub (hD.const_mul 2)))).fun_add (hD.fun_mul (hD.fun_sub hS))
  refine this.congr_deriv ?_
  unfold casW3Tu1
  push_cast
  ring

theorem cas_w3_Tu1_deriv {fB fK fD fS fB1 fK1 fD1 fS1 : ℝ → ℝ} {a B2 K2 D2 S2 x : ℝ}
    (hB : HasDerivAt fB (fB1 x) x) (hK : HasDerivAt fK (fK1 x) x) (hD : HasDerivAt fD (fD1 x) x)
    (hS : HasDerivAt fS (fS1 x) x) (hB1 : HasDerivAt fB1 B2 x) (hK1 : HasDerivAt fK1 K2 x)
    (hD1 : HasDerivAt fD1 D2 x) (hS1 : HasDerivAt fS1 S2 x) :
    HasDerivAt (fun x => casW3Tu1 a (fB x) (fK x) (fD x) (fS x) (fB1 x) (fK1 x) (fD1 x) (fS1 x))
      (casW3Tu2 a (fB x) (fK x) (fD x) (fS x) (fB1 x) (fK1 x) (fD1 x) (fS1 x) B2 K2 D2 S2) x := by
  have := (((((hB.const_mul 2).fun_mul hK).fun_add ((hS.fun_sub (hD.const_mul 2)).const_mul a)).fun_mul
    hB1).fun_add ((hB.fun_pow 2).fun_mul hK1)).fun_add
    ((((hB.const_mul (2 * a)).fun_neg.fun_add (hD.const_mul 2)).fun_sub hS).fun_mul hD1) |>.fun_add
    (((hB.const_mul a).fun_sub hD).fun_mul hS1)
  refine this.congr_deriv ?_
  unfold casW3Tu2
  push_cast
  ring

/-- `T_u > 0`: `T_u = B(B - a)K + Ba(K - 2D) + S³(aB - D) + D²`. -/
theorem cas_w3_Tu_pos {a B K D S3 : ℝ} (ha : 0 < a) (hB : a ≤ B) (hK0 : 0 < K) (hK : 2 * D < K)
    (hD : D ≤ a * B) (hS : 0 ≤ S3) : 0 < casW3Tu a B K D S3 := by
  have e : casW3Tu a B K D S3 =
      B * ((B - a) * K) + B * (a * (K - 2 * D)) + S3 * (a * B - D) + D ^ 2 := by
    unfold casW3Tu
    ring
  rw [e]
  have h1 : 0 < B * (a * (K - 2 * D)) := mul_pos (by linarith) (mul_pos ha (by linarith))
  have h2 : 0 ≤ B * ((B - a) * K) := mul_nonneg (by linarith) (mul_nonneg (by linarith) hK0.le)
  have h3 : 0 ≤ S3 * (a * B - D) := mul_nonneg hS (by linarith)
  have h4 : 0 ≤ D ^ 2 := sq_nonneg D
  linarith

/-! ### On the curve -/

/-- `T_u` on the curve. -/
noncomputable def casW3TuC (x d : ℝ) : ℝ :=
  casW3Tu (1 + 13 / 5 * d) (casW3B x d) (casW3K x d) (casW3D x d) ((1 + x) ^ 3)

/-- `(T_u)_x` on the curve. -/
noncomputable def casW3Tu1C (x d : ℝ) : ℝ :=
  casW3Tu1 (1 + 13 / 5 * d) (casW3B x d) (casW3K x d) (casW3D x d) ((1 + x) ^ 3) (1 + d)
    (2 * x + 2) (casW3Dx x d) (3 * (1 + x) ^ 2)

/-- `(T_u)_xx` on the curve. -/
noncomputable def casW3Tu2C (x d : ℝ) : ℝ :=
  casW3Tu2 (1 + 13 / 5 * d) (casW3B x d) (casW3K x d) (casW3D x d) ((1 + x) ^ 3) (1 + d)
    (2 * x + 2) (casW3Dx x d) (3 * (1 + x) ^ 2) 0 2 (-4 * (1 + d)) (6 * (1 + x))

/-- The norm coefficient `ρ = (r₁)_u = T_u/(aBK)`. -/
noncomputable def casW3rho (x d : ℝ) : ℝ :=
  casW3TuC x d / ((1 + 13 / 5 * d) * casW3B x d * casW3K x d)

/-- `q = (T_u)_x BK - T_u(B_x K + BK_x)`, so that `ρ_x = q/(aB²K²)` and `Q = 78125q`. -/
noncomputable def casW3q (x d : ℝ) : ℝ :=
  casW3Tu1C x d * casW3B x d * casW3K x d -
    casW3TuC x d * ((1 + d) * casW3K x d + casW3B x d * (2 * x + 2))

/-- The polynomial `J(d, h) = Q_x`. -/
noncomputable def casW3J (d h : ℝ) : ℝ :=
  7140250 * d ^ 7 * h + 32845150 * d ^ 7 - 32955000 * d ^ 6 * h ^ 2 - 185097250 * d ^ 6 * h -
    165543950 * d ^ 6 + 13097500 * d ^ 5 * h ^ 3 - 20660250 * d ^ 5 * h ^ 2 - 460863000 * d ^ 5 * h -
    562609450 * d ^ 5 + 21125000 * d ^ 4 * h ^ 4 + 306507500 * d ^ 4 * h ^ 3 +
    1320647250 * d ^ 4 * h ^ 2 + 1973614500 * d ^ 4 * h + 1000723750 * d ^ 4 +
    1125000 * d ^ 3 * h ^ 5 + 78375000 * d ^ 3 * h ^ 4 + 851722500 * d ^ 3 * h ^ 3 +
    3396397500 * d ^ 3 * h ^ 2 + 5513992500 * d ^ 3 * h + 3177307500 * d ^ 3 +
    2187500 * d ^ 2 * h ^ 6 + 46125000 * d ^ 2 * h ^ 5 + 453187500 * d ^ 2 * h ^ 4 +
    2373937500 * d ^ 2 * h ^ 3 + 6553162500 * d ^ 2 * h ^ 2 + 8809037500 * d ^ 2 * h +
    4522462500 * d ^ 2 + 4375000 * d * h ^ 6 + 83437500 * d * h ^ 5 + 674687500 * d * h ^ 4 +
    2863000000 * d * h ^ 3 + 6580875000 * d * h ^ 2 + 7674562500 * d * h + 3529062500 * d +
    2187500 * h ^ 6 + 38437500 * h ^ 5 + 281250000 * h ^ 4 + 1076875000 * h ^ 3 + 2250937500 * h ^ 2 +
    2419687500 * h + 1040625000

/-- The polynomial `Q(2, d)`. -/
noncomputable def casW3Q2 (d : ℝ) : ℝ :=
  51409800 * d ^ 7 - 48773400 * d ^ 6 - 288842125 * d ^ 5 + 529878375 * d ^ 4 +
    1501150625 * d ^ 3 + 1867559375 * d ^ 2 + 1316312500 * d + 367031250

theorem cas_w3_TuC_deriv (x d : ℝ) : HasDerivAt (fun x => casW3TuC x d) (casW3Tu1C x d) x :=
  cas_w3_Tu_deriv (cas_w3_B_dx x d) (cas_w3_K_dx x d) (cas_w3_D_dx x d) (cas_w3_S3_dx x)

theorem cas_w3_Tu1C_deriv (x d : ℝ) : HasDerivAt (fun x => casW3Tu1C x d) (casW3Tu2C x d) x :=
  cas_w3_Tu1_deriv (fB1 := fun _ => 1 + d) (fK1 := fun x => 2 * x + 2)
    (fD1 := fun x => casW3Dx x d) (fS1 := fun x => 3 * (1 + x) ^ 2)
    (cas_w3_B_dx x d) (cas_w3_K_dx x d) (cas_w3_D_dx x d) (cas_w3_S3_dx x)
    (hasDerivAt_const x (1 + d)) (cas_w3_K1_dx x) (cas_w3_Dx_dx x d) (cas_w3_S1_dx x)

/-- `78125 q_x = J(d, x - 2)`; the source is differentiated before expansion. -/
theorem cas_w3_q_deriv (x d : ℝ) : HasDerivAt (fun x => casW3q x d) (casW3J d (x - 2) / 78125) x := by
  have hB := cas_w3_B_dx x d
  have hK := cas_w3_K_dx x d
  have := ((((cas_w3_Tu1C_deriv x d).fun_mul hB).fun_mul hK).fun_sub
    ((cas_w3_TuC_deriv x d).fun_mul (((hasDerivAt_const x (1 + d)).fun_mul hK).fun_add
      (hB.fun_mul (cas_w3_K1_dx x)))))
  refine this.congr_deriv ?_
  unfold casW3J casW3Tu2C casW3TuC casW3Tu1C casW3Tu2 casW3Tu casW3Tu1 casW3B casW3K
    casW3D casW3Dx ssDg
  ring

/-- `78125 q(2, d) = Q(2, d)`. -/
theorem cas_w3_q2 (d : ℝ) : casW3q 2 d = casW3Q2 d / 78125 := by
  unfold casW3q casW3Q2 casW3TuC casW3Tu1C casW3Tu casW3Tu1 casW3B casW3K casW3D
    casW3Dx ssDg
  ring

/-- `J > 0`: discard the positive `d`-terms and put `d = 1/19` in the negative ones; the
remaining polynomial in `h` has positive coefficients. -/
theorem cas_w3_J_pos {d h : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (hh : 0 ≤ h) : 0 < casW3J d h := by
  unfold casW3J
  linarith [
    mul_nonneg (pow_nonneg hd 7) (pow_nonneg hh 1),
    pow_nonneg hd 7,
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 6) (pow_nonneg hh 2),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 6) (pow_nonneg hh 1),
    pow_le_pow_left₀ hd hd' 6,
    mul_nonneg (pow_nonneg hd 5) (pow_nonneg hh 3),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 5) (pow_nonneg hh 2),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 5) (pow_nonneg hh 1),
    pow_le_pow_left₀ hd hd' 5,
    mul_nonneg (pow_nonneg hd 4) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 4) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 4) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 4) (pow_nonneg hh 1),
    pow_nonneg hd 4,
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 5),
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 1),
    pow_nonneg hd 3,
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 6),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 5),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 1),
    pow_nonneg hd 2,
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 6),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 5),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 1),
    pow_nonneg hd 1,
    pow_nonneg hh 6,
    pow_nonneg hh 5,
    pow_nonneg hh 4,
    pow_nonneg hh 3,
    pow_nonneg hh 2,
    pow_nonneg hh 1]

theorem cas_w3_Q2_pos {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) : 0 < casW3Q2 d := by
  unfold casW3Q2
  nlinarith [pow_nonneg hd 7, pow_le_pow_left₀ hd hd' 6, pow_le_pow_left₀ hd hd' 5, pow_nonneg hd 4,
    pow_nonneg hd 3, pow_nonneg hd 2]

/-- `q > 0` on the rectangle (integrate `J > 0` from `x = 2`). -/
theorem cas_w3_q_pos {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    0 < casW3q x d := by
  have h2 : 0 < casW3q 2 d := by
    rw [cas_w3_q2]
    exact div_pos (cas_w3_Q2_pos hd hd') (by norm_num)
  have := jet_mono_of (f := fun x => casW3q x d) (f₁ := fun x => casW3J d (x - 2) / 78125)
    (a := 2) (b := 13 / 6) (fun y _ => cas_w3_q_deriv y d)
    (fun y hy => div_nonneg (cas_w3_J_pos hd hd' (by linarith [hy.1])).le (by norm_num))
    le_rfl hx hx'
  linarith

/-- `ρ_x = q/(aB²K²)`. -/
theorem cas_w3_rho_deriv {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    HasDerivAt (fun x => casW3rho x d)
      (casW3q x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2)) x := by
  obtain ⟨ha, haB, hK, -, -⟩ := cas_w3_curve hx hx' hd hd'
  have ha0 : (1 + 13 / 5 * d) ≠ 0 := by linarith
  have hB0 : casW3B x d ≠ 0 := by linarith
  have hK0 : casW3K x d ≠ 0 := hK.ne'
  have := (cas_w3_TuC_deriv x d).fun_div (((hasDerivAt_const x (1 + 13 / 5 * d)).fun_mul
    (cas_w3_B_dx x d)).fun_mul (cas_w3_K_dx x d)) (by positivity)
  refine this.congr_deriv ?_
  unfold casW3q
  field_simp
  ring

/-- `ρ > 0`. -/
theorem cas_w3_rho_pos {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    0 < casW3rho x d := by
  obtain ⟨ha, haB, hK, hKD, hD⟩ := cas_w3_curve hx hx' hd hd'
  unfold casW3rho casW3TuC
  exact div_pos (cas_w3_Tu_pos (by linarith) haB hK hKD hD (by positivity))
    (mul_pos (mul_pos (by linarith) (by linarith)) hK)

/-- `ρ_x ≥ 0`. -/
theorem cas_w3_rho_deriv_nonneg {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) :
    0 ≤ casW3q x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2) := by
  obtain ⟨ha, -, -, -, -⟩ := cas_w3_curve hx hx' hd hd'
  exact div_nonneg (cas_w3_q_pos hx hx' hd hd').le (by positivity)

end SmoothedOctagon

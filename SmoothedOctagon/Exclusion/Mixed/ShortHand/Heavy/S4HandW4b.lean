module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4c

/-!
# Gate S4, hand proof W4: the norm motion in the cost derivative

`archive/lighter-proofs/SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md` §§2-3. On the boundary
`b = 20x/19`, `a` fixed, `r₀(x, a, u) = 2w - 1/2 + (u - 1)B/a + a/B - a²/K - E_L + log(2aB/K)` is
affine in `u` with slope `ρ = (r₀)_u = B/a + (S³/K)(1 - 2D/K) + 2(D/K)(D/K - 1)`
(`hl46W4_R0_affine`), and `∂_x ρ = ∂_u r_{0,x}^♭ = C(c, h)/(361aK³)` with the note's printed `C`
(`hl46W4_rho_deriv`). Hence `r₀(x, a, U) = r₀(x, a, v) + (U - v)ρ` and
`d/dx r₀(x, a, U) = f + (U' - v')ρ + (U - v)C/(361aK³) ≥ f`, `f = d/dx r₀(x, a, v(x))`, which is
the comparison (4). Finally `f + 9/200 = N/(45125aC*²K³)` with the product source (5)
(`hl46W4_f_eq`), proved term by term against the derivative of `r₀(x, a, v(x))`.

Route: `ρ > 0` is shown as `ρ = (B/a - 1/2) + S³(K - 2D)/K² + 2(D - K/2)²/K²` with `K > 2D`, instead
of the note's `0 < D/K < 1/3`.

## Main API

* `hl46W4R0`, `hl46W4rho`, `hl46W4C`, `hl46W4f`.
* `hl46W4_R0_affine`, `hl46W4_rho_deriv`, `hl46W4_ell_deriv`, `hl46W4_f_eq`, `hl46W4_C_pos`,
  `hl46W4_rho_pos`; derivatives `hl46W4_D_deriv`, `hl46W4_K_deriv`, `hl46W4_v_deriv`,
  `hl46W4_E_deriv`, `hl46W4_W_deriv`, `hl46W4_Q_deriv`; `hl46W4_K_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The bracket `r₀` of `Φ = Γ - r₀/7` on the boundary `b = 20x/19`. -/
noncomputable def hl46W4R0 (x a u : ℝ) : ℝ :=
  2 * hh46S4Wc x (x * (1 + 1 / 19)) a u - 1 / 2 + hh46S4Rest x (x * (1 + 1 / 19)) a u +
    log (2 * a * (a + x * (1 + 1 / 19)) / (x * (x + 2) + a ^ 2))

/-- `ρ = (r₀)_u = 2(D² - DS³)/K² + B/a - (2D - S³)/K`. -/
noncomputable def hl46W4rho (x a : ℝ) : ℝ :=
  2 * (hl46W4D x a ^ 2 - hl46W4D x a * (1 + x) ^ 3) / hl46W4K x a ^ 2 +
    (a + x * (1 + 1 / 19)) / a - (2 * hl46W4D x a - (1 + x) ^ 3) / hl46W4K x a

/-- The note's `C(c, h)`. -/
noncomputable def hl46W4C (c h : ℝ) : ℝ :=
  1900 * c ^ 6 - 1083 * c ^ 5 * h ^ 2 - 4582 * c ^ 5 * h + 5485 * c ^ 5 - 6080 * c ^ 4 * h ^ 3 -
    82755 * c ^ 4 * h ^ 2 - 263110 * c ^ 4 * h - 219235 * c ^ 4 + 9766 * c ^ 3 * h ^ 4 +
    91900 * c ^ 3 * h ^ 3 + 140808 * c ^ 3 * h ^ 2 - 256460 * c ^ 3 * h - 466846 * c ^ 3 +
    36838 * c ^ 2 * h ^ 4 + 355140 * c ^ 2 * h ^ 3 + 984924 * c ^ 2 * h ^ 2 + 793380 * c ^ 2 * h -
    83098 * c ^ 2 + 1881 * c * h ^ 6 + 33858 * c * h ^ 5 + 310391 * c * h ^ 4 +
    1493972 * c * h ^ 3 + 3601311 * c * h ^ 2 + 4007850 * c * h + 1562449 * c + 2261 * h ^ 6 +
    40698 * h ^ 5 + 333479 * h ^ 4 + 1428332 * h ^ 3 + 3240147 * h ^ 2 + 3654298 * h + 1596081

/-- The total `x`-derivative of `r₀` along `u = v(x)`. -/
noncomputable def hl46W4f (x a : ℝ) : ℝ :=
  2 * ((hl46W4Wx x a * hl46W4K x a - 2 * hl46W4W x a * (2 * x + 2)) / hl46W4K x a ^ 3) +
    (9 / 1000 * (a + x * (1 + 1 / 19)) + (hl46W4v x - 1) * (1 + 1 / 19)) / a -
    a * (1 + 1 / 19) / (a + x * (1 + 1 / 19)) ^ 2 + a ^ 2 * (2 * x + 2) / hl46W4K x a ^ 2 -
    (hl46W4Qx x a * hl46W4K x a - hl46W4Q x a * (2 * x + 2)) / hl46W4K x a ^ 2 +
    (1 + 1 / 19) / (a + x * (1 + 1 / 19)) - (2 * x + 2) / hl46W4K x a

/-- `r₀` is affine in `u` with slope `ρ`. -/
theorem hl46W4_R0_affine (x a u w : ℝ) :
    hl46W4R0 x a u = hl46W4R0 x a w + (u - w) * hl46W4rho x a := by
  unfold hl46W4R0 hl46W4rho hh46S4Wc hh46S4Rest hh46S4EL hh46S4P hl46W4D hl46W4K
  ring

/-- `∂_x D = D'`. -/
theorem hl46W4_D_deriv (x a : ℝ) : HasDerivAt (fun x => hl46W4D x a) (hl46W4Dx x a) x := by
  have := ((((hasDerivAt_id' x).const_mul (1 +
    1 / 19)).const_mul (2 * a)).const_add (a ^ 2)).fun_add
    ((((hasDerivAt_id' x).const_mul 2).const_add 1).fun_sub
      (((hasDerivAt_pow 2 x).const_mul (1 + 1 / 19)).const_mul 2))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold hl46W4Dx; push_cast; ring
  · unfold hl46W4D hsDg; ring

/-- `∂_x K = 2x + 2`. -/
theorem hl46W4_K_deriv (x a : ℝ) : HasDerivAt (fun x => hl46W4K x a) (2 * x + 2) x := by
  have := ((hasDerivAt_pow 2 x).fun_add ((hasDerivAt_id' x).const_mul 2)).add_const (a ^ 2)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · push_cast; ring
  · unfold hl46W4K; ring

/-- `v' = 9/1000`. -/
theorem hl46W4_v_deriv (x : ℝ) : HasDerivAt hl46W4v (9 / 1000) x := by
  have := (((hasDerivAt_id' x).sub_const 2).const_mul (9 / 1000)).const_add (757 / 1000)
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  unfold hl46W4v; ring

/-- `∂_x E = E'`. -/
theorem hl46W4_E_deriv (x : ℝ) : HasDerivAt hl46W4E (hl46W4Ex x) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have := (((hS.fun_pow 3).fun_mul ((hl46W4_v_deriv x).sub_const 1)).fun_add
    (hS.const_mul 3)).sub_const 1
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold hl46W4Ex; push_cast; ring
  · unfold hl46W4E hh46S4P; ring

/-- `∂_x W = W'`. -/
theorem hl46W4_W_deriv (x a : ℝ) : HasDerivAt (fun x => hl46W4W x a) (hl46W4Wx x a) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have hM : HasDerivAt hl46W4M (hl46W4Mx x) x := by
    have := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · unfold hl46W4Mx; push_cast; ring
    · unfold hl46W4M; ring
  have hD := hl46W4_D_deriv x a
  have := (hM.fun_add ((hD.fun_pow 2).fun_mul (hl46W4_v_deriv x))).fun_sub
    (hD.fun_mul (hl46W4_E_deriv x))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold hl46W4Wx; push_cast; ring
  · unfold hl46W4W; ring

/-- `∂_x Q = Q'`. -/
theorem hl46W4_Q_deriv (x a : ℝ) : HasDerivAt (fun x => hl46W4Q x a) (hl46W4Qx x a) x := by
  have := (((hl46W4_D_deriv x a).const_mul 2).fun_mul (hl46W4_v_deriv x)).fun_sub
    (hl46W4_E_deriv x)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold hl46W4Qx; ring
  · unfold hl46W4Q; ring

/-- `K > 0`. -/
theorem hl46W4_K_pos (x a : ℝ) (hx : 0 < x) : 0 < hl46W4K x a := by
  unfold hl46W4K; positivity

/-- `∂_x ρ = C(a - 1, x - 2)/(361aK³)` (the note's coefficient of §2). -/
theorem hl46W4_rho_deriv {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    HasDerivAt (fun x => hl46W4rho x a) (hl46W4C (a - 1) (x -
      2) / (361 * a * hl46W4K x a ^ 3)) x := by
  have hK0 := hl46W4_K_pos x a hx
  have hD := hl46W4_D_deriv x a
  have hK := hl46W4_K_deriv x a
  have hS3 : HasDerivAt (fun x : ℝ => (1 + x) ^ 3) (3 * (1 + x) ^ 2) x := by
    have := ((hasDerivAt_id' x).const_add 1).fun_pow 3
    refine this.congr_deriv ?_; push_cast; ring
  have hb : HasDerivAt (fun x : ℝ => a + x * (1 + 1 / 19)) (1 + 1 / 19) x := by
    have := ((hasDerivAt_id' x).mul_const (1 + 1 / 19)).const_add a
    refine this.congr_deriv ?_; ring
  have := ((((hD.fun_pow 2).fun_sub (hD.fun_mul hS3)).const_mul 2).fun_div (hK.fun_pow 2)
    (by positivity)).fun_add (hb.div_const a) |>.fun_sub
    (((hD.const_mul 2).fun_sub hS3).fun_div hK hK0.ne')
  refine this.congr_deriv ?_
  unfold hl46W4C hl46W4K hl46W4D hsDg hl46W4Dx at *
  field_simp
  ring

/-- `d/dx r₀(x, a, v(x)) = f(x, a)`. -/
theorem hl46W4_ell_deriv {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    HasDerivAt (fun x => hl46W4R0 x a (hl46W4v x)) (hl46W4f x a) x := by
  have hK0 := hl46W4_K_pos x a hx
  have hB0 : 0 < a + x * (1 + 1 / 19) := by positivity
  have hW := hl46W4_W_deriv x a
  have hQ := hl46W4_Q_deriv x a
  have hK := hl46W4_K_deriv x a
  have hv := hl46W4_v_deriv x
  have hb : HasDerivAt (fun x : ℝ => a + x * (1 + 1 / 19)) (1 + 1 / 19) x := by
    have := ((hasDerivAt_id' x).mul_const (1 + 1 / 19)).const_add a
    refine this.congr_deriv ?_; ring
  have p1 := (hW.fun_div (hK.fun_pow 2) (by positivity)).const_mul 2
  have p2 := ((hv.sub_const 1).fun_mul hb).div_const a
  have p3 := (hasDerivAt_const x a).fun_div hb hB0.ne'
  have p4 := (hasDerivAt_const x (a ^ 2)).fun_div hK hK0.ne'
  have p5 := hQ.fun_div hK hK0.ne'
  have p6 := ((hb.const_mul (2 * a)).fun_div hK hK0.ne').log (by positivity)
  have := ((p1.sub_const (1 / 2)).fun_add (((p2.fun_add p3).fun_sub p4).fun_sub p5)).fun_add p6
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold hl46W4f
    field_simp
    ring
  · rfl

/-- The normalisation (5): `f + 9/200 = N/(45125aC*²K³)`. -/
theorem hl46W4_f_eq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hl46W4f x a + 9 / 200 = hl46W4N x a / (45125 * a * hl46W4Cs x a ^ 2 * hl46W4K x a ^ 3) := by
  have hK0 := hl46W4_K_pos x a hx
  have hB0 : 0 < a + x * (1 + 1 / 19) := by positivity
  have hC0 : 0 < hl46W4Cs x a := by unfold hl46W4Cs; positivity
  have e : a + x * (1 + 1 / 19) = hl46W4Cs x a / 19 := by unfold hl46W4Cs; ring
  rw [eq_div_iff (by positivity)]
  unfold hl46W4f hl46W4N
  rw [e]
  field_simp
  ring

/-- `C > 0` on `1/8 ≤ c ≤ 1/6`, `h ≥ 0` (monomial rule; the note's `C_low` has positive
coefficients). -/
theorem hl46W4_C_pos {c h : ℝ} (hc : 1 / 8 ≤ c) (hc' : c ≤ 1 / 6) (hh : 0 ≤ h) :
    0 < hl46W4C c h := by
  have hc0 : 0 ≤ c := by linarith
  unfold hl46W4C
  linarith [hl46W4_mlo hc hh 6 0, hl46W4_mlo hc hh 5 0, hl46W4_mlo hc hh 3 4, hl46W4_mlo hc hh 3 3,
    hl46W4_mlo hc hh 3 2, hl46W4_mlo hc hh 2 4, hl46W4_mlo hc hh 2 3, hl46W4_mlo hc hh 2 2,
    hl46W4_mlo hc hh 2 1, hl46W4_mlo hc hh 1 6, hl46W4_mlo hc hh 1 5, hl46W4_mlo hc hh 1 4,
    hl46W4_mlo hc hh 1 3, hl46W4_mlo hc hh 1 2, hl46W4_mlo hc hh 1 1, hl46W4_mlo hc hh 1 0,
    hl46W4_mhi hc0 hc' hh 5 2, hl46W4_mhi hc0 hc' hh 5 1, hl46W4_mhi hc0 hc' hh 4 3,
    hl46W4_mhi hc0 hc' hh 4 2, hl46W4_mhi hc0 hc' hh 4 1, hl46W4_mhi hc0 hc' hh 4 0,
    hl46W4_mhi hc0 hc' hh 3 1, hl46W4_mhi hc0 hc' hh 3 0, hl46W4_mhi hc0 hc' hh 2 0,
    pow_nonneg hh 1, pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4, pow_nonneg hh 5,
    pow_nonneg hh 6]

/-- `ρ = (r₀)_u > 0`. -/
theorem hl46W4_rho_pos {x a : ℝ} (hx : 2 ≤ x) (ha : 1 ≤ a) (ha' : a ≤ 22 / 19) :
    0 < hl46W4rho x a := by
  have hK0 := hl46W4_K_pos x a (by linarith)
  have hKD : 0 < hl46W4K x a - 2 * hl46W4D x a := by
    unfold hl46W4K hl46W4D hsDg; nlinarith
  have key : hl46W4rho x a = ((a + x * (1 + 1 / 19)) / a - 1 / 2) +
      (1 + x) ^ 3 * (hl46W4K x a - 2 * hl46W4D x a) / hl46W4K x a ^ 2 +
      2 * (hl46W4D x a - hl46W4K x a / 2) ^ 2 / hl46W4K x a ^ 2 := by
    unfold hl46W4rho
    field_simp
    ring
  have h1 : 1 / 2 < (a + x * (1 + 1 / 19)) / a := by
    rw [lt_div_iff₀ (by linarith)]; nlinarith
  have h2 : 0 < (1 + x) ^ 3 * (hl46W4K x a - 2 * hl46W4D x a) / hl46W4K x a ^ 2 := by positivity
  have h3 : 0 ≤ 2 * (hl46W4D x a - hl46W4K x a / 2) ^ 2 / hl46W4K x a ^ 2 := by positivity
  linarith

end SmoothedOctagon

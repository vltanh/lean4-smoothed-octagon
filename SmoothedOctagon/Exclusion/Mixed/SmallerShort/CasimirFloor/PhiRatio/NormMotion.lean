module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiRatio.Numerator

/-!
# Smaller-short window, Casimir floor: the norm motion in the cost derivative

On the boundary `b = 20x/19`, `a` fixed,
`r₀(x, a, u) = 2w - 1/2 + (u - 1)B/a + a/B - a²/K - E_L + log(2aB/K)` is affine in `u` with slope
`ρ = (r₀)_u = B/a + (S³/K)(1 - 2D/K) + 2(D/K)(D/K - 1)` (`casW4_R0_affine`), and
`∂_x ρ = ∂_u r_{0,x}^♭ = C(c, h)/(361aK³)` with an explicit polynomial `C` (`casW4_rho_deriv`).
Hence `r₀(x, a, U) = r₀(x, a, v) + (U - v)ρ` and
`d/dx r₀(x, a, U) = f + (U' - v')ρ + (U - v)C/(361aK³) ≥ f`, `f = d/dx r₀(x, a, v(x))`. Finally
`f + 9/200 = N/(45125aC*²K³)` with the eight-term product numerator `N` of `PhiRatio/Numerator`
(`casW4_f_eq`), proved term by term against the derivative of `r₀(x, a, v(x))`.

`ρ > 0` follows from `ρ = (B/a - 1/2) + S³(K - 2D)/K² + 2(D - K/2)²/K²` and `K > 2D`.

## Main API

* `casW4R0`, `casW4rho`, `casW4C`, `casW4f`.
* `casW4_R0_affine`, `casW4_rho_deriv`, `casW4_ell_deriv`, `casW4_f_eq`, `casW4_C_pos`,
  `casW4_rho_pos`; derivatives `casW4_D_deriv`, `casW4_K_deriv`, `casW4_v_deriv`,
  `casW4_E_deriv`, `casW4_W_deriv`, `casW4_Q_deriv`; `casW4_K_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The bracket `r₀` of `Φ = Γ - r₀/7` on the boundary `b = 20x/19`. -/
noncomputable def casW4R0 (x a u : ℝ) : ℝ :=
  2 * casClosedWc x (x * (1 + 1 / 19)) a u - 1 / 2 + casClosedRest x (x * (1 + 1 / 19)) a u +
    log (2 * a * (a + x * (1 + 1 / 19)) / (x * (x + 2) + a ^ 2))

/-- `ρ = (r₀)_u = 2(D² - DS³)/K² + B/a - (2D - S³)/K`. -/
noncomputable def casW4rho (x a : ℝ) : ℝ :=
  2 * (casW4D x a ^ 2 - casW4D x a * (1 + x) ^ 3) / casW4K x a ^ 2 +
    (a + x * (1 + 1 / 19)) / a - (2 * casW4D x a - (1 + x) ^ 3) / casW4K x a

/-- The polynomial `C(c, h)` with `∂_x ρ = C(a - 1, x - 2)/(361aK³)`. -/
noncomputable def casW4C (c h : ℝ) : ℝ :=
  1900 * c ^ 6 - 1083 * c ^ 5 * h ^ 2 - 4582 * c ^ 5 * h + 5485 * c ^ 5 - 6080 * c ^ 4 * h ^ 3 -
    82755 * c ^ 4 * h ^ 2 - 263110 * c ^ 4 * h - 219235 * c ^ 4 + 9766 * c ^ 3 * h ^ 4 +
    91900 * c ^ 3 * h ^ 3 + 140808 * c ^ 3 * h ^ 2 - 256460 * c ^ 3 * h - 466846 * c ^ 3 +
    36838 * c ^ 2 * h ^ 4 + 355140 * c ^ 2 * h ^ 3 + 984924 * c ^ 2 * h ^ 2 + 793380 * c ^ 2 * h -
    83098 * c ^ 2 + 1881 * c * h ^ 6 + 33858 * c * h ^ 5 + 310391 * c * h ^ 4 +
    1493972 * c * h ^ 3 + 3601311 * c * h ^ 2 + 4007850 * c * h + 1562449 * c + 2261 * h ^ 6 +
    40698 * h ^ 5 + 333479 * h ^ 4 + 1428332 * h ^ 3 + 3240147 * h ^ 2 + 3654298 * h + 1596081

/-- The total `x`-derivative of `r₀` along `u = v(x)`. -/
noncomputable def casW4f (x a : ℝ) : ℝ :=
  2 * ((casW4Wx x a * casW4K x a - 2 * casW4W x a * (2 * x + 2)) / casW4K x a ^ 3) +
    (9 / 1000 * (a + x * (1 + 1 / 19)) + (casW4v x - 1) * (1 + 1 / 19)) / a -
    a * (1 + 1 / 19) / (a + x * (1 + 1 / 19)) ^ 2 + a ^ 2 * (2 * x + 2) / casW4K x a ^ 2 -
    (casW4Qx x a * casW4K x a - casW4Q x a * (2 * x + 2)) / casW4K x a ^ 2 +
    (1 + 1 / 19) / (a + x * (1 + 1 / 19)) - (2 * x + 2) / casW4K x a

/-- `r₀` is affine in `u` with slope `ρ`. -/
theorem casW4_R0_affine (x a u w : ℝ) :
    casW4R0 x a u = casW4R0 x a w + (u - w) * casW4rho x a := by
  unfold casW4R0 casW4rho casClosedWc casClosedRest casClosedEL casClosedP casW4D casW4K
  ring

/-- `∂_x D = D'`. -/
theorem casW4_D_deriv (x a : ℝ) : HasDerivAt (fun x => casW4D x a) (casW4Dx x a) x := by
  have := ((((hasDerivAt_id' x).const_mul (1 +
    1 / 19)).const_mul (2 * a)).const_add (a ^ 2)).fun_add
    ((((hasDerivAt_id' x).const_mul 2).const_add 1).fun_sub
      (((hasDerivAt_pow 2 x).const_mul (1 + 1 / 19)).const_mul 2))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold casW4Dx; push_cast; ring
  · unfold casW4D ssDg; ring

/-- `∂_x K = 2x + 2`. -/
theorem casW4_K_deriv (x a : ℝ) : HasDerivAt (fun x => casW4K x a) (2 * x + 2) x := by
  have := ((hasDerivAt_pow 2 x).fun_add ((hasDerivAt_id' x).const_mul 2)).add_const (a ^ 2)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · push_cast; ring
  · unfold casW4K; ring

/-- `v' = 9/1000`. -/
theorem casW4_v_deriv (x : ℝ) : HasDerivAt casW4v (9 / 1000) x := by
  have := (((hasDerivAt_id' x).sub_const 2).const_mul (9 / 1000)).const_add (757 / 1000)
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  unfold casW4v; ring

/-- `∂_x E = E'`. -/
theorem casW4_E_deriv (x : ℝ) : HasDerivAt casW4E (casW4Ex x) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have := (((hS.fun_pow 3).fun_mul ((casW4_v_deriv x).sub_const 1)).fun_add
    (hS.const_mul 3)).sub_const 1
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold casW4Ex; push_cast; ring
  · unfold casW4E casClosedP; ring

/-- `∂_x W = W'`. -/
theorem casW4_W_deriv (x a : ℝ) : HasDerivAt (fun x => casW4W x a) (casW4Wx x a) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have hM : HasDerivAt casW4M (casW4Mx x) x := by
    have := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · unfold casW4Mx; push_cast; ring
    · unfold casW4M; ring
  have hD := casW4_D_deriv x a
  have := (hM.fun_add ((hD.fun_pow 2).fun_mul (casW4_v_deriv x))).fun_sub
    (hD.fun_mul (casW4_E_deriv x))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold casW4Wx; push_cast; ring
  · unfold casW4W; ring

/-- `∂_x Q = Q'`. -/
theorem casW4_Q_deriv (x a : ℝ) : HasDerivAt (fun x => casW4Q x a) (casW4Qx x a) x := by
  have := (((casW4_D_deriv x a).const_mul 2).fun_mul (casW4_v_deriv x)).fun_sub
    (casW4_E_deriv x)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold casW4Qx; ring
  · unfold casW4Q; ring

/-- `K > 0`. -/
theorem casW4_K_pos (x a : ℝ) (hx : 0 < x) : 0 < casW4K x a := by
  unfold casW4K; positivity

/-- `∂_x ρ = C(a - 1, x - 2)/(361aK³)`. -/
theorem casW4_rho_deriv {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    HasDerivAt (fun x => casW4rho x a) (casW4C (a - 1) (x -
      2) / (361 * a * casW4K x a ^ 3)) x := by
  have hK0 := casW4_K_pos x a hx
  have hD := casW4_D_deriv x a
  have hK := casW4_K_deriv x a
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
  unfold casW4C casW4K casW4D ssDg casW4Dx at *
  field_simp
  ring

/-- `d/dx r₀(x, a, v(x)) = f(x, a)`. -/
theorem casW4_ell_deriv {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    HasDerivAt (fun x => casW4R0 x a (casW4v x)) (casW4f x a) x := by
  have hK0 := casW4_K_pos x a hx
  have hB0 : 0 < a + x * (1 + 1 / 19) := by positivity
  have hW := casW4_W_deriv x a
  have hQ := casW4_Q_deriv x a
  have hK := casW4_K_deriv x a
  have hv := casW4_v_deriv x
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
  · unfold casW4f
    field_simp
    ring
  · rfl

/-- The normalisation `f + 9/200 = N/(45125aC*²K³)`. -/
theorem casW4_f_eq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    casW4f x a + 9 / 200 = casW4N x a / (45125 * a * casW4Cs x a ^ 2 * casW4K x a ^ 3) := by
  have hK0 := casW4_K_pos x a hx
  have hB0 : 0 < a + x * (1 + 1 / 19) := by positivity
  have hC0 : 0 < casW4Cs x a := by unfold casW4Cs; positivity
  have e : a + x * (1 + 1 / 19) = casW4Cs x a / 19 := by unfold casW4Cs; ring
  rw [eq_div_iff (by positivity)]
  unfold casW4f casW4N
  rw [e]
  field_simp
  ring

/-- `C > 0` on `1/8 ≤ c ≤ 1/6`, `h ≥ 0` (monomial rule: the resulting lower polynomial in
`h` has positive coefficients). -/
theorem casW4_C_pos {c h : ℝ} (hc : 1 / 8 ≤ c) (hc' : c ≤ 1 / 6) (hh : 0 ≤ h) :
    0 < casW4C c h := by
  have hc0 : 0 ≤ c := by linarith
  unfold casW4C
  linarith [casW4_mlo hc hh 6 0, casW4_mlo hc hh 5 0, casW4_mlo hc hh 3 4, casW4_mlo hc hh 3 3,
    casW4_mlo hc hh 3 2, casW4_mlo hc hh 2 4, casW4_mlo hc hh 2 3, casW4_mlo hc hh 2 2,
    casW4_mlo hc hh 2 1, casW4_mlo hc hh 1 6, casW4_mlo hc hh 1 5, casW4_mlo hc hh 1 4,
    casW4_mlo hc hh 1 3, casW4_mlo hc hh 1 2, casW4_mlo hc hh 1 1, casW4_mlo hc hh 1 0,
    casW4_mhi hc0 hc' hh 5 2, casW4_mhi hc0 hc' hh 5 1, casW4_mhi hc0 hc' hh 4 3,
    casW4_mhi hc0 hc' hh 4 2, casW4_mhi hc0 hc' hh 4 1, casW4_mhi hc0 hc' hh 4 0,
    casW4_mhi hc0 hc' hh 3 1, casW4_mhi hc0 hc' hh 3 0, casW4_mhi hc0 hc' hh 2 0,
    pow_nonneg hh 1, pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4, pow_nonneg hh 5,
    pow_nonneg hh 6]

/-- `ρ = (r₀)_u > 0`. -/
theorem casW4_rho_pos {x a : ℝ} (hx : 2 ≤ x) (ha : 1 ≤ a) (ha' : a ≤ 22 / 19) :
    0 < casW4rho x a := by
  have hK0 := casW4_K_pos x a (by linarith)
  have hKD : 0 < casW4K x a - 2 * casW4D x a := by
    unfold casW4K casW4D ssDg; nlinarith
  have key : casW4rho x a = ((a + x * (1 + 1 / 19)) / a - 1 / 2) +
      (1 + x) ^ 3 * (casW4K x a - 2 * casW4D x a) / casW4K x a ^ 2 +
      2 * (casW4D x a - casW4K x a / 2) ^ 2 / casW4K x a ^ 2 := by
    unfold casW4rho
    field_simp
    ring
  have h1 : 1 / 2 < (a + x * (1 + 1 / 19)) / a := by
    rw [lt_div_iff₀ (by linarith)]; nlinarith
  have h2 : 0 < (1 + x) ^ 3 * (casW4K x a - 2 * casW4D x a) / casW4K x a ^ 2 := by positivity
  have h3 : 0 ≤ 2 * (casW4D x a - casW4K x a / 2) ^ 2 / casW4K x a ^ 2 := by positivity
  linarith

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOLowC

/-!
# Gate S3, the outer face by hand: the two lower-shape curves

Proof of the leaf `hs3_outer_face`, fourth part. Along the slope `C = 19x/50`
at the lower shape `r_* = 13/(5S)`, `R_n = p + Vd + 1/z - 56/(5z + 14)` with `p = P_n(r_*)`,
`d = A_n(r_*)`, `V = U(r_*) - 3/4`, `z = Z(r_*)`. For `n = 25/8` and `n = 7/2`, the derivatives
satisfy `p' < -41/200` (resp. `-23/100`), `d' < 19/4` (resp. `26/5`), `0 < d < 18/5`,
`0 ≤ V < 1/110`, `V' < 7/800`, `0 < z' < 14/25`, `0 < f(z) < 8/35`, so `R_n' < 0`, and
`R_n(2) < -1/100000` (resp. `-1/400`) is a rational value. Each derivative is taken before
clearing: `p` and `d` are quartics in `r_*` whose coefficients are differentiated separately
(`hl3_hd_qvar`), and `V` is used in its closed form.

## Main API

* `hl3o_low_curve`: `G(x, 19x/50, n, r_*) < 0` for `n ∈ {25/8, 7/2}`, `2 ≤ x ≤ 13/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The derivative of a quartic in `r(s)` with variable coefficients. -/
theorem hl3_hd_qvar {c0 c1 c2 c3 c4 r : ℝ → ℝ} {c0' c1' c2' c3' c4' r' t : ℝ}
    (h0 : HasDerivAt c0 c0' t) (h1 : HasDerivAt c1 c1' t) (h2 : HasDerivAt c2 c2' t)
    (h3 : HasDerivAt c3 c3' t) (h4 : HasDerivAt c4 c4' t) (hr : HasDerivAt r r' t) :
    HasDerivAt (fun s => c0 s + c1 s * r s + c2 s * r s ^ 2 + c3 s * r s ^ 3 + c4 s * r s ^ 4)
      (c0' + (c1' * r t + c1 t * r') + (c2' * r t ^ 2 + c2 t * (2 * r t * r')) +
        (c3' * r t ^ 3 + c3 t * (3 * r t ^ 2 * r')) + (c4' * r t ^ 4 + c4 t * (4 * r t ^ 3 * r'))) t := by
  have := (((h0.add (h1.mul hr)).add (h2.mul (hr.fun_pow 2))).add (h3.mul (hr.fun_pow 3))).add
    (h4.mul (hr.fun_pow 4))
  refine this.congr_deriv ?_
  push_cast
  ring

/-- The lower shape `r_* = 13/(5S)` has derivative `-13/(5S²)`. -/
theorem hl3_hd_rs {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => 13 / (5 * (s + 1))) (-(13 / (5 * (t + 1) ^ 2))) t := by
  have h5 : 5 * (t + 1) ≠ 0 := by positivity
  have := (hasDerivAt_const t (13 : ℝ)).fun_div (((hasDerivAt_id t).add_const 1).const_mul 5) h5
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-! ### The two quartics along the curve -/

/-- `p' ` along `C = 19x/50`, `r = r_*`, with the coefficient derivatives kept separate. -/
noncomputable def hl3oLpD (n x : ℝ) : ℝ :=
  deriv (fun s => hl3oPc0 s (19 * s / 50) n) x +
    (deriv (fun s => hl3oPc1 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) +
      hl3oPc1 x (19 * x / 50) n * (-(13 / (5 * (x + 1) ^ 2)))) +
    (deriv (fun s => hl3oPc2 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) ^ 2 +
      hl3oPc2 x (19 * x / 50) n * (2 * (13 / (5 * (x + 1))) * (-(13 / (5 * (x + 1) ^ 2))))) +
    (deriv (fun s => hl3oPc3 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) ^ 3 +
      hl3oPc3 x (19 * x / 50) n * (3 * (13 / (5 * (x + 1))) ^ 2 * (-(13 / (5 * (x + 1) ^ 2))))) +
    (deriv (fun s => hl3oPc4 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) ^ 4 +
      hl3oPc4 x (19 * x / 50) n * (4 * (13 / (5 * (x + 1))) ^ 3 * (-(13 / (5 * (x + 1) ^ 2)))))

/-- `d'` along `C = 19x/50`, `r = r_*`. -/
noncomputable def hl3oLdD (n x : ℝ) : ℝ :=
  deriv (fun s => hl3oAc0 s (19 * s / 50) n) x +
    (deriv (fun s => hl3oAc1 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) +
      hl3oAc1 x (19 * x / 50) n * (-(13 / (5 * (x + 1) ^ 2)))) +
    (deriv (fun s => hl3oAc2 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) ^ 2 +
      hl3oAc2 x (19 * x / 50) n * (2 * (13 / (5 * (x + 1))) * (-(13 / (5 * (x + 1) ^ 2))))) +
    (deriv (fun s => hl3oAc3 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) ^ 3 +
      hl3oAc3 x (19 * x / 50) n * (3 * (13 / (5 * (x + 1))) ^ 2 * (-(13 / (5 * (x + 1) ^ 2))))) +
    (deriv (fun s => hl3oAc4 s (19 * s / 50) n) x * (13 / (5 * (x + 1))) ^ 4 +
      hl3oAc4 x (19 * x / 50) n * (4 * (13 / (5 * (x + 1))) ^ 3 * (-(13 / (5 * (x + 1) ^ 2)))))

section Curve

variable {n x : ℝ}

theorem hl3o_hd_Lp (hx : 0 < x) :
    HasDerivAt (fun s => hl3oP s (19 * s / 50) n (13 / (5 * (s + 1)))) (hl3oLpD n x) x := by
  have hd : ∀ (c : ℝ → ℝ), DifferentiableAt ℝ c x → HasDerivAt c (deriv c x) x :=
    fun c hc => hc.hasDerivAt
  have h0 := hd (fun s => hl3oPc0 s (19 * s / 50) n) (by
    unfold hl3oPc0 hl3oAc0 hl3oα0 hl3oβ0 hl3oγ0 hl3oδ0
    fun_prop (disch := positivity))
  have h1 := hd (fun s => hl3oPc1 s (19 * s / 50) n) (by
    unfold hl3oPc1 hl3oAc1 hl3oα1 hl3oβ1 hl3oγ1 hl3oδ1
    fun_prop (disch := positivity))
  have h2 := hd (fun s => hl3oPc2 s (19 * s / 50) n) (by
    unfold hl3oPc2 hl3oAc2 hl3oα2 hl3oβ2 hl3oγ2 hl3oδ2
    fun_prop (disch := positivity))
  have h3 := hd (fun s => hl3oPc3 s (19 * s / 50) n) (by
    unfold hl3oPc3 hl3oAc3 hl3oα3 hl3oγ3
    fun_prop (disch := positivity))
  have h4 := hd (fun s => hl3oPc4 s (19 * s / 50) n) (by
    unfold hl3oPc4 hl3oAc4 hl3oα4 hl3oγ4
    fun_prop (disch := positivity))
  have := hl3_hd_qvar h0 h1 h2 h3 h4 (hl3_hd_rs hx)
  unfold hl3oP hl3oLpD
  exact this

theorem hl3o_hd_Ld (hx : 0 < x) :
    HasDerivAt (fun s => hl3oA s (19 * s / 50) n (13 / (5 * (s + 1)))) (hl3oLdD n x) x := by
  have hd : ∀ (c : ℝ → ℝ), DifferentiableAt ℝ c x → HasDerivAt c (deriv c x) x :=
    fun c hc => hc.hasDerivAt
  have h0 := hd (fun s => hl3oAc0 s (19 * s / 50) n) (by
    unfold hl3oAc0 hl3oα0 hl3oβ0; fun_prop)
  have h1 := hd (fun s => hl3oAc1 s (19 * s / 50) n) (by
    unfold hl3oAc1 hl3oα1 hl3oβ1; fun_prop)
  have h2 := hd (fun s => hl3oAc2 s (19 * s / 50) n) (by
    unfold hl3oAc2 hl3oα2 hl3oβ2; fun_prop)
  have h3 := hd (fun s => hl3oAc3 s (19 * s / 50) n) (by
    unfold hl3oAc3 hl3oα3; fun_prop)
  have h4 := hd (fun s => hl3oAc4 s (19 * s / 50) n) (by
    unfold hl3oAc4 hl3oα4; fun_prop)
  have := hl3_hd_qvar h0 h1 h2 h3 h4 (hl3_hd_rs hx)
  unfold hl3oA hl3oLdD
  exact this

set_option linter.unusedSimpArgs false in
theorem hl3o_O0_id (hx : 0 < x) :
    (-hl3oLpD (25 / 8) x - 41 / 200) * (6125000 * (x + 1) ^ 6) =
      558600 * (x - 2) ^ 7 + 10651040 * (x - 2) ^ 6 + 86143320 * (x - 2) ^ 5 +
        342670492 * (x - 2) ^ 4 + 691815823 * (x - 2) ^ 3 + 709620600 * (x - 2) ^ 2 +
        292950023 * (x - 2) + 4785838 := by
  unfold hl3oLpD hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2 hl3oAc3 hl3oAc4
    hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1 hl3oγ2 hl3oγ3 hl3oγ4
    hl3oδ0 hl3oδ1 hl3oδ2
  have hx1 : x + 1 ≠ 0 := by linarith
  hl3_deriv
  field_simp
  ring

set_option linter.unusedSimpArgs false in
theorem hl3o_O1_id (hx : 0 < x) :
    (-hl3oLpD (7 / 2) x - 23 / 100) * (21875000 * (x + 1) ^ 6) =
      2234400 * (x - 2) ^ 7 + 42467535 * (x - 2) ^ 6 + 342114030 * (x - 2) ^ 5 +
        1358603668 * (x - 2) ^ 4 + 2757913492 * (x - 2) ^ 3 + 2900959275 * (x - 2) ^ 2 +
        1291446542 * (x - 2) + 43690402 := by
  unfold hl3oLpD hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2 hl3oAc3 hl3oAc4
    hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1 hl3oγ2 hl3oγ3 hl3oγ4
    hl3oδ0 hl3oδ1 hl3oδ2
  have hx1 : x + 1 ≠ 0 := by linarith
  hl3_deriv
  field_simp
  ring

end Curve

end SmoothedOctagon

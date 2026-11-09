module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface

/-!
# Smaller-short window, displacement, central face: β-monotonicity, the log majorant and the endpoint signs

Lemmas for `SmallerShort/Displacement/Faces` (the face lemmas `dsp_beta_mono`, `dsp_log_maj`,
`dsp_central_endpoint`).
The module cannot import `Displacement/Faces`, so it carries copies of
its definitions with identical bodies (`dspfFn = dspFn`, `dspfF0 = dspF0`, `dspfF1 = dspF1`,
`dspfUCB = ssUCB`, `dspfamin = dspamin`); the face lemmas follow by definitional unfolding.

## Main API

* `dspfFn`, `dspfF0`, `dspfF1`, `dspfUCB`, `dspfamin` (copies of the face definitions).
* `dspf_log_maj`: `log y ≤ -40153/180000 + 2(5y - 4)/(5y + 4)` for `0 < y ≤ 6/7`.
* `dspf_beta_mono`: `F_i(x, α, β; ū(x, β))` at `q = q_c` is nondecreasing in `β` on the
  central-beta domain.
* `dspf_central_endpoint`: `F₀, F₁ < 0` at `α = a_min(x)`, `β = 20x/19`, `q = q_c`, `u = ū`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- Copy of `dspFn`: the duration test `J + n(w_* - 3/4)`. -/
noncomputable def dspfFn (x be al u q n ℓ : ℝ) : ℝ :=
  (u - 1) / ssRA al be + ssRA al be + 1 - q - ssELs x be al u q + ℓ +
    n * (ssWs x be al u q - 3 / 4)

/-- Copy of `dspF0`. -/
noncomputable def dspfF0 (x be al u q : ℝ) : ℝ :=
  dspfFn x be al u q (2 + 4 * (4 - 3 * (2 * q / ssRA al be)) / (5 * al - 1))
    (log (2 * q / ssRA al be))

/-- Copy of `dspF1`. -/
noncomputable def dspfF1 (x be al u q : ℝ) : ℝ :=
  dspfFn x be al u q (ssRA al be / q + 4 / (5 * al - 1)) (log (2 * q / ssRA al be))

/-- Copy of `ssUCB`: the central ceiling `ū(x, β)`. -/
noncomputable def dspfUCB (x be : ℝ) : ℝ :=
  3 / 4 + ((x - 1) * (ssVG x - 3 / 4) + (be - x) / 5808) / (be - 1)

/-- Copy of `dspamin`: `a_min(x) = (15x + 511)/475`. -/
noncomputable def dspfamin (x : ℝ) : ℝ := (15 * x + 511) / 475

/-! ### The rational log majorant -/

/-- **The rational log majorant**: for `0 < y ≤ 6/7`,
`log y ≤ -40153/180000 + 2(5y - 4)/(5y + 4)`.
The difference `log t - 2(5t - 4)/(5t + 4)` has derivative `(5t - 4)²/(t(5t + 4)²) ≥ 0`, so it
is at most its value at `6/7`, and `log(7/6) ≥ 2/13 + 2/(3·13³)` (`ss_log_ge_cubic`). -/
theorem dspf_log_maj {y : ℝ} (hy : 0 < y) (hy7 : y ≤ 6 / 7) :
    log y ≤ -40153 / 180000 + 2 * (5 * y - 4) / (5 * y + 4) := by
  have h := ss_le_of_deriv (f := fun t => Real.log t - 2 * (5 * t - 4) / (5 * t + 4))
    (f' := fun t => (5 * t - 4) ^ 2 / (t * (5 * t + 4) ^ 2)) hy7 (fun t ht => ?_)
    (fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity)
  · have h76 := ss_log_ge_cubic (z := 7 / 6) (by norm_num)
    have hl : Real.log (6 / 7) = - Real.log (7 / 6) := by
      rw [← Real.log_inv]; norm_num
    rw [hl] at h
    norm_num at h h76
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have h1 : HasDerivAt (fun t : ℝ => 2 * (5 * t - 4)) 10 t := by
    convert (((hasDerivAt_id t).const_mul 5).sub_const 4).const_mul (2 : ℝ) using 1 <;> norm_num
  have h2 : HasDerivAt (fun t : ℝ => 5 * t + 4) 5 t := by
    simpa using ((hasDerivAt_id t).const_mul 5).add_const 4
  have := (Real.hasDerivAt_log ht.ne').sub (h1.div h2 (by positivity))
  refine this.congr_deriv ?_
  field_simp
  ring

/-! ### Shape bounds on the central-beta domain -/

section Beta

variable {x al be : ℝ}

private theorem dspfk_al_le (hx : 2 ≤ x) (hqc : 6 * al ^ 2 ≤ x * (x + 2)) :
    al ≤ (5 * x + 4) / 12 := by
  nlinarith [sq_nonneg (x - 4), sq_nonneg (al - (5 * x + 4) / 12)]

private theorem dspfk_al_le' (hx : 2 ≤ x) (hqc : 6 * al ^ 2 ≤ x * (x + 2)) :
    al < 13 * (3 * x + 2) / 90 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (al + 13 * (3 * x + 2) / 90)]

/-- `-d_β = 2(x - α)/K ≥ 7/40`. -/
private theorem dspfk_e (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hqc : 6 * al ^ 2 ≤ x * (x + 2)) :
    7 * (x * (x + 2) + al ^ 2) ≤ 80 * (x - al) := by
  have := dspfk_al_le hx hqc
  nlinarith

/-- `d = D/K ≥ 1/6`. -/
private theorem dspfk_d_lo (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb3 : be ≤ x + 5 * x * (al - 1) / 13) :
    x * (x + 2) + al ^ 2 ≤ 6 * ssDg x be al := by
  have h1 := dspfk_al_le hx hqc
  unfold ssDg
  have hxa : 0 ≤ x - al := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb3 hxa, mul_nonneg (sub_nonneg.2 hal) (sub_nonneg.2 hx)]

/-- `d = D/K ≤ 1/3`. -/
private theorem dspfk_d_hi (hx : 2 ≤ x) (hqc : 6 * al ^ 2 ≤ x * (x + 2))
    (hb : 20 * x / 19 ≤ be) : 3 * ssDg x be al ≤ x * (x + 2) + al ^ 2 := by
  have h1 := dspfk_al_le' hx hqc
  unfold ssDg
  have hxa : 0 ≤ x - al := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb hxa]

/-- `λS = S³/K ≥ 20/7`. -/
private theorem dspfk_lamS (hx : 2 ≤ x) (hqc : 6 * al ^ 2 ≤ x * (x + 2)) :
    20 * (x * (x + 2) + al ^ 2) ≤ 7 * (1 + x) ^ 3 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)]

/-- `E_L ≤ 5/16` at `u = 3/4`. -/
private theorem dspfk_EL0 (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hqc : 6 * al ^ 2 ≤ x * (x + 2))
    (hb : 20 * x / 19 ≤ be) :
    4 * (6 * ssDg x be al + (1 + x) ^ 3 - 12 * (1 + x) + 4) ≤ 5 * (x * (x + 2) + al ^ 2) := by
  have h1 := dspfk_al_le' hx hqc
  unfold ssDg
  have hxa : 0 ≤ x - al := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb hxa, mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]

/-- `y = 2q_c/r_A ≥ 3/4`. -/
private theorem dspfk_y_lo (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hb : 20 * x / 19 ≤ be) : 3 * (x * (x + 2) + al ^ 2) ≤ 8 * al * (al + be) := by
  have h0 : 0 ≤ al := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb h0, mul_nonneg (sub_nonneg.2 hal) (sub_nonneg.2 hx),
    mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2),
    mul_nonneg (sub_nonneg.2 hal) (sub_nonneg.2 hal)]

/-- `y = 2q_c/r_A ≤ 6/7`. -/
private theorem dspfk_y_hi (hal : 108 / 95 ≤ al) (hqc : 6 * al ^ 2 ≤ x * (x + 2))
    (hb2 : be ≤ 2 * al) : 7 * al * (al + be) ≤ 3 * (x * (x + 2) + al ^ 2) := by
  have h0 : 0 ≤ al := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb2 h0]

/-! ### The scale form at `q = q_c` -/

private theorem dspfk_EL_eq (hx : 0 < x) (hal : 1 ≤ al) (u : ℝ) :
    ssELs x be al u (ssQc x al) * (x * (x + 2) + al ^ 2) =
      2 * ssDg x be al * u - (1 + x) ^ 3 * (u - 1) - 3 * (1 + x) + 1 := by
  have ha : al ≠ 0 := by positivity
  have hK : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have hS : 1 + x ≠ 0 := by positivity
  unfold ssELs ssA3 ssE0 ssQc
  field_simp
  ring

private theorem dspfk_W_eq (hx : 0 < x) (hal : 1 ≤ al) (u : ℝ) :
    ssWs x be al u (ssQc x al) * (x * (x + 2) + al ^ 2) ^ 2 =
      (1 + x) ^ 4 - (1 + x) ^ 3 + (1 + x) ^ 2 + ssDg x be al ^ 2 * u -
        ssDg x be al * ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1) := by
  have ha : al ≠ 0 := by positivity
  have hK : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have hS : 1 + x ≠ 0 := by positivity
  unfold ssWs ssA1 ssA2 ssE0 ssQc
  field_simp
  ring

/-- `w_*` is quadratic in `β` with exact secant slope `e·avg(E_{L,*})`, `e = q(2α - 2x)/α²`. -/
private theorem dspfk_W_diff (b₁ b₂ u q : ℝ) :
    ssWs x b₂ al u q - ssWs x b₁ al u q =
      (b₂ - b₁) * (q * (2 * al - 2 * x) / al ^ 2) *
        ((ssELs x b₁ al u q + ssELs x b₂ al u q) / 2) := by
  unfold ssWs ssA1 ssA2 ssELs ssA3 ssDg
  ring

/-- `E_{L,*}` is affine in `β` with slope `2eu`. -/
private theorem dspfk_EL_diff (b₁ b₂ u q : ℝ) :
    ssELs x b₂ al u q - ssELs x b₁ al u q =
      (b₂ - b₁) * (q * (2 * al - 2 * x) / al ^ 2) * (2 * u) := by
  unfold ssELs ssA3 ssDg
  ring

/-- The test is affine in `u`. -/
private theorem dspfk_u_aff (u₁ u₂ q n ℓ : ℝ) :
    dspfFn x be al u₂ q n ℓ - dspfFn x be al u₁ q n ℓ =
      (u₂ - u₁) * (1 / ssRA al be + (1 + x) -
        q * (2 * (ssDg x be al / al ^ 2) + (1 - 1 / al ^ 2) * (1 + x)) +
        n * (-q * (ssDg x be al / al ^ 2) * (1 + x) +
          q ^ 2 * ((ssDg x be al / al ^ 2) ^ 2 +
            ssDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * (1 + x)))) := by
  unfold dspfFn ssWs ssELs ssA1 ssA2 ssA3 ssE0
  ring

private theorem dspfk_y (hx : 0 < x) (hal : 1 ≤ al) (be : ℝ) (hb : 0 < al + be) :
    2 * ssQc x al / ssRA al be = 2 * al * (al + be) / (x * (x + 2) + al ^ 2) := by
  have ha : al ≠ 0 := by positivity
  unfold ssQc ssRA
  field_simp

private theorem dspfk_T (hx : 0 < x) (hal : 1 ≤ al) (be : ℝ) (hb : 0 < al + be) :
    ssRA al be / ssQc x al = (x * (x + 2) + al ^ 2) / (al * (al + be)) := by
  have ha : al ≠ 0 := by positivity
  unfold ssQc ssRA
  field_simp

/-! ### The bounds entering the β-slope -/

private theorem dspfk_P0 {h z : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hz : 0 ≤ z)
    (hz1 : z ≤ 1 / 10) :
    0 ≤ 10/19 * h^5 - 10/19 * h^4 * z + 31691/14440 * h^4 - 1/4 * h^3 * z^2 + 524/1805 * h^3 * z
      + 1285029/685900 * h^3 - 3127/3610 * h^2 * z^2 + 2441034/171475 * h^2 * z
      - 63727381/65160500 * h^2 - 60/19 * h * z^3 - 64149/7220 * h * z^2 + 5185724/171475 * h * z
      + 31007899/65160500 * h + 1/40 * z^4 - 2946/475 * z^3 - 2862933/180500 * z^2
      + 64305406/4286875 * z + 1583395749/814506250 := by
  have hz' : 0 ≤ 1 / 10 - z := by linarith
  have hh' : 0 ≤ 1 / 6 - h := by linarith
  have hz2 := pow_nonneg hz 2
  have hh2 := pow_nonneg hh 2
  have hh3 := pow_nonneg hh 3
  linarith [mul_nonneg hh hh', mul_nonneg hz hz', mul_nonneg hz2 hz',
    mul_nonneg (mul_nonneg hh hz) hz',
    mul_nonneg (mul_nonneg hh hz2) hz', mul_nonneg (mul_nonneg hh2 hz) hz',
    mul_nonneg (mul_nonneg hh3 hz) hz', mul_nonneg (mul_nonneg hh3 hz) hh', pow_nonneg hh 5,
    pow_nonneg hh 4, mul_nonneg hh3 hz, mul_nonneg hh2 hz, mul_nonneg hh hz, pow_nonneg hz 4]

/-- `K²(31/40 - w)` at `u = 3/4`, `β = 20x/19`. -/
private theorem dspfk_P0' (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) :
    0 ≤ 31 / 40 * (x * (x + 2) + al ^ 2) ^ 2 - ((1 + x) ^ 4 - (1 + x) ^ 3 + (1 + x) ^ 2) -
      3 / 4 * ssDg x (20 * x / 19) al ^ 2 -
      ssDg x (20 * x / 19) al * ((1 + x) ^ 3 / 4 - 3 * (1 + x) + 1) := by
  have h1 := dspfk_al_le hx hqc
  refine le_of_le_of_eq (dspfk_P0 (h := x - 2) (z := al - 108 / 95) (by linarith) (by linarith)
    (by linarith) (by linarith)) ?_
  unfold ssDg
  ring

/-- **`w_* ≤ 31/40`** at `q = q_c`.
`w_*` decreases in `u` and in `β`; the corner `u = 3/4`, `β = 20x/19` is a two-variable
polynomial with positive constant term. -/
private theorem dspfk_W_le (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be)
    (hb3 : be ≤ x + 5 * x * (al - 1) / 13) {u : ℝ} (hu : 3 / 4 ≤ u) :
    ssWs x be al u (ssQc x al) ≤ 31 / 40 := by
  have h1 := dspfk_al_le hx hqc
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hW := dspfk_W_eq (x := x) (al := al) (be := be) (by linarith) (by linarith) u
  have hb0 : 20 * x / 19 ≤ x + 5 * x * (al - 1) / 13 := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ x) (sub_nonneg.2 hal)
    linarith
  have hD := dspfk_d_lo hx hx2 hal hqc hb3
  have hD3 := dspfk_d_hi hx hqc hb
  have hD0 := dspfk_d_lo (be := 20 * x / 19) hx hx2 hal hqc hb0
  have hP := dspfk_P0' hx hx2 hal hqc
  have hDD : ssDg x be al ≤ ssDg x (20 * x / 19) al := by
    unfold ssDg
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - al) (sub_nonneg.2 hb)]
  have hS3' : -(5 / 4) ≤ (1 + x) ^ 3 / 4 - 3 * (1 + x) + 1 := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ x - 2)
      (by linarith [sq_nonneg (1 + x)] : (0:ℝ) ≤ (1 + x) ^ 2 + 3 * (1 + x) - 3)
    linarith
  have hK9 : 9 ≤ x * (x + 2) + al ^ 2 := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ x + 4),
      mul_nonneg (by linarith : (0:ℝ) ≤ al - 1) (by linarith : (0:ℝ) ≤ al + 1)]
  have hc : 0 ≤ 3 / 4 * (ssDg x be al + ssDg x (20 * x / 19) al) +
      ((1 + x) ^ 3 / 4 - 3 * (1 + x) + 1) := by linarith
  have hS3 : ssDg x be al ≤ (1 + x) ^ 3 := by
    linarith [dspfk_lamS hx hqc, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + x) 3]
  have hDpos : 0 ≤ ssDg x be al := by linarith
  have key : ssWs x be al u (ssQc x al) * (x * (x + 2) + al ^ 2) ^ 2 ≤
      31 / 40 * (x * (x + 2) + al ^ 2) ^ 2 := by
    rw [hW]
    have p1 := mul_nonneg (sub_nonneg.2 hDD) hc
    have p2 := mul_nonneg (mul_nonneg (sub_nonneg.2 hu) hDpos) (sub_nonneg.2 hS3)
    generalize ssDg x be al = D at *
    generalize ssDg x (20 * x / 19) al = D0 at *
    linarith [p1, p2, hP]
  exact le_of_mul_le_mul_right key (by positivity)

/-- **The incoming coefficient** `2u - nE_{L,*} ≥ 3793/8400`, for `u ≥ 3/4 + 13/2000` and
`3 ≤ n ≤ 53/15`. -/
private theorem dspfk_c (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be) {u n : ℝ}
    (hu : 3 / 4 + 13 / 2000 ≤ u) (hn : 3 ≤ n)
    (hn' : n ≤ 53 / 15) :
    3793 / 8400 ≤ 2 * u - n * ssELs x be al u (ssQc x al) := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hE := dspfk_EL_eq (x := x) (al := al) (be := be) (by linarith) (by linarith) u
  have f6 := dspfk_EL0 hx hx2 hqc hb
  have f4 := dspfk_d_hi hx hqc hb
  have f5 := dspfk_lamS hx hqc
  have key : 3793 / 8400 * (x * (x + 2) + al ^ 2) ≤
      (2 * u - n * ssELs x be al u (ssQc x al)) * (x * (x + 2) + al ^ 2) := by
    have e : (2 * u - n * ssELs x be al u (ssQc x al)) * (x * (x + 2) + al ^ 2) =
        2 * u * (x * (x + 2) + al ^ 2) -
          n * (2 * ssDg x be al * u - (1 + x) ^ 3 * (u - 1) - 3 * (1 + x) + 1) := by
      rw [← hE]; ring
    rw [e]
    have hn0 : 0 ≤ n := by linarith
    have p1 := mul_nonneg hn0 (sub_nonneg.2 f6)
    have p2 := mul_nonneg (sub_nonneg.2 hn') hK.le
    have hS : 0 ≤ (1 + x) ^ 3 - 2 * ssDg x be al - 46 / 21 * (x * (x + 2) + al ^ 2) := by
      linarith
    have p3 := mul_nonneg (mul_nonneg (sub_nonneg.2 hn) (by linarith : (0:ℝ) ≤ u - 3 / 4))
      (by linarith : 0 ≤ (1 + x) ^ 3 - 2 * ssDg x be al)
    have p4 := mul_nonneg hS (by linarith : (0:ℝ) ≤ u - 3 / 4)
    have p5 := mul_nonneg (sub_nonneg.2 hu) hK.le
    linarith [p1, p2, p3, p4, p5]
  exact le_of_mul_le_mul_right key hK

/-- **`c_u ≤ 13/3`**. -/
private theorem dspfk_cu (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be) (hb2 : be ≤ 2 * al)
    (hb3 : be ≤ x + 5 * x * (al - 1) / 13) {n : ℝ} (hn : 3 ≤ n) :
    1 / ssRA al be + (1 + x) -
        ssQc x al * (2 * (ssDg x be al / al ^ 2) + (1 - 1 / al ^ 2) * (1 + x)) +
        n * (-ssQc x al * (ssDg x be al / al ^ 2) * (1 + x) +
          ssQc x al ^ 2 * ((ssDg x be al / al ^ 2) ^ 2 +
            ssDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * (1 + x))) ≤ 13 / 3 := by
  have ha : 0 < al := by linarith
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have e : 1 / ssRA al be + (1 + x) -
        ssQc x al * (2 * (ssDg x be al / al ^ 2) + (1 - 1 / al ^ 2) * (1 + x)) +
        n * (-ssQc x al * (ssDg x be al / al ^ 2) * (1 + x) +
          ssQc x al ^ 2 * ((ssDg x be al / al ^ 2) ^ 2 +
            ssDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * (1 + x))) =
      (al + be) / al + ((1 + x) ^ 3 * (x * (x + 2) + al ^ 2) -
        2 * ssDg x be al * (x * (x + 2) + al ^ 2) +
        n * ssDg x be al * (ssDg x be al - (1 + x) ^ 3)) / (x * (x + 2) + al ^ 2) ^ 2 := by
    unfold ssRA ssQc
    field_simp
    ring
  rw [e]
  have h1 : (al + be) / al ≤ 3 := by rw [div_le_iff₀ ha]; linarith
  have f3 := dspfk_d_lo hx hx2 hal hqc hb3
  have f4 := dspfk_d_hi hx hqc hb
  have hS : (1 + x) ^ 3 ≤ 19 / 6 * (x * (x + 2) + al ^ 2) := by
    have h1 : 1 ≤ al ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left (by linarith : 1 + x ≤ 19 / 6) (sq_nonneg (1 + x))
    nlinarith
  have h2 : ((1 + x) ^ 3 * (x * (x + 2) + al ^ 2) - 2 * ssDg x be al * (x * (x + 2) + al ^ 2) +
        n * ssDg x be al * (ssDg x be al - (1 + x) ^ 3)) / (x * (x + 2) + al ^ 2) ^ 2 ≤
        4 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    have hn3 := mul_nonneg (sub_nonneg.2 hn) (by linarith : (0:ℝ) ≤ ssDg x be al)
    have p1 := mul_nonneg (by linarith : (0:ℝ) ≤ n * ssDg x be al - (x * (x + 2) + al ^ 2) / 2)
      (by linarith [dspfk_lamS hx hqc] : (0:ℝ) ≤ (1 + x) ^ 3 - ssDg x be al)
    linarith [p1, mul_le_mul_of_nonneg_right hS hK.le, mul_le_mul_of_nonneg_right f3 hK.le]
  linarith

/-- The averaged slope `-α/(s₁s₂) + 2/(s₁ + s₂) ≥ 2/(9α)` for `2α ≤ sᵢ ≤ 3α`
(the discrete form of `p - p² ≥ 2/9` on `[1/3, 1/2]`). -/
private theorem dspfk_s {s₁ s₂ : ℝ} (ha : 0 < al) (h1 : 2 * al ≤ s₁) (h1' : s₁ ≤ 3 * al)
    (h2 : 2 * al ≤ s₂) (h2' : s₂ ≤ 3 * al) : 2 / (9 * al) ≤ 2 / (s₁ + s₂) - al / (s₁ * s₂) := by
  have hs1 : 0 < s₁ := by linarith
  have hs2 : 0 < s₂ := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have a1 := sub_nonneg.2 h1
  have a1' := sub_nonneg.2 h1'
  have a2 := sub_nonneg.2 h2
  have a2' := sub_nonneg.2 h2'
  nlinarith [mul_nonneg (mul_nonneg ha.le a1') a1, mul_nonneg (mul_nonneg ha.le a1') a2,
    mul_nonneg (mul_nonneg ha.le a2') a2, mul_nonneg (mul_nonneg ha.le a2') a1,
    mul_nonneg (mul_nonneg a1' a2') (by linarith : (0:ℝ) ≤ 6 * al - s₁ - s₂)]

/-! ### The weights `n₀`, `n₁` -/

private theorem dspfk_n0 (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be) (hb2 : be ≤ 2 * al) :
    3 ≤ 2 + 4 * (4 - 3 * (2 * ssQc x al / ssRA al be)) / (5 * al - 1) ∧
      2 + 4 * (4 - 3 * (2 * ssQc x al / ssRA al be)) / (5 * al - 1) ≤ 53 / 15 := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  rw [dspfk_y (by linarith) (by linarith) be (by nlinarith)]
  have h1 := dspfk_al_le hx hqc
  have ylo := dspfk_y_lo hx hx2 hal hb
  have yhi := dspfk_y_hi hal hqc hb2
  have hk : 0 < 5 * al - 1 := by linarith
  set y := 2 * al * (al + be) / (x * (x + 2) + al ^ 2) with hy
  have y1 : 3 / 4 ≤ y := by rw [hy, le_div_iff₀ hK]; linarith
  have y2 : y ≤ 6 / 7 := by rw [hy, div_le_iff₀ hK]; linarith
  constructor
  · rw [← sub_nonneg]
    have : 2 + 4 * (4 - 3 * y) / (5 * al - 1) - 3 = (17 - 12 * y - 5 * al) / (5 * al - 1) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ hk.le; linarith
  · rw [← sub_nonneg]
    have : 53 / 15 - (2 + 4 * (4 - 3 * y) / (5 * al - 1)) =
        (115 * al - 263 + 180 * y) / (15 * (5 * al - 1)) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ (by linarith); linarith

private theorem dspfk_n0_diff (hx : 2 ≤ x) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) {b₁ b₂ : ℝ} (hb : 0 < al + b₁) (hbb : b₁ ≤ b₂) :
    2 + 4 * (4 - 3 * (2 * ssQc x al / ssRA al b₂)) / (5 * al - 1) ≤
        2 + 4 * (4 - 3 * (2 * ssQc x al / ssRA al b₁)) / (5 * al - 1) ∧
      2 + 4 * (4 - 3 * (2 * ssQc x al / ssRA al b₁)) / (5 * al - 1) -
          (2 + 4 * (4 - 3 * (2 * ssQc x al / ssRA al b₂)) / (5 * al - 1)) ≤
        5 / 6 * (b₂ - b₁) := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  rw [dspfk_y (by linarith) (by linarith) b₁ hb,
    dspfk_y (by linarith) (by linarith) b₂ (by linarith)]
  have hk : 0 < 5 * al - 1 := by linarith
  have e : 2 + 4 * (4 - 3 * (2 * al * (al + b₁) / (x * (x + 2) + al ^ 2))) / (5 * al - 1) -
      (2 + 4 * (4 - 3 * (2 * al * (al + b₂) / (x * (x + 2) + al ^ 2))) / (5 * al - 1)) =
      24 * al * (b₂ - b₁) / ((x * (x + 2) + al ^ 2) * (5 * al - 1)) := by
    field_simp; ring
  have hd : 0 ≤ b₂ - b₁ := by linarith
  constructor
  · rw [← sub_nonneg, e]; positivity
  · rw [e, div_le_iff₀ (by positivity)]
    have : 144 * al ≤ 5 * ((x * (x + 2) + al ^ 2) * (5 * al - 1)) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hd]

private theorem dspfk_n1 (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be) (hb2 : be ≤ 2 * al) :
    3 ≤ ssRA al be / ssQc x al + 4 / (5 * al - 1) ∧
      ssRA al be / ssQc x al + 4 / (5 * al - 1) ≤ 53 / 15 := by
  have hab : 0 < al * (al + be) := by nlinarith
  rw [dspfk_T (by linarith) (by linarith) be (by nlinarith)]
  have h1 := dspfk_al_le hx hqc
  have ylo := dspfk_y_lo hx hx2 hal hb
  have yhi := dspfk_y_hi hal hqc hb2
  have hk : 0 < 5 * al - 1 := by linarith
  have T1 : 7 / 3 ≤ (x * (x + 2) + al ^ 2) / (al * (al + be)) := by
    rw [le_div_iff₀ hab]; linarith
  have T2 : (x * (x + 2) + al ^ 2) / (al * (al + be)) ≤ 8 / 3 := by
    rw [div_le_iff₀ hab]; linarith
  have k1 : 2 / 3 ≤ 4 / (5 * al - 1) := by rw [le_div_iff₀ hk]; linarith
  have k2 : 4 / (5 * al - 1) ≤ 76 / 89 := by rw [div_le_iff₀ hk]; linarith
  constructor <;> linarith

private theorem dspfk_n1_diff (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    {b₁ b₂ : ℝ} (hb : 20 * x / 19 ≤ b₁) (hbb : b₁ ≤ b₂) :
    ssRA al b₂ / ssQc x al + 4 / (5 * al - 1) ≤ ssRA al b₁ / ssQc x al + 4 / (5 * al - 1) ∧
      ssRA al b₁ / ssQc x al + 4 / (5 * al - 1) - (ssRA al b₂ / ssQc x al + 4 / (5 * al - 1)) ≤
        5 / 6 * (b₂ - b₁) := by
  have hb0 : 0 < b₁ := by nlinarith
  rw [dspfk_T (by linarith) (by linarith) b₁ (by linarith),
    dspfk_T (by linarith) (by linarith) b₂ (by linarith)]
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have ha : 0 < al := by linarith
  have e : (x * (x + 2) + al ^ 2) / (al * (al + b₁)) + 4 / (5 * al - 1) -
      ((x * (x + 2) + al ^ 2) / (al * (al + b₂)) + 4 / (5 * al - 1)) =
      (x * (x + 2) + al ^ 2) * (b₂ - b₁) / (al * (al + b₁) * (al + b₂)) := by
    have : 0 < al + b₂ := by linarith
    field_simp; ring
  have hd : 0 ≤ b₂ - b₁ := by linarith
  have hp : 0 < al * (al + b₁) * (al + b₂) := mul_pos (mul_pos ha (by linarith)) (by linarith)
  constructor
  · rw [← sub_nonneg, e]; exact div_nonneg (mul_nonneg hK.le hd) hp.le
  · rw [e, div_le_iff₀ hp]
    have ylo := dspfk_y_lo hx hx2 hal hb
    have : 6 * (x * (x + 2) + al ^ 2) ≤ 5 * (al * (al + b₁) * (al + b₂)) := by
      have h3 : 308 / 95 ≤ al + b₂ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 (by nlinarith : (0:ℝ) ≤ al * (al + b₁))]
    nlinarith [mul_le_mul_of_nonneg_right this hd]

/-! ### The central ceiling `ū` -/

private theorem dspfk_VG : ssVG x - 3 / 4 =
    (x - 1) ^ 2 * (71 * x ^ 2 + 48 * x + 1) / (96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3)) := by
  unfold ssVG; ring

private theorem dspfk_Ga (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    13 * (x - 1 + 5 * x * (5 * x - 8) / 156) ≤ 2000 * ((x - 1) * (ssVG x - 3 / 4)) := by
  rw [dspfk_VG]
  have hd : 0 < 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by positivity
  rw [mul_div_assoc', mul_div_assoc', le_div_iff₀ hd]
  have hh : 0 ≤ x - 2 := by linarith
  have hh6 : x - 2 ≤ 1 / 6 := by linarith
  nlinarith [pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4, pow_nonneg hh 5,
    mul_le_mul_of_nonneg_left hh6 (pow_nonneg hh 5)]

private theorem dspfk_Gb (hx : 2 ≤ x) : (x - 1) / 5808 ≤ (x - 1) * (ssVG x - 3 / 4) := by
  rw [dspfk_VG]
  have hd : 0 < 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by norm_num) hd]
  have hh : 0 ≤ x - 2 := by linarith
  have h1 : 0 ≤ x - 1 := by linarith
  have : 0 ≤ 5808 * ((x - 1) ^ 2 * (71 * x ^ 2 + 48 * x + 1)) -
      96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by
    nlinarith [pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4]
  nlinarith [mul_nonneg h1 this]

private theorem dspfk_Gc (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    (x - 1) * (ssVG x - 3 / 4) ≤ 7 / 1000 * (20 * x / 19 - 1) ^ 2 + (x - 1) / 5808 := by
  rw [dspfk_VG]
  have hd : 0 < 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by positivity
  rw [mul_div_assoc', div_le_iff₀ hd]
  have hh : 0 ≤ x - 2 := by linarith
  have hh6 : x - 2 ≤ 1 / 6 := by linarith
  nlinarith [pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4, pow_nonneg hh 5, pow_nonneg hh 6,
    mul_le_mul_of_nonneg_left hh6 hh, mul_le_mul_of_nonneg_left hh6 (pow_nonneg hh 2),
    mul_le_mul_of_nonneg_left hh6 (pow_nonneg hh 3)]

/-- `ū ≥ 3/4 + 13/2000`. -/
private theorem dspfk_u_lo (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hqc : 6 * al ^ 2 ≤ x * (x + 2))
    (hb : x ≤ be) (hb3 : be ≤ x + 5 * x * (al - 1) / 13) : 3 / 4 + 13 / 2000 ≤ dspfUCB x be := by
  have h1 := dspfk_al_le hx hqc
  have hG := dspfk_Ga hx hx2
  unfold dspfUCB
  have hb1 : 0 < be - 1 := by linarith
  have hbu : be - 1 ≤ x - 1 + 5 * x * (5 * x - 8) / 156 := by nlinarith
  rw [add_le_add_iff_left, le_div_iff₀ hb1]
  nlinarith

/-- `ū` decreases in `β` with slope above `-7/1000`. -/
private theorem dspfk_u_diff (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) {b₁ b₂ : ℝ}
    (hb : 20 * x / 19 ≤ b₁) (hbb : b₁ ≤ b₂) :
    dspfUCB x b₂ ≤ dspfUCB x b₁ ∧ dspfUCB x b₁ - dspfUCB x b₂ ≤ 7 / 1000 * (b₂ - b₁) := by
  have hGb := dspfk_Gb hx
  have hGc := dspfk_Gc hx hx2
  have h1 : 0 < b₁ - 1 := by linarith
  have h2 : 0 < b₂ - 1 := by linarith
  unfold dspfUCB
  generalize (x - 1) * (ssVG x - 3 / 4) = G at *
  have e : 3 / 4 + (G + (b₁ - x) / 5808) / (b₁ - 1) - (3 / 4 + (G + (b₂ - x) / 5808) / (b₂ - 1)) =
      (G - (x - 1) / 5808) * (b₂ - b₁) / ((b₁ - 1) * (b₂ - 1)) := by
    field_simp; ring
  have hd : 0 ≤ b₂ - b₁ := by linarith
  have hp : 0 < (b₁ - 1) * (b₂ - 1) := mul_pos h1 h2
  constructor
  · rw [← sub_nonneg, e]; exact div_nonneg (mul_nonneg (by linarith) hd) hp.le
  · rw [e, div_le_iff₀ hp]
    have hsq : (20 * x / 19 - 1) ^ 2 ≤ (b₁ - 1) * (b₂ - 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hd, mul_nonneg (sub_nonneg.2 hGc) hd]

/-! ### The β-step at fixed `u` and the `u`-step -/

/-- The log step `log(s₂/s₁) ≥ 2(s₂ - s₁)/(s₂ + s₁)`, `sᵢ = α + βᵢ`, in the notation of the face tests. -/
private theorem dspfk_logstep (hx : 0 < x) (hal : 1 ≤ al) {b₁ b₂ : ℝ} (hs1 : 0 < al + b₁)
    (hbb : b₁ ≤ b₂) :
    2 * (b₂ - b₁) / ((al + b₁) + (al + b₂)) ≤
      log (2 * ssQc x al / ssRA al b₂) - log (2 * ssQc x al / ssRA al b₁) := by
  have hs2 : 0 < al + b₂ := by linarith
  have ha : 0 < al := by linarith
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  rw [dspfk_y hx hal b₁ hs1, dspfk_y hx hal b₂ hs2, ← Real.log_div (by positivity) (by positivity)]
  have hz : 2 * al * (al + b₂) / (x * (x + 2) + al ^ 2) /
      (2 * al * (al + b₁) / (x * (x + 2) + al ^ 2)) = (al + b₂) / (al + b₁) := by
    field_simp
  rw [hz]
  have hp := ss_log_ge_pade (z := (al + b₂) / (al + b₁)) (by rw [le_div_iff₀ hs1]; linarith)
  have hz' : 2 * ((al + b₂) / (al + b₁) - 1) / ((al + b₂) / (al + b₁) + 1) =
      2 * (b₂ - b₁) / ((al + b₁) + (al + b₂)) := by
    field_simp; ring
  linarith

/-- **The β-step at fixed incoming norm** (in secant form):
for `u ≥ 3/4 + 13/2000` the test increases by at least `(91/3000)(β₂ - β₁)`.
The proof uses exact secant identities (`w_*` quadratic and `E_{L,*}` affine in `β`) and
`log(s₂/s₁) ≥ 2(s₂ - s₁)/(s₂ + s₁)`. -/
private theorem dspfk_stepA (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) {b₁ b₂ : ℝ} (hb : 20 * x / 19 ≤ b₁) (hbb : b₁ ≤ b₂)
    (hb2 : b₂ ≤ 2 * al) (hb3 : b₂ ≤ x + 5 * x * (al - 1) / 13) {u N₁ N₂ : ℝ}
    (hu : 3 / 4 + 13 / 2000 ≤ u) (hN₂ : 3 ≤ N₂) (hN₂' : N₂ ≤ 53 / 15) (hN : N₂ ≤ N₁)
    (hN' : N₁ - N₂ ≤ 5 / 6 * (b₂ - b₁)) :
    dspfFn x b₁ al u (ssQc x al) N₁ (log (2 * ssQc x al / ssRA al b₁)) + 91 / 3000 * (b₂ - b₁) ≤
      dspfFn x b₂ al u (ssQc x al) N₂ (log (2 * ssQc x al / ssRA al b₂)) := by
  have ha : 0 < al := by linarith only [hal]
  have h1 := dspfk_al_le hx hqc
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hxb : al < b₁ := by linarith only [h1, hb, hx]
  have hs1 : 0 < al + b₁ := by linarith only [ha, hxb]
  have hs2 : 0 < al + b₂ := by linarith only [hs1, hbb]
  have hd : 0 ≤ b₂ - b₁ := by linarith only [hbb]
  have hbm1 : 20 * x / 19 ≤ (b₁ + b₂) / 2 := by linarith only [hb, hbb]
  have hb13 : b₁ ≤ x + 5 * x * (al - 1) / 13 := by linarith only [hbb, hb3]
  -- the bounds
  have hl := dspfk_logstep (by linarith only [hx]) (by linarith only [hal]) hs1 hbb
  have hc := dspfk_c hx hx2 hal hqc hbm1 hu hN₂ hN₂'
  have hW1 := dspfk_W_le hx hx2 hal hqc hb hb13 (u := u) (by linarith only [hu])
  have hsI := dspfk_s ha (s₁ := al + b₁) (s₂ := al + b₂) (by linarith only [hxb])
    (by linarith only [hb2, hbb]) (by linarith only [hxb, hbb]) (by linarith only [hb2])
  have he : ssQc x al * (2 * al - 2 * x) / al ^ 2 = (2 * al - 2 * x) / (x * (x + 2) + al ^ 2) := by
    unfold ssQc; field_simp
  have he' : ssQc x al * (2 * al - 2 * x) / al ^ 2 ≤ -(7 / 40) := by
    rw [he, div_le_iff₀ hK]; linarith only [dspfk_e hx hx2 hqc]
  set q := ssQc x al with hq
  set bm := (b₁ + b₂) / 2 with hbm
  -- secant identities
  have hW := dspfk_W_diff (x := x) (al := al) b₁ b₂ u q
  have hE := dspfk_EL_diff (x := x) (al := al) b₁ b₂ u q
  have hEm := dspfk_EL_diff (x := x) (al := al) b₁ bm u q
  have hEavg : (ssELs x b₁ al u q + ssELs x b₂ al u q) / 2 = ssELs x bm al u q := by
    rw [hbm] at hEm; linear_combination (1 / 2) * hE - hEm
  -- assemble
  have hr : ∀ b : ℝ, 0 < al + b →
      (u - 1) / ssRA al b + ssRA al b = (u - 1) * (al + b) / al + al / (al + b) := by
    intro b hb'
    unfold ssRA; field_simp
  unfold dspfFn
  rw [hr b₁ hs1, hr b₂ hs2]
  have hr2 : (u - 1) * (al + b₂) / al + al / (al + b₂) -
      ((u - 1) * (al + b₁) / al + al / (al + b₁)) =
      (b₂ - b₁) * ((u - 1) / al + 2 / ((al + b₁) + (al + b₂)) -
        al / ((al + b₁) * (al + b₂))) - 2 * (b₂ - b₁) / ((al + b₁) + (al + b₂)) := by
    field_simp; ring
  -- lower bound of the `u - U(p)` part
  have hB : (u - 1) / al + 2 / (9 * al) ≥ -(1532 / 72000 * (95 / 108)) := by
    have : (u - 1) / al + 2 / (9 * al) = (u - 7 / 9) / al := by field_simp; ring
    rw [this, ge_iff_le, le_div_iff₀ ha]; linarith only [hu, hal]
  have t1 : (b₂ - b₁) * (-(1532 / 72000 * (95 / 108))) ≤ (b₂ - b₁) * ((u - 1) / al +
      2 / ((al + b₁) + (al + b₂)) - al / ((al + b₁) * (al + b₂))) := by
    apply mul_le_mul_of_nonneg_left _ hd; linarith only [hB, hsI]
  have t2 : (b₂ - b₁) * (7 / 40 * (3793 / 8400)) ≤
      (b₂ - b₁) * (-(q * (2 * al - 2 * x) / al ^ 2) * (2 * u - N₂ * ssELs x bm al u q)) := by
    apply mul_le_mul_of_nonneg_left _ hd
    exact mul_le_mul (by linarith only [he']) hc (by norm_num) (by linarith only [he'])
  have t3 : -(5 / 6 * (b₂ - b₁) / 40) ≤ (N₂ - N₁) * (ssWs x b₁ al u q - 3 / 4) := by
    rcases le_or_gt 0 (ssWs x b₁ al u q - 3 / 4) with hw | hw
    · have m1 := mul_le_mul_of_nonneg_right hN' hw
      have m2 := mul_le_mul_of_nonneg_left
        (by linarith only [hW1] : ssWs x b₁ al u q - 3 / 4 ≤ 1 / 40)
        (by linarith only [hd] : (0:ℝ) ≤ 5 / 6 * (b₂ - b₁))
      linarith only [m1, m2]
    · have := mul_nonneg_of_nonpos_of_nonpos (by linarith only [hN] : N₂ - N₁ ≤ 0) hw.le
      linarith only [this, hd]
  rw [← hEavg] at t2
  have hWW : N₂ * (ssWs x b₂ al u q - 3 / 4) - N₁ * (ssWs x b₁ al u q - 3 / 4) =
      N₂ * (ssWs x b₂ al u q - ssWs x b₁ al u q) + (N₂ - N₁) * (ssWs x b₁ al u q - 3 / 4) := by
    ring
  rw [hW] at hWW
  linarith only [hWW, hE, t1, t2, t3, hl, hr2, hd, hEavg, hW]

/-- The β-step and the `u`-step combined: the test at `(β₁, ū(β₁))` is below the test at
`(β₂, ū(β₂))` for any weights `N₁ ≥ N₂` in `[3, 53/15]` with `N₁ - N₂ ≤ (5/6)(β₂ - β₁)`. -/
private theorem dspfk_core (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) {b₁ b₂ : ℝ} (hb : 20 * x / 19 ≤ b₁) (hbb : b₁ ≤ b₂)
    (hb2 : b₂ ≤ 2 * al) (hb3 : b₂ ≤ x + 5 * x * (al - 1) / 13) {N₁ N₂ : ℝ} (hN₁ : 3 ≤ N₁)
    (hN₂ : 3 ≤ N₂) (hN₂' : N₂ ≤ 53 / 15) (hN : N₂ ≤ N₁) (hN' : N₁ - N₂ ≤ 5 / 6 * (b₂ - b₁)) :
    dspfFn x b₁ al (dspfUCB x b₁) (ssQc x al) N₁ (log (2 * ssQc x al / ssRA al b₁)) ≤
      dspfFn x b₂ al (dspfUCB x b₂) (ssQc x al) N₂ (log (2 * ssQc x al / ssRA al b₂)) := by
  have hu2 := dspfk_u_lo hx hx2 hqc (by nlinarith : x ≤ b₂) hb3
  obtain ⟨hu12, hu12'⟩ := dspfk_u_diff hx hx2 hb hbb
  have hA := dspfk_stepA hx hx2 hal hqc hb hbb hb2 hb3 hu2 hN₂ hN₂' hN hN'
  have hB := dspfk_u_aff (x := x) (be := b₁) (al := al) (dspfUCB x b₁) (dspfUCB x b₂)
    (ssQc x al) N₁ (log (2 * ssQc x al / ssRA al b₁))
  have hcu := dspfk_cu hx hx2 hal hqc hb (by linarith) (by linarith) hN₁
  have hm := mul_le_mul_of_nonpos_left hcu (by linarith : dspfUCB x b₂ - dspfUCB x b₁ ≤ 0)
  rw [← hB] at hm
  linarith

/-- **β-monotonicity on the central face**: on
`2 ≤ x ≤ 13/6`, `α ≥ 108/95`, `6α² ≤ x(x + 2)`, for `20x/19 ≤ β₁ ≤ β₂ ≤ min{2α, x + 5x(α - 1)/13}`,
`F_i(x, α, β₁; ū) ≤ F_i(x, α, β₂; ū)` at `q = q_c`.
The β-derivative bound is used in secant form: the `u`-step
`c_u(ū₂ - ū₁) ≥ -(91/3000)Δβ` (`c_u ≤ 13/3`, `ū_β ≥ -7/1000`) and the β-step at fixed `u`
(`≥ (91/3000)Δβ`, from `-d_β ≥ 7/40`, `2u - nE_L ≥ 3793/8400`, `w ≤ 31/40`, `|Δn| ≤ (5/6)Δβ`,
`p - p² ≥ 2/9` and `log(s₂/s₁) ≥ 2(s₂ - s₁)/(s₂ + s₁)`). -/
theorem dspf_beta_mono {x al be₁ be₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be₁) (hbb : be₁ ≤ be₂)
    (hb2 : be₂ ≤ 2 * al) (hb2' : be₂ ≤ x + 5 * x * (al - 1) / 13) :
    dspfF0 x be₁ al (dspfUCB x be₁) (ssQc x al) ≤ dspfF0 x be₂ al (dspfUCB x be₂) (ssQc x al) ∧
      dspfF1 x be₁ al (dspfUCB x be₁) (ssQc x al) ≤
        dspfF1 x be₂ al (dspfUCB x be₂) (ssQc x al) := by
  have hb1 : 0 < al + be₁ := by nlinarith
  constructor
  · obtain ⟨n1, -⟩ := dspfk_n0 hx hx2 hal hqc hb (by linarith)
    obtain ⟨n2, n2'⟩ := dspfk_n0 hx hx2 hal hqc (by linarith) hb2
    obtain ⟨d1, d2⟩ := dspfk_n0_diff hx hal hqc hb1 hbb
    exact dspfk_core hx hx2 hal hqc hb hbb hb2 hb2' n1 n2 n2' d1 d2
  · obtain ⟨n1, -⟩ := dspfk_n1 hx hx2 hal hqc hb (by linarith)
    obtain ⟨n2, n2'⟩ := dspfk_n1 hx hx2 hal hqc (by linarith) hb2
    obtain ⟨d1, d2⟩ := dspfk_n1_diff hx hx2 hal hb hbb
    exact dspfk_core hx hx2 hal hqc hb hbb hb2 hb2' n1 n2 n2' d1 d2

end Beta

/-! ### The central endpoint -/

section Endpoint

variable {x : ℝ}

private theorem dspfk_EL_div {al be : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (u : ℝ) :
    ssELs x be al u (ssQc x al) =
      (2 * ssDg x be al * u - (1 + x) ^ 3 * (u - 1) - 3 * (1 + x) + 1) /
        (x * (x + 2) + al ^ 2) :=
  eq_div_of_mul_eq (by positivity) (dspfk_EL_eq hx hal u)

private theorem dspfk_W_div {al be : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (u : ℝ) :
    ssWs x be al u (ssQc x al) =
      ((1 + x) ^ 4 - (1 + x) ^ 3 + (1 + x) ^ 2 + ssDg x be al ^ 2 * u -
        ssDg x be al * ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1)) / (x * (x + 2) + al ^ 2) ^ 2 :=
  eq_div_of_mul_eq (by positivity) (dspfk_W_eq hx hal u)

/-- The numerator `N₀` of `-F̄₀` in `h = x - 2`. -/
private noncomputable def dspfkN0 (h : ℝ) : ℝ :=
  2413534919007629868137070688732034410098588 - 26254301047758970029152099025587912698031754 * h
    + 70210600598363805662951295893340160342087806 * h ^ 2
    + 1231260666018762280352657134177895028581204721 * h ^ 3
    + 4498601593628546463194691113956045245845235813 * h ^ 4
    + 8821418563599351427456297390873555558331292630 * h ^ 5
    + 11155720247429732414771122665383587490751693525 * h ^ 6
    + 9824378285326805045976584313731635978432494375 * h ^ 7
    + 6260501806502667667485414232430338901594628125 * h ^ 8
    + 2940300218027638502485142956836091990035603125 * h ^ 9
    + 1022727874541701156868178804828673324875796875 * h ^ 10
    + 261642089606588828515012621238014687723906250 * h ^ 11
    + 48258209590394165569656174095510203980468750 * h ^ 12
    + 6179636018751166406735015238165612880859375 * h ^ 13
    + 513881158757646744686699205111204707031250 * h ^ 14
    + 24541332826675464716798510630404980468750 * h ^ 15
    + 526347440193952489082215283692382812500 * h ^ 16
    + 3679624501492989173967224121093750000 * h ^ 17

/-- The numerator `N₁` of `-F̄₁` in `h = x - 2`. -/
private noncomputable def dspfkN1 (h : ℝ) : ℝ :=
  1066695320050756620827029638308435448 - 11554078212748962290130793009859116224 * h
    + 43895838980852054366148716751111284496 * h ^ 2
    + 530856372984235900631901782361718380936 * h ^ 3
    + 1660483178009696646905224092812029954443 * h ^ 4
    + 2808623110857556111554791547311208452940 * h ^ 5
    + 3038756659112858923251352168551179093150 * h ^ 6
    + 2258207973164675397156836896798409091500 * h ^ 7
    + 1192602713354221799935768401537330971250 * h ^ 8
    + 453660106978019845283139933325845987500 * h ^ 9
    + 124044858401168171760883592299032562500 * h ^ 10
    + 23953632656597836417010188357685000000 * h ^ 11
    + 3143798989151344183582072553027734375 * h ^ 12
    + 260593616101531121669269257914062500 * h ^ 13 + 11745215959060390878951090878906250 * h ^ 14
    + 194414857058510946990966796875000 * h ^ 15

private theorem dspfk_N0 {h : ℝ} (hh : 0 ≤ h) : 0 < dspfkN0 h := by
  unfold dspfkN0
  linarith [mul_nonneg hh (sq_nonneg (h - 1 / 12)),
    sq_nonneg (h - 185625185810964961650020718291205720633251011 /
      2937820923749235758809537616956330650015522768),
    pow_nonneg hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8,
    pow_nonneg hh 9, pow_nonneg hh 10, pow_nonneg hh 11, pow_nonneg hh 12, pow_nonneg hh 13,
    pow_nonneg hh 14, pow_nonneg hh 15, pow_nonneg hh 16, pow_nonneg hh 17]

private theorem dspfk_N1 {h : ℝ} (hh : 0 ≤ h) : 0 < dspfkN1 h := by
  unfold dspfkN1
  linarith [mul_nonneg hh (sq_nonneg (h - 1 / 12)),
    sq_nonneg (h - 1128931911327204974491119329105674443 /
      19610652021465388316760347725145335504),
    pow_nonneg hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8,
    pow_nonneg hh 9, pow_nonneg hh 10, pow_nonneg hh 11, pow_nonneg hh 12, pow_nonneg hh 13,
    pow_nonneg hh 14, pow_nonneg hh 15]

/-- The denominator `D*` of the endpoint identities. -/
private noncomputable def dspfkDs (x : ℝ) : ℝ :=
  21780000 * x * (x + 1) * (15 * x + 416) * (15 * x + 511) * (20 * x - 19) * (515 * x + 511) *
    (13 * x ^ 2 + 14 * x + 3) * (490325 * x ^ 2 + 2287310 * x + 1827847)

/-- The endpoint data in closed form: `r_A`, `q_c`, `y = 2q_c/r_A`, `ū`, `D`, `K`. -/
private theorem dspfk_end_forms (hx : 2 ≤ x) :
    ssRA (dspfamin x) (20 * x / 19) = (15 * x + 511) / (515 * x + 511) ∧
      ssQc x (dspfamin x) = (15 * x + 511) ^ 2 / (225850 * x ^ 2 + 466580 * x + 261121) ∧
      2 * ssQc x (dspfamin x) / ssRA (dspfamin x) (20 * x / 19) =
        2 * (15 * x + 511) * (515 * x + 511) / (225850 * x ^ 2 + 466580 * x + 261121) ∧
      dspfUCB x (20 * x / 19) = (2428375 * x ^ 5 + 2173335 * x ^ 4 - 1346212 * x ^ 3 -
        2130320 * x ^ 2 - 600039 * x - 2299) /
        (11616 * x * (x + 1) * (20 * x - 19) * (13 * x ^ 2 + 14 * x + 3)) ∧
      ssDg x (20 * x / 19) (dspfamin x) = (-459775 * x ^ 2 + 977580 * x + 486746) / 225625 ∧
      x * (x + 2) + dspfamin x ^ 2 = (225850 * x ^ 2 + 466580 * x + 261121) / 225625 := by
  have hx0 : 0 < x := by linarith
  have h1' : x * 20 - 19 ≠ 0 := by linarith
  have hr : ssRA (dspfamin x) (20 * x / 19) = (15 * x + 511) / (515 * x + 511) := by
    unfold ssRA dspfamin; field_simp; ring
  have hq : ssQc x (dspfamin x) = (15 * x + 511) ^ 2 / (225850 * x ^ 2 + 466580 * x + 261121) := by
    unfold ssQc dspfamin; field_simp; ring
  refine ⟨hr, hq, ?_, ?_, ?_, ?_⟩
  · rw [hq, hr]; field_simp
  · unfold dspfUCB ssVG
    rw [show 20 * x / 19 - 1 = (20 * x - 19) / 19 by ring, show 20 * x / 19 - x = x / 19 by ring]
    field_simp; ring
  · unfold ssDg dspfamin; ring
  · unfold dspfamin; ring

/-- The log majorant at the endpoint: `log y = L*(y) - δ`, `δ ≥ 0`. -/
private theorem dspfk_end_log (hx : 2 ≤ x) : ∃ δ : ℝ, 0 ≤ δ ∧
    log (2 * (15 * x + 511) * (515 * x + 511) / (225850 * x ^ 2 + 466580 * x + 261121)) =
      -40153 / 180000 + 2 * (5 * (2 * (15 * x + 511) * (515 * x + 511) /
        (225850 * x ^ 2 + 466580 * x + 261121)) - 4) /
        (5 * (2 * (15 * x + 511) * (515 * x + 511) / (225850 * x ^ 2 + 466580 * x + 261121)) + 4) -
      δ := by
  have hx0 : 0 < x := by linarith
  have hQ : 0 < 225850 * x ^ 2 + 466580 * x + 261121 := by positivity
  have hY0 : 0 < 2 * (15 * x + 511) * (515 * x + 511) / (225850 * x ^ 2 + 466580 * x + 261121) := by
    positivity
  have hY7 : 2 * (15 * x + 511) * (515 * x + 511) / (225850 * x ^ 2 + 466580 * x + 261121) ≤
      6 / 7 := by
    rw [div_le_iff₀ hQ]
    linarith [mul_nonneg hx0.le (by linarith : (0:ℝ) ≤ x - 2)]
  exact ⟨_, sub_nonneg.2 (dspf_log_maj hY0 hY7), by ring⟩

private theorem dspfk_Ds_pos (hx : 2 ≤ x) : 0 < dspfkDs x := by
  have hx0 : 0 < x := by linarith
  have h20 : 0 < 20 * x - 19 := by linarith
  have hA : 0 < 21780000 * x * (x + 1) * (15 * x + 416) * (15 * x + 511) := by positivity
  exact mul_pos (mul_pos (mul_pos (mul_pos hA h20) (by positivity)) (by positivity))
    (by positivity)

private theorem dspfk_end0 (hx : 2 ≤ x) :
    dspfF0 x (20 * x / 19) (dspfamin x) (dspfUCB x (20 * x / 19)) (ssQc x (dspfamin x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have ha1 : 1 ≤ dspfamin x := by unfold dspfamin; linarith
  have h1' : x * 20 - 19 ≠ 0 := by linarith
  have hk : x * 75 + 2080 ≠ 0 := by positivity
  have hk' : 2080 + x * 75 ≠ 0 := by positivity
  have hk'' : (x * 15 + 511) * 5 - 475 ≠ 0 := by linarith
  obtain ⟨hr, hq, hy, hu, hD, hK⟩ := dspfk_end_forms hx
  obtain ⟨δ, hδ0, hδ⟩ := dspfk_end_log hx
  have ha : dspfamin x = (15 * x + 511) / 475 := rfl
  have hQ : 0 < 225850 * x ^ 2 + 466580 * x + 261121 := by positivity
  have hN := div_pos (dspfk_N0 (by linarith : (0:ℝ) ≤ x - 2))
    (mul_pos (dspfk_Ds_pos hx) (pow_pos hQ 3))
  unfold dspfF0 dspfFn
  rw [dspfk_EL_div hx0 ha1, dspfk_W_div hx0 ha1, hy, hr, hu, hD, hK, hq, ha, hδ]
  suffices h : -(dspfkN0 (x - 2) /
      (dspfkDs x * (225850 * x ^ 2 + 466580 * x + 261121) ^ 3)) - δ < 0 by
    convert h using 1
    unfold dspfkN0 dspfkDs
    field_simp
    ring
  linarith

private theorem dspfk_end1 (hx : 2 ≤ x) :
    dspfF1 x (20 * x / 19) (dspfamin x) (dspfUCB x (20 * x / 19)) (ssQc x (dspfamin x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have ha1 : 1 ≤ dspfamin x := by unfold dspfamin; linarith
  have h1' : x * 20 - 19 ≠ 0 := by linarith
  have hk : x * 75 + 2080 ≠ 0 := by positivity
  have hk' : 2080 + x * 75 ≠ 0 := by positivity
  have hk'' : (x * 15 + 511) * 5 - 475 ≠ 0 := by linarith
  obtain ⟨hr, hq, hy, hu, hD, hK⟩ := dspfk_end_forms hx
  obtain ⟨δ, hδ0, hδ⟩ := dspfk_end_log hx
  have ha : dspfamin x = (15 * x + 511) / 475 := rfl
  have hQ : 0 < 225850 * x ^ 2 + 466580 * x + 261121 := by positivity
  have hN := div_pos (dspfk_N1 (by linarith : (0:ℝ) ≤ x - 2))
    (mul_pos (dspfk_Ds_pos hx) (pow_pos hQ 2))
  unfold dspfF1 dspfFn
  rw [dspfk_EL_div hx0 ha1, dspfk_W_div hx0 ha1, hy, hr, hu, hD, hK, hq, ha, hδ]
  suffices h : -(dspfkN1 (x - 2) /
      (dspfkDs x * (225850 * x ^ 2 + 466580 * x + 261121) ^ 2)) - δ < 0 by
    convert h using 1
    unfold dspfkN1 dspfkDs
    field_simp
    ring
  linarith

/-- **The central endpoint signs**: for `2 ≤ x ≤ 13/6`, at
`α = a_min(x)`, `β = 20x/19`, `q = q_c`, `u = ū`: `F₀ < 0`, `F₁ < 0`.
After the log majorant `dspf_log_maj` (`y = 2q_c/r_A ≤ 6/7`), `-F̄ᵢ = Nᵢ(x - 2)/(D*Q^{3-i})` with
the integer polynomials `N₀`, `N₁` (one univariate identity each), and `Nᵢ(h) > 0` for
`h ≥ 0` (a cubic sum of squares plus nonnegative higher terms). -/
theorem dspf_central_endpoint {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    dspfF0 x (20 * x / 19) (dspfamin x) (dspfUCB x (20 * x / 19)) (ssQc x (dspfamin x)) < 0 ∧
      dspfF1 x (20 * x / 19) (dspfamin x) (dspfUCB x (20 * x / 19)) (ssQc x (dspfamin x)) < 0 := by
  have _ := hx2
  exact ⟨dspfk_end0 hx, dspfk_end1 hx⟩

end Endpoint

end SmoothedOctagon

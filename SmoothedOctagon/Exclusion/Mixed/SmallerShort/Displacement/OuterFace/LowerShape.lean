module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.Convexity

/-!
# Smaller-short window, displacement, outer face: the lower shape increases with the beta slope

The outer face sign `dsp_outer_face_proof`, third part. At the lower shape
`r_* = 13/(5S)` (`α = a_* = 5(x + 1)/13`) and `5/2 ≤ n ≤ 7/2`, `3/5 ≤ C ≤ 5/6`:
`(P_n)_C > -53/2000`, `(A_n)_C > 0`, `A_n < 4`, `U_C > -3/4000` and `f(Z) ≥ f(3)`, so
`(R_n)_C > 3487/45414000 > 0`. The `C`-derivatives of the quartics are explicit:
every coefficient is quadratic in `C`, so its second-order Taylor expansion in `C` is exact
(`dsp_hd_quad`).

## Main API

* `dspoAC`, `dspoPC`, `dspoVC`, `dspoGC`: the `C`-derivatives; `dspo_hdC_G`.
* `dspoIl`-`dspoL`: the printed polynomials.
* `dspo_low_mono`: `G(x, C, n, r_*) ≤ G(x, C', n, r_*)` for `3/5 ≤ C ≤ C' ≤ 5/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- A function that equals its exact second-order Taylor polynomial at `t` has derivative `f'`. -/
theorem dsp_hd_quad {f : ℝ → ℝ} {t f' k : ℝ} (h : ∀ s, f s = f t + f' * (s - t) + k * (s - t) ^ 2) :
    HasDerivAt f f' t := by
  have hd : HasDerivAt (fun s => f t + f' * (s - t) + k * (s - t) ^ 2) f' t := by
    have := ((((hasDerivAt_id t).sub_const t).const_mul f').const_add (f t)).add
      ((((hasDerivAt_id t).sub_const t).fun_pow 2).const_mul k)
    refine this.congr_deriv ?_
    simp
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall h)

/-! ### The `C`-derivatives -/

/-- `(A_n)_C`: the `C`-derivatives of the printed coefficients. -/
noncomputable def dspoAC (x C n r : ℝ) : ℝ :=
  ((n * (8 * C - 12 * x - 8) + 21) +
    (n * (-16 * C * x - 16 * C + 12 * x ^ 2 + 28 * x + 8) + (28 * x - 21)) * r +
    (n * (8 * C * x ^ 2 + 32 * C * x + 8 * C - 28 * x ^ 2 - 10 * x + 2) - 28 * x) * r ^ 2 +
    n * (-16 * C * x ^ 2 - 16 * C * x + 8 * x ^ 3 + 10 * x ^ 2 - 8 * x - 2) * r ^ 3 +
    n * (8 * C * x ^ 2 - 8 * x ^ 3 + 6 * x ^ 2 + 2 * x) * r ^ 4) / 49

/-- `(A_n)_{CC}`. -/
noncomputable def dspoACC (x n r : ℝ) : ℝ :=
  n * (8 + (-16 * x - 16) * r + (8 * x ^ 2 + 32 * x + 8) * r ^ 2 + (-16 * x ^ 2 - 16 * x) * r ^ 3 +
    8 * x ^ 2 * r ^ 4) / 49

/-- `(P_n)_C`. -/
noncomputable def dspoPC (x C n r : ℝ) : ℝ :=
  3 / 4 * dspoAC x C n r +
    ((n * (12 * x ^ 2 + 24 * x) + (-49 * x - 49)) +
      (n * (-12 * x ^ 3 - 36 * x ^ 2 - 24 * x) + (49 * x + 49)) * r +
      n * (12 * x ^ 3 + 22 * x ^ 2 - 2 * x - 2) * r ^ 2 + n * (2 * x ^ 3 + 4 * x ^ 2 + 4 * x + 2) * r ^ 3 +
      n * (-2 * x ^ 3 - 2 * x ^ 2 - 2 * x) * r ^ 4) / (49 * (x + 1))

/-- `U_C = V_C = -c(x - 1)r(1 - r)/H²`. -/
noncomputable def dspoVC (x C r : ℝ) : ℝ :=
  -(dspoc x * (x - 1) * r * (1 - r)) / (C + (x - C - 1) * r) ^ 2

/-- `(R_n)_C = (P_n)_C + V_CA_n + V(A_n)_C + (1 - r)f(Z)`. -/
noncomputable def dspoGC (x C n r : ℝ) : ℝ :=
  dspoPC x C n r + dspoVC x C r * dspoA x C n r + dspoV x C r * dspoAC x C n r +
    (1 - r) * dspof (1 + C + (x - C) * r)

section DerivC

variable {x n r t : ℝ}

theorem dspo_hdC_A : HasDerivAt (fun C => dspoA x C n r) (dspoAC x t n r) t := by
  refine dsp_hd_quad (k := dspoACC x n r / 2) fun s => ?_
  unfold dspoA dspoAC dspoACC dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3
    dspoα4 dspoβ0 dspoβ1 dspoβ2
  ring

theorem dspo_hdC_P : HasDerivAt (fun C => dspoP x C n r) (dspoPC x t n r) t := by
  refine dsp_hd_quad (k := 3 / 4 * dspoACC x n r / 2) fun s => ?_
  unfold dspoP dspoPC dspoAC dspoACC dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0 dspoAc1
    dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2 dspoγ0 dspoγ1
    dspoγ2 dspoγ3 dspoγ4 dspoδ0 dspoδ1 dspoδ2
  ring

theorem dspo_hdC_V (hH : t + (x - t - 1) * r ≠ 0) :
    HasDerivAt (fun C => dspoV x C r) (dspoVC x t r) t := by
  have hHd : HasDerivAt (fun C => C + (x - C - 1) * r) (1 - r) t := by
    have := (hasDerivAt_id t).add ((((hasDerivAt_id t).const_sub x).sub_const 1).mul_const r)
    refine this.congr_deriv ?_
    ring
  have := ((hasDerivAt_const t (dspoc x * (x - 1) * r)).fun_div hHd hH).const_add (dspoc x)
  unfold dspoV dspoVC
  refine this.congr_deriv ?_
  field_simp
  ring

theorem dspo_hdC_Phi (hZ : 0 < 1 + t + (x - t) * r) :
    HasDerivAt (fun C => dspoPhi x C r) ((1 - r) * dspof (1 + t + (x - t) * r)) t := by
  have hZd : HasDerivAt (fun C => 1 + C + (x - C) * r) (1 - r) t := by
    have := ((hasDerivAt_id t).const_add 1).add (((hasDerivAt_id t).const_sub x).mul_const r)
    refine this.congr_deriv ?_
    ring
  have hK : (5 * (1 + t + (x - t) * r) + 14) ≠ 0 := by positivity
  have := ((hasDerivAt_const t (1 : ℝ)).fun_div hZd hZ.ne').sub
    ((hasDerivAt_const t (56 : ℝ)).fun_div ((hZd.const_mul 5).add_const 14) hK)
  unfold dspoPhi dspof
  refine this.congr_deriv ?_
  field_simp
  ring

theorem dspo_hdC_G (hH : t + (x - t - 1) * r ≠ 0) (hZ : 0 < 1 + t + (x - t) * r) :
    HasDerivAt (fun C => dspoG x C n r) (dspoGC x t n r) t := by
  have := ((dspo_hdC_P (x := x) (n := n) (r := r) (t := t)).add
    ((dspo_hdC_V hH).mul (dspo_hdC_A (x := x) (n := n) (r := r) (t := t)))).add (dspo_hdC_Phi hZ)
  unfold dspoG dspoGC
  exact this.congr_deriv (by ring)

end DerivC

/-! ### The printed polynomials, in `h = x - 2`, `v = C - 3/5`

Each pair (`l` at `n = 5/2`, `h` at `n = 7/2`) clears one bound at the lower shape `r_*`; see
`dspo_I_id`, `dspo_J_id`, `dspo_K_id`, `dspo_L_id`. -/

/-- The polynomial `Il` of the bound `(P_n)_C > -53/2000` (`dspo_I_id`, `n = 5/2`). -/
noncomputable def dspoIl (h v : ℝ) : ℝ :=
    h ^ 6 * (-120000) +
    h ^ 5 * (384000 * v - 317715) +
    h ^ 4 * (2515200 * v + 1351255) +
    h ^ 3 * (5721840 * v + 4993694) +
    h ^ 2 * (5646480 * v + 4409598) +
    h * (2365440 * v + 1102949) +
    (348480 * v + 1560683)

/-- The polynomial `Ih` of the bound `(P_n)_C > -53/2000` (`dspo_I_id`, `n = 7/2`). -/
noncomputable def dspoIh (h v : ℝ) : ℝ :=
    h ^ 6 * (-120000) +
    h ^ 5 * (384000 * v - 382425) +
    h ^ 4 * (2515200 * v + 695205) +
    h ^ 3 * (5721840 * v + 2539394) +
    h ^ 2 * (5646480 * v + 275898) +
    h * (2365440 * v - 2079001) +
    (348480 * v + 367553)

/-- The polynomial `Jl` of the bound `(A_n)_C > 0` (`dspo_J_id`, `n = 5/2`). -/
noncomputable def dspoJl (h v : ℝ) : ℝ :=
    h ^ 5 * (30000) +
    h ^ 4 * (32000 * v + 474275) +
    h ^ 3 * (113600 * v + 2128815) +
    h ^ 2 * (136020 * v + 4134982) +
    h * (62480 * v + 3510138) +
    (9680 * v + 866868)

/-- The polynomial `Jh` of the bound `(A_n)_C > 0` (`dspo_J_id`, `n = 7/2`). -/
noncomputable def dspoJh (h v : ℝ) : ℝ :=
    h ^ 5 * (30000) +
    h ^ 4 * (32000 * v + 457525) +
    h ^ 3 * (113600 * v + 1984365) +
    h ^ 2 * (136020 * v + 3705632) +
    h * (62480 * v + 3025188) +
    (9680 * v + 732768)

/-- The polynomial `Kl` of the bound `A_n < 4` (`dspo_K_id`, `n = 5/2`). -/
noncomputable def dspoKl (h v : ℝ) : ℝ :=
    h ^ 5 * (-300000 * v - 1128750) +
    h ^ 4 * (-160000 * v ^ 2 - 4742750 * v - 15059525) +
    h ^ 3 * (-568000 * v ^ 2 - 21288150 * v - 65429935) +
    h ^ 2 * (-680100 * v ^ 2 - 41349820 * v - 116036681) +
    h * (-312400 * v ^ 2 - 35101380 * v - 63325164) +
    (-48400 * v ^ 2 - 8668680 * v + 20686266)

/-- The polynomial `Kh` of the bound `A_n < 4` (`dspo_K_id`, `n = 7/2`). -/
noncomputable def dspoKh (h v : ℝ) : ℝ :=
    h ^ 5 * (-300000 * v - 1053750) +
    h ^ 4 * (-160000 * v ^ 2 - 4575250 * v - 13686025) +
    h ^ 3 * (-568000 * v ^ 2 - 19843650 * v - 57064235) +
    h ^ 2 * (-680100 * v ^ 2 - 37056320 * v - 93954581) +
    h * (-312400 * v ^ 2 - 30251880 * v - 38743464) +
    (-48400 * v ^ 2 - 7327680 * v + 28537866)

/-- The polynomial `L` of the bound `U_C > -3/4000` (`dspo_L_id`). -/
noncomputable def dspoL (h v : ℝ) : ℝ :=
    h ^ 4 * (65625 * v ^ 2 + 420000 * v - 5828000) +
    h ^ 3 * (405000 * v ^ 2 + 2796750 * v - 17297600) +
    h ^ 2 * (759375 * v ^ 2 + 6041700 * v - 15582855) +
    h * (429900 * v ^ 2 + 4647930 * v - 2970956) +
    (74700 * v ^ 2 + 1060740 * v + 1165627)

theorem dspoIl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoIl h v := by
  unfold dspoIl; dsp_box

theorem dspoIh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoIh h v := by
  unfold dspoIh; dsp_box

theorem dspoJl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoJl h v := by
  unfold dspoJl; dsp_box

theorem dspoJh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoJh h v := by
  unfold dspoJh; dsp_box

theorem dspoKl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoKl h v := by
  unfold dspoKl; dsp_box

theorem dspoKh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoKh h v := by
  unfold dspoKh; dsp_box

theorem dspoL_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoL h v := by
  unfold dspoL; dsp_box

/-! ### The identities at the lower shape `r_* = 13/(5S)` -/

section Lower

variable {x C n : ℝ}

theorem dspo_I_id (hx : 0 < x) :
    (dspoPC x C n (13 / (5 * (x + 1))) + 53 / 2000) * (2450000 * (x + 1) ^ 5) =
      5 * (7 / 2 - n) * dspoIl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * dspoIh (x - 2) (C - 3 / 5) := by
  unfold dspoPC dspoAC dspoIl dspoIh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_J_id (hx : 0 < x) :
    dspoAC x C n (13 / (5 * (x + 1))) * (153125 * (x + 1) ^ 4) =
      5 * (7 / 2 - n) * dspoJl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * dspoJh (x - 2) (C - 3 / 5) := by
  unfold dspoAC dspoJl dspoJh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_K_id (hx : 0 < x) :
    (4 - dspoA x C n (13 / (5 * (x + 1)))) * (1531250 * (x + 1) ^ 4) =
      5 * (7 / 2 - n) * dspoKl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * dspoKh (x - 2) (C - 3 / 5) := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2 dspoKl dspoKh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_L_id (hx : 2 ≤ x) (hC : 0 ≤ C) :
    (3 / 4000 + dspoVC x C (13 / (5 * (x + 1)))) *
      (100000 * (x + 1) * (35 * x + 13) * (5 * C * x - 8 * C + 13 * x - 13) ^ 2) =
      dspoL (x - 2) (C - 3 / 5) := by
  have hB : 0 < 5 * C * x - 8 * C + 13 * x - 13 := by nlinarith
  have hH : C + (x - C - 1) * (13 / (5 * (x + 1))) = (5 * C * x - 8 * C + 13 * x - 13) / (5 * (x + 1)) := by
    have : x + 1 ≠ 0 := by linarith
    field_simp; ring
  unfold dspoVC
  rw [hH]
  unfold dspoc dspoL
  have : x + 1 ≠ 0 := by linarith
  have : 35 * x + 13 ≠ 0 := by linarith
  generalize hBd : 5 * C * x - 8 * C + 13 * x - 13 = B at hB ⊢
  have : B ≠ 0 := hB.ne'
  field_simp
  rw [← hBd]
  ring

/-- **The lower shape increases with the slope**: `(R_n)_C > 0` at `r_*`. -/
theorem dspo_GC_pos (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) (hn : 5 / 2 ≤ n)
    (hn' : n ≤ 7 / 2) : 0 < dspoGC x C n (13 / (5 * (x + 1))) := by
  have hx0 : 0 < x := by linarith
  have hh : 0 ≤ x - 2 := by linarith
  have hh6 : x - 2 ≤ 1 / 6 := by linarith
  have hv : 0 ≤ C - 3 / 5 := by linarith
  have hv7 : C - 3 / 5 ≤ 7 / 30 := by linarith
  have hr1 : 1 / x ≤ 13 / (5 * (x + 1)) := by
    rw [div_le_div_iff₀ hx0 (by positivity)]; linarith
  have hr2 : 13 / (5 * (x + 1)) ≤ 13 / 15 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hr2' : 13 / (5 * (x + 1)) ≤ 7 / 8 := by linarith
  have hw1 : 0 ≤ 7 / 2 - n := by linarith
  have hw2 : 0 ≤ n - 5 / 2 := by linarith
  -- `(P_n)_C > -53/2000`
  have hI : -(53 / 2000) < dspoPC x C n (13 / (5 * (x + 1))) := by
    have h1 := dspoIl_pos hh hh6 hv hv7
    have h2 := dspoIh_pos hh hh6 hv hv7
    have : 0 < 5 * (7 / 2 - n) * dspoIl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * dspoIh (x - 2) (C - 3 / 5) := by
      rcases eq_or_lt_of_le hw1 with e | e
      · rw [← e]; have : 0 < n - 5 / 2 := by linarith
        positivity
      · have : 0 ≤ 7 * (n - 5 / 2) * dspoIh (x - 2) (C - 3 / 5) := by positivity
        have : 0 < 5 * (7 / 2 - n) * dspoIl (x - 2) (C - 3 / 5) := by positivity
        linarith
    rw [← dspo_I_id hx0] at this
    have := pos_of_mul_pos_left this (by positivity)
    linarith
  -- `(A_n)_C > 0`
  have hJ : 0 < dspoAC x C n (13 / (5 * (x + 1))) := by
    have h1 := dspoJl_pos hh hh6 hv hv7
    have h2 := dspoJh_pos hh hh6 hv hv7
    have : 0 < 5 * (7 / 2 - n) * dspoJl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * dspoJh (x - 2) (C - 3 / 5) := by
      rcases eq_or_lt_of_le hw1 with e | e
      · rw [← e]; have : 0 < n - 5 / 2 := by linarith
        positivity
      · have : 0 ≤ 7 * (n - 5 / 2) * dspoJh (x - 2) (C - 3 / 5) := by positivity
        have : 0 < 5 * (7 / 2 - n) * dspoJl (x - 2) (C - 3 / 5) := by positivity
        linarith
    rw [← dspo_J_id hx0] at this
    exact pos_of_mul_pos_left this (by positivity)
  -- `A_n < 4`
  have hK : dspoA x C n (13 / (5 * (x + 1))) < 4 := by
    have h1 := dspoKl_pos hh hh6 hv hv7
    have h2 := dspoKh_pos hh hh6 hv hv7
    have : 0 < 5 * (7 / 2 - n) * dspoKl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * dspoKh (x - 2) (C - 3 / 5) := by
      rcases eq_or_lt_of_le hw1 with e | e
      · rw [← e]; have : 0 < n - 5 / 2 := by linarith
        positivity
      · have : 0 ≤ 7 * (n - 5 / 2) * dspoKh (x - 2) (C - 3 / 5) := by positivity
        have : 0 < 5 * (7 / 2 - n) * dspoKl (x - 2) (C - 3 / 5) := by positivity
        linarith
    rw [← dspo_K_id hx0] at this
    have := pos_of_mul_pos_left this (by positivity)
    linarith
  -- `-3/4000 < U_C ≤ 0`
  have hL : -(3 / 4000) < dspoVC x C (13 / (5 * (x + 1))) := by
    have h1 := dspoL_pos hh hh6 hv hv7
    rw [← dspo_L_id hx (by linarith)] at h1
    have hB : 0 < 5 * C * x - 8 * C + 13 * x - 13 := by nlinarith
    have := pos_of_mul_pos_left h1 (by positivity)
    linarith
  have hL0 : dspoVC x C (13 / (5 * (x + 1))) ≤ 0 := by
    unfold dspoVC
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have : 0 ≤ dspoc x := by unfold dspoc; positivity
    have : 0 ≤ 1 - 13 / (5 * (x + 1)) := by linarith
    have : 0 ≤ x - 1 := by linarith
    have : 0 ≤ dspoc x * (x - 1) * (13 / (5 * (x + 1))) * (1 - 13 / (5 * (x + 1))) := by positivity
    linarith
  obtain ⟨hA1, -, -⟩ := dspo_A_bds hx hx2 hC hC' hn hn' hr1 hr2'
  obtain ⟨hV0, -, -, -⟩ := dspo_V_bds hx hx2 hC hC' hr1 hr2'
  obtain ⟨-, hZ1, hZ2⟩ := dspo_HZ hx hx2 hC hC' hr1 hr2'
  have hf := dspof_ge hZ1 hZ2
  unfold dspoGC
  have e1 : dspoVC x C (13 / (5 * (x + 1))) * 4 ≤
      dspoVC x C (13 / (5 * (x + 1))) * dspoA x C n (13 / (5 * (x + 1))) :=
    mul_le_mul_of_nonpos_left hK.le hL0
  have e2 : 0 ≤ dspoV x C (13 / (5 * (x + 1))) * dspoAC x C n (13 / (5 * (x + 1))) :=
    mul_nonneg hV0 hJ.le
  have e3 : 2 / 15 * (1679 / 7569) ≤ (1 - 13 / (5 * (x + 1))) * dspof (1 + C + (x - C) * (13 / (5 * (x + 1)))) :=
    mul_le_mul (by linarith) hf (by norm_num) (by linarith)
  linarith

/-- **The lower-shape tests increase with the slope**: `G(x, C, n, r_*) ≤ G(x, C', n, r_*)` for
`3/5 ≤ C ≤ C' ≤ 5/6`; in particular they are bounded by their values at `C' = 19x/50`. -/
theorem dspo_low_mono {C' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hCC : C ≤ C')
    (hC' : C' ≤ 5 / 6) (hn : 5 / 2 ≤ n) (hn' : n ≤ 7 / 2) :
    dspoG x C n (13 / (5 * (x + 1))) ≤ dspoG x C' n (13 / (5 * (x + 1))) := by
  have hx0 : 0 < x := by linarith
  have hr1 : 1 / x ≤ 13 / (5 * (x + 1)) := by
    rw [div_le_div_iff₀ hx0 (by positivity)]; linarith
  have hr2 : 13 / (5 * (x + 1)) ≤ 7 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  apply ss_le_of_deriv hCC
  · intro t ht
    obtain ⟨hH, hZ, -⟩ := dspo_HZ hx hx2 (hC.trans ht.1) (ht.2.trans hC') hr1 hr2
    exact dspo_hdC_G (by linarith) (by linarith)
  · intro t ht
    exact (dspo_GC_pos hx hx2 (hC.trans ht.1.le) (ht.2.le.trans hC') hn hn').le

end Lower

end SmoothedOctagon

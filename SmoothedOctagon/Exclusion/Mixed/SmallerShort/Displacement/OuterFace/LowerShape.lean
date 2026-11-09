module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOCurv

/-!
# Gate S3, the outer face by hand: the lower shape increases with the beta slope

Proof of the leaf `hs3_outer_face`, third part. At the lower shape
`r_* = 13/(5S)` (`α = a_* = 5(x + 1)/13`) and `5/2 ≤ n ≤ 7/2`, `3/5 ≤ C ≤ 5/6`:
`(P_n)_C > -53/2000`, `(A_n)_C > 0`, `A_n < 4`, `U_C > -3/4000` and `f(Z) ≥ f(3)`, so
`(R_n)_C > 3487/45414000 > 0`. The `C`-derivatives of the quartics are explicit:
every coefficient is quadratic in `C`, so its second-order Taylor expansion in `C` is exact
(`hl3_hd_quad`).

## Main API

* `hl3oAC`, `hl3oPC`, `hl3oVC`, `hl3oGC`: the `C`-derivatives; `hl3o_hdC_G`.
* `hl3oIl`-`hl3oL`: the printed polynomials.
* `hl3o_low_mono`: `G(x, C, n, r_*) ≤ G(x, C', n, r_*)` for `3/5 ≤ C ≤ C' ≤ 5/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- A function that equals its exact second-order Taylor polynomial at `t` has derivative `f'`. -/
theorem hl3_hd_quad {f : ℝ → ℝ} {t f' k : ℝ} (h : ∀ s, f s = f t + f' * (s - t) + k * (s - t) ^ 2) :
    HasDerivAt f f' t := by
  have hd : HasDerivAt (fun s => f t + f' * (s - t) + k * (s - t) ^ 2) f' t := by
    have := ((((hasDerivAt_id t).sub_const t).const_mul f').const_add (f t)).add
      ((((hasDerivAt_id t).sub_const t).fun_pow 2).const_mul k)
    refine this.congr_deriv ?_
    simp
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall h)

/-! ### The `C`-derivatives -/

/-- `(A_n)_C`: the `C`-derivatives of the printed coefficients. -/
noncomputable def hl3oAC (x C n r : ℝ) : ℝ :=
  ((n * (8 * C - 12 * x - 8) + 21) +
    (n * (-16 * C * x - 16 * C + 12 * x ^ 2 + 28 * x + 8) + (28 * x - 21)) * r +
    (n * (8 * C * x ^ 2 + 32 * C * x + 8 * C - 28 * x ^ 2 - 10 * x + 2) - 28 * x) * r ^ 2 +
    n * (-16 * C * x ^ 2 - 16 * C * x + 8 * x ^ 3 + 10 * x ^ 2 - 8 * x - 2) * r ^ 3 +
    n * (8 * C * x ^ 2 - 8 * x ^ 3 + 6 * x ^ 2 + 2 * x) * r ^ 4) / 49

/-- `(A_n)_{CC}`. -/
noncomputable def hl3oACC (x n r : ℝ) : ℝ :=
  n * (8 + (-16 * x - 16) * r + (8 * x ^ 2 + 32 * x + 8) * r ^ 2 + (-16 * x ^ 2 - 16 * x) * r ^ 3 +
    8 * x ^ 2 * r ^ 4) / 49

/-- `(P_n)_C`. -/
noncomputable def hl3oPC (x C n r : ℝ) : ℝ :=
  3 / 4 * hl3oAC x C n r +
    ((n * (12 * x ^ 2 + 24 * x) + (-49 * x - 49)) +
      (n * (-12 * x ^ 3 - 36 * x ^ 2 - 24 * x) + (49 * x + 49)) * r +
      n * (12 * x ^ 3 + 22 * x ^ 2 - 2 * x - 2) * r ^ 2 + n * (2 * x ^ 3 + 4 * x ^ 2 + 4 * x + 2) * r ^ 3 +
      n * (-2 * x ^ 3 - 2 * x ^ 2 - 2 * x) * r ^ 4) / (49 * (x + 1))

/-- `U_C = V_C = -c(x - 1)r(1 - r)/H²`. -/
noncomputable def hl3oVC (x C r : ℝ) : ℝ :=
  -(hl3oc x * (x - 1) * r * (1 - r)) / (C + (x - C - 1) * r) ^ 2

/-- `(R_n)_C = (P_n)_C + V_CA_n + V(A_n)_C + (1 - r)f(Z)`. -/
noncomputable def hl3oGC (x C n r : ℝ) : ℝ :=
  hl3oPC x C n r + hl3oVC x C r * hl3oA x C n r + hl3oV x C r * hl3oAC x C n r +
    (1 - r) * hl3of (1 + C + (x - C) * r)

section DerivC

variable {x n r t : ℝ}

theorem hl3o_hdC_A : HasDerivAt (fun C => hl3oA x C n r) (hl3oAC x t n r) t := by
  refine hl3_hd_quad (k := hl3oACC x n r / 2) fun s => ?_
  unfold hl3oA hl3oAC hl3oACC hl3oAc0 hl3oAc1 hl3oAc2 hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3
    hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2
  ring

theorem hl3o_hdC_P : HasDerivAt (fun C => hl3oP x C n r) (hl3oPC x t n r) t := by
  refine hl3_hd_quad (k := 3 / 4 * hl3oACC x n r / 2) fun s => ?_
  unfold hl3oP hl3oPC hl3oAC hl3oACC hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1
    hl3oAc2 hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1
    hl3oγ2 hl3oγ3 hl3oγ4 hl3oδ0 hl3oδ1 hl3oδ2
  ring

theorem hl3o_hdC_V (hH : t + (x - t - 1) * r ≠ 0) :
    HasDerivAt (fun C => hl3oV x C r) (hl3oVC x t r) t := by
  have hHd : HasDerivAt (fun C => C + (x - C - 1) * r) (1 - r) t := by
    have := (hasDerivAt_id t).add ((((hasDerivAt_id t).const_sub x).sub_const 1).mul_const r)
    refine this.congr_deriv ?_
    ring
  have := ((hasDerivAt_const t (hl3oc x * (x - 1) * r)).fun_div hHd hH).const_add (hl3oc x)
  unfold hl3oV hl3oVC
  refine this.congr_deriv ?_
  field_simp
  ring

theorem hl3o_hdC_Phi (hZ : 0 < 1 + t + (x - t) * r) :
    HasDerivAt (fun C => hl3oPhi x C r) ((1 - r) * hl3of (1 + t + (x - t) * r)) t := by
  have hZd : HasDerivAt (fun C => 1 + C + (x - C) * r) (1 - r) t := by
    have := ((hasDerivAt_id t).const_add 1).add (((hasDerivAt_id t).const_sub x).mul_const r)
    refine this.congr_deriv ?_
    ring
  have hK : (5 * (1 + t + (x - t) * r) + 14) ≠ 0 := by positivity
  have := ((hasDerivAt_const t (1 : ℝ)).fun_div hZd hZ.ne').sub
    ((hasDerivAt_const t (56 : ℝ)).fun_div ((hZd.const_mul 5).add_const 14) hK)
  unfold hl3oPhi hl3of
  refine this.congr_deriv ?_
  field_simp
  ring

theorem hl3o_hdC_G (hH : t + (x - t - 1) * r ≠ 0) (hZ : 0 < 1 + t + (x - t) * r) :
    HasDerivAt (fun C => hl3oG x C n r) (hl3oGC x t n r) t := by
  have := ((hl3o_hdC_P (x := x) (n := n) (r := r) (t := t)).add
    ((hl3o_hdC_V hH).mul (hl3o_hdC_A (x := x) (n := n) (r := r) (t := t)))).add (hl3o_hdC_Phi hZ)
  unfold hl3oG hl3oGC
  exact this.congr_deriv (by ring)

end DerivC

/-! ### The printed polynomials, in `h = x - 2`, `v = C - 3/5`

Each pair (`l` at `n = 5/2`, `h` at `n = 7/2`) clears one bound at the lower shape `r_*`; see
`hl3o_I_id`, `hl3o_J_id`, `hl3o_K_id`, `hl3o_L_id`. -/

/-- The polynomial `Il` of the bound `(P_n)_C > -53/2000` (`hl3o_I_id`, `n = 5/2`). -/
noncomputable def hl3oIl (h v : ℝ) : ℝ :=
    h ^ 6 * (-120000) +
    h ^ 5 * (384000 * v - 317715) +
    h ^ 4 * (2515200 * v + 1351255) +
    h ^ 3 * (5721840 * v + 4993694) +
    h ^ 2 * (5646480 * v + 4409598) +
    h * (2365440 * v + 1102949) +
    (348480 * v + 1560683)

/-- The polynomial `Ih` of the bound `(P_n)_C > -53/2000` (`hl3o_I_id`, `n = 7/2`). -/
noncomputable def hl3oIh (h v : ℝ) : ℝ :=
    h ^ 6 * (-120000) +
    h ^ 5 * (384000 * v - 382425) +
    h ^ 4 * (2515200 * v + 695205) +
    h ^ 3 * (5721840 * v + 2539394) +
    h ^ 2 * (5646480 * v + 275898) +
    h * (2365440 * v - 2079001) +
    (348480 * v + 367553)

/-- The polynomial `Jl` of the bound `(A_n)_C > 0` (`hl3o_J_id`, `n = 5/2`). -/
noncomputable def hl3oJl (h v : ℝ) : ℝ :=
    h ^ 5 * (30000) +
    h ^ 4 * (32000 * v + 474275) +
    h ^ 3 * (113600 * v + 2128815) +
    h ^ 2 * (136020 * v + 4134982) +
    h * (62480 * v + 3510138) +
    (9680 * v + 866868)

/-- The polynomial `Jh` of the bound `(A_n)_C > 0` (`hl3o_J_id`, `n = 7/2`). -/
noncomputable def hl3oJh (h v : ℝ) : ℝ :=
    h ^ 5 * (30000) +
    h ^ 4 * (32000 * v + 457525) +
    h ^ 3 * (113600 * v + 1984365) +
    h ^ 2 * (136020 * v + 3705632) +
    h * (62480 * v + 3025188) +
    (9680 * v + 732768)

/-- The polynomial `Kl` of the bound `A_n < 4` (`hl3o_K_id`, `n = 5/2`). -/
noncomputable def hl3oKl (h v : ℝ) : ℝ :=
    h ^ 5 * (-300000 * v - 1128750) +
    h ^ 4 * (-160000 * v ^ 2 - 4742750 * v - 15059525) +
    h ^ 3 * (-568000 * v ^ 2 - 21288150 * v - 65429935) +
    h ^ 2 * (-680100 * v ^ 2 - 41349820 * v - 116036681) +
    h * (-312400 * v ^ 2 - 35101380 * v - 63325164) +
    (-48400 * v ^ 2 - 8668680 * v + 20686266)

/-- The polynomial `Kh` of the bound `A_n < 4` (`hl3o_K_id`, `n = 7/2`). -/
noncomputable def hl3oKh (h v : ℝ) : ℝ :=
    h ^ 5 * (-300000 * v - 1053750) +
    h ^ 4 * (-160000 * v ^ 2 - 4575250 * v - 13686025) +
    h ^ 3 * (-568000 * v ^ 2 - 19843650 * v - 57064235) +
    h ^ 2 * (-680100 * v ^ 2 - 37056320 * v - 93954581) +
    h * (-312400 * v ^ 2 - 30251880 * v - 38743464) +
    (-48400 * v ^ 2 - 7327680 * v + 28537866)

/-- The polynomial `L` of the bound `U_C > -3/4000` (`hl3o_L_id`). -/
noncomputable def hl3oL (h v : ℝ) : ℝ :=
    h ^ 4 * (65625 * v ^ 2 + 420000 * v - 5828000) +
    h ^ 3 * (405000 * v ^ 2 + 2796750 * v - 17297600) +
    h ^ 2 * (759375 * v ^ 2 + 6041700 * v - 15582855) +
    h * (429900 * v ^ 2 + 4647930 * v - 2970956) +
    (74700 * v ^ 2 + 1060740 * v + 1165627)

theorem hl3oIl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oIl h v := by
  unfold hl3oIl; hl3_box

theorem hl3oIh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oIh h v := by
  unfold hl3oIh; hl3_box

theorem hl3oJl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oJl h v := by
  unfold hl3oJl; hl3_box

theorem hl3oJh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oJh h v := by
  unfold hl3oJh; hl3_box

theorem hl3oKl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oKl h v := by
  unfold hl3oKl; hl3_box

theorem hl3oKh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oKh h v := by
  unfold hl3oKh; hl3_box

theorem hl3oL_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < hl3oL h v := by
  unfold hl3oL; hl3_box

/-! ### The identities at the lower shape `r_* = 13/(5S)` -/

section Lower

variable {x C n : ℝ}

theorem hl3o_I_id (hx : 0 < x) :
    (hl3oPC x C n (13 / (5 * (x + 1))) + 53 / 2000) * (2450000 * (x + 1) ^ 5) =
      5 * (7 / 2 - n) * hl3oIl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * hl3oIh (x - 2) (C - 3 / 5) := by
  unfold hl3oPC hl3oAC hl3oIl hl3oIh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem hl3o_J_id (hx : 0 < x) :
    hl3oAC x C n (13 / (5 * (x + 1))) * (153125 * (x + 1) ^ 4) =
      5 * (7 / 2 - n) * hl3oJl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * hl3oJh (x - 2) (C - 3 / 5) := by
  unfold hl3oAC hl3oJl hl3oJh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem hl3o_K_id (hx : 0 < x) :
    (4 - hl3oA x C n (13 / (5 * (x + 1)))) * (1531250 * (x + 1) ^ 4) =
      5 * (7 / 2 - n) * hl3oKl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * hl3oKh (x - 2) (C - 3 / 5) := by
  unfold hl3oA hl3oAc0 hl3oAc1 hl3oAc2 hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0
    hl3oβ1 hl3oβ2 hl3oKl hl3oKh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem hl3o_L_id (hx : 2 ≤ x) (hC : 0 ≤ C) :
    (3 / 4000 + hl3oVC x C (13 / (5 * (x + 1)))) *
      (100000 * (x + 1) * (35 * x + 13) * (5 * C * x - 8 * C + 13 * x - 13) ^ 2) =
      hl3oL (x - 2) (C - 3 / 5) := by
  have hB : 0 < 5 * C * x - 8 * C + 13 * x - 13 := by nlinarith
  have hH : C + (x - C - 1) * (13 / (5 * (x + 1))) = (5 * C * x - 8 * C + 13 * x - 13) / (5 * (x + 1)) := by
    have : x + 1 ≠ 0 := by linarith
    field_simp; ring
  unfold hl3oVC
  rw [hH]
  unfold hl3oc hl3oL
  have : x + 1 ≠ 0 := by linarith
  have : 35 * x + 13 ≠ 0 := by linarith
  generalize hBd : 5 * C * x - 8 * C + 13 * x - 13 = B at hB ⊢
  have : B ≠ 0 := hB.ne'
  field_simp
  rw [← hBd]
  ring

/-- **The lower shape increases with the slope**: `(R_n)_C > 0` at `r_*`. -/
theorem hl3o_GC_pos (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) (hn : 5 / 2 ≤ n)
    (hn' : n ≤ 7 / 2) : 0 < hl3oGC x C n (13 / (5 * (x + 1))) := by
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
  have hI : -(53 / 2000) < hl3oPC x C n (13 / (5 * (x + 1))) := by
    have h1 := hl3oIl_pos hh hh6 hv hv7
    have h2 := hl3oIh_pos hh hh6 hv hv7
    have : 0 < 5 * (7 / 2 - n) * hl3oIl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * hl3oIh (x - 2) (C - 3 / 5) := by
      rcases eq_or_lt_of_le hw1 with e | e
      · rw [← e]; have : 0 < n - 5 / 2 := by linarith
        positivity
      · have : 0 ≤ 7 * (n - 5 / 2) * hl3oIh (x - 2) (C - 3 / 5) := by positivity
        have : 0 < 5 * (7 / 2 - n) * hl3oIl (x - 2) (C - 3 / 5) := by positivity
        linarith
    rw [← hl3o_I_id hx0] at this
    have := pos_of_mul_pos_left this (by positivity)
    linarith
  -- `(A_n)_C > 0`
  have hJ : 0 < hl3oAC x C n (13 / (5 * (x + 1))) := by
    have h1 := hl3oJl_pos hh hh6 hv hv7
    have h2 := hl3oJh_pos hh hh6 hv hv7
    have : 0 < 5 * (7 / 2 - n) * hl3oJl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * hl3oJh (x - 2) (C - 3 / 5) := by
      rcases eq_or_lt_of_le hw1 with e | e
      · rw [← e]; have : 0 < n - 5 / 2 := by linarith
        positivity
      · have : 0 ≤ 7 * (n - 5 / 2) * hl3oJh (x - 2) (C - 3 / 5) := by positivity
        have : 0 < 5 * (7 / 2 - n) * hl3oJl (x - 2) (C - 3 / 5) := by positivity
        linarith
    rw [← hl3o_J_id hx0] at this
    exact pos_of_mul_pos_left this (by positivity)
  -- `A_n < 4`
  have hK : hl3oA x C n (13 / (5 * (x + 1))) < 4 := by
    have h1 := hl3oKl_pos hh hh6 hv hv7
    have h2 := hl3oKh_pos hh hh6 hv hv7
    have : 0 < 5 * (7 / 2 - n) * hl3oKl (x - 2) (C - 3 / 5) + 7 * (n - 5 / 2) * hl3oKh (x - 2) (C - 3 / 5) := by
      rcases eq_or_lt_of_le hw1 with e | e
      · rw [← e]; have : 0 < n - 5 / 2 := by linarith
        positivity
      · have : 0 ≤ 7 * (n - 5 / 2) * hl3oKh (x - 2) (C - 3 / 5) := by positivity
        have : 0 < 5 * (7 / 2 - n) * hl3oKl (x - 2) (C - 3 / 5) := by positivity
        linarith
    rw [← hl3o_K_id hx0] at this
    have := pos_of_mul_pos_left this (by positivity)
    linarith
  -- `-3/4000 < U_C ≤ 0`
  have hL : -(3 / 4000) < hl3oVC x C (13 / (5 * (x + 1))) := by
    have h1 := hl3oL_pos hh hh6 hv hv7
    rw [← hl3o_L_id hx (by linarith)] at h1
    have hB : 0 < 5 * C * x - 8 * C + 13 * x - 13 := by nlinarith
    have := pos_of_mul_pos_left h1 (by positivity)
    linarith
  have hL0 : hl3oVC x C (13 / (5 * (x + 1))) ≤ 0 := by
    unfold hl3oVC
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have : 0 ≤ hl3oc x := by unfold hl3oc; positivity
    have : 0 ≤ 1 - 13 / (5 * (x + 1)) := by linarith
    have : 0 ≤ x - 1 := by linarith
    have : 0 ≤ hl3oc x * (x - 1) * (13 / (5 * (x + 1))) * (1 - 13 / (5 * (x + 1))) := by positivity
    linarith
  obtain ⟨hA1, -, -⟩ := hl3o_A_bds hx hx2 hC hC' hn hn' hr1 hr2'
  obtain ⟨hV0, -, -, -⟩ := hl3o_V_bds hx hx2 hC hC' hr1 hr2'
  obtain ⟨-, hZ1, hZ2⟩ := hl3o_HZ hx hx2 hC hC' hr1 hr2'
  have hf := hl3of_ge hZ1 hZ2
  unfold hl3oGC
  have e1 : hl3oVC x C (13 / (5 * (x + 1))) * 4 ≤
      hl3oVC x C (13 / (5 * (x + 1))) * hl3oA x C n (13 / (5 * (x + 1))) :=
    mul_le_mul_of_nonpos_left hK.le hL0
  have e2 : 0 ≤ hl3oV x C (13 / (5 * (x + 1))) * hl3oAC x C n (13 / (5 * (x + 1))) :=
    mul_nonneg hV0 hJ.le
  have e3 : 2 / 15 * (1679 / 7569) ≤ (1 - 13 / (5 * (x + 1))) * hl3of (1 + C + (x - C) * (13 / (5 * (x + 1)))) :=
    mul_le_mul (by linarith) hf (by norm_num) (by linarith)
  linarith

/-- **The lower-shape tests increase with the slope**: `G(x, C, n, r_*) ≤ G(x, C', n, r_*)` for
`3/5 ≤ C ≤ C' ≤ 5/6`; in particular they are bounded by their values at `C' = 19x/50`. -/
theorem hl3o_low_mono {C' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hCC : C ≤ C')
    (hC' : C' ≤ 5 / 6) (hn : 5 / 2 ≤ n) (hn' : n ≤ 7 / 2) :
    hl3oG x C n (13 / (5 * (x + 1))) ≤ hl3oG x C' n (13 / (5 * (x + 1))) := by
  have hx0 : 0 < x := by linarith
  have hr1 : 1 / x ≤ 13 / (5 * (x + 1)) := by
    rw [div_le_div_iff₀ hx0 (by positivity)]; linarith
  have hr2 : 13 / (5 * (x + 1)) ≤ 7 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  apply ss_le_of_deriv hCC
  · intro t ht
    obtain ⟨hH, hZ, -⟩ := hl3o_HZ hx hx2 (hC.trans ht.1) (ht.2.trans hC') hr1 hr2
    exact hl3o_hdC_G (by linarith) (by linarith)
  · intro t ht
    exact (hl3o_GC_pos hx hx2 (hC.trans ht.1.le) (ht.2.le.trans hC') hn hn').le

end Lower

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S3Leaves

/-!
# Gate S3, the central face by hand: the shape derivative

Hand proof of the leaf `hs3_central_alpha` (`DISPLACEMENT_CENTRAL_FACE` §2), first part:
the derivative of the two central tests along the central boundary, following
`archive/lighter-proofs/SHORT_DISPLACEMENT_CENTRAL_SHAPE.md` §1 (identity (3)).

Along `b = x + B(a - 1)`, `B = 25x/(15x + 36)`, at `q = q_c = a²/K`, `K = x(x + 2) + a²`, the
transport is `w = λ²v + d²u - dλE`, `E_L = 2du - λE` with `λ = S²/K`, `d = D/K`, `S = 1 + x`,
`E = S(u - 1) + 3/S - 1/S²`, `v = 1 - 1/S + 1/S²` (`hl3c_ELs`, `hl3c_Ws`). With `L = 2a/K`,
`A = 1 + 2B + (x - B - Bx)/a`, `u_b = -(x - 1)(g - 1/5808)/(b - 1)²`, the chain rule gives
`q' = L(1 - q)`, `λ' = -Lλ`, `d' = LA - Ld`, `u' = Bu_b`, `p' = (x - B)/(a + b)²`, and the test
`F_i = J + n_i(w - 3/4)` has derivative `hl3cH x a n_i N_i` (the note's (3)), `N_i = n_i'`.
The identity is assembled from these small chain-rule pieces; no cleared numerator is expanded.

## Main API

* Path quantities `hl3cK`, `hl3cB`, `hl3cE`, `hl3cv`, `hl3cW`, `hl3cEL`, `hl3cp`, `hl3cu`, `hl3clam`,
  `hl3cd`, `hl3cL`, `hl3cA`, `hl3cub`, `hl3cz`, `hl3cy`, `hl3cn0`, `hl3cn1`, `hl3cN0`, `hl3cN1`.
* `hl3cH x a n N`: the derivative (3).
* `hl3c_hasDerivAt_F0`, `hl3c_hasDerivAt_F1`: `F_i(x, a, b(x, a), ū(x, b(x, a)), q_c(x, a))` has
  derivative `hl3cH x a n_i N_i` at every `a > 1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `K = x(x + 2) + a²`. -/
noncomputable def hl3cK (x a : ℝ) : ℝ := x * (x + 2) + a ^ 2

/-- The slope `B = 25x/(15x + 36)` of the central boundary `b(x, a) = x + B(a - 1)`. -/
noncomputable def hl3cB (x : ℝ) : ℝ := 25 * x / (15 * x + 36)

/-- `E = S(u - 1) + 3/S - 1/S²`, `S = 1 + x`. -/
noncomputable def hl3cE (x u : ℝ) : ℝ := (1 + x) * (u - 1) + 3 / (1 + x) - 1 / (1 + x) ^ 2

/-- `v = 1 - 1/S + 1/S²`. -/
noncomputable def hl3cv (x : ℝ) : ℝ := 1 - 1 / (1 + x) + 1 / (1 + x) ^ 2

/-- The transported norm `w = λ²v + d²u - dλE`. -/
noncomputable def hl3cW (x lam d u : ℝ) : ℝ := lam ^ 2 * hl3cv x + d ^ 2 * u - d * lam * hl3cE x u

/-- The transported pairing `E_L = 2du - λE`. -/
noncomputable def hl3cEL (x lam d u : ℝ) : ℝ := 2 * d * u - lam * hl3cE x u

/-- `p = r_A = a/(a + b)` along the central boundary. -/
noncomputable def hl3cp (x a : ℝ) : ℝ := hsRA a (hs3b x a)

/-- The incoming ceiling `u = ū(x, b)` along the central boundary. -/
noncomputable def hl3cu (x a : ℝ) : ℝ := hsUCB x (hs3b x a)

/-- `λ = S²/K`. -/
noncomputable def hl3clam (x a : ℝ) : ℝ := (1 + x) ^ 2 / hl3cK x a

/-- `d = D/K` along the central boundary. -/
noncomputable def hl3cd (x a : ℝ) : ℝ := hsDg x (hs3b x a) a / hl3cK x a

/-- `L = 2a/K`. -/
noncomputable def hl3cL (x a : ℝ) : ℝ := 2 * a / hl3cK x a

/-- `A = 1 + 2B + (x - B - Bx)/a`, so that `D' = 2aA`. -/
noncomputable def hl3cA (x a : ℝ) : ℝ := 1 + 2 * hl3cB x + (x - hl3cB x - hl3cB x * x) / a

/-- `u_b = (x - 1)(1/5808 - g)/(b - 1)²`, `g = V_G - 3/4`: the `b`-derivative of `ū`. -/
noncomputable def hl3cub (x a : ℝ) : ℝ :=
  (x - 1) * (1 / 5808 - (hsVG x - 3 / 4)) / (hs3b x a - 1) ^ 2

/-- `z = 2/a - L - (x - B)/(a(a + b))`, so that `y' = yz`. -/
noncomputable def hl3cz (x a : ℝ) : ℝ := 2 / a - hl3cL x a - (x - hl3cB x) / (a * (a + hs3b x a))

/-- `y = 2q/p`. -/
noncomputable def hl3cy (x a : ℝ) : ℝ := 2 * hsQc x a / hl3cp x a

/-- `n₀ = 2 + 4(4 - 3y)/k`, `k = 5a - 1`. -/
noncomputable def hl3cn0 (x a : ℝ) : ℝ := 2 + 4 * (4 - 3 * hl3cy x a) / (5 * a - 1)

/-- `n₁ = T + 4/k`, `T = p/q`. -/
noncomputable def hl3cn1 (x a : ℝ) : ℝ := hl3cp x a / hsQc x a + 4 / (5 * a - 1)

/-- `N₀ = n₀' = -12yz/k - 20(4 - 3y)/k²`. -/
noncomputable def hl3cN0 (x a : ℝ) : ℝ :=
  -12 * hl3cy x a * hl3cz x a / (5 * a - 1) - 20 * (4 - 3 * hl3cy x a) / (5 * a - 1) ^ 2

/-- `N₁ = n₁' = -Tz - 20/k²`. -/
noncomputable def hl3cN1 (x a : ℝ) : ℝ :=
  -(hl3cp x a / hsQc x a) * hl3cz x a - 20 / (5 * a - 1) ^ 2

/-- **The shape derivative** (the note's (3)) of `F = J + n(w - 3/4)` with `n' = N`. -/
noncomputable def hl3cH (x a n N : ℝ) : ℝ :=
  (x - hl3cB x) / a ^ 2 * (1 - hl3cp x a + hl3cp x a ^ 2 - hl3cu x a) +
    2 * (1 - hsQc x a) ^ 2 / a +
    hl3cL x a * hl3cA x a *
      (n * hl3cEL x (hl3clam x a) (hl3cd x a) (hl3cu x a) - 2 * hl3cu x a) +
    hl3cL x a * (hl3cEL x (hl3clam x a) (hl3cd x a) (hl3cu x a) -
      2 * n * hl3cW x (hl3clam x a) (hl3cd x a) (hl3cu x a)) +
    hl3cB x * hl3cub x a * (1 / hl3cp x a + hl3clam x a * (1 + x) - 2 * hl3cd x a +
      n * hl3cd x a * (hl3cd x a - hl3clam x a * (1 + x))) +
    N * (hl3cW x (hl3clam x a) (hl3cd x a) (hl3cu x a) - 3 / 4)

/-! ### The transport at the central scale -/

theorem hl3c_ELs (x be al u : ℝ) (hx : 0 < x) (hal : 0 < al) :
    hsELs x be al u (hsQc x al) =
      hl3cEL x ((1 + x) ^ 2 / hl3cK x al) (hsDg x be al / hl3cK x al) u := by
  unfold hsELs hsA3 hsE0 hsQc hl3cEL hl3cE hl3cK
  generalize hsDg x be al = D
  have h1 : 0 < x * (x + 2) + al ^ 2 := by positivity
  field_simp
  ring

theorem hl3c_Ws (x be al u : ℝ) (hx : 0 < x) (hal : 0 < al) :
    hsWs x be al u (hsQc x al) =
      hl3cW x ((1 + x) ^ 2 / hl3cK x al) (hsDg x be al / hl3cK x al) u := by
  unfold hsWs hsA1 hsA2 hsE0 hsQc hl3cW hl3cv hl3cE hl3cK
  generalize hsDg x be al = D
  have h1 : 0 < x * (x + 2) + al ^ 2 := by positivity
  field_simp
  ring

/-- The central tests in the note's form. -/
theorem hl3c_F_eq (x a n : ℝ) (hx : 0 < x) (ha : 0 < a) :
    hs3Fn x (hs3b x a) a (hl3cu x a) (hsQc x a) n (log (2 * hsQc x a / hl3cp x a)) =
      (hl3cu x a - 1) / hl3cp x a + hl3cp x a + 1 - hsQc x a -
        hl3cEL x (hl3clam x a) (hl3cd x a) (hl3cu x a) + log (2 * hsQc x a / hl3cp x a) +
        n * (hl3cW x (hl3clam x a) (hl3cd x a) (hl3cu x a) - 3 / 4) := by
  unfold hs3Fn
  rw [hl3c_ELs _ _ _ _ hx ha, hl3c_Ws _ _ _ _ hx ha]
  rfl

/-! ### Chain-rule pieces -/

section Pieces

variable {x a : ℝ}

theorem hl3c_hd_b : HasDerivAt (fun s => hs3b x s) (hl3cB x) a := by
  unfold hs3b hl3cB
  have := (((hasDerivAt_id a).sub_const 1).const_mul (25 * x / (15 * x + 36))).const_add x
  refine this.congr_deriv ?_
  ring

theorem hl3c_hd_K : HasDerivAt (fun s => hl3cK x s) (2 * a) a := by
  unfold hl3cK
  have := (hasDerivAt_pow 2 a).const_add (x * (x + 2))
  refine this.congr_deriv ?_
  push_cast; ring

theorem hl3c_K_pos (hx : 0 < x) : 0 < hl3cK x a := by unfold hl3cK; positivity

theorem hl3c_hd_q (hx : 0 < x) :
    HasDerivAt (fun s => hsQc x s) (hl3cL x a * (1 - hsQc x a)) a := by
  have hK := hl3c_K_pos (a := a) hx
  have := (hasDerivAt_pow 2 a).fun_div (hl3c_hd_K (x := x) (a := a)) hK.ne'
  unfold hsQc
  refine this.congr_deriv ?_
  unfold hl3cL
  unfold hl3cK at hK ⊢
  norm_num
  field_simp

theorem hl3c_b_eq (x a : ℝ) : hs3b x a = x + hl3cB x * (a - 1) := by
  unfold hs3b hl3cB; ring

theorem hl3c_b_gt (hx : 0 < x) (ha : 1 < a) : x < hs3b x a := by
  rw [hl3c_b_eq]
  have : 0 < hl3cB x := by unfold hl3cB; positivity
  nlinarith

theorem hl3c_hd_p (hx : 0 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cp x s) ((x - hl3cB x) / (a + hs3b x a) ^ 2) a := by
  have hb := hl3c_b_gt hx ha
  have hab : a + hs3b x a ≠ 0 := by linarith
  have := (hasDerivAt_id a).fun_div ((hasDerivAt_id a).add (hl3c_hd_b (x := x) (a := a))) hab
  unfold hl3cp hsRA
  refine this.congr_deriv ?_
  simp only [Pi.add_apply, id]
  rw [hl3c_b_eq] at hab ⊢
  field_simp
  ring

theorem hl3c_hd_u (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cu x s) (hl3cB x * hl3cub x a) a := by
  have hb := hl3c_b_gt (x := x) (a := a) (by linarith) ha
  have hb1 : hs3b x a - 1 ≠ 0 := by linarith
  have := ((((hl3c_hd_b (x := x) (a := a)).sub_const x).div_const 5808).const_add
    ((x - 1) * (hsVG x - 3 / 4))).fun_div ((hl3c_hd_b (x := x) (a := a)).sub_const 1) hb1
  have h2 := this.const_add (3 / 4)
  unfold hl3cu hsUCB
  refine h2.congr_deriv ?_
  unfold hl3cub
  field_simp
  ring

theorem hl3c_hd_D (ha : 0 < a) :
    HasDerivAt (fun s => hsDg x (hs3b x s) s) (2 * a * hl3cA x a) a := by
  have hbd := hl3c_hd_b (x := x) (a := a)
  have := (((((hasDerivAt_pow 2 a).add (((hasDerivAt_id a).const_mul 2).mul hbd)).add_const 1).add_const
    (2 * x)).sub (hbd.const_mul 2 |>.mul_const x))
  unfold hsDg
  refine this.congr_deriv ?_
  unfold hl3cA
  rw [hl3c_b_eq]
  field_simp
  simp only [id]
  ring

theorem hl3c_hd_lam (hx : 0 < x) :
    HasDerivAt (fun s => hl3clam x s) (-(hl3cL x a) * hl3clam x a) a := by
  have hK := hl3c_K_pos (a := a) hx
  have := (hasDerivAt_const a ((1 + x) ^ 2)).fun_div (hl3c_hd_K (x := x) (a := a)) hK.ne'
  unfold hl3clam
  refine this.congr_deriv ?_
  unfold hl3cL
  field_simp
  ring

theorem hl3c_hd_d (hx : 0 < x) (ha : 0 < a) :
    HasDerivAt (fun s => hl3cd x s) (hl3cL x a * hl3cA x a - hl3cL x a * hl3cd x a) a := by
  have hK := hl3c_K_pos (a := a) hx
  have := (hl3c_hd_D (x := x) ha).fun_div (hl3c_hd_K (x := x) (a := a)) hK.ne'
  unfold hl3cd
  refine this.congr_deriv ?_
  unfold hl3cL
  field_simp

end Pieces

/-- The chain rule for `E_L = 2du - λE`. -/
theorem hl3c_hd_EL {x a l' d' u' : ℝ} {lamF dF uF : ℝ → ℝ}
    (hl : HasDerivAt lamF l' a) (hd : HasDerivAt dF d' a) (hu : HasDerivAt uF u' a) :
    HasDerivAt (fun s => hl3cEL x (lamF s) (dF s) (uF s))
      (2 * d' * uF a + 2 * dF a * u' - l' * hl3cE x (uF a) - lamF a * ((1 + x) * u')) a := by
  have hE : HasDerivAt (fun s => hl3cE x (uF s)) ((1 + x) * u') a := by
    unfold hl3cE
    exact (((hu.sub_const 1).const_mul (1 + x)).add_const _).sub_const _
  have := ((hd.const_mul 2).mul hu).sub (hl.mul hE)
  unfold hl3cEL
  refine this.congr_deriv ?_
  ring

/-- The chain rule for `w = λ²v + d²u - dλE`. -/
theorem hl3c_hd_W {x a l' d' u' : ℝ} {lamF dF uF : ℝ → ℝ}
    (hl : HasDerivAt lamF l' a) (hd : HasDerivAt dF d' a) (hu : HasDerivAt uF u' a) :
    HasDerivAt (fun s => hl3cW x (lamF s) (dF s) (uF s))
      (2 * lamF a * l' * hl3cv x + 2 * dF a * d' * uF a + dF a ^ 2 * u' -
        (d' * lamF a + dF a * l') * hl3cE x (uF a) - dF a * lamF a * ((1 + x) * u')) a := by
  have hE : HasDerivAt (fun s => hl3cE x (uF s)) ((1 + x) * u') a := by
    unfold hl3cE
    exact (((hu.sub_const 1).const_mul (1 + x)).add_const _).sub_const _
  have := (((hl.fun_pow 2).mul_const (hl3cv x)).add ((hd.fun_pow 2).mul hu)).sub
    ((hd.mul hl).mul hE)
  unfold hl3cW
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  push_cast
  ring

section Assembly

variable {x a : ℝ}

theorem hl3c_p_pos (hx : 0 < x) (ha : 1 < a) : 0 < hl3cp x a := by
  have := hl3c_b_gt (x := x) (a := a) hx ha
  unfold hl3cp hsRA
  apply div_pos <;> linarith

theorem hl3c_q_pos (hx : 0 < x) (ha : 1 < a) : 0 < hsQc x a := by
  unfold hsQc
  have : 0 < a := by linarith
  positivity

/-- `y' = yz`. -/
theorem hl3c_hd_y (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cy x s) (hl3cy x a * hl3cz x a) a := by
  have hb := hl3c_b_gt (x := x) (a := a) (by linarith) ha
  have hp0 := hl3c_p_pos (x := x) (a := a) (by linarith) ha
  have := ((hl3c_hd_q (x := x) (a := a) (by linarith)).const_mul 2).fun_div
    (hl3c_hd_p (x := x) (a := a) (by linarith) ha) hp0.ne'
  unfold hl3cy
  refine this.congr_deriv ?_
  unfold hl3cz hl3cL
  unfold hl3cp hsRA at hp0 ⊢
  unfold hsQc hl3cK
  have hK : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hab : a + hs3b x a ≠ 0 := by linarith
  have ha0 : a ≠ 0 := by linarith
  field_simp

/-- `T' = -Tz`, `T = p/q`. -/
theorem hl3c_hd_T (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cp x s / hsQc x s) (-(hl3cp x a / hsQc x a) * hl3cz x a) a := by
  have hb := hl3c_b_gt (x := x) (a := a) (by linarith) ha
  have hq0 := hl3c_q_pos (x := x) (a := a) (by linarith) ha
  have := (hl3c_hd_p (x := x) (a := a) (by linarith) ha).fun_div
    (hl3c_hd_q (x := x) (a := a) (by linarith)) hq0.ne'
  refine this.congr_deriv ?_
  unfold hl3cz hl3cL
  unfold hsQc at hq0 ⊢
  unfold hl3cp hsRA hl3cK
  have hK : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hab : a + hs3b x a ≠ 0 := by linarith
  have ha0 : a ≠ 0 := by linarith
  field_simp
  ring

theorem hl3c_hd_n0 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cn0 x s) (hl3cN0 x a) a := by
  have hk : 5 * a - 1 ≠ 0 := by linarith
  have := ((((hl3c_hd_y (x := x) (a := a) hx ha).const_mul 3).const_sub 4).const_mul 4).fun_div
    (((hasDerivAt_id a).const_mul 5).sub_const 1) hk
  unfold hl3cn0
  refine (this.const_add 2).congr_deriv ?_
  unfold hl3cN0
  simp only [id]
  field_simp
  ring

theorem hl3c_hd_n1 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cn1 x s) (hl3cN1 x a) a := by
  have hk : 5 * a - 1 ≠ 0 := by linarith
  have := (hl3c_hd_T (x := x) (a := a) hx ha).add ((hasDerivAt_const a (4 : ℝ)).fun_div
    (((hasDerivAt_id a).const_mul 5).sub_const 1) hk)
  unfold hl3cn1
  refine this.congr_deriv ?_
  unfold hl3cN1
  simp only [id]
  field_simp
  ring

/-- `E_L' = 2uLA - LE_L + (2d - λS)u'`. -/
theorem hl3c_hd_EL' (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cEL x (hl3clam x s) (hl3cd x s) (hl3cu x s))
      (2 * hl3cu x a * hl3cL x a * hl3cA x a -
        hl3cL x a * hl3cEL x (hl3clam x a) (hl3cd x a) (hl3cu x a) +
        (2 * hl3cd x a - hl3clam x a * (1 + x)) * (hl3cB x * hl3cub x a)) a := by
  have hEL := hl3c_hd_EL (x := x) (hl3c_hd_lam (x := x) (a := a) (by linarith))
    (hl3c_hd_d (x := x) (a := a) (by linarith) (by linarith)) (hl3c_hd_u (x := x) (a := a) hx ha)
  refine hEL.congr_deriv ?_
  unfold hl3cEL
  ring

/-- `w' = LAE_L - 2Lw + d(d - λS)u'`. -/
theorem hl3c_hd_W' (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hl3cW x (hl3clam x s) (hl3cd x s) (hl3cu x s))
      (hl3cL x a * hl3cA x a * hl3cEL x (hl3clam x a) (hl3cd x a) (hl3cu x a) -
        2 * hl3cL x a * hl3cW x (hl3clam x a) (hl3cd x a) (hl3cu x a) +
        hl3cd x a * (hl3cd x a - hl3clam x a * (1 + x)) * (hl3cB x * hl3cub x a)) a := by
  have hW := hl3c_hd_W (x := x) (hl3c_hd_lam (x := x) (a := a) (by linarith))
    (hl3c_hd_d (x := x) (a := a) (by linarith) (by linarith)) (hl3c_hd_u (x := x) (a := a) hx ha)
  refine hW.congr_deriv ?_
  unfold hl3cEL hl3cW
  ring

/-- The derivative of `J + E_L = (u - 1)/p + p + 1 - q + log(2q/p)`. -/
theorem hl3c_hd_J (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => (hl3cu x s - 1) / hl3cp x s + hl3cp x s + 1 - hsQc x s +
        log (2 * hsQc x s / hl3cp x s))
      (hl3cB x * hl3cub x a / hl3cp x a +
        (x - hl3cB x) / a ^ 2 * (1 - hl3cp x a + hl3cp x a ^ 2 - hl3cu x a) +
        2 * (1 - hsQc x a) ^ 2 / a) a := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hb := hl3c_b_gt (x := x) (a := a) hx0 ha
  have hp0 := hl3c_p_pos (x := x) (a := a) hx0 ha
  have hq0 := hl3c_q_pos (x := x) (a := a) hx0 ha
  have hp := hl3c_hd_p (x := x) (a := a) hx0 ha
  have hq := hl3c_hd_q (x := x) (a := a) hx0
  have hu := hl3c_hd_u (x := x) (a := a) hx ha
  have hlog := ((hq.const_mul 2).fun_div hp hp0.ne').log (by positivity)
  have := (((((hu.sub_const 1).fun_div hp hp0.ne').add hp).add_const 1).sub hq).add hlog
  refine this.congr_deriv ?_
  generalize hl3cB x * hl3cub x a = u'
  generalize hl3cu x a = u
  unfold hl3cL
  unfold hl3cp hsRA at hp0 ⊢
  unfold hsQc at hq0 ⊢
  unfold hl3cK
  rw [hl3c_b_eq] at hp0 hb ⊢
  have hK : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hab : a + (x + hl3cB x * (a - 1)) ≠ 0 := by linarith
  generalize hl3cB x = B at hab ⊢
  field_simp
  ring

/-- **The shape derivative** (the note's (3)), for any duration weight `n` with `n' = N`. -/
theorem hl3c_hasDerivAt {nF : ℝ → ℝ} {N : ℝ} (hx : 1 < x) (ha : 1 < a) (hn : HasDerivAt nF N a) :
    HasDerivAt (fun s => (hl3cu x s - 1) / hl3cp x s + hl3cp x s + 1 - hsQc x s -
        hl3cEL x (hl3clam x s) (hl3cd x s) (hl3cu x s) + log (2 * hsQc x s / hl3cp x s) +
        nF s * (hl3cW x (hl3clam x s) (hl3cd x s) (hl3cu x s) - 3 / 4)) (hl3cH x a (nF a) N) a := by
  have := ((hl3c_hd_J (x := x) (a := a) hx ha).sub (hl3c_hd_EL' (x := x) (a := a) hx ha)).add
    (hn.mul ((hl3c_hd_W' (x := x) (a := a) hx ha).sub_const (3 / 4)))
  have e : (fun s => (hl3cu x s - 1) / hl3cp x s + hl3cp x s + 1 - hsQc x s -
        hl3cEL x (hl3clam x s) (hl3cd x s) (hl3cu x s) + log (2 * hsQc x s / hl3cp x s) +
        nF s * (hl3cW x (hl3clam x s) (hl3cd x s) (hl3cu x s) - 3 / 4)) =
      fun s => (hl3cu x s - 1) / hl3cp x s + hl3cp x s + 1 - hsQc x s +
        log (2 * hsQc x s / hl3cp x s) - hl3cEL x (hl3clam x s) (hl3cd x s) (hl3cu x s) +
        nF s * (hl3cW x (hl3clam x s) (hl3cd x s) (hl3cu x s) - 3 / 4) := by
    funext s; ring
  rw [e]
  refine this.congr_deriv ?_
  unfold hl3cH
  ring

/-- **The central test `F₀` along the central boundary has derivative `H(n₀, N₀)`**. -/
theorem hl3c_hasDerivAt_F0 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hs3F0 x (hs3b x s) s (hsUCB x (hs3b x s)) (hsQc x s))
      (hl3cH x a (hl3cn0 x a) (hl3cN0 x a)) a := by
  have h := hl3c_hasDerivAt (nF := fun s => hl3cn0 x s) hx ha (hl3c_hd_n0 (x := x) (a := a) hx ha)
  refine h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds (by linarith : (0 : ℝ) < a))
    fun s hs => ?_)
  exact hl3c_F_eq x s _ (by linarith) hs

/-- **The central test `F₁` along the central boundary has derivative `H(n₁, N₁)`**. -/
theorem hl3c_hasDerivAt_F1 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => hs3F1 x (hs3b x s) s (hsUCB x (hs3b x s)) (hsQc x s))
      (hl3cH x a (hl3cn1 x a) (hl3cN1 x a)) a := by
  have h := hl3c_hasDerivAt (nF := fun s => hl3cn1 x s) hx ha (hl3c_hd_n1 (x := x) (a := a) hx ha)
  refine h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds (by linarith : (0 : ℝ) < a))
    fun s hs => ?_)
  exact hl3c_F_eq x s _ (by linarith) hs

end Assembly

end SmoothedOctagon

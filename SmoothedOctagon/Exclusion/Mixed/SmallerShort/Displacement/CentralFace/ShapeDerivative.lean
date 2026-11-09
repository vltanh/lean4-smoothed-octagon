module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.Faces

/-!
# Smaller-short window, displacement, central face: the shape derivative

The central face sign `dsp_central_alpha_proof`, first part: the derivative of the two central tests along
the central boundary.

Along `b = x + B(a - 1)`, `B = 25x/(15x + 36)`, at `q = q_c = a²/K`, `K = x(x + 2) + a²`, the
transport is `w = λ²v + d²u - dλE`, `E_L = 2du - λE` with `λ = S²/K`, `d = D/K`, `S = 1 + x`,
`E = S(u - 1) + 3/S - 1/S²`, `v = 1 - 1/S + 1/S²` (`dspc_ELs`, `dspc_Ws`). With `L = 2a/K`,
`A = 1 + 2B + (x - B - Bx)/a`, `u_b = -(x - 1)(g - 1/5808)/(b - 1)²`, the chain rule gives
`q' = L(1 - q)`, `λ' = -Lλ`, `d' = LA - Ld`, `u' = Bu_b`, `p' = (x - B)/(a + b)²`, and the test
`F_i = J + n_i(w - 3/4)` has derivative `dspcH x a n_i N_i`, `N_i = n_i'`.
The identity is assembled from these small chain-rule pieces; no cleared numerator is expanded.

## Main API

* Path quantities `dspcK`, `dspcB`, `dspcE`, `dspcv`, `dspcW`, `dspcEL`, `dspcp`, `dspcu`, `dspclam`,
  `dspcd`, `dspcL`, `dspcA`, `dspcub`, `dspcz`, `dspcy`, `dspcn0`, `dspcn1`, `dspcN0`, `dspcN1`.
* `dspcH x a n N`: the shape derivative.
* `dspc_hasDerivAt_F0`, `dspc_hasDerivAt_F1`: `F_i(x, a, b(x, a), ū(x, b(x, a)), q_c(x, a))` has
  derivative `dspcH x a n_i N_i` at every `a > 1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `K = x(x + 2) + a²`. -/
noncomputable def dspcK (x a : ℝ) : ℝ := x * (x + 2) + a ^ 2

/-- The slope `B = 25x/(15x + 36)` of the central boundary `b(x, a) = x + B(a - 1)`. -/
noncomputable def dspcB (x : ℝ) : ℝ := 25 * x / (15 * x + 36)

/-- `E = S(u - 1) + 3/S - 1/S²`, `S = 1 + x`. -/
noncomputable def dspcE (x u : ℝ) : ℝ := (1 + x) * (u - 1) + 3 / (1 + x) - 1 / (1 + x) ^ 2

/-- `v = 1 - 1/S + 1/S²`. -/
noncomputable def dspcv (x : ℝ) : ℝ := 1 - 1 / (1 + x) + 1 / (1 + x) ^ 2

/-- The transported norm `w = λ²v + d²u - dλE`. -/
noncomputable def dspcW (x lam d u : ℝ) : ℝ := lam ^ 2 * dspcv x + d ^ 2 * u - d * lam * dspcE x u

/-- The transported pairing `E_L = 2du - λE`. -/
noncomputable def dspcEL (x lam d u : ℝ) : ℝ := 2 * d * u - lam * dspcE x u

/-- `p = r_A = a/(a + b)` along the central boundary. -/
noncomputable def dspcp (x a : ℝ) : ℝ := ssRA a (dspb x a)

/-- The incoming ceiling `u = ū(x, b)` along the central boundary. -/
noncomputable def dspcu (x a : ℝ) : ℝ := ssUCB x (dspb x a)

/-- `λ = S²/K`. -/
noncomputable def dspclam (x a : ℝ) : ℝ := (1 + x) ^ 2 / dspcK x a

/-- `d = D/K` along the central boundary. -/
noncomputable def dspcd (x a : ℝ) : ℝ := ssDg x (dspb x a) a / dspcK x a

/-- `L = 2a/K`. -/
noncomputable def dspcL (x a : ℝ) : ℝ := 2 * a / dspcK x a

/-- `A = 1 + 2B + (x - B - Bx)/a`, so that `D' = 2aA`. -/
noncomputable def dspcA (x a : ℝ) : ℝ := 1 + 2 * dspcB x + (x - dspcB x - dspcB x * x) / a

/-- `u_b = (x - 1)(1/5808 - g)/(b - 1)²`, `g = V_G - 3/4`: the `b`-derivative of `ū`. -/
noncomputable def dspcub (x a : ℝ) : ℝ :=
  (x - 1) * (1 / 5808 - (ssVG x - 3 / 4)) / (dspb x a - 1) ^ 2

/-- `z = 2/a - L - (x - B)/(a(a + b))`, so that `y' = yz`. -/
noncomputable def dspcz (x a : ℝ) : ℝ := 2 / a - dspcL x a - (x - dspcB x) / (a * (a + dspb x a))

/-- `y = 2q/p`. -/
noncomputable def dspcy (x a : ℝ) : ℝ := 2 * ssQc x a / dspcp x a

/-- `n₀ = 2 + 4(4 - 3y)/k`, `k = 5a - 1`. -/
noncomputable def dspcn0 (x a : ℝ) : ℝ := 2 + 4 * (4 - 3 * dspcy x a) / (5 * a - 1)

/-- `n₁ = T + 4/k`, `T = p/q`. -/
noncomputable def dspcn1 (x a : ℝ) : ℝ := dspcp x a / ssQc x a + 4 / (5 * a - 1)

/-- `N₀ = n₀' = -12yz/k - 20(4 - 3y)/k²`. -/
noncomputable def dspcN0 (x a : ℝ) : ℝ :=
  -12 * dspcy x a * dspcz x a / (5 * a - 1) - 20 * (4 - 3 * dspcy x a) / (5 * a - 1) ^ 2

/-- `N₁ = n₁' = -Tz - 20/k²`. -/
noncomputable def dspcN1 (x a : ℝ) : ℝ :=
  -(dspcp x a / ssQc x a) * dspcz x a - 20 / (5 * a - 1) ^ 2

/-- **The shape derivative** of `F = J + n(w - 3/4)` with `n' = N`. -/
noncomputable def dspcH (x a n N : ℝ) : ℝ :=
  (x - dspcB x) / a ^ 2 * (1 - dspcp x a + dspcp x a ^ 2 - dspcu x a) +
    2 * (1 - ssQc x a) ^ 2 / a +
    dspcL x a * dspcA x a *
      (n * dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) - 2 * dspcu x a) +
    dspcL x a * (dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) -
      2 * n * dspcW x (dspclam x a) (dspcd x a) (dspcu x a)) +
    dspcB x * dspcub x a * (1 / dspcp x a + dspclam x a * (1 + x) - 2 * dspcd x a +
      n * dspcd x a * (dspcd x a - dspclam x a * (1 + x))) +
    N * (dspcW x (dspclam x a) (dspcd x a) (dspcu x a) - 3 / 4)

/-! ### The transport at the central scale -/

theorem dspc_ELs (x be al u : ℝ) (hx : 0 < x) (hal : 0 < al) :
    ssELs x be al u (ssQc x al) =
      dspcEL x ((1 + x) ^ 2 / dspcK x al) (ssDg x be al / dspcK x al) u := by
  unfold ssELs ssA3 ssE0 ssQc dspcEL dspcE dspcK
  generalize ssDg x be al = D
  have h1 : 0 < x * (x + 2) + al ^ 2 := by positivity
  field_simp
  ring

theorem dspc_Ws (x be al u : ℝ) (hx : 0 < x) (hal : 0 < al) :
    ssWs x be al u (ssQc x al) =
      dspcW x ((1 + x) ^ 2 / dspcK x al) (ssDg x be al / dspcK x al) u := by
  unfold ssWs ssA1 ssA2 ssE0 ssQc dspcW dspcv dspcE dspcK
  generalize ssDg x be al = D
  have h1 : 0 < x * (x + 2) + al ^ 2 := by positivity
  field_simp
  ring

/-- The central tests in the path quantities: `J + n(w - 3/4)` with `p`, `u`, `E_L`, `w` along the
central boundary. -/
theorem dspc_F_eq (x a n : ℝ) (hx : 0 < x) (ha : 0 < a) :
    dspFn x (dspb x a) a (dspcu x a) (ssQc x a) n (log (2 * ssQc x a / dspcp x a)) =
      (dspcu x a - 1) / dspcp x a + dspcp x a + 1 - ssQc x a -
        dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) + log (2 * ssQc x a / dspcp x a) +
        n * (dspcW x (dspclam x a) (dspcd x a) (dspcu x a) - 3 / 4) := by
  unfold dspFn
  rw [dspc_ELs _ _ _ _ hx ha, dspc_Ws _ _ _ _ hx ha]
  rfl

/-! ### Chain-rule pieces -/

section Pieces

variable {x a : ℝ}

theorem dspc_hd_b : HasDerivAt (fun s => dspb x s) (dspcB x) a := by
  unfold dspb dspcB
  have := (((hasDerivAt_id a).sub_const 1).const_mul (25 * x / (15 * x + 36))).const_add x
  refine this.congr_deriv ?_
  ring

theorem dspc_hd_K : HasDerivAt (fun s => dspcK x s) (2 * a) a := by
  unfold dspcK
  have := (hasDerivAt_pow 2 a).const_add (x * (x + 2))
  refine this.congr_deriv ?_
  push_cast; ring

theorem dspc_K_pos (hx : 0 < x) : 0 < dspcK x a := by unfold dspcK; positivity

theorem dspc_hd_q (hx : 0 < x) :
    HasDerivAt (fun s => ssQc x s) (dspcL x a * (1 - ssQc x a)) a := by
  have hK := dspc_K_pos (a := a) hx
  have := (hasDerivAt_pow 2 a).fun_div (dspc_hd_K (x := x) (a := a)) hK.ne'
  unfold ssQc
  refine this.congr_deriv ?_
  unfold dspcL
  unfold dspcK at hK ⊢
  norm_num
  field_simp

theorem dspc_b_eq (x a : ℝ) : dspb x a = x + dspcB x * (a - 1) := by
  unfold dspb dspcB; ring

theorem dspc_b_gt (hx : 0 < x) (ha : 1 < a) : x < dspb x a := by
  rw [dspc_b_eq]
  have : 0 < dspcB x := by unfold dspcB; positivity
  nlinarith

theorem dspc_hd_p (hx : 0 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcp x s) ((x - dspcB x) / (a + dspb x a) ^ 2) a := by
  have hb := dspc_b_gt hx ha
  have hab : a + dspb x a ≠ 0 := by linarith
  have := (hasDerivAt_id a).fun_div ((hasDerivAt_id a).add (dspc_hd_b (x := x) (a := a))) hab
  unfold dspcp ssRA
  refine this.congr_deriv ?_
  simp only [Pi.add_apply, id]
  rw [dspc_b_eq] at hab ⊢
  field_simp
  ring

theorem dspc_hd_u (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcu x s) (dspcB x * dspcub x a) a := by
  have hb := dspc_b_gt (x := x) (a := a) (by linarith) ha
  have hb1 : dspb x a - 1 ≠ 0 := by linarith
  have := ((((dspc_hd_b (x := x) (a := a)).sub_const x).div_const 5808).const_add
    ((x - 1) * (ssVG x - 3 / 4))).fun_div ((dspc_hd_b (x := x) (a := a)).sub_const 1) hb1
  have h2 := this.const_add (3 / 4)
  unfold dspcu ssUCB
  refine h2.congr_deriv ?_
  unfold dspcub
  field_simp
  ring

theorem dspc_hd_D (ha : 0 < a) :
    HasDerivAt (fun s => ssDg x (dspb x s) s) (2 * a * dspcA x a) a := by
  have hbd := dspc_hd_b (x := x) (a := a)
  have := (((((hasDerivAt_pow 2 a).add (((hasDerivAt_id a).const_mul 2).mul hbd)).add_const 1).add_const
    (2 * x)).sub (hbd.const_mul 2 |>.mul_const x))
  unfold ssDg
  refine this.congr_deriv ?_
  unfold dspcA
  rw [dspc_b_eq]
  field_simp
  simp only [id]
  ring

theorem dspc_hd_lam (hx : 0 < x) :
    HasDerivAt (fun s => dspclam x s) (-(dspcL x a) * dspclam x a) a := by
  have hK := dspc_K_pos (a := a) hx
  have := (hasDerivAt_const a ((1 + x) ^ 2)).fun_div (dspc_hd_K (x := x) (a := a)) hK.ne'
  unfold dspclam
  refine this.congr_deriv ?_
  unfold dspcL
  field_simp
  ring

theorem dspc_hd_d (hx : 0 < x) (ha : 0 < a) :
    HasDerivAt (fun s => dspcd x s) (dspcL x a * dspcA x a - dspcL x a * dspcd x a) a := by
  have hK := dspc_K_pos (a := a) hx
  have := (dspc_hd_D (x := x) ha).fun_div (dspc_hd_K (x := x) (a := a)) hK.ne'
  unfold dspcd
  refine this.congr_deriv ?_
  unfold dspcL
  field_simp

end Pieces

/-- The chain rule for `E_L = 2du - λE`. -/
theorem dspc_hd_EL {x a l' d' u' : ℝ} {lamF dF uF : ℝ → ℝ}
    (hl : HasDerivAt lamF l' a) (hd : HasDerivAt dF d' a) (hu : HasDerivAt uF u' a) :
    HasDerivAt (fun s => dspcEL x (lamF s) (dF s) (uF s))
      (2 * d' * uF a + 2 * dF a * u' - l' * dspcE x (uF a) - lamF a * ((1 + x) * u')) a := by
  have hE : HasDerivAt (fun s => dspcE x (uF s)) ((1 + x) * u') a := by
    unfold dspcE
    exact (((hu.sub_const 1).const_mul (1 + x)).add_const _).sub_const _
  have := ((hd.const_mul 2).mul hu).sub (hl.mul hE)
  unfold dspcEL
  refine this.congr_deriv ?_
  ring

/-- The chain rule for `w = λ²v + d²u - dλE`. -/
theorem dspc_hd_W {x a l' d' u' : ℝ} {lamF dF uF : ℝ → ℝ}
    (hl : HasDerivAt lamF l' a) (hd : HasDerivAt dF d' a) (hu : HasDerivAt uF u' a) :
    HasDerivAt (fun s => dspcW x (lamF s) (dF s) (uF s))
      (2 * lamF a * l' * dspcv x + 2 * dF a * d' * uF a + dF a ^ 2 * u' -
        (d' * lamF a + dF a * l') * dspcE x (uF a) - dF a * lamF a * ((1 + x) * u')) a := by
  have hE : HasDerivAt (fun s => dspcE x (uF s)) ((1 + x) * u') a := by
    unfold dspcE
    exact (((hu.sub_const 1).const_mul (1 + x)).add_const _).sub_const _
  have := (((hl.fun_pow 2).mul_const (dspcv x)).add ((hd.fun_pow 2).mul hu)).sub
    ((hd.mul hl).mul hE)
  unfold dspcW
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  push_cast
  ring

section Assembly

variable {x a : ℝ}

theorem dspc_p_pos (hx : 0 < x) (ha : 1 < a) : 0 < dspcp x a := by
  have := dspc_b_gt (x := x) (a := a) hx ha
  unfold dspcp ssRA
  apply div_pos <;> linarith

theorem dspc_q_pos (hx : 0 < x) (ha : 1 < a) : 0 < ssQc x a := by
  unfold ssQc
  have : 0 < a := by linarith
  positivity

/-- `y' = yz`. -/
theorem dspc_hd_y (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcy x s) (dspcy x a * dspcz x a) a := by
  have hb := dspc_b_gt (x := x) (a := a) (by linarith) ha
  have hp0 := dspc_p_pos (x := x) (a := a) (by linarith) ha
  have := ((dspc_hd_q (x := x) (a := a) (by linarith)).const_mul 2).fun_div
    (dspc_hd_p (x := x) (a := a) (by linarith) ha) hp0.ne'
  unfold dspcy
  refine this.congr_deriv ?_
  unfold dspcz dspcL
  unfold dspcp ssRA at hp0 ⊢
  unfold ssQc dspcK
  have hK : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hab : a + dspb x a ≠ 0 := by linarith
  have ha0 : a ≠ 0 := by linarith
  field_simp

/-- `T' = -Tz`, `T = p/q`. -/
theorem dspc_hd_T (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcp x s / ssQc x s) (-(dspcp x a / ssQc x a) * dspcz x a) a := by
  have hb := dspc_b_gt (x := x) (a := a) (by linarith) ha
  have hq0 := dspc_q_pos (x := x) (a := a) (by linarith) ha
  have := (dspc_hd_p (x := x) (a := a) (by linarith) ha).fun_div
    (dspc_hd_q (x := x) (a := a) (by linarith)) hq0.ne'
  refine this.congr_deriv ?_
  unfold dspcz dspcL
  unfold ssQc at hq0 ⊢
  unfold dspcp ssRA dspcK
  have hK : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hab : a + dspb x a ≠ 0 := by linarith
  have ha0 : a ≠ 0 := by linarith
  field_simp
  ring

theorem dspc_hd_n0 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcn0 x s) (dspcN0 x a) a := by
  have hk : 5 * a - 1 ≠ 0 := by linarith
  have := ((((dspc_hd_y (x := x) (a := a) hx ha).const_mul 3).const_sub 4).const_mul 4).fun_div
    (((hasDerivAt_id a).const_mul 5).sub_const 1) hk
  unfold dspcn0
  refine (this.const_add 2).congr_deriv ?_
  unfold dspcN0
  simp only [id]
  field_simp
  ring

theorem dspc_hd_n1 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcn1 x s) (dspcN1 x a) a := by
  have hk : 5 * a - 1 ≠ 0 := by linarith
  have := (dspc_hd_T (x := x) (a := a) hx ha).add ((hasDerivAt_const a (4 : ℝ)).fun_div
    (((hasDerivAt_id a).const_mul 5).sub_const 1) hk)
  unfold dspcn1
  refine this.congr_deriv ?_
  unfold dspcN1
  simp only [id]
  field_simp
  ring

/-- `E_L' = 2uLA - LE_L + (2d - λS)u'`. -/
theorem dspc_hd_EL' (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcEL x (dspclam x s) (dspcd x s) (dspcu x s))
      (2 * dspcu x a * dspcL x a * dspcA x a -
        dspcL x a * dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) +
        (2 * dspcd x a - dspclam x a * (1 + x)) * (dspcB x * dspcub x a)) a := by
  have hEL := dspc_hd_EL (x := x) (dspc_hd_lam (x := x) (a := a) (by linarith))
    (dspc_hd_d (x := x) (a := a) (by linarith) (by linarith)) (dspc_hd_u (x := x) (a := a) hx ha)
  refine hEL.congr_deriv ?_
  unfold dspcEL
  ring

/-- `w' = LAE_L - 2Lw + d(d - λS)u'`. -/
theorem dspc_hd_W' (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspcW x (dspclam x s) (dspcd x s) (dspcu x s))
      (dspcL x a * dspcA x a * dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) -
        2 * dspcL x a * dspcW x (dspclam x a) (dspcd x a) (dspcu x a) +
        dspcd x a * (dspcd x a - dspclam x a * (1 + x)) * (dspcB x * dspcub x a)) a := by
  have hW := dspc_hd_W (x := x) (dspc_hd_lam (x := x) (a := a) (by linarith))
    (dspc_hd_d (x := x) (a := a) (by linarith) (by linarith)) (dspc_hd_u (x := x) (a := a) hx ha)
  refine hW.congr_deriv ?_
  unfold dspcEL dspcW
  ring

/-- The derivative of `J + E_L = (u - 1)/p + p + 1 - q + log(2q/p)`. -/
theorem dspc_hd_J (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => (dspcu x s - 1) / dspcp x s + dspcp x s + 1 - ssQc x s +
        log (2 * ssQc x s / dspcp x s))
      (dspcB x * dspcub x a / dspcp x a +
        (x - dspcB x) / a ^ 2 * (1 - dspcp x a + dspcp x a ^ 2 - dspcu x a) +
        2 * (1 - ssQc x a) ^ 2 / a) a := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hb := dspc_b_gt (x := x) (a := a) hx0 ha
  have hp0 := dspc_p_pos (x := x) (a := a) hx0 ha
  have hq0 := dspc_q_pos (x := x) (a := a) hx0 ha
  have hp := dspc_hd_p (x := x) (a := a) hx0 ha
  have hq := dspc_hd_q (x := x) (a := a) hx0
  have hu := dspc_hd_u (x := x) (a := a) hx ha
  have hlog := ((hq.const_mul 2).fun_div hp hp0.ne').log (by positivity)
  have := (((((hu.sub_const 1).fun_div hp hp0.ne').add hp).add_const 1).sub hq).add hlog
  refine this.congr_deriv ?_
  generalize dspcB x * dspcub x a = u'
  generalize dspcu x a = u
  unfold dspcL
  unfold dspcp ssRA at hp0 ⊢
  unfold ssQc at hq0 ⊢
  unfold dspcK
  rw [dspc_b_eq] at hp0 hb ⊢
  have hK : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hab : a + (x + dspcB x * (a - 1)) ≠ 0 := by linarith
  generalize dspcB x = B at hab ⊢
  field_simp
  ring

/-- **The shape derivative**, for any duration weight `n` with `n' = N`. -/
theorem dspc_hasDerivAt {nF : ℝ → ℝ} {N : ℝ} (hx : 1 < x) (ha : 1 < a) (hn : HasDerivAt nF N a) :
    HasDerivAt (fun s => (dspcu x s - 1) / dspcp x s + dspcp x s + 1 - ssQc x s -
        dspcEL x (dspclam x s) (dspcd x s) (dspcu x s) + log (2 * ssQc x s / dspcp x s) +
        nF s * (dspcW x (dspclam x s) (dspcd x s) (dspcu x s) - 3 / 4)) (dspcH x a (nF a) N) a := by
  have := ((dspc_hd_J (x := x) (a := a) hx ha).sub (dspc_hd_EL' (x := x) (a := a) hx ha)).add
    (hn.mul ((dspc_hd_W' (x := x) (a := a) hx ha).sub_const (3 / 4)))
  have e : (fun s => (dspcu x s - 1) / dspcp x s + dspcp x s + 1 - ssQc x s -
        dspcEL x (dspclam x s) (dspcd x s) (dspcu x s) + log (2 * ssQc x s / dspcp x s) +
        nF s * (dspcW x (dspclam x s) (dspcd x s) (dspcu x s) - 3 / 4)) =
      fun s => (dspcu x s - 1) / dspcp x s + dspcp x s + 1 - ssQc x s +
        log (2 * ssQc x s / dspcp x s) - dspcEL x (dspclam x s) (dspcd x s) (dspcu x s) +
        nF s * (dspcW x (dspclam x s) (dspcd x s) (dspcu x s) - 3 / 4) := by
    funext s; ring
  rw [e]
  refine this.congr_deriv ?_
  unfold dspcH
  ring

/-- **The central test `F₀` along the central boundary has derivative `H(n₀, N₀)`**. -/
theorem dspc_hasDerivAt_F0 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspF0 x (dspb x s) s (ssUCB x (dspb x s)) (ssQc x s))
      (dspcH x a (dspcn0 x a) (dspcN0 x a)) a := by
  have h := dspc_hasDerivAt (nF := fun s => dspcn0 x s) hx ha (dspc_hd_n0 (x := x) (a := a) hx ha)
  refine h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds (by linarith : (0 : ℝ) < a))
    fun s hs => ?_)
  exact dspc_F_eq x s _ (by linarith) hs

/-- **The central test `F₁` along the central boundary has derivative `H(n₁, N₁)`**. -/
theorem dspc_hasDerivAt_F1 (hx : 1 < x) (ha : 1 < a) :
    HasDerivAt (fun s => dspF1 x (dspb x s) s (ssUCB x (dspb x s)) (ssQc x s))
      (dspcH x a (dspcn1 x a) (dspcN1 x a)) a := by
  have h := dspc_hasDerivAt (nF := fun s => dspcn1 x s) hx ha (dspc_hd_n1 (x := x) (a := a) hx ha)
  refine h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds (by linarith : (0 : ℝ) < a))
    fun s hs => ?_)
  exact dspc_F_eq x s _ (by linarith) hs

end Assembly

end SmoothedOctagon

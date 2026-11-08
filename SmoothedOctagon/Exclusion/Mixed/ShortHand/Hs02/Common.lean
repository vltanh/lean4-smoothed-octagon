module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case: shared helpers of gates S0 and S2

Scalar identities on the face value `hsF` and the comparison chain from the actual outer root to
the scale polynomial, shared by `ShortHand.S0` (the large-ratio gate) and `ShortHand.S2` (the
sharp-ratio gate).

## Main API

* `hs02_F_u_sub`: `hsF` is affine in `u` with slope `(τ + m)d(d - λS) + 1/r_A + λS - 2d`.
* `hs02_F_ell_mono`: `hsF` increases in the log value `ℓ`.
* `hs02_F_dur`: the three duration tests (`hs_dur_three`) in terms of `hsF`.
* `hs02_rA_A1`: `r_A·A₁ = 2r_A + (x - 1)/Q + (D/Q)E₀`.
* `hs02_D_pos`: `D ≥ 2 + 4x - 2x² ≥ 2/25` on `1 < x ≤ 12/5`, `β ≤ αx`.
* `HsData.hs02_root_phi`: for a floor weight `m ≥ 0` with a positive factor `B_{τ+m}`, the actual
  root gives `0 ≤ Φ(q)` at `p = τq` (the weighted outer envelope in scale coordinates).
* `HsData.hs02_strip_up`, `HsData.hs02_strip_54`, `HsData.hs02_strip_98`: the β-strips of the
  strong lower order and the two upper orders.
* `HsData.hs02_u_le_1316`: `u ≤ 13/16`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The `u`-increment of the face value: `hsF` is affine in `u` with slope
`(τ + m)d(d - λS) + 1/r_A + λS - 2d`, `d = qD/α²`, `λ = 1 - (1 - α⁻²)q`. -/
theorem hs02_F_u_sub (x be al u u' q τ ℓ m : ℝ) :
    hsF x be al u' q τ ℓ m - hsF x be al u q τ ℓ m = (u' - u) *
      ((τ + m) * (q * (hsDg x be al / al ^ 2)) * (q * (hsDg x be al / al ^ 2) -
        (1 - (1 - 1 / al ^ 2) * q) * (1 + x)) + 1 / hsRA al be +
        (1 - (1 - 1 / al ^ 2) * q) * (1 + x) - 2 * (q * (hsDg x be al / al ^ 2))) := by
  unfold hsF hsWs hsELs hsA1 hsA2 hsA3 hsE0
  ring

/-- `hsF` increases with its log value `ℓ`. -/
theorem hs02_F_ell_mono {x be al u q τ ℓ ℓ' m : ℝ} (h : ℓ ≤ ℓ') :
    hsF x be al u q τ ℓ m ≤ hsF x be al u q τ ℓ' m := by
  unfold hsF
  linarith

/-- **The three duration tests for `hsF`**: for
`2 ≤ τ ≤ T`, `F(τ, log(τ/T)) ≤ max{F(2, 5/(2T) - 11/9), F(8T/9, -1/9), F(T, 0)}`. -/
theorem hs02_F_dur {x be al u q m T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    hsF x be al u q τ (log (τ / T)) m ≤
      max (hsF x be al u q 2 (5 / (2 * T) - 11 / 9) m)
        (max (hsF x be al u q (8 * T / 9) (-1 / 9) m) (hsF x be al u q T 0 m)) := by
  have hT : 0 < T := by linarith
  have h := hs_dur_three (c₁ := hsWs x be al u q - 1)
    (c₀ := (u - 1) / hsRA al be + hsRA al be + 1 - q - hsELs x be al u q +
      m * (hsWs x be al u q - 3 / 4)) h2 hτ
  have e : ∀ τ' ℓ', hsF x be al u q τ' ℓ' m = (hsWs x be al u q - 1) * τ' + 1 / τ' +
      ((u - 1) / hsRA al be + hsRA al be + 1 - q - hsELs x be al u q +
        m * (hsWs x be al u q - 3 / 4)) + ℓ' := by
    intro τ' ℓ'; unfold hsF; ring
  have e8 : 1 / (8 * T / 9) = 9 / (8 * T) := by field_simp
  rw [e, e, e, e, e8]
  convert h using 3 <;> ring

/-- `r_A·A₁ = 2r_A + (x - 1)/Q + (D/Q)E₀`, `Q = α(α + β)`. -/
theorem hs02_rA_A1 {x be al u : ℝ} (hal : 0 < al) (hbe : 0 < be) :
    hsRA al be * hsA1 x be al u = 2 * hsRA al be + (x - 1) / (al * (al + be)) +
      hsDg x be al / (al * (al + be)) * hsE0 x u := by
  unfold hsRA hsA1
  have : al + be ≠ 0 := by positivity
  field_simp
  ring

/-- **The positive diagonal** (from `D ≥ αD₀`): for
`1 < x ≤ 12/5`, `1 ≤ α ≤ x ≤ β ≤ αx`, `D ≥ 2 + 4x - 2x² ≥ 2/25`. -/
theorem hs02_D_pos {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al) (hax : al ≤ x)
    (hb : be ≤ al * x) :
    2 + 4 * x - 2 * x ^ 2 ≤ hsDg x be al ∧ 2 / 25 ≤ hsDg x be al := by
  have hD0 : 2 / 25 ≤ 2 + 4 * x - 2 * x ^ 2 := by nlinarith
  have e1 : hsDg x be al = (1 + 2 * x) * al ^ 2 - 2 * x ^ 2 * al + (1 + 2 * x) +
      2 * (x - al) * (al * x - be) := by unfold hsDg; ring
  have e2 : (1 + 2 * x) * al ^ 2 - 2 * x ^ 2 * al + (1 + 2 * x) - (2 + 4 * x - 2 * x ^ 2) =
      (al - 1) * ((1 + 2 * x) * (al + 1) - 2 * x ^ 2) := by ring
  have h3 : 0 ≤ (al - 1) * ((1 + 2 * x) * (al + 1) - 2 * x ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have h4 : 0 ≤ 2 * (x - al) * (al * x - be) :=
    mul_nonneg (by linarith) (by linarith)
  constructor <;> linarith

namespace HsData

variable (H : HsData)

theorem hs02_q_pos : 0 < H.q := by
  unfold q hsQ hsLam
  have h1 := H.rho_pos
  have h2 : 0 ≤ H.rho * (H.al ^ 2 - 1) := mul_nonneg h1.le (by nlinarith [H.one_le_al])
  have h3 : 0 < H.al := by linarith [H.one_le_al]
  positivity

theorem hs02_rA_pos : 0 < hsRA H.al H.be := by
  have h1 := H.one_le_al
  have h2 := H.x_le_be
  have h3 := H.one_lt_x
  unfold hsRA
  exact div_pos (by linarith) (by linarith)

theorem hs02_two_q : 2 * H.q < hsRA H.al H.be := by
  have h1 := H.τ_lt
  have h2 := H.two_lt_τ
  have h3 := H.hs02_q_pos
  unfold q
  unfold q at h3
  nlinarith

/-- `u ≤ 13/16` (`ss_V_le` at `a = 1`, `C = x`). -/
theorem hs02_u_le_1316 : H.u ≤ 13 / 16 :=
  H.u_le_V.trans (ss_V_le one_pos H.one_lt_x)

/-- **The comparison chain**: for a floor weight `m ≥ 0` with `B_{τ+m} > 0` on `[t₀, t]`, the
actual root gives `0 ≤ Φ(q)` at `p = τq`. The weighted outer envelope `hs_env_weighted` at the root
`R_τ = 0` with `w ≥ 3/4` is rewritten in the scale coordinates (`hs_env_scale`) and identified with
`Φ` (`hs_phi_eq`). -/
theorem hs02_root_phi {m : ℝ} (hm : 0 ≤ m)
    (hB : ∀ s ∈ Icc (H.rho * (1 + H.x)) H.t,
      0 < 1 + (H.τ + m) * (hsLam H.al H.rho * s - hsLam H.al H.rho * H.rho * hsDg H.x H.be H.al)) :
    0 ≤ hsPhi H.x H.be H.al H.u (H.τ * H.q) m H.q := by
  have hx1 := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hq0 := H.hs02_q_pos
  have hq1 : H.q < 1 := by have := H.q_lt; unfold q; linarith
  have ht0 : H.rho * (1 + H.x) ≤ H.t := by
    have h := H.rho_lt_rt
    rw [one_div_mul_eq_div, lt_div_iff₀ (by linarith)] at h
    linarith
  have henv := hs_env_weighted (be := H.be) (u := H.u) (τ := H.τ) hx1 H.one_le_al H.rho_pos ht0
    H.t_le_r H.v_le hB
  have h0 := H.root_zero
  have hw : 0 ≤ m * (hsW H.x H.be H.al H.rho H.u H.t H.v - 3 / 4) := by
    rw [← H.w_eq]; exact mul_nonneg hm (by linarith [H.w_ge])
  have hsc := (hs_scale_coords (x := H.x) (be := H.be) H.one_le_al H.rho_pos).1
  have hes := hs_env_scale (be := H.be) (u := H.u) (τ := H.τ) hx0 H.one_le_al hq0 hq1
  unfold q at hes hq0
  rw [hsc] at hes
  rw [hes.1, hes.2.2.1] at henv
  have hτ0 : 0 < H.τ := by linarith [H.two_lt_τ]
  have hphi := hs_phi_eq (x := H.x) (be := H.be) (al := H.al) (u := H.u) (m := m)
    (mul_pos hτ0 hq0) hq0
  rw [mul_div_cancel_right₀ _ hq0.ne'] at hphi
  unfold q
  rw [← hphi]
  unfold hsRs at henv
  have e : hsF H.x H.be H.al H.u (hsQ H.al H.rho) H.τ (log (H.τ * hsQ H.al H.rho / hsRA H.al H.be))
      m = hsF H.x H.be H.al H.u (hsQ H.al H.rho) H.τ
        (log (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) 0 +
      m * (hsWs H.x H.be H.al H.u (hsQ H.al H.rho) - 3 / 4) := by
    unfold hsF; ring
  rw [e]
  linarith

/-- The strong-order strip: `β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`. -/
theorem hs02_strip_up :
    H.be ≤ H.x + H.x * (7 * H.x + 1) * (H.al - 1) / (4 * H.x ^ 2 + 11 * H.x + 1) := by
  have h := H.strong_order
  have hx0 : 0 < H.x := by linarith [H.one_lt_x]
  have hR : 0 < 4 * H.x ^ 2 + 11 * H.x + 1 := by positivity
  have h7 : 0 < 7 * H.x + 1 := by positivity
  unfold hsKs at h
  have e : H.be / H.x + 4 * (H.x + 1) / (7 * H.x + 1) * (H.be - H.x) =
      1 + (H.be - H.x) * (4 * H.x ^ 2 + 11 * H.x + 1) / (H.x * (7 * H.x + 1)) := by
    field_simp; ring
  rw [e] at h
  have h2 : (H.be - H.x) * (4 * H.x ^ 2 + 11 * H.x + 1) ≤ (H.al - 1) * (H.x * (7 * H.x + 1)) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < H.x * (7 * H.x + 1))).1
      (show (H.be - H.x) * (4 * H.x ^ 2 + 11 * H.x + 1) / (H.x * (7 * H.x + 1)) ≤ H.al - 1 by
        linarith)
    linarith
  have h3 : H.be - H.x ≤ H.x * (7 * H.x + 1) * (H.al - 1) / (4 * H.x ^ 2 + 11 * H.x + 1) := by
    rw [le_div_iff₀ hR]; linarith
  linarith

/-- The `5/4`-order strip: `β ≥ x + 4x(α - 1)/(5x + 4)`. -/
theorem hs02_strip_54 : H.x + 4 * H.x * (H.al - 1) / (5 * H.x + 4) ≤ H.be := by
  have h := H.upper_order_54
  have hx0 : 0 < H.x := by linarith [H.one_lt_x]
  have e : H.be / H.x + 5 / 4 * (H.be - H.x) = 1 + (H.be - H.x) * (5 * H.x + 4) / (4 * H.x) := by
    field_simp; ring
  rw [e] at h
  have h2 : (H.al - 1) * (4 * H.x) ≤ (H.be - H.x) * (5 * H.x + 4) := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * H.x)).1
      (show H.al - 1 ≤ (H.be - H.x) * (5 * H.x + 4) / (4 * H.x) by linarith)
    linarith
  have h3 : 4 * H.x * (H.al - 1) / (5 * H.x + 4) ≤ H.be - H.x := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- The `9/8`-order strip: `β ≥ x + 8x(α - 1)/(9x + 8)`. -/
theorem hs02_strip_98 (hx5 : H.x ≤ 5) : H.x + 8 * H.x * (H.al - 1) / (9 * H.x + 8) ≤ H.be := by
  have h := H.upper_order_98 hx5
  have hx0 : 0 < H.x := by linarith [H.one_lt_x]
  have e : H.be / H.x + 9 / 8 * (H.be - H.x) = 1 + (H.be - H.x) * (9 * H.x + 8) / (8 * H.x) := by
    field_simp; ring
  rw [e] at h
  have h2 : (H.al - 1) * (8 * H.x) ≤ (H.be - H.x) * (9 * H.x + 8) := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * H.x)).1
      (show H.al - 1 ≤ (H.be - H.x) * (9 * H.x + 8) / (8 * H.x) by linarith)
    linarith
  have h3 : 8 * H.x * (H.al - 1) / (9 * H.x + 8) ≤ H.be - H.x := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

end HsData

end SmoothedOctagon

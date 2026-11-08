module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs02.Common
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S2Defs
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCentral
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandSmall
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandLarge

/-!
# Hand proof of the smaller-short case, gate S2: `x < 13/6`

This module excludes `13/6 ≤ x < 12/5` (the upper end comes from S0). Assuming it, the
variable-floor weight `m = 2 - 7τ/(4T)` gives `G_τ = R_τ + m(w - 3/4) ≥ 0` at the actual root; the
envelope (`hs_env_weighted`, `hs_B_pos_weighted`), the convex scale polynomial (`hs_A2_pos`,
`hs_phi_convex_max`, `hs2_zero_neg`) and the `τ = 2` continuation (`hs2_tau2_mono`) reach a face
`q* = min{q_c, 1/7}`; the incoming coefficient (`hs2_uslope`) and the face ceilings
(`hs2_central_ceiling`, `hs2_outer_ceiling`) reduce to the face signs `hs2_central_sign`,
`hs2_outer_sign_small`, `hs2_outer_sign_large` (hand proofs in `Heavy/S2Hand*.lean`).

## Main API

* `hsUC`, `hsUs`: the face ceilings `u_C`, `u_s`.
* `hs2_uslope`, `hs2_zero_neg`, `hs2_tau2_mono`, `hs2_central_ceiling`, `hs2_outer_ceiling`.
* Face signs, proved in `Heavy/S2HandCentral`, `Heavy/S2HandSmall` and `Heavy/S2HandLarge`:
  `hs2_central_sign`, `hs2_outer_sign_small`, `hs2_outer_sign_large`.
* Gate: `HsData.s2`, `M2Short.hs_S2`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The `u`-slope in scalar form. -/
private theorem hs2_slope_pos {S lam d z ri : ℝ} (hS : 0 < S) (hS2 : S ≤ 17 / 5) (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) (hd0 : 0 < d) (hd : d < 3 / 7) (hz : 0 ≤ z) (hzd : z * d < 1 + d / 4)
    (hri : 2 ≤ ri) : 0 < z * d * (d - lam * S) + ri + lam * S - 2 * d := by
  have e : z * d * (d - lam * S) + ri + lam * S - 2 * d =
      ri - 2 * d + z * d ^ 2 + lam * S * (1 - z * d) := by ring
  rw [e]
  have h1 : lam * S * (-(d / 4)) ≤ lam * S * (1 - z * d) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : lam * S ≤ 17 / 5 := by nlinarith
  have h3 : 0 ≤ z * d ^ 2 := by positivity
  nlinarith

/-- **The positive incoming coefficient**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ x ≤ β`, `α < β`,
`0 < D < α(α + β)`, `D < 3α²`, `0 < q ≤ 1/7`, `2 ≤ τ ≤ T = r_A/q`, the variable-floor face value
(weight `m = 2 - 7τq/(4r_A)`) is nondecreasing in `u` (slope `> 109/140`). -/
theorem hs2_uslope {x be al q τ ℓ u u' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hab : al < be) (hD : 0 < hsDg x be al)
    (hDQ : hsDg x be al < al * (al + be)) (hD3 : hsDg x be al < 3 * al ^ 2) (hq : 0 < q)
    (hq7 : q ≤ 1 / 7) (hτ : 2 ≤ τ) (hτT : τ * q ≤ hsRA al be) (huu : u ≤ u') :
    hsF x be al u q τ ℓ (2 - 7 * τ * q / (4 * hsRA al be)) ≤
      hsF x be al u' q τ ℓ (2 - 7 * τ * q / (4 * hsRA al be)) := by
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hQ : 0 < al * (al + be) := by positivity
  have hr0 : 0 < hsRA al be := by unfold hsRA; positivity
  have hri : 2 ≤ 1 / hsRA al be := by
    unfold hsRA
    rw [one_div_div, le_div_iff₀ hal0]; linarith
  have hε : 0 ≤ 1 - 1 / al ^ 2 := by
    rw [sub_nonneg, div_le_one ha2]; exact one_le_pow₀ hal
  have hε1 : 1 - 1 / al ^ 2 ≤ 1 := by
    have : 0 ≤ 1 / al ^ 2 := by positivity
    linarith
  have hΔ0 : 0 < hsDg x be al / al ^ 2 := div_pos hD ha2
  have hΔ3 : hsDg x be al / al ^ 2 < 3 := by rw [div_lt_iff₀ ha2]; linarith
  have hd0 : 0 < q * (hsDg x be al / al ^ 2) := mul_pos hq hΔ0
  have hd : q * (hsDg x be al / al ^ 2) < 3 / 7 := by
    have := mul_lt_mul_of_pos_left hΔ3 hq
    linarith
  -- `T·d = D/Q < 1`
  have hTd : hsRA al be * (hsDg x be al / al ^ 2) < 1 := by
    have e : hsRA al be * (hsDg x be al / al ^ 2) = hsDg x be al / (al * (al + be)) := by
      unfold hsRA; field_simp
    rw [e, div_lt_one hQ]; exact hDQ
  -- `z = τ + m ≤ T + 1/4`
  have hq2 : 2 * q ≤ hsRA al be := by
    have := mul_le_mul_of_nonneg_right hτ hq.le
    linarith
  have hz : τ + (2 - 7 * τ * q / (4 * hsRA al be)) ≤ hsRA al be / q + 1 / 4 := by
    have e : τ + (2 - 7 * τ * q / (4 * hsRA al be)) - (hsRA al be / q + 1 / 4) =
        (τ * q - hsRA al be) * (4 * hsRA al be - 7 * q) / (4 * hsRA al be * q) := by
      field_simp; ring
    have : (τ * q - hsRA al be) * (4 * hsRA al be - 7 * q) / (4 * hsRA al be * q) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
        (by positivity)
    linarith
  have hm : 1 / 4 ≤ 2 - 7 * τ * q / (4 * hsRA al be) := by
    have : 7 * τ * q / (4 * hsRA al be) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hzd : (τ + (2 - 7 * τ * q / (4 * hsRA al be))) * (q * (hsDg x be al / al ^ 2)) <
      1 + q * (hsDg x be al / al ^ 2) / 4 := by
    have h1 := mul_le_mul_of_nonneg_right hz hd0.le
    have e : (hsRA al be / q + 1 / 4) * (q * (hsDg x be al / al ^ 2)) =
        hsRA al be * (hsDg x be al / al ^ 2) + q * (hsDg x be al / al ^ 2) / 4 := by
      field_simp
    linarith
  have hpos := hs2_slope_pos (S := 1 + x) (lam := 1 - (1 - 1 / al ^ 2) * q) (by linarith)
    (by linarith) (by linarith [mul_le_of_le_one_left hq.le hε1])
    (by linarith [mul_nonneg hε hq.le])
    hd0 hd (by linarith) hzd hri
  have e := hs02_F_u_sub x be al u u' q τ ℓ (2 - 7 * τ * q / (4 * hsRA al be))
  linarith [mul_nonneg (sub_nonneg.2 huu) hpos.le]

/-- `F(0) < 0`. -/
private theorem hs2_F0_neg {x u r : ℝ} (hx : 13 / 6 ≤ x) (hu' : u ≤ 61 / 80) (hr0 : 0 < r)
    (hrA : r < 3 / 7) : hsE0 x u + (u - 1) / r + r + 1 / 2 < 0 := by
  have hS : 0 < 1 + x := by linarith
  have hE0 : hsE0 x u ≤ -(19 / 80) * (1 + x) + 1 / (1 + x) := by
    unfold hsE0; nlinarith
  have hE0n : 1 / (1 + x) ≤ 6 / 19 := by rw [div_le_iff₀ hS]; linarith
  have h1 : (u - 1) / r ≤ -(19 / 80) / r := div_le_div_of_nonneg_right (by linarith) hr0.le
  have h2 : 133 / 240 ≤ 19 / 80 / r := by rw [le_div_iff₀ hr0]; linarith
  have h3 : -(19 / 80) / r = -(19 / 80 / r) := by ring
  linarith

/-- `F(1) < 0`; `k = D/Q`, `Qi = 1/Q`. -/
private theorem hs2_F1_neg {x u r k Qi : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hu' : u ≤ 61 / 80) (hr0 : 0 < r) (hurA : u ≤ m2U r) (hk : k < 1)
    (hQi : 1 / (x ^ 2 * (1 + x)) ≤ Qi) :
    hsE0 x u * (1 - k) + (u - 1) / r + 17 / 16 - r - (x - 1) * Qi < 0 := by
  have hS : 0 < 1 + x := by linarith
  have hE0 : hsE0 x u ≤ -(19 / 80) * (1 + x) + 1 / (1 + x) := by
    unfold hsE0; nlinarith
  have hE0n : 1 / (1 + x) ≤ 6 / 19 := by rw [div_le_iff₀ hS]; linarith
  have hE0neg : hsE0 x u * (1 - k) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hu1 : (u - 1) / r ≤ r - 1 := by
    rw [div_le_iff₀ hr0]; unfold m2U at hurA; nlinarith
  have hx1 : 1 / 16 < (x - 1) * (1 / (x ^ 2 * (1 + x))) := by
    rw [mul_one_div, lt_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  have := mul_le_mul_of_nonneg_left hQi (by linarith : (0 : ℝ) ≤ x - 1)
  linarith

/-- **The zero-scale end**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ x ≤ β ≤ αx`, `r_A < 3/7`,
`D < α(α + β)`, `3/4 ≤ u ≤ 61/80`, `u ≤ U(r_A)` and `0 < p ≤ r_A`: `Φ(0) = C(p) + m/4 < 0`,
`m = 2 - 7p/(4r_A)`. -/
theorem hs2_zero_neg {x be al u p : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hbx : be ≤ al * x) (hrA : hsRA al be < 3 / 7)
    (hDQ : hsDg x be al < al * (al + be)) (hu : 3 / 4 ≤ u) (hu' : u ≤ 61 / 80)
    (hurA : u ≤ m2U (hsRA al be)) (hp : 0 < p) (hpr : p ≤ hsRA al be) :
    hsPhi x be al u p (2 - 7 * p / (4 * hsRA al be)) 0 < 0 := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hQ : 0 < al * (al + be) := by positivity
  have e0 : hsPhi x be al u p (2 - 7 * p / (4 * hsRA al be)) 0 = hsE0 x u + (u - 1) / hsRA al be +
      hsRA al be + 1 - p * hsA1 x be al u + log (p / hsRA al be) +
      (2 - 7 * p / (4 * hsRA al be)) / 4 := by
    unfold hsPhi hsCp; ring
  rw [e0]
  have hrA1 := hs02_rA_A1 (x := x) (u := u) hal0 hbe0
  have hr0 : 0 < hsRA al be := by unfold hsRA; positivity
  have hk : hsDg x be al / (al * (al + be)) < 1 := by rwa [div_lt_one hQ]
  have hQi : 1 / (x ^ 2 * (1 + x)) ≤ 1 / (al * (al + be)) := by
    apply one_div_le_one_div_of_le hQ
    have : al + be ≤ x * (1 + x) := by nlinarith
    calc al * (al + be) ≤ x * (x * (1 + x)) :=
          mul_le_mul hax this (by positivity) hx0.le
      _ = x ^ 2 * (1 + x) := by ring
  have hF0 := hs2_F0_neg hx hu' hr0 hrA
  have hF1 := hs2_F1_neg hx hx2 hu' hr0 hurA hk hQi
  generalize hsRA al be = r at *
  generalize hsA1 x be al u = A1 at *
  have hlog : log (p / r) ≤ p / r - 1 := Real.log_le_sub_one_of_pos (div_pos hp hr0)
  have hF1' : hsE0 x u + (u - 1) / r + r + 1 / 2 + 9 / 16 - r * A1 < 0 := by
    rw [hrA1]
    have e : (x - 1) / (al * (al + be)) = (x - 1) * (1 / (al * (al + be))) := by ring
    linarith only [hF1, e]
  have hpr' : p / r ≤ 1 := by rw [div_le_one hr0]; exact hpr
  have hp0 : 0 < p / r := div_pos hp hr0
  have e2 : hsE0 x u + (u - 1) / r + r + 1 - p * A1 + (p / r - 1) + (2 - 7 * p / (4 * r)) / 4 =
      (1 - p / r) * (hsE0 x u + (u - 1) / r + r + 1 / 2) +
        p / r * (hsE0 x u + (u - 1) / r + r + 1 / 2 + 9 / 16 - r * A1) := by
    have hpr2 : p / r * r = p := div_mul_cancel₀ p hr0.ne'
    have e3 : 7 * p / (4 * r) = 7 / 4 * (p / r) := by ring
    rw [e3]
    linear_combination A1 * hpr2
  have h1 : (1 - p / r) * (hsE0 x u + (u - 1) / r + r + 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith only [hpr']) hF0.le
  have h2 : p / r * (hsE0 x u + (u - 1) / r + r + 1 / 2 + 9 / 16 - r * A1) < 0 :=
    mul_neg_of_pos_of_neg hp0 hF1'
  linarith only [e2, hlog, h1, h2]

/-- `384uS²F_2` at `a = 0` is positive: convex in `P` with `∂_P ≤ 0` at `P = 3/7`, concave in `u`,
positive quartic endpoints. -/
private theorem hs2_G20 {S u P : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : P ≤ 3 / 7) :
    0 < -64*P^2*S^4*u^2 + 128*P^2*S^4*u - 64*P^2*S^4 + 128*P^2*S^2*u + 128*P^2*S^2 - 64*P^2
        + 144*P*S^4*u^2 - 288*P*S^4*u + 144*P*S^4 - 416*P*S^2*u - 288*P*S^2 + 144*P - 81*S^4*u^2
        + 162*S^4*u - 81*S^4 - 144*S^3*u^2 + 144*S^3*u - 64*S^2*u^2 + 110*S^2*u + 162*S^2
        - 144*S*u - 81 := by
  have hc2 : 0 ≤ -64*(S^2*u - S^2 - 2*S - 1)*(S^2*u - S^2 + 2*S - 1) := by
    have f1 : S^2*u - S^2 - 2*S - 1 ≤ 0 := by nlinarith
    have f2 : 0 ≤ S^2*u - S^2 + 2*S - 1 := by nlinarith
    have := mul_nonneg (neg_nonneg.2 f1) f2
    linarith
  have hd : 16*(39*S^4*u^2 - 78*S^4*u + 39*S^4 - 134*S^2*u - 78*S^2 + 39)/7 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hS) (sub_nonneg.2 hS2),
      mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu')]
  have hg0 : 0 < -1521*S^4/784 + 27*S^3 - 15*S^2/2 - 108*S - 1521/49 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : -1521*(h + 19 / 6)^4/784 + 27*(h + 19 / 6)^3 - 15*(h + 19 / 6)^2/2 - 108*(h
        + 19 / 6) - 1521/49 = -1521*h^4/784 + 951*h^3/392 + 207405*h^2/1568 + 1930181*h/4704
        + 24164423/112896 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hg1 : 0 < -549081*S^4/313600 + 10431*S^3/400 - 90843*S^2/9800 - 549*S/5 - 1521/49 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : -549081*(h + 19 / 6)^4/313600 + 10431*(h + 19 / 6)^3/400 - 90843*(h + 19 / 6)^2/9800
        - 549*(h + 19 / 6)/5 - 1521/49 = -549081*h^4/313600 + 611439*h^3/156800
        + 83493477*h^2/627200 + 740586173*h/1881600 + 1163296073/6451200 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hcu : 0 ≤ S^2*(1521*S^2 + 7056*S + 3136)/49 := by positivity
  have hg : 0 < (1 - 80 * (u - 3 / 4)) * (-1521*S^4/784 + 27*S^3 - 15*S^2/2 - 108*S - 1521/49)
      + 80 * (u - 3 / 4) * (-549081*S^4/313600 + 10431*S^3/400 - 90843*S^2/9800 - 549*S/5
      - 1521/49) +
      S^2*(1521*S^2 + 7056*S + 3136)/49 * ((u - 3 / 4) * (61 / 80 - u)) := by
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 80 * (u - 3 / 4)) hg0.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 80 * (u - 3 / 4)) hg1.le
    have k3 := mul_nonneg hcu (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'))
    rcases le_total u (121 / 160) with h | h
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 80 * (u - 3 / 4)) hg0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 80 * (u - 3 / 4)) hg1; linarith
  have e : -64*P^2*S^4*u^2 + 128*P^2*S^4*u - 64*P^2*S^4 + 128*P^2*S^2*u + 128*P^2*S^2 - 64*P^2
      + 144*P*S^4*u^2 - 288*P*S^4*u + 144*P*S^4 - 416*P*S^2*u - 288*P*S^2 + 144*P - 81*S^4*u^2
      + 162*S^4*u - 81*S^4 - 144*S^3*u^2 + 144*S^3*u - 64*S^2*u^2 + 110*S^2*u + 162*S^2 - 144*S*u
      - 81 = ((1 - 80 * (u - 3 / 4)) * (-1521*S^4/784 + 27*S^3 - 15*S^2/2 - 108*S - 1521/49)
      + 80 * (u - 3 / 4) * (-549081*S^4/313600 + 10431*S^3/400 - 90843*S^2/9800 - 549*S/5
      - 1521/49) +
      S^2*(1521*S^2 + 7056*S + 3136)/49 * ((u - 3 / 4) * (61 / 80 - u))) + (16*(39*S^4*u^2
          - 78*S^4*u + 39*S^4 - 134*S^2*u - 78*S^2 + 39)/7) * (P - 3 / 7) +
      (-64*(S^2*u - S^2 - 2*S - 1)*(S^2*u - S^2 + 2*S - 1)) * (P - 3 / 7) ^ 2 := by ring
  rw [e]
  have := mul_nonneg_of_nonpos_of_nonpos hd (by linarith : P - 3 / 7 ≤ 0)
  have := mul_nonneg hc2 (sq_nonneg (P - 3 / 7))
  linarith

/-- `384uS²F_2` at `a = 1` is positive: convex in `P` with `∂_P ≤ 0` at `P = 3/7`, concave in `u`,
positive quartic endpoints. -/
private theorem hs2_G21 {S u P : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : P ≤ 3 / 7) :
    0 < 256*P^2*S^4*u - 256*P^2*S^4 + 256*P^2*S^3 - 64*P^2*S^2 - 288*P*S^4*u + 288*P*S^4
        - 144*P*S^3*u - 144*P*S^3 - 128*P*S^2*u - 288*P*S^2 + 144*P*S - 81*S^4*u^2 + 162*S^4*u
        - 81*S^4 - 144*S^3*u^2 + 144*S^3*u - 64*S^2*u^2 + 110*S^2*u + 162*S^2 - 144*S*u - 81 := by
  have hc2 : 0 ≤ 64*S^2*(4*S^2*u - 4*S^2 + 4*S - 1) := by
    have f2 : 0 ≤ 4*S^2*u - 4*S^2 + 4*S - 1 := by nlinarith
    positivity
  have hd : -16*S*(30*S^3*u - 30*S^3 + 63*S^2*u - 33*S^2 + 56*S*u + 150*S - 63)/7 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hS) (sub_nonneg.2 hS2),
      mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu')]
  have hg0 : 0 < 11007*S^4/784 - 1665*S^3/49 + 3153*S^2/98 - 324*S/7 - 81 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : 11007*(h + 19 / 6)^4/784 - 1665*(h + 19 / 6)^3/49 + 3153*(h + 19 / 6)^2/98 - 324*(h
        + 19 / 6)/7 - 81 = 11007*h^4/784 + 56391*h^3/392 + 868797*h^2/1568 + 4320821*h/4704
        + 48298295/112896 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hg1 : 0 < 4258071*S^4/313600 - 699201*S^3/19600 + 310197*S^2/9800 - 1683*S/35 - 81 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : 4258071*(h + 19 / 6)^4/313600 - 699201*(h + 19 / 6)^3/19600 + 310197*(h
        + 19 / 6)^2/9800 - 1683*(h + 19 / 6)/35 - 81 = 4258071*h^4/313600 + 854967*h^3/6272
        + 319683381*h^2/627200 + 302510441*h/376320 + 14301349999/45158400 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hcu : 0 ≤ S^2*(9*S + 8)^2 := by positivity
  have hg : 0 < (1 - 80 * (u - 3 / 4)) * (11007*S^4/784 - 1665*S^3/49 + 3153*S^2/98 - 324*S/7
      - 81) + 80 * (u - 3 / 4) * (4258071*S^4/313600 - 699201*S^3/19600 + 310197*S^2/9800
      - 1683*S/35 - 81) +
      S^2*(9*S + 8)^2 * ((u - 3 / 4) * (61 / 80 - u)) := by
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 80 * (u - 3 / 4)) hg0.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 80 * (u - 3 / 4)) hg1.le
    have k3 := mul_nonneg hcu (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'))
    rcases le_total u (121 / 160) with h | h
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 80 * (u - 3 / 4)) hg0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 80 * (u - 3 / 4)) hg1; linarith
  have e : 256*P^2*S^4*u - 256*P^2*S^4 + 256*P^2*S^3 - 64*P^2*S^2 - 288*P*S^4*u + 288*P*S^4
      - 144*P*S^3*u - 144*P*S^3 - 128*P*S^2*u - 288*P*S^2 + 144*P*S - 81*S^4*u^2 + 162*S^4*u
      - 81*S^4 - 144*S^3*u^2 + 144*S^3*u - 64*S^2*u^2 + 110*S^2*u + 162*S^2 - 144*S*u - 81 = ((1
      - 80 * (u - 3 / 4)) * (11007*S^4/784 - 1665*S^3/49 + 3153*S^2/98 - 324*S/7 - 81) + 80 * (u
      - 3 / 4) * (4258071*S^4/313600 - 699201*S^3/19600 + 310197*S^2/9800 - 1683*S/35 - 81) +
      S^2*(9*S + 8)^2 * ((u - 3 / 4) * (61 / 80 - u))) + (-16*S*(30*S^3*u - 30*S^3 + 63*S^2*u
          - 33*S^2 + 56*S*u + 150*S - 63)/7) * (P - 3 / 7) +
      (64*S^2*(4*S^2*u - 4*S^2 + 4*S - 1)) * (P - 3 / 7) ^ 2 := by ring
  rw [e]
  have := mul_nonneg_of_nonpos_of_nonpos hd (by linarith : P - 3 / 7 ≤ 0)
  have := mul_nonneg hc2 (sq_nonneg (P - 3 / 7))
  linarith

/-- `704uS²F_3` at `a = 0` is positive: convex in `P` with `∂_P ≤ 0` at `P = 3/7`, concave in `u`,
positive quartic endpoints. -/
private theorem hs2_G30 {S u P : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : P ≤ 3 / 7) :
    0 < -121*P^2*S^4*u^2 + 242*P^2*S^4*u - 121*P^2*S^4 + 242*P^2*S^2*u + 242*P^2*S^2 - 121*P^2
        + 88*P*S^4*u^2 - 176*P*S^4*u + 88*P*S^4 - 528*P*S^2*u - 176*P*S^2 + 88*P - 16*S^4*u^2
        + 32*S^4*u - 16*S^4 - 128*S^3*u^2 + 128*S^3*u - 256*S^2*u^2 + 364*S^2*u + 32*S^2
        - 128*S*u - 16 := by
  have hc2 : 0 ≤ -121*(S^2*u - S^2 - 2*S - 1)*(S^2*u - S^2 + 2*S - 1) := by
    have f1 : S^2*u - S^2 - 2*S - 1 ≤ 0 := by nlinarith
    have f2 : 0 ≤ S^2*u - S^2 + 2*S - 1 := by nlinarith
    have := mul_nonneg (neg_nonneg.2 f1) f2
    linarith
  have hd : -22*(5*S^4*u^2 - 10*S^4*u + 5*S^4 + 102*S^2*u - 10*S^2 + 5)/7 ≤ 0 := by
    have h1 : 0 ≤ 5 * S ^ 4 * (u - 1) ^ 2 := by positivity
    have h2 : 0 < S ^ 2 * (102 * u - 10) := mul_pos (by positivity) (by linarith)
    have e : 5*S^4*u^2 - 10*S^4*u + 5*S^4 + 102*S^2*u - 10*S^2 + 5 =
        5 * S ^ 4 * (u - 1) ^ 2 + S ^ 2 * (102 * u - 10) + 5 := by ring
    rw [e]; linarith
  have hg0 : 0 < -25*S^4/784 + 24*S^3 - 89*S^2/14 - 96*S - 25/49 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : -25*(h + 19 / 6)^4/784 + 24*(h + 19 / 6)^3 - 89*(h + 19 / 6)^2/14 - 96*(h + 19 / 6)
        - 25/49 = -25*h^4/784 + 27749*h^3/1176 + 1033583*h^2/4704 + 24626333*h/42336
        + 396921719/1016064 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hg1 : 0 < -361*S^4/12544 + 1159*S^3/50 - 87417*S^2/9800 - 488*S/5 - 25/49 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : -361*(h + 19 / 6)^4/12544 + 1159*(h + 19 / 6)^3/50 - 87417*(h + 19 / 6)^2/9800
        - 488*(h + 19 / 6)/5 - 25/49 = -361*h^4/12544 + 10732397*h^3/470400
        + 394305047*h^2/1881600 + 9137501813*h/16934400 + 19401176729/58060800 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hcu : 0 ≤ S^2*(25*S^2 + 6272*S + 12544)/49 := by positivity
  have hg : 0 < (1 - 80 * (u - 3 / 4)) * (-25*S^4/784 + 24*S^3 - 89*S^2/14 - 96*S - 25/49)
      + 80 * (u - 3 / 4) * (-361*S^4/12544 + 1159*S^3/50 - 87417*S^2/9800 - 488*S/5 - 25/49) +
      S^2*(25*S^2 + 6272*S + 12544)/49 * ((u - 3 / 4) * (61 / 80 - u)) := by
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 80 * (u - 3 / 4)) hg0.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 80 * (u - 3 / 4)) hg1.le
    have k3 := mul_nonneg hcu (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'))
    rcases le_total u (121 / 160) with h | h
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 80 * (u - 3 / 4)) hg0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 80 * (u - 3 / 4)) hg1; linarith
  have e : -121*P^2*S^4*u^2 + 242*P^2*S^4*u - 121*P^2*S^4 + 242*P^2*S^2*u + 242*P^2*S^2 - 121*P^2
      + 88*P*S^4*u^2 - 176*P*S^4*u + 88*P*S^4 - 528*P*S^2*u - 176*P*S^2 + 88*P - 16*S^4*u^2
      + 32*S^4*u - 16*S^4 - 128*S^3*u^2 + 128*S^3*u - 256*S^2*u^2 + 364*S^2*u + 32*S^2 - 128*S*u
      - 16 = ((1 - 80 * (u - 3 / 4)) * (-25*S^4/784 + 24*S^3 - 89*S^2/14 - 96*S - 25/49)
      + 80 * (u - 3 / 4) * (-361*S^4/12544 + 1159*S^3/50 - 87417*S^2/9800 - 488*S/5 - 25/49) +
      S^2*(25*S^2 + 6272*S + 12544)/49 * ((u - 3 / 4) * (61 / 80 - u))) + (-22*(5*S^4*u^2
          - 10*S^4*u + 5*S^4 + 102*S^2*u - 10*S^2 + 5)/7) * (P - 3 / 7) +
      (-121*(S^2*u - S^2 - 2*S - 1)*(S^2*u - S^2 + 2*S - 1)) * (P - 3 / 7) ^ 2 := by ring
  rw [e]
  have := mul_nonneg_of_nonpos_of_nonpos hd (by linarith : P - 3 / 7 ≤ 0)
  have := mul_nonneg hc2 (sq_nonneg (P - 3 / 7))
  linarith

/-- `704uS²F_3` at `a = 1` is positive: convex in `P` with `∂_P ≤ 0` at `P = 3/7`, concave in `u`,
positive quartic endpoints. -/
private theorem hs2_G31 {S u P : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : P ≤ 3 / 7) :
    0 < 484*P^2*S^4*u - 484*P^2*S^4 + 484*P^2*S^3 - 121*P^2*S^2 - 176*P*S^4*u + 176*P*S^4
        - 88*P*S^3*u - 88*P*S^3 - 352*P*S^2*u - 176*P*S^2 + 88*P*S - 16*S^4*u^2 + 32*S^4*u
        - 16*S^4 - 128*S^3*u^2 + 128*S^3*u - 256*S^2*u^2 + 364*S^2*u + 32*S^2 - 128*S*u - 16 := by
  have hc2 : 0 ≤ 121*S^2*(4*S^2*u - 4*S^2 + 4*S - 1) := by
    have f2 : 0 ≤ 4*S^2*u - 4*S^2 + 4*S - 1 := by nlinarith
    positivity
  have hd : 22*S*(76*S^3*u - 76*S^3 - 28*S^2*u + 104*S^2 - 112*S*u - 89*S + 28)/7 ≤ 0 := by
    have hS0 : 0 < S := by linarith
    have h1 := mul_le_mul_of_nonneg_left (by linarith : u - 1 ≤ -19 / 80)
      (by positivity : (0 : ℝ) ≤ S ^ 3)
    have h2 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ S ^ 2)
    have h3 := mul_le_mul_of_nonneg_left hu hS0.le
    have h4 : -(1444 / 80) * S ^ 3 + 83 * S ^ 2 - 173 * S + 28 < 0 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hS) (sub_nonneg.2 hS), sq_nonneg (S - 3)]
    have : 76*S^3*u - 76*S^3 - 28*S^2*u + 104*S^2 - 112*S*u - 89*S + 28 < 0 := by
      nlinarith
    have : 22 * S * (76*S^3*u - 76*S^3 - 28*S^2*u + 104*S^2 - 112*S*u - 89*S + 28) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this.le
    linarith
  have hg0 : 0 < -214*S^4/49 + 2298*S^3/49 - 2440*S^2/49 - 408*S/7 - 16 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : -214*(h + 19 / 6)^4/49 + 2298*(h + 19 / 6)^3/49 - 2440*(h + 19 / 6)^2/49 - 408*(h
        + 19 / 6)/7 - 16 = -214*h^4/49 - 1238*h^3/147 + 19546*h^2/147 + 1276571*h/2646
        + 11117935/31752 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hg1 : 0 < -80389*S^4/19600 + 55868*S^3/1225 - 254661*S^2/4900 - 2096*S/35 - 16 := by
    obtain ⟨h, rfl⟩ : ∃ h, S = h + 19 / 6 := ⟨S - 19 / 6, by ring⟩
    have hh : 0 ≤ h := by linarith
    have hh' : h ≤ 7 / 30 := by linarith
    have e : -80389*(h + 19 / 6)^4/19600 + 55868*(h + 19 / 6)^3/1225 - 254661*(h + 19 / 6)^2/4900
        - 2096*(h + 19 / 6)/35 - 16 = -80389*h^4/19600 - 186559*h^3/29400 + 15819323*h^2/117600
        + 488973617*h/1058400 + 7848857819/25401600 := by ring
    rw [e]
    nlinarith [mul_nonneg hh (sub_nonneg.2 hh'), mul_nonneg (mul_nonneg hh hh) (sub_nonneg.2 hh'),
      mul_nonneg (mul_nonneg (mul_nonneg hh hh) hh) (sub_nonneg.2 hh')]
  have hcu : 0 ≤ 16*S^2*(S + 4)^2 := by positivity
  have hg : 0 < (1 - 80 * (u - 3 / 4)) * (-214*S^4/49 + 2298*S^3/49 - 2440*S^2/49 - 408*S/7 - 16)
      + 80 * (u - 3 / 4) * (-80389*S^4/19600 + 55868*S^3/1225 - 254661*S^2/4900 - 2096*S/35 - 16) +
      16*S^2*(S + 4)^2 * ((u - 3 / 4) * (61 / 80 - u)) := by
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 80 * (u - 3 / 4)) hg0.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 80 * (u - 3 / 4)) hg1.le
    have k3 := mul_nonneg hcu (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'))
    rcases le_total u (121 / 160) with h | h
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 80 * (u - 3 / 4)) hg0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 80 * (u - 3 / 4)) hg1; linarith
  have e : 484*P^2*S^4*u - 484*P^2*S^4 + 484*P^2*S^3 - 121*P^2*S^2 - 176*P*S^4*u + 176*P*S^4
      - 88*P*S^3*u - 88*P*S^3 - 352*P*S^2*u - 176*P*S^2 + 88*P*S - 16*S^4*u^2 + 32*S^4*u - 16*S^4
      - 128*S^3*u^2 + 128*S^3*u - 256*S^2*u^2 + 364*S^2*u + 32*S^2 - 128*S*u - 16 = ((1 - 80 * (u
      - 3 / 4)) * (-214*S^4/49 + 2298*S^3/49 - 2440*S^2/49 - 408*S/7 - 16) + 80 * (u
      - 3 / 4) * (-80389*S^4/19600 + 55868*S^3/1225 - 254661*S^2/4900 - 2096*S/35 - 16) +
      16*S^2*(S + 4)^2 * ((u - 3 / 4) * (61 / 80 - u))) + (22*S*(76*S^3*u - 76*S^3 - 28*S^2*u
          + 104*S^2 - 112*S*u - 89*S + 28)/7) * (P - 3 / 7) +
      (121*S^2*(4*S^2*u - 4*S^2 + 4*S - 1)) * (P - 3 / 7) ^ 2 := by ring
  rw [e]
  have := mul_nonneg_of_nonpos_of_nonpos hd (by linarith : P - 3 / 7 ≤ 0)
  have := mul_nonneg hc2 (sq_nonneg (P - 3 / 7))
  linarith

/-- `F_2 > 0` (concave in `a`). -/
private theorem hs2_F2 {S u P a H : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : P ≤ 3 / 7) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hH : H = S * (1 - u) - 1 / S) :
    0 < 17 / 24 - P / 3 - 3 * (P * (2 * (1 - a) + S * a)) / 4 + P * ((1 - a) * H + (2 * S
        - 1) * a) / 3 + 2 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 3 - (9 * H
        - 8 * u - 8 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (384 * u) := by
  have hS0 : 0 < S := by linarith
  have hu0 : 0 < u := by linarith
  have h0 := hs2_G20 hS hS2 hu hu' hP
  have h1 := hs2_G21 hS hS2 hu hu' hP
  have e : 384 * u * S ^ 2 * (17 / 24 - P / 3 - 3 * (P * (2 * (1 - a) + S * a)) / 4 + P * ((1
      - a) * H + (2 * S - 1) * a) / 3 + 2 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a)
      + (S * a) ^ 2) / 3 - (9 * H - 8 * u - 8 * (P * ((1 - a) * H + (2 * S
      - 1) * a))) ^ 2 / (384 * u)) = (1 - a) * (-64*P^2*S^4*u^2 + 128*P^2*S^4*u - 64*P^2*S^4
      + 128*P^2*S^2*u + 128*P^2*S^2 - 64*P^2 + 144*P*S^4*u^2 - 288*P*S^4*u + 144*P*S^4
      - 416*P*S^2*u - 288*P*S^2 + 144*P - 81*S^4*u^2 + 162*S^4*u - 81*S^4 - 144*S^3*u^2
      + 144*S^3*u - 64*S^2*u^2 + 110*S^2*u + 162*S^2 - 144*S*u - 81) + a * (256*P^2*S^4*u
      - 256*P^2*S^4 + 256*P^2*S^3 - 64*P^2*S^2 - 288*P*S^4*u + 288*P*S^4 - 144*P*S^3*u
      - 144*P*S^3 - 128*P*S^2*u - 288*P*S^2 + 144*P*S - 81*S^4*u^2 + 162*S^4*u - 81*S^4
      - 144*S^3*u^2 + 144*S^3*u - 64*S^2*u^2 + 110*S^2*u + 162*S^2 - 144*S*u - 81)
      + 64 * P ^ 2 * (S ^ 2 * u - S ^ 2 + S - 1) ^ 2 * (a * (1 - a)) := by
    rw [hH]; field_simp; ring
  have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) h0.le
  have k2 := mul_nonneg ha0 h1.le
  have k3 : 0 ≤ 64 * P ^ 2 * (S ^ 2 * u - S ^ 2 + S - 1) ^ 2 * (a * (1 - a)) :=
    mul_nonneg (by positivity) (mul_nonneg ha0 (by linarith))
  have hpos : 0 < 384 * u * S ^ 2 * (17 / 24 - P / 3 - 3 * (P * (2 * (1 - a) + S * a)) / 4
      + P * ((1 - a) * H + (2 * S - 1) * a) / 3 + 2 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a)
      + (S * a) ^ 2) / 3 - (9 * H - 8 * u - 8 * (P * ((1 - a) * H + (2 * S
      - 1) * a))) ^ 2 / (384 * u)) := by
    rw [e]
    rcases le_total a (1 / 2) with h | h
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - a) h0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < a) h1; linarith
  exact pos_of_mul_pos_right hpos (by positivity)

/-- `F_3 > 0` (concave in `a`). -/
private theorem hs2_F3 {S u P a H : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : P ≤ 3 / 7) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hH : H = S * (1 - u) - 1 / S) :
    0 < 9 / 16 - P / 2 - P * (2 * (1 - a) + S * a) / 4 + P * ((1 - a) * H + (2 * S - 1) * a) / 2
        + 11 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 16 - (4 * H - 16 * u
        - 11 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (704 * u) := by
  have hS0 : 0 < S := by linarith
  have hu0 : 0 < u := by linarith
  have h0 := hs2_G30 hS hS2 hu hu' hP
  have h1 := hs2_G31 hS hS2 hu hu' hP
  have e : 704 * u * S ^ 2 * (9 / 16 - P / 2 - P * (2 * (1 - a) + S * a) / 4 + P * ((1 - a) * H
      + (2 * S - 1) * a) / 2 + 11 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 16
      - (4 * H - 16 * u - 11 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (704 * u)) = (1
      - a) * (-121*P^2*S^4*u^2 + 242*P^2*S^4*u - 121*P^2*S^4 + 242*P^2*S^2*u + 242*P^2*S^2
      - 121*P^2 + 88*P*S^4*u^2 - 176*P*S^4*u + 88*P*S^4 - 528*P*S^2*u - 176*P*S^2 + 88*P
      - 16*S^4*u^2 + 32*S^4*u - 16*S^4 - 128*S^3*u^2 + 128*S^3*u - 256*S^2*u^2 + 364*S^2*u
      + 32*S^2 - 128*S*u - 16) + a * (484*P^2*S^4*u - 484*P^2*S^4 + 484*P^2*S^3 - 121*P^2*S^2
      - 176*P*S^4*u + 176*P*S^4 - 88*P*S^3*u - 88*P*S^3 - 352*P*S^2*u - 176*P*S^2 + 88*P*S
      - 16*S^4*u^2 + 32*S^4*u - 16*S^4 - 128*S^3*u^2 + 128*S^3*u - 256*S^2*u^2 + 364*S^2*u
      + 32*S^2 - 128*S*u - 16) + 121 * P ^ 2 * (S ^ 2 * u - S ^ 2 + S - 1) ^ 2 * (a * (1 - a)) := by
    rw [hH]; field_simp; ring
  have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) h0.le
  have k2 := mul_nonneg ha0 h1.le
  have k3 : 0 ≤ 121 * P ^ 2 * (S ^ 2 * u - S ^ 2 + S - 1) ^ 2 * (a * (1 - a)) :=
    mul_nonneg (by positivity) (mul_nonneg ha0 (by linarith))
  have hpos : 0 < 704 * u * S ^ 2 * (9 / 16 - P / 2 - P * (2 * (1 - a) + S * a) / 4 + P * ((1
      - a) * H + (2 * S - 1) * a) / 2 + 11 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a)
      + (S * a) ^ 2) / 16 - (4 * H - 16 * u - 11 * (P * ((1 - a) * H + (2 * S
      - 1) * a))) ^ 2 / (704 * u)) := by
    rw [e]
    rcases le_total a (1 / 2) with h | h
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - a) h0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < a) h1; linarith
  exact pos_of_mul_pos_right hpos (by positivity)

/-- **The Bernstein coefficients**: with `P = r_A`, `a = α⁻²`, `Δ = D/α² ≥ 0`, `H = -E₀`,
`Y = 2q/P ∈ (0, 1]`, the `τ = 2` slope `qG₂'(q) = Σ C(3, i)B_iY^i(1 - Y)^{3-i}` is positive
(`B₀ = 1`, `B₁, B₂, B₃ > 0`). -/
private theorem hs2_qG {S u P a Δ H q : ℝ} (hS : 19 / 6 ≤ S) (hS2 : S ≤ 17 / 5) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 61 / 80) (hP : 5 / 17 ≤ P) (hP' : P ≤ 3 / 7) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hΔ : 0 ≤ Δ) (hBv : P * (2 * (1 - a) + S * a) ≤ 9 / 8) (hH : H = S * (1 - u) - 1 / S)
    (hq : 0 < q) (hq2 : 2 * q ≤ P) :
    0 < 1 - q * (4 * (2 * (1 - a) + S * a + Δ * -H) + 1 +
      (2 * Δ * u + (1 - a) * -H - (2 * S - 1) * a) + 7 / (8 * P)) +
      q ^ 2 * (8 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
        Δ * (1 - a) * -H - Δ * (2 * S - 1) * a) + 7 * (2 * (1 - a) + S * a + Δ * -H) / P) -
      21 * q ^ 3 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
        Δ * (1 - a) * -H - Δ * (2 * S - 1) * a) / (2 * P) := by
  have hS0 : 0 < S := by linarith
  have hP0 : 0 < P := by linarith
  have hu0 : 0 < u := by linarith
  have hS1 : 1 / S ≤ 6 / 19 := by rw [div_le_iff₀ hS0]; linarith
  have hHu : u ≤ 2 * H := by rw [hH]; nlinarith
  have hH0 : 0 ≤ H := by linarith
  set A1 := 2 * (1 - a) + S * a + Δ * -H with hA1
  set A2 := (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u + Δ * (1 - a) * -H -
    Δ * (2 * S - 1) * a with hA2
  set A3 := 2 * Δ * u + (1 - a) * -H - (2 * S - 1) * a with hA3
  set J := P * ((1 - a) * H + (2 * S - 1) * a) with hJ
  have hJ0 : 0 ≤ J := by
    have : 0 ≤ (1 - a) * H := mul_nonneg (by linarith) hH0
    have : 0 ≤ (2 * S - 1) * a := mul_nonneg (by linarith) ha0
    exact mul_nonneg hP0.le (by linarith)
  -- `B₁ > 0`
  have hB1 : 0 < 41 / 48 - P * (1 + A3 + 4 * A1) / 6 := by
    have e : 41 / 48 - P * (1 + A3 + 4 * A1) / 6 = 41 / 48 - P / 6 + J / 6 -
        2 * (P * (2 * (1 - a) + S * a)) / 3 + (P * Δ) * (2 * H - u) / 3 := by
      rw [hA1, hA3, hJ]; ring
    rw [e]
    have : 0 ≤ (P * Δ) * (2 * H - u) := mul_nonneg (mul_nonneg hP0.le hΔ) (by linarith)
    linarith
  -- `B₂ > 0`
  have hB2 : 0 < 17 / 24 - P * (1 + A3) / 3 - 3 * P * A1 / 4 + 2 * P ^ 2 * A2 / 3 := by
    have hF := hs2_F2 hS hS2 hu hu' hP' ha0 ha1 hH
    have e : 384 * u * ((17 / 24 - P * (1 + A3) / 3 - 3 * P * A1 / 4 + 2 * P ^ 2 * A2 / 3) -
        (17 / 24 - P / 3 - 3 * (P * (2 * (1 - a) + S * a)) / 4 +
          P * ((1 - a) * H + (2 * S - 1) * a) / 3 +
          2 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 3 -
          (9 * H - 8 * u - 8 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (384 * u))) =
        (16 * u * (P * Δ) + (9 * H - 8 * u - 8 * J)) ^ 2 := by
      rw [hA1, hA2, hA3, hJ]; field_simp; ring
    have : 0 ≤ 384 * u * ((17 / 24 - P * (1 + A3) / 3 - 3 * P * A1 / 4 + 2 * P ^ 2 * A2 / 3) -
        (17 / 24 - P / 3 - 3 * (P * (2 * (1 - a) + S * a)) / 4 +
          P * ((1 - a) * H + (2 * S - 1) * a) / 3 +
          2 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 3 -
          (9 * H - 8 * u - 8 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (384 * u))) := by
      rw [e]; positivity
    have := nonneg_of_mul_nonneg_right this (by positivity)
    linarith
  -- `B₃ > 0`
  have hB3 : 0 < 9 / 16 - P * (1 + A3) / 2 - P * A1 / 4 + 11 * P ^ 2 * A2 / 16 := by
    have hF := hs2_F3 hS hS2 hu hu' hP' ha0 ha1 hH
    have e : 704 * u * ((9 / 16 - P * (1 + A3) / 2 - P * A1 / 4 + 11 * P ^ 2 * A2 / 16) -
        (9 / 16 - P / 2 - P * (2 * (1 - a) + S * a) / 4 +
          P * ((1 - a) * H + (2 * S - 1) * a) / 2 +
          11 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 16 -
          (4 * H - 16 * u - 11 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (704 * u))) =
        (22 * u * (P * Δ) + (4 * H - 16 * u - 11 * J)) ^ 2 := by
      rw [hA1, hA2, hA3, hJ]; field_simp; ring
    have : 0 ≤ 704 * u * ((9 / 16 - P * (1 + A3) / 2 - P * A1 / 4 + 11 * P ^ 2 * A2 / 16) -
        (9 / 16 - P / 2 - P * (2 * (1 - a) + S * a) / 4 +
          P * ((1 - a) * H + (2 * S - 1) * a) / 2 +
          11 * P ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) / 16 -
          (4 * H - 16 * u - 11 * (P * ((1 - a) * H + (2 * S - 1) * a))) ^ 2 / (704 * u))) := by
      rw [e]; positivity
    have := nonneg_of_mul_nonneg_right this (by positivity)
    linarith
  -- the Bernstein form in `Y = 2q/P`
  set Y := 2 * q / P with hY
  have hY0 : 0 < Y := by positivity
  have hY1 : Y ≤ 1 := by rw [hY, div_le_one hP0]; exact hq2
  have e : 1 - q * (4 * A1 + 1 + A3 + 7 / (8 * P)) + q ^ 2 * (8 * A2 + 7 * A1 / P) -
      21 * q ^ 3 * A2 / (2 * P) = (1 - Y) ^ 3 + 3 * (41 / 48 - P * (1 + A3 + 4 * A1) / 6) * Y *
      (1 - Y) ^ 2 + 3 * (17 / 24 - P * (1 + A3) / 3 - 3 * P * A1 / 4 + 2 * P ^ 2 * A2 / 3) *
      Y ^ 2 * (1 - Y) + (9 / 16 - P * (1 + A3) / 2 - P * A1 / 4
          + 11 * P ^ 2 * A2 / 16) * Y ^ 3 := by
    rw [hY]; field_simp; ring
  rw [e]
  have hY1' : 0 ≤ 1 - Y := by linarith
  have k1 : 0 ≤ 3 * (41 / 48 - P * (1 + A3 + 4 * A1) / 6) * Y * (1 - Y) ^ 2 := by positivity
  have k2 : 0 ≤ 3 * (17 / 24 - P * (1 + A3) / 3 - 3 * P * A1 / 4 + 2 * P ^ 2 * A2 / 3) * Y ^ 2 *
      (1 - Y) := by positivity
  have k3 : 0 ≤ (9 / 16 - P * (1 + A3) / 2 - P * A1 / 4 + 11 * P ^ 2 * A2 / 16) * Y ^ 3 := by
    positivity
  rcases le_total Y (1 / 2) with h | h
  · have : 0 < (1 - Y) ^ 3 := by have : 0 < 1 - Y := by linarith
                                 positivity
    linarith
  · have : 0 < (9 / 16 - P * (1 + A3) / 2 - P * A1 / 4 + 11 * P ^ 2 * A2 / 16) * Y ^ 3 := by
      positivity
    have : 0 ≤ (1 - Y) ^ 3 := by positivity
    linarith

/-- `B_v = r_A(2ε + S/α²) ≤ 9/8`. -/
private theorem hs2_Bv {x al be : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be) :
    hsRA al be * (2 * (1 - 1 / al ^ 2) + (1 + x) * (1 / al ^ 2)) ≤ 9 / 8 := by
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have e : hsRA al be * (2 * (1 - 1 / al ^ 2) + (1 + x) * (1 / al ^ 2)) =
      (2 * al ^ 2 + x - 1) / (al * (al + be)) := by
    unfold hsRA; field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have key : (x - 1) * (-7 * al ^ 2 + 9 * al * x - 8 * x + 8) = (x - al) * (x + 1) +
      (al - 1) * (2 * (x - 2) ^ 2) + 7 * (x - 1) * (al - 1) * (x - al) := by ring
  have h1 : 0 ≤ (x - 1) * (-7 * al ^ 2 + 9 * al * x - 8 * x + 8) := by
    rw [key]
    have := mul_nonneg (sub_nonneg.2 hax) (by linarith : (0 : ℝ) ≤ x + 1)
    have := mul_nonneg (sub_nonneg.2 hal) (by positivity : (0 : ℝ) ≤ 2 * (x - 2) ^ 2)
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 7 * (x - 1)) (sub_nonneg.2 hal))
      (sub_nonneg.2 hax)
    linarith
  have h2 : 0 ≤ -7 * al ^ 2 + 9 * al * x - 8 * x + 8 :=
    nonneg_of_mul_nonneg_right h1 (by linarith)
  have h3 : al * (al + x) ≤ al * (al + be) := mul_le_mul_of_nonneg_left (by linarith) hal0.le
  nlinarith

/-- **The `τ = 2` continuation**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ x ≤ β`, `D ≥ 0`,
`5/17 ≤ r_A ≤ 3/7`, `3/4 ≤ u ≤ 61/80`, `G₂(q) = R*_2(q) + (2 - 7q/(2r_A))(w_*(q) - 3/4)` is strictly
increasing on `(0, 1/7]`.
Each `F_i` at `α⁻² ∈ {0, 1}` is convex in `P = r_A` with `∂_P ≤ 0` at `P = 3/7`. -/
theorem hs2_tau2_mono {x be al u q₁ q₂ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hD : 0 ≤ hsDg x be al) (hrA : 5 / 17 ≤ hsRA al be)
    (hrA' : hsRA al be ≤ 3 / 7) (hu : 3 / 4 ≤ u) (hu' : u ≤ 61 / 80) (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hq₂ : q₂ ≤ 1 / 7) :
    hsF x be al u q₁ 2 (log (2 * q₁ / hsRA al be)) (2 - 7 * q₁ / (2 * hsRA al be)) <
      hsF x be al u q₂ 2 (log (2 * q₂ / hsRA al be)) (2 - 7 * q₂ / (2 * hsRA al be)) := by
  have hal0 : 0 < al := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hr0 : 0 < hsRA al be := by linarith
  have hBv := hs2_Bv (by linarith) hal hax hxb
  -- the slope `qG₂'(q) > 0` on `(0, 1/7]`
  have hslope : ∀ z, 0 < z → z ≤ 1 / 7 → 0 < 1 - z * (4 * hsA1 x be al u + 1 + hsA3 x be al u +
      7 / (8 * hsRA al be)) + z ^ 2 * (8 * hsA2 x be al u + 7 * hsA1 x be al u / hsRA al be) -
      21 * z ^ 3 * hsA2 x be al u / (2 * hsRA al be) := by
    intro z hz hz7
    have h := hs2_qG (S := 1 + x) (u := u) (P := hsRA al be) (a := 1 / al ^ 2)
      (Δ := hsDg x be al / al ^ 2) (H := -hsE0 x u) (q := z) (by linarith) (by linarith) hu hu'
      hrA hrA' (by positivity) (by rw [div_le_one ha2]; exact one_le_pow₀ hal)
      (div_nonneg hD ha2.le) hBv (by unfold hsE0; ring) hz (by linarith)
    have e1 : hsA1 x be al u = 2 * (1 - 1 / al ^ 2) + (1 + x) * (1 / al ^ 2) +
        hsDg x be al / al ^ 2 * - -hsE0 x u := by unfold hsA1; ring
    have e2 : hsA2 x be al u = (1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * ((1 + x) * (1 / al ^ 2)) +
        ((1 + x) * (1 / al ^ 2)) ^ 2 + (hsDg x be al / al ^ 2) ^ 2 * u +
        hsDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * - -hsE0 x u -
        hsDg x be al / al ^ 2 * (2 * (1 + x) - 1) * (1 / al ^ 2) := by unfold hsA2; ring
    have e3 : hsA3 x be al u = 2 * (hsDg x be al / al ^ 2) * u + (1 - 1 / al ^ 2) * - -hsE0 x u -
        (2 * (1 + x) - 1) * (1 / al ^ 2) := by unfold hsA3; ring
    rw [e1, e2, e3]
    exact h
  -- `G₂` as an explicit function of `q`
  set r := hsRA al be with hr
  set A1 := hsA1 x be al u
  set A2 := hsA2 x be al u
  set A3 := hsA3 x be al u
  set c0 := 2 + (u - 1) / r + r + hsE0 x u
  set c1 := -4 * A1 - 1 - A3 - 7 / (8 * r) with hc1
  set c2 := 4 * A2 + 7 * A1 / (2 * r) with hc2
  set c3 := -(7 * A2 / (2 * r)) with hc3
  have hfeq : ∀ q, hsF x be al u q 2 (log (2 * q / r)) (2 - 7 * q / (2 * r)) =
      c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3 + log (2 * q / r) := by
    intro q
    unfold hsF hsWs hsELs
    ring
  rw [hfeq, hfeq]
  apply ss_lt_of_deriv (f' := fun z => c1 + 2 * c2 * z + 3 * c3 * z ^ 2 + 1 / z) hq
  · intro z hz
    have hz0 : 0 < z := by linarith [hz.1]
    have hp : HasDerivAt (fun q => c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3)
        (c1 + 2 * c2 * z + 3 * c3 * z ^ 2) z := by
      have := (((hasDerivAt_const z c0).add ((hasDerivAt_id z).const_mul c1)).add
        ((hasDerivAt_pow 2 z).const_mul c2)).add ((hasDerivAt_pow 3 z).const_mul c3)
      convert this using 1
      · funext q; simp
      · simp; ring
    have hl : HasDerivAt (fun q => log (2 * q / r)) (1 / z) z := by
      have h1 : HasDerivAt (fun q : ℝ => 2 * q / r) (2 / r) z := by
        simpa using ((hasDerivAt_id z).const_mul 2).div_const r
      have := h1.log (by positivity)
      convert this using 1
      field_simp
    exact hp.add hl
  · intro z hz
    have hz0 : 0 < z := by linarith [hz.1]
    have hz7 : z ≤ 1 / 7 := by linarith [hz.2]
    have h := hslope z hz0 hz7
    have e : c1 + 2 * c2 * z + 3 * c3 * z ^ 2 + 1 / z = (1 - z * (4 * A1 + 1 + A3 + 7 / (8 * r)) +
        z ^ 2 * (8 * A2 + 7 * A1 / r) - 21 * z ^ 3 * A2 / (2 * r)) / z := by
      rw [hc1, hc2, hc3]; field_simp; ring
    show 0 < c1 + 2 * c2 * z + 3 * c3 * z ^ 2 + 1 / z
    rw [e]
    exact div_pos h hz0

/-- The Gauss ceiling at `β = x`: `V(x) - 3/4 < 17(x - 1)²/(240S²)` for `x ≥ 13/6` (from
`V < V_G`, `hs_V_lt_VG`, and the sign of a cubic in `x`). -/
private theorem hs2_V_lt_17 {x : ℝ} (hx : 13 / 6 ≤ x) :
    m2Sec 1 x x - 3 / 4 < 17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have h := hs_V_lt_VG (by linarith : 1 < x)
  have hc : 0 ≤ 87 * x ^ 3 - 119 * x ^ 2 - 143 * x - 5 := by
    obtain ⟨X, rfl⟩ : ∃ X, x = X + 13 / 6 := ⟨x - 13 / 6, by ring⟩
    have hX : 0 ≤ X := by linarith
    have e : 87 * (X + 13 / 6) ^ 3 - 119 * (X + 13 / 6) ^ 2 - 143 * (X + 13 / 6) - 5 =
        87 * X ^ 3 + 893 / 2 * X ^ 2 + 6799 / 12 * X + 823 / 72 := by ring
    rw [e]; positivity
  have e : 17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2) - (hsVG x - 3 / 4) =
      (x - 1) ^ 2 * (87 * x ^ 3 - 119 * x ^ 2 - 143 * x - 5) /
        (480 * x * (x + 1) ^ 2 * (13 * x ^ 2 + 14 * x + 3)) := by
    unfold hsVG; field_simp; ring
  have : 0 ≤ 17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2) - (hsVG x - 3 / 4) := by
    rw [e]; positivity
  linarith

/-- The split incoming bound (additivity of the secant integral at `x`) with an abstract bound on
`V - 3/4` and a bound `κ` on `(β - x)²/(48x²)`:
`(β - 1)(Sec(1, x, β) - 3/4) ≤ (x - 1)·c + (β - x)·κ`. -/
private theorem hs2_sec_split {x be c κ : ℝ} (hx : 1 < x) (hxb : x ≤ be)
    (hV : m2Sec 1 x x - 3 / 4 ≤ c) (hκ : (be - x) ^ 2 / (48 * x ^ 2) ≤ κ) :
    (be - 1) * (m2Sec 1 x be - 3 / 4) ≤ (x - 1) * c + (be - x) * κ := by
  have hx0 : 0 < x := by linarith
  have hbe0 : 0 < be := by linarith
  have hadd := ss_sec_add (A := 1) (B := x) (M := x) (P := be) one_pos hx0 hx0 hbe0
  have ht := hs_sec_tail_le hx0 hxb
  have h1 := mul_le_mul_of_nonneg_left hV (by linarith : (0 : ℝ) ≤ x - 1)
  have h2 := mul_le_mul_of_nonneg_left (ht.trans (by linarith : 3 / 4 + (be - x) ^ 2 / (48 * x ^ 2)
    ≤ 3 / 4 + κ)) (by linarith : (0 : ℝ) ≤ be - x)
  nlinarith

/-- **The central ceiling**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α`, `6α² ≤ x(x + 2)`,
`x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`: `Sec(1, x, β) ≤ u_C(x, β)`. -/
theorem hs2_central_ceiling {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    m2Sec 1 x be ≤ hsUC x be := by
  have hx0 : 0 < x := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  -- `α ≤ (5x + 4)/12`
  have hal' : al ≤ (5 * x + 4) / 12 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul'' hc hc (by positivity) (by positivity), sq_nonneg (x - 4)]
  -- `β - x ≤ 3x/25`
  have hb3 : be - x ≤ 3 * x / 25 := by
    have h1 : x * (7 * x + 1) * (al - 1) ≤ x * (7 * x + 1) * ((5 * x - 8) / 12) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : x * (7 * x + 1) * ((5 * x - 8) / 12) ≤ 3 * x / 25 * (4 * x ^ 2 + 11 * x + 1) := by
      nlinarith [mul_nonneg hx0.le (by nlinarith : (0 : ℝ) ≤ -731 * x ^ 2 + 1671 * x + 236)]
    have h3 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ 3 * x / 25 := by
      rw [div_le_iff₀ hR]; linarith
    linarith
  have hb0 : 0 ≤ be - x := by linarith
  have hκ : (be - x) ^ 2 / (48 * x ^ 2) ≤ 1 / 3200 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hb3 hb3 hb0 (by positivity)]
  have hsplit := hs2_sec_split (by linarith) hxb (hs2_V_lt_17 hx).le hκ
  have hb1 : 0 < be - 1 := by linarith
  have e : hsUC x be = 3 / 4 + ((x - 1) * (17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2)) +
      (be - x) * (1 / 3200)) / (be - 1) := by
    unfold hsUC; field_simp; ring
  rw [e, ← sub_le_iff_le_add', le_div_iff₀ hb1, mul_comm]
  exact hsplit

/-- **The outer ceiling**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ 3/2`,
`x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`: `Sec(1, x, β) ≤ u_s(x, β)`. -/
theorem hs2_outer_ceiling {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 3 / 2) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    m2Sec 1 x be ≤ hsUs x be := by
  have hx0 : 0 < x := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  -- `β - x ≤ x/5`
  have hb3 : be - x ≤ x / 5 := by
    have h1 : x * (7 * x + 1) * (al - 1) ≤ x * (7 * x + 1) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : x * (7 * x + 1) * (1 / 2) ≤ x / 5 * (4 * x ^ 2 + 11 * x + 1) := by
      nlinarith [mul_nonneg hx0.le (by nlinarith : (0 : ℝ) ≤ 8 * x ^ 2 - 13 * x - 3)]
    have h3 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ x / 5 := by
      rw [div_le_iff₀ hR]; linarith
    linarith
  have hb0 : 0 ≤ be - x := by linarith
  have hκ : (be - x) ^ 2 / (48 * x ^ 2) ≤ 1 / 1200 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hb3 hb3 hb0 (by positivity)]
  have hsplit := hs2_sec_split (by linarith) hxb (hs2_V_lt_17 hx).le hκ
  have hb1 : 0 < be - 1 := by linarith
  have e : hsUs x be = 3 / 4 + ((x - 1) * (17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2)) +
      (be - x) * (1 / 1200)) / (be - 1) := by
    unfold hsUs; field_simp
  rw [e, ← sub_le_iff_le_add', le_div_iff₀ hb1, mul_comm]
  exact hsplit

/-! ### Face signs -/

/-- **The central sharp-ratio face**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α`, `6α² ≤ x(x + 2)`, the strip
`x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `q = q_c`, `u = u_C(x, β)` and
`2 ≤ τ ≤ T = r_A/q_c`: `G_τ = R*_τ + (2 - 7τ/(4T))(w_* - 3/4) < 0`. Proved in `Heavy/S2HandCentral`.
-/
theorem hs2_central_sign {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ * hsQc x al ≤ hsRA al be) :
    hsF x be al (hsUC x be) (hsQc x al) τ (log (τ * hsQc x al / hsRA al be))
      (2 - 7 * τ * hsQc x al / (4 * hsRA al be)) < 0 := by
  apply hs2_central_sign_proof <;> assumption

/-- **The outer sharp-ratio face, small `α`**: for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ 3/2`, `α ≤ x`,
`x(x + 2) ≤ 6α²`, the strip of `hs2_central_sign`, `q = 1/7`, `u = u_s(x, β)` and `2 ≤ τ ≤ 7r_A`:
`G_τ < 0`. Proved in `Heavy/S2HandSmall`. -/
theorem hs2_outer_sign_small {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 3 / 2) (hax : al ≤ x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsUs x be) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  apply hs2_outer_sign_small_proof <;> assumption

/-- **The outer sharp-ratio face, large `α`**: for `13/6 ≤ x ≤ 12/5`, `3/2 ≤ α ≤ x`, the strip of
`hs2_central_sign`, `q = 1/7`, `u = V̄(x)` and `2 ≤ τ ≤ 7r_A`: `G_τ < 0`. Proved in
`Heavy/S2HandLarge`. -/
theorem hs2_outer_sign_large {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hal : 3 / 2 ≤ al) (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsVbar x) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  apply hs2_outer_sign_large_proof <;> assumption

/-! ### Gate S2 -/

/-- `r_A < 3/7` from the lower edge `β ≥ x(9x + 8α)/(9x + 8)` of the strip. -/
private theorem hs2_rA_lt {x al be : ℝ} (hx : 13 / 6 ≤ x) (hal0 : 0 < al) (hax : al < x)
    (hb0 : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) : hsRA al be < 3 / 7 := by
  have hx0 : 0 < x := by linarith
  have h1 : x * (9 * x + 8 * al) ≤ be * (9 * x + 8) := by
    rwa [div_le_iff₀ (by positivity)] at hb0
  have hbe0 : 0 < be := by nlinarith
  unfold hsRA
  rw [div_lt_iff₀ (by linarith)]
  by_contra hc
  push Not at hc
  have h2 := mul_le_mul_of_nonneg_right (show 3 * be ≤ 4 * al by linarith)
    (by linarith : (0 : ℝ) ≤ 9 * x + 8)
  have h3 := mul_lt_mul_of_pos_right hax (by linarith : (0 : ℝ) < 12 * x + 32)
  have h4 : 32 * x ≤ 15 * x ^ 2 := by nlinarith
  nlinarith

/-- `r_A ≥ 1/S ≥ 5/17` from `β ≤ αx`. -/
private theorem hs2_rA_ge {x al be : ℝ} (hx2 : x ≤ 12 / 5) (hal0 : 0 < al) (hbe0 : 0 < be)
    (hbx : be ≤ al * x) : 5 / 17 ≤ hsRA al be := by
  unfold hsRA
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- `V̄(x) < 61/80` on `[13/6, 12/5]`. -/
private theorem hs2_Vbar_lt {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) : hsVbar x < 61 / 80 := by
  unfold hsVbar
  have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) < 1 / 80 := by
    rw [div_lt_iff₀ (by nlinarith)]; nlinarith
  linarith

namespace HsData

variable (H : HsData)

/-- **The variable-floor reduction**: for `13/6 ≤ x < 12/5`, the actual root gives a nonnegative
variable-floor value on the face `q* = min{q_c, 1/7}` at some `τ* ∈ [2, r_A/q*]`. -/
private theorem hs2_face (h0 : H.x < 12 / 5) (hx : 13 / 6 ≤ H.x) :
    ∃ τs, 2 ≤ τs ∧ τs * min (hsQc H.x H.al) (1 / 7) ≤ hsRA H.al H.be ∧
      0 ≤ hsF H.x H.be H.al H.u (min (hsQc H.x H.al) (1 / 7)) τs
        (log (τs * min (hsQc H.x H.al) (1 / 7) / hsRA H.al H.be))
        (2 - 7 * τs * min (hsQc H.x H.al) (1 / 7) / (4 * hsRA H.al H.be)) := by
  have hx1 := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hal := H.one_le_al
  have hax := H.al_lt_x
  have hxb := H.x_le_be
  have hal0 : 0 < H.al := by linarith
  have hbe0 : 0 < H.be := by linarith
  have hbx := H.be_le_al_x
  -- shape: `D > 0`, `D < Q`, `5/17 ≤ r_A < 3/7`
  have hD := (hs02_D_pos hx1 h0.le hal hax.le hbx).2
  have hD0 : 0 < hsDg H.x H.be H.al := by linarith
  have hs98 := H.hs02_strip_98 (by linarith)
  have hb0 : H.x * (9 * H.x + 8 * H.al) / (9 * H.x + 8) ≤ H.be := by
    have e : H.x * (9 * H.x + 8 * H.al) / (9 * H.x + 8) =
        H.x + 8 * H.x * (H.al - 1) / (9 * H.x + 8) := by field_simp; ring
    rw [e]; exact hs98
  have hDQ := (hs_D_lt_Q (by linarith) hal hax.le hb0).1
  have hrA := hs2_rA_lt hx hal0 hax hb0
  have hrA5 := hs2_rA_ge h0.le hal0 hbe0 hbx
  -- incoming norm
  have hu34 := H.u_ge_34
  have huV : H.u ≤ hsVbar H.x := H.u_le_V.trans (hs_V_le_Vbar hx1)
  have hVb := hs2_Vbar_lt hx h0.le
  have hu61 : H.u ≤ 61 / 80 := by linarith
  -- scale
  have hq0 := H.hs02_q_pos
  have hq7 := H.q_lt_seventh
  have hqc := H.q_le_qc
  have hτ2 := H.two_lt_τ
  have hτT : H.τ * H.q < hsRA H.al H.be := H.τ_lt
  have h2q := H.hs02_two_q
  have hr0 := H.hs02_rA_pos
  have hm0 : 1 / 4 ≤ 2 - 7 * (H.τ * H.q) / (4 * hsRA H.al H.be) := by
    have : 7 * (H.τ * H.q) / (4 * hsRA H.al H.be) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  -- the comparison chain with the variable floor `m = 2 - 7τq/(4r_A)`
  have hB : ∀ s ∈ Icc (H.rho * (1 + H.x)) H.t, 0 < 1 +
      (H.τ + (2 - 7 * (H.τ * H.q) / (4 * hsRA H.al H.be))) *
      (hsLam H.al H.rho * s - hsLam H.al H.rho * H.rho * hsDg H.x H.be H.al) := by
    intro s hs
    have hτT' : H.τ * hsQ H.al H.rho < hsRA H.al H.be := H.τ_lt
    have h2q' : 2 * hsQ H.al H.rho < hsRA H.al H.be := h2q
    have hq0' : 0 < hsQ H.al H.rho := hq0
    refine hs_B_pos_weighted (by linarith) hal hax.le hxb H.rho_pos hs.1 (by linarith) h2q'.le ?_
    -- `r_A + q/2 - zq = (r_A - τq)(1 - 7q/(4r_A)) + q/4`
    have e : hsRA H.al H.be + hsQ H.al H.rho / 2 - (H.τ + (2 - 7 * (H.τ * H.q) /
        (4 * hsRA H.al H.be))) * hsQ H.al H.rho = (hsRA H.al H.be - H.τ * hsQ H.al H.rho) *
        (1 - 7 * hsQ H.al H.rho / (4 * hsRA H.al H.be)) + hsQ H.al H.rho / 4 := by
      unfold q; field_simp; ring
    have h7 : 0 ≤ 1 - 7 * hsQ H.al H.rho / (4 * hsRA H.al H.be) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ hsRA H.al H.be - H.τ * hsQ H.al H.rho) h7
    linarith
  have hphi := H.hs02_root_phi (by linarith) hB
  set p := H.τ * H.q with hp
  have hp0 : 0 < p := by positivity
  have hpr : p ≤ hsRA H.al H.be := hτT.le
  have hq2 : H.q ≤ p / 2 := by
    have := mul_le_mul_of_nonneg_right hτ2.le hq0.le
    rw [hp]; linarith
  have hqc0 : 0 < hsQc H.x H.al := by unfold hsQc; positivity
  set qh := min (hsQc H.x H.al) (1 / 7) with hqh
  have hqh0 : 0 < qh := lt_min hqc0 (by norm_num)
  have hqh7 : qh ≤ 1 / 7 := min_le_right _ _
  -- convexity and the zero-scale end
  have hA2 := hs_A2_pos (be := H.be) (by linarith) h0.le hal hu34 (by linarith)
  have halt := hs_phi_convex_max (p := p) (m := 2 - 7 * p / (4 * hsRA H.al H.be))
    (qm := min qh (p / 2)) (by linarith) hA2.le hq0.le
    (le_min (le_min hqc hq7.le) hq2)
  have hz := hs2_zero_neg hx h0.le hal hax.le hxb hbx hrA hDQ hu34 hu61 H.u_le_rA hp0 hpr
  have hm : 0 ≤ hsPhi H.x H.be H.al H.u p (2 - 7 * p / (4 * hsRA H.al H.be)) (min qh (p / 2)) := by
    rcases le_total (hsPhi H.x H.be H.al H.u p (2 - 7 * p / (4 * hsRA H.al H.be)) 0)
      (hsPhi H.x H.be H.al H.u p (2 - 7 * p / (4 * hsRA H.al H.be)) (min qh (p / 2))) with h | h
    · rw [max_eq_right h] at halt; linarith
    · rw [max_eq_left h] at halt; linarith
  -- a nonnegative value on the face `q = q̂`
  rcases le_total qh (p / 2) with h | h
  · rw [min_eq_left h] at hm
    refine ⟨p / qh, by rw [le_div_iff₀ hqh0]; linarith, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ hqh0.ne']; exact hpr
    · have e : 7 * (p / qh) * qh = 7 * p := by field_simp
      rw [div_mul_cancel₀ _ hqh0.ne', e, hs_phi_eq hp0 hqh0]; exact hm
  · rw [min_eq_right h] at hm
    refine ⟨2, le_refl _, by linarith, ?_⟩
    rw [← hs_phi_eq hp0 (by positivity : (0 : ℝ) < p / 2)] at hm
    have e1 : p / (p / 2) = 2 := by field_simp
    have e2 : p / hsRA H.al H.be = 2 * (p / 2) / hsRA H.al H.be := by ring
    have e3 : 7 * p / (4 * hsRA H.al H.be) = 7 * (p / 2) / (2 * hsRA H.al H.be) := by ring
    rw [e1, e2, e3] at hm
    have e4 : 7 * 2 * qh / (4 * hsRA H.al H.be) = 7 * qh / (2 * hsRA H.al H.be) := by ring
    rw [e4]
    rcases eq_or_lt_of_le h with h' | h'
    · rw [← h']; exact hm
    · exact (hm.trans (hs2_tau2_mono hx h0.le hal hax.le hxb hD0.le hrA5 hrA.le hu34 hu61
        (by positivity) h' hqh7).le)

/-- **The sharp-ratio exclusion**: `13/6 ≤ x < 12/5` is impossible. -/
private theorem hs2_sharp (h0 : H.x < 12 / 5) (hx : 13 / 6 ≤ H.x) : False := by
  have hx1 := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hal := H.one_le_al
  have hax := H.al_lt_x
  have hxb := H.x_le_be
  have hab : H.al < H.be := by linarith
  have hal0 : 0 < H.al := by linarith
  have hbx := H.be_le_al_x
  have hD := (hs02_D_pos hx1 h0.le hal hax.le hbx).2
  have hD0 : 0 < hsDg H.x H.be H.al := by linarith
  have hs98 := H.hs02_strip_98 (by linarith)
  have hsup := H.hs02_strip_up
  have hb0 : H.x * (9 * H.x + 8 * H.al) / (9 * H.x + 8) ≤ H.be := by
    have e : H.x * (9 * H.x + 8 * H.al) / (9 * H.x + 8) =
        H.x + 8 * H.x * (H.al - 1) / (9 * H.x + 8) := by field_simp; ring
    rw [e]; exact hs98
  obtain ⟨hDQ, hD3⟩ := hs_D_lt_Q (by linarith) hal hax.le hb0
  have huV : H.u ≤ hsVbar H.x := H.u_le_V.trans (hs_V_le_Vbar hx1)
  have hqc0 : 0 < hsQc H.x H.al := by unfold hsQc; positivity
  obtain ⟨τs, hτs, hτsT, h1⟩ := H.hs2_face h0 hx
  rcases le_or_gt (hsQc H.x H.al) (1 / 7) with hc | hc
  · -- the central face `q = q_c ≤ 1/7`
    rw [min_eq_left hc] at hτsT h1
    have h6 := (hs_qc_le_iff hx0).1 hc
    have huc : H.u ≤ hsUC H.x H.be := by
      rw [H.u_eq]; exact hs2_central_ceiling hx h0.le hal h6 hxb hsup
    have h2 := h1.trans (hs2_uslope hx h0.le hal hax.le hxb hab hD0 hDQ hD3 hqc0 hc hτs hτsT huc)
    have := hs2_central_sign hx h0.le hal h6 hs98 hsup hτs hτsT
    linarith
  · -- the outer face `q = 1/7 < q_c`
    rw [min_eq_right hc.le] at hτsT h1
    have h6 : H.x * (H.x + 2) ≤ 6 * H.al ^ 2 := by
      by_contra h'
      push Not at h'
      exact absurd ((hs_qc_le_iff hx0).2 h'.le) (not_le.2 hc)
    have hτ7 : τs ≤ 7 * hsRA H.al H.be := by linarith
    rcases le_total H.al (3 / 2) with ha | ha
    · have huc : H.u ≤ hsUs H.x H.be := by
        rw [H.u_eq]; exact hs2_outer_ceiling hx h0.le hal ha hxb hsup
      have h2 := h1.trans (hs2_uslope hx h0.le hal hax.le hxb hab hD0 hDQ hD3 (by norm_num)
        (le_refl _) hτs hτsT huc)
      have := hs2_outer_sign_small hx h0.le hal ha hax.le h6 hs98 hsup hτs hτ7
      linarith
    · have h2 := h1.trans (hs2_uslope hx h0.le hal hax.le hxb hab hD0 hDQ hD3 (by norm_num)
        (le_refl _) hτs hτsT huV)
      have := hs2_outer_sign_large hx h0.le ha hax.le hs98 hsup hτs hτ7
      linarith

/-- **Gate S2**: given S0's `x < 12/5`, `x < 13/6`.
Proof: if `x ≥ 13/6`: `root_zero`, `w_ge`, `hs_env_weighted` with `m = 2 - 7τq/(4r_A)`
(`hs_B_pos_weighted`) give `0 ≤ G*_τ`; `hs_phi_eq`, `hs_A2_pos` (with `u_le_V`, `hs_V_le_Vbar`),
`hs_phi_convex_max`, `hs2_zero_neg` (`hs_D_lt_Q`, `upper_order_98`, `be_le_al_x`, `u_le_rA`) and
`hs2_tau2_mono` reach `G*(q*, τ*) ≥ 0` at `q* = min{q_c, 1/7}`; `hs2_uslope` with
`hs2_central_ceiling` or `hs2_outer_ceiling` / `hs_V_le_Vbar` replaces `u`; the strip is
`strong_order`, `upper_order_98`; contradiction with `hs2_central_sign`, `hs2_outer_sign_small`,
`hs2_outer_sign_large`. Here `D > 0` comes from `D ≥ αD₀` (`hs02_D_pos`) and `r_A < 3/7` from the
`9/8` strip. -/
theorem s2 (h0 : H.x < 12 / 5) : H.x < 13 / 6 := by
  by_contra h
  push Not at h
  exact H.hs2_sharp h0 h

end HsData

/-- **Gate S2 for the actual window**: given `C/a < 12/5`, `C/a < 13/6`. -/
theorem M2Short.hs_S2 (D : M2Short) (h0 : D.C / D.a < 12 / 5) : D.C / D.a < 13 / 6 := by
  have h := D.toHs.s2 (by rwa [D.toHs_x])
  rwa [D.toHs_x] at h

end SmoothedOctagon

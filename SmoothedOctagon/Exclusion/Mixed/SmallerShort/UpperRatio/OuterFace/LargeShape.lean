module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecip

/-!
# S2 hand signs: the outer face for large `α`

`hs2_outer_sign_large_proof` proves the statement of `hs2_outer_sign_large`: with the incoming
norm `u_v = V̄(x)` fixed, both outer tests are convex in `r = 1/α` (`S2HandRecip`), so on
`1/x ≤ r ≤ 2/3` they are bounded by their values at two terminal shapes: the middle shape
`α = 3/2` (`log y ≤ y - 1` and the two bivariate polynomials `P₀`, `P₁`) and the upper shape
`α = x` (`D = S²`, `log y ≤ (y - 1) - (y - 1)²/2`, convexity in `Z` between `c = 5/8` and
`c = 7/8`, and four univariate polynomials with positive coefficients).

## Main API

* `hl2_Vbar_le`: `3/4 ≤ V̄(x) < 4/5`.
* `hl2_mid_H0`, `hl2_mid_H1`: both tests are negative at `α = 3/2`, norm `u_v`.
* `hl2_up_H0`, `hl2_up_H1`: both tests are negative at `α = x`, norm `u_v`.
* `hs2_outer_sign_large_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `3/4 ≤ u_v < 4/5`: `u_v - 3/4 = 2(x - 1)²/((x + 1)(35x + 13)) < 1/20`. -/
theorem hl2_Vbar_le {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) :
    3 / 4 ≤ hsVbar x ∧ hsVbar x < 4 / 5 := by
  unfold hsVbar
  have hd : 0 < (x + 1) * (35 * x + 13) := by positivity
  constructor
  · have : 0 ≤ 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) := by positivity
    linarith
  · have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) < 1 / 20 := by
      rw [div_lt_iff₀ hd]; nlinarith
    linarith

/-- **Chord bound for `A + BZ + CZ² + g/Z`**: if `CZZ₅Z₇ + g ≥ 0` the function lies below its
chord, so negativity at `Z₅` and `Z₇` gives negativity in between. -/
theorem hl2_chord {A B C g Z Z5 Z7 : ℝ} (h5 : 0 < Z5) (h57 : Z5 ≤ Z) (h7 : Z ≤ Z7)
    (hg : 0 ≤ C * (Z * Z5 * Z7) + g) (hf5 : A + B * Z5 + C * Z5 ^ 2 + g / Z5 < 0)
    (hf7 : A + B * Z7 + C * Z7 ^ 2 + g / Z7 < 0) : A + B * Z + C * Z ^ 2 + g / Z < 0 := by
  have hZ : 0 < Z := by linarith
  have hZ7 : 0 < Z7 := by linarith
  rcases eq_or_lt_of_le (h57.trans h7) with h | h
  · have e1 : Z5 = Z := le_antisymm h57 (h ▸ h7)
    rw [← e1]; exact hf5
  · have key : (Z7 - Z5) * (A + B * Z + C * Z ^ 2 + g / Z) - (Z7 - Z) *
        (A + B * Z5 + C * Z5 ^ 2 + g / Z5) - (Z - Z5) * (A + B * Z7 + C * Z7 ^ 2 + g / Z7) =
        (Z - Z5) * (Z - Z7) * (Z7 - Z5) * ((C * (Z * Z5 * Z7) + g) / (Z * Z5 * Z7)) := by
      field_simp; ring
    have h1 : (Z - Z5) * (Z - Z7) * (Z7 - Z5) * ((C * (Z * Z5 * Z7) + g) / (Z * Z5 * Z7)) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith)
          (by linarith)) (by linarith)
      · positivity
    have h2 : (Z7 - Z) * (A + B * Z5 + C * Z5 ^ 2 + g / Z5) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hf5.le
    have h3 : (Z - Z5) * (A + B * Z7 + C * Z7 ^ 2 + g / Z7) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hf7.le
    by_contra hc
    push Not at hc
    have : 0 ≤ (Z7 - Z5) * (A + B * Z + C * Z ^ 2 + g / Z) := mul_nonneg (by linarith) hc
    rcases eq_or_lt_of_le h57 with h' | h'
    · rw [← h'] at hc; linarith
    · have h3' : (Z - Z5) * (A + B * Z7 + C * Z7 ^ 2 + g / Z7) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hf7
      linarith

/-! ### The middle shape `α = 3/2` -/

/-- `P₀ = -47628S(35x + 13)(c + 2x + 3)J₀`, `h = x - 2`, `t = c - 5/8`, where `J₀` is the first
test at `α = 3/2` with `log y` raised to `y - 1`. -/
noncomputable def hl2P0 (h t : ℝ) : ℝ :=
  (29622272) * h ^ 8 +
      (59244544*t + 115212288) * h ^ 7 +
      (44433408*t^2 + 263651328*t - 1504835584) * h ^ 6 +
      (14811136*t^3 + 222658560*t^2 - 1498626048*t - 11746991104) * h ^ 5 +
      (1851392*t^4 + 82526208*t^3 - 280657408*t^2 - 11527271936*t - 30345562348) * h ^ 4 +
      (11354112*t^4 + 90894336*t^3 - 3195671552*t^2 - 25752693184*t - 27186736708) * h ^ 3 +
      (22335488*t^4 - 154900480*t^3 - 6179157120*t^2 - 22281431136*t + 14420692653) * h ^ 2 +
      (14745600*t^4 - 278351872*t^3 - 4590814720*t^2 - 1399708608*t + 35831008232) * h +
      (3092480*t^4 - 93784064*t^3 - 1136097152*t^2 + 8441036000*t + 5522142723)

/-- `P₁ = -31752S(35x + 13)(c + 2x + 3)J₁`, `J₁` the second test likewise. -/
noncomputable def hl2P1 (h t : ℝ) : ℝ :=
  (-1851392) * h ^ 7 +
      (-2777088*t - 100117504) * h ^ 6 +
      (-1388544*t^2 - 105794560*t - 848275648) * h ^ 5 +
      (-231424*t^3 - 30706432*t^2 - 767762016*t - 2631801700) * h ^ 4 +
      (-1419264*t^3 - 177395968*t^2 - 2110288736*t - 2736950236) * h ^ 3 +
      (-2791936*t^3 - 430245056*t^2 - 2276207224*t + 1436109239) * h ^ 2 +
      (-1843200*t^3 - 448134656*t^2 - 247508736*t + 3486400264) * h +
      (-386560*t^3 - 154005312*t^2 + 887736184*t + 261744249)

theorem hl2_P0_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < hl2P0 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) ht ht'
  unfold hl2P0
  linarith [mul_nonneg (tp 1) (hp 7), mul_nonneg (tp 2) (hp 6), mul_nonneg (tp 1) (hp 6), mul_nonneg (tp 3) (hp 5), mul_nonneg (tp 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tp 4) (hp 4), mul_nonneg (tp 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tp 4) (hp 3), mul_nonneg (tp 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tq 3, tq 2, tp 1, hl 8, hl 7, hu 6, hu 5, hu 4, hu 3, hl 2, hl 1]

theorem hl2_P1_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < hl2P1 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) ht ht'
  unfold hl2P1
  linarith [mul_nonneg (tq 1) (hp 6), mul_nonneg (tq 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tq 3, tq 2, tp 1, hu 7, hu 6, hu 5, hu 4, hu 3, hl 2, hl 1]

/-- `H₀ < 0` at `α = 3/2`, norm `u_v`: `log y ≤ y - 1` and `P₀ > 0`. -/
theorem hl2_mid_H0 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : hl2H0 x c (hsVbar x) (2 / 3) < 0 := by
  have hZ : 0 < hl2Zr x c (2 / 3) := by unfold hl2Zr; nlinarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 2 * hl2Zr x c (2 / 3) / 7 by positivity)
  have hS : 0 < 1 + x := by linarith
  have hB : 0 < c + 2 * x + 3 := by linarith
  have key : -47628 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) * (6 / 7 +
      (hsVbar x - 1) * hl2Zr x c (2 / 3) + 1 / hl2Zr x c (2 / 3) - hl2ELr x c (hsVbar x) (2 / 3) +
      (4 - hl2Zr x c (2 / 3) / 2) * (hl2Wr x c (hsVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * hl2Zr x c (2 / 3) / 7 - 1)) = hl2P0 (x - 2) (c - 5 / 8) / 2048 := by
    have eZ : hl2Zr x c (2 / 3) = (c + 2 * x + 3) / 3 := by unfold hl2Zr; ring
    have hB' := hB.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    rw [eZ]
    unfold hsVbar hl2ELr hl2Wr hl2Dr hl2d1 hl2d2 hl2J2 hsE0 hl2P0
    field_simp
    ring
  have hP := hl2_P0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hd : 0 < 47628 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) := by positivity
  have hJ : 6 / 7 + (hsVbar x - 1) * hl2Zr x c (2 / 3) + 1 / hl2Zr x c (2 / 3) -
      hl2ELr x c (hsVbar x) (2 / 3) +
      (4 - hl2Zr x c (2 / 3) / 2) * (hl2Wr x c (hsVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * hl2Zr x c (2 / 3) / 7 - 1) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hd.le h]
  unfold hl2H0 hl2Ht
  linarith

/-- `H₁ < 0` at `α = 3/2`, norm `u_v`: `log y ≤ y - 1` and `P₁ > 0`. -/
theorem hl2_mid_H1 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : hl2H1 x c (hsVbar x) (2 / 3) < 0 := by
  have hZ : 0 < hl2Zr x c (2 / 3) := by unfold hl2Zr; nlinarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 2 * hl2Zr x c (2 / 3) / 7 by positivity)
  have hS : 0 < 1 + x := by linarith
  have hB : 0 < c + 2 * x + 3 := by linarith
  have key : -31752 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) * (6 / 7 +
      (hsVbar x - 1) * hl2Zr x c (2 / 3) + 1 / hl2Zr x c (2 / 3) - hl2ELr x c (hsVbar x) (2 / 3) +
      (7 / hl2Zr x c (2 / 3) + 1 / 4) * (hl2Wr x c (hsVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * hl2Zr x c (2 / 3) / 7 - 1)) = hl2P1 (x - 2) (c - 5 / 8) / 256 := by
    have eZ : hl2Zr x c (2 / 3) = (c + 2 * x + 3) / 3 := by unfold hl2Zr; ring
    have hB' := hB.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    rw [eZ]
    unfold hsVbar hl2ELr hl2Wr hl2Dr hl2d1 hl2d2 hl2J2 hsE0 hl2P1
    field_simp
    ring
  have hP := hl2_P1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hd : 0 < 31752 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) := by positivity
  have hJ : 6 / 7 + (hsVbar x - 1) * hl2Zr x c (2 / 3) + 1 / hl2Zr x c (2 / 3) -
      hl2ELr x c (hsVbar x) (2 / 3) +
      (7 / hl2Zr x c (2 / 3) + 1 / 4) * (hl2Wr x c (hsVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * hl2Zr x c (2 / 3) / 7 - 1) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hd.le h]
  unfold hl2H1 hl2Ht
  linarith

/-! ### The upper shape `α = x` -/

/-- At `r = 1/x`, `D_r = S²/x²` does not depend on `c`. -/
theorem hl2_Dr_edge {x : ℝ} (c c' : ℝ) (hx : x ≠ 0) : hl2Dr x c (1 / x) = hl2Dr x c' (1 / x) := by
  unfold hl2Dr hl2d1 hl2d2
  field_simp
  ring

/-- `h = w - 3/4` at the upper shape (independent of `c`). -/
noncomputable def hl2Wb (x u : ℝ) : ℝ := hl2Wr x (5 / 8) u (1 / x) / 49 - 3 / 4

/-- `E_L` at the upper shape (independent of `c`). -/
noncomputable def hl2Eb (x u : ℝ) : ℝ := hl2ELr x (5 / 8) u (1 / x)

/-- `K₀` at the upper shape as a function of `Z`, with `q(2Z/7) = 4Z/7 - 2Z²/49 - 3/2` in place
of the logarithm (`log y ≤ (y - 1) - (y - 1)²/2` at `y = 2Z/7`). -/
noncomputable def hl2K0 (x u Z : ℝ) : ℝ :=
  (6 / 7 - hl2Eb x u + 4 * hl2Wb x u - 3 / 2) + (u - 1 - hl2Wb x u / 2 + 4 / 7) * Z +
    (-(2 / 49)) * Z ^ 2 + 1 / Z

/-- `K₁` at the upper shape as a function of `Z`. -/
noncomputable def hl2K1 (x u Z : ℝ) : ℝ :=
  (6 / 7 - hl2Eb x u + hl2Wb x u / 4 - 3 / 2) + (u - 1 + 4 / 7) * Z + (-(2 / 49)) * Z ^ 2 +
    (1 + 7 * hl2Wb x u) / Z

theorem hl2_Wb_eq {x c u : ℝ} (hx : x ≠ 0) : hl2Wr x c u (1 / x) / 49 - 3 / 4 = hl2Wb x u := by
  unfold hl2Wb hl2Wr; rw [hl2_Dr_edge c (5 / 8) hx]

theorem hl2_Eb_eq {x c u : ℝ} (hx : x ≠ 0) : hl2ELr x c u (1 / x) = hl2Eb x u := by
  unfold hl2Eb hl2ELr; rw [hl2_Dr_edge c (5 / 8) hx]

/-- `w > 3/4` at the upper shape for `u ≤ 4/5`. -/
theorem hl2_Wb_pos {x u : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) (hu : u ≤ 4 / 5) :
    0 ≤ hl2Wb x u := by
  have hx0 : 0 < x := by linarith
  have e : 49 * x ^ 3 * (hl2Wb x u + 3 / 4) = 6 * x ^ 4 + 54 * x ^ 3 + 5 * x ^ 2 + 5 * x - 1 -
      u * (6 * x ^ 4 + 17 * x ^ 3 + 15 * x ^ 2 + 3 * x - 1) := by
    unfold hl2Wb hl2Wr hl2Dr hl2d1 hl2d2 hsE0
    field_simp
    ring
  have hk : 0 ≤ 6 * x ^ 4 + 17 * x ^ 3 + 15 * x ^ 2 + 3 * x - 1 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hu hk
  have h2 : 0 ≤ 49 * x ^ 3 * hl2Wb x u := by nlinarith
  exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 49 * x ^ 3)

/-- `Q_{0,5}`: `K0` at `c = 5/8` is negative (its cleared form is a polynomial in `x - 2` with
positive coefficients). -/
theorem hl2_up_K0_5 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    hl2K0 x (hsVbar x) ((21 * x - 5) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -3136 * x ^ 4 * (1 + x) * (21 * x - 5) * (35 * x + 13) * hl2K0 x (hsVbar x) ((21 * x - 5) / (8 * x)) =
      234738 * (x - 2) ^ 8 + 3667214 * (x - 2) ^ 7 + 24648615 * (x - 2) ^ 6 +
        92851363 * (x - 2) ^ 5 + 213716967 * (x - 2) ^ 4 + 306333042 * (x - 2) ^ 3 +
        264962511 * (x - 2) ^ 2 + 124682189 * (x - 2) + 23749793 := by
    have h1 : 21 * x - 5 ≠ 0 := by linarith
    have h1' : x * 21 - 5 ≠ 0 := by linarith
    have h1'' : -5 + x * 21 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold hl2K0 hl2Wb hl2Eb hsVbar hl2ELr hl2Wr hl2Dr hl2d1 hl2d2 hl2J2 hsE0
    field_simp
    ring
  have hP : 0 < 234738 * (x - 2) ^ 8 + 3667214 * (x - 2) ^ 7 + 24648615 * (x - 2) ^ 6 +
        92851363 * (x - 2) ^ 5 + 213716967 * (x - 2) ^ 4 + 306333042 * (x - 2) ^ 3 +
        264962511 * (x - 2) ^ 2 + 124682189 * (x - 2) + 23749793 := by
    have : 0 ≤ x - 2 := by linarith
    positivity
  have hd : 0 < 3136 * x ^ 4 * (1 + x) * (21 * x - 5) * (35 * x + 13) := by
    have : 0 < 21 * x - 5 := by linarith
    positivity
  by_contra h
  push Not at h
  linarith [mul_nonneg hd.le h]

/-- `Q_{0,7}`: `K0` at `c = 7/8` is negative. -/
theorem hl2_up_K0_7 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    hl2K0 x (hsVbar x) ((23 * x - 7) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -3136 * x ^ 4 * (1 + x) * (23 * x - 7) * (35 * x + 13) * hl2K0 x (hsVbar x) ((23 * x - 7) / (8 * x)) =
      264546 * (x - 2) ^ 8 + 4135722 * (x - 2) ^ 7 + 27918195 * (x - 2) ^ 6 +
        105942595 * (x - 2) ^ 5 + 246387335 * (x - 2) ^ 4 + 358167934 * (x - 2) ^ 3 +
        315902859 * (x - 2) ^ 2 + 152970501 * (x - 2) + 30522633 := by
    have h1 : 23 * x - 7 ≠ 0 := by linarith
    have h1' : x * 23 - 7 ≠ 0 := by linarith
    have h1'' : -7 + x * 23 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold hl2K0 hl2Wb hl2Eb hsVbar hl2ELr hl2Wr hl2Dr hl2d1 hl2d2 hl2J2 hsE0
    field_simp
    ring
  have hP : 0 < 264546 * (x - 2) ^ 8 + 4135722 * (x - 2) ^ 7 + 27918195 * (x - 2) ^ 6 +
        105942595 * (x - 2) ^ 5 + 246387335 * (x - 2) ^ 4 + 358167934 * (x - 2) ^ 3 +
        315902859 * (x - 2) ^ 2 + 152970501 * (x - 2) + 30522633 := by
    have : 0 ≤ x - 2 := by linarith
    positivity
  have hd : 0 < 3136 * x ^ 4 * (1 + x) * (23 * x - 7) * (35 * x + 13) := by
    have : 0 < 23 * x - 7 := by linarith
    positivity
  by_contra h
  push Not at h
  linarith [mul_nonneg hd.le h]

/-- `Q_{1,5}`: `K1` at `c = 5/8` is negative. -/
theorem hl2_up_K1_5 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    hl2K1 x (hsVbar x) ((21 * x - 5) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -1568 * x ^ 3 * (1 + x) * (21 * x - 5) * (35 * x + 13) * hl2K1 x (hsVbar x) ((21 * x - 5) / (8 * x)) =
      111132 * (x - 2) ^ 7 + 1470458 * (x - 2) ^ 6 + 8061427 * (x - 2) ^ 5 +
        23480036 * (x - 2) ^ 4 + 38542410 * (x - 2) ^ 3 + 34349390 * (x - 2) ^ 2 +
        13879207 * (x - 2) + 1100756 := by
    have h1 : 21 * x - 5 ≠ 0 := by linarith
    have h1' : x * 21 - 5 ≠ 0 := by linarith
    have h1'' : -5 + x * 21 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold hl2K1 hl2Wb hl2Eb hsVbar hl2ELr hl2Wr hl2Dr hl2d1 hl2d2 hl2J2 hsE0
    field_simp
    ring
  have hP : 0 < 111132 * (x - 2) ^ 7 + 1470458 * (x - 2) ^ 6 + 8061427 * (x - 2) ^ 5 +
        23480036 * (x - 2) ^ 4 + 38542410 * (x - 2) ^ 3 + 34349390 * (x - 2) ^ 2 +
        13879207 * (x - 2) + 1100756 := by
    have : 0 ≤ x - 2 := by linarith
    positivity
  have hd : 0 < 1568 * x ^ 3 * (1 + x) * (21 * x - 5) * (35 * x + 13) := by
    have : 0 < 21 * x - 5 := by linarith
    positivity
  by_contra h
  push Not at h
  linarith [mul_nonneg hd.le h]

/-- `Q_{1,7}`: `K1` at `c = 7/8` is negative. -/
theorem hl2_up_K1_7 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    hl2K1 x (hsVbar x) ((23 * x - 7) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -1568 * x ^ 3 * (1 + x) * (23 * x - 7) * (35 * x + 13) * hl2K1 x (hsVbar x) ((23 * x - 7) / (8 * x)) =
      128628 * (x - 2) ^ 7 + 1724592 * (x - 2) ^ 6 + 9663133 * (x - 2) ^ 5 +
        29057180 * (x - 2) ^ 4 + 50024402 * (x - 2) ^ 3 + 48266480 * (x - 2) ^ 2 +
        23049277 * (x - 2) + 3623652 := by
    have h1 : 23 * x - 7 ≠ 0 := by linarith
    have h1' : x * 23 - 7 ≠ 0 := by linarith
    have h1'' : -7 + x * 23 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold hl2K1 hl2Wb hl2Eb hsVbar hl2ELr hl2Wr hl2Dr hl2d1 hl2d2 hl2J2 hsE0
    field_simp
    ring
  have hP : 0 < 128628 * (x - 2) ^ 7 + 1724592 * (x - 2) ^ 6 + 9663133 * (x - 2) ^ 5 +
        29057180 * (x - 2) ^ 4 + 50024402 * (x - 2) ^ 3 + 48266480 * (x - 2) ^ 2 +
        23049277 * (x - 2) + 3623652 := by
    have : 0 ≤ x - 2 := by linarith
    positivity
  have hd : 0 < 1568 * x ^ 3 * (1 + x) * (23 * x - 7) * (35 * x + 13) := by
    have : 0 < 23 * x - 7 := by linarith
    positivity
  by_contra h
  push Not at h
  linarith [mul_nonneg hd.le h]

/-- `Z` at `r = 1/x` lies between its values at `c = 5/8` and `c = 7/8`. -/
theorem hl2_up_Zc {x c : ℝ} (hx : 13 / 6 ≤ x) (hc : 5 / 8 ≤ c) (hc2 : c ≤ 7 / 8) :
    (21 * x - 5) / (8 * x) ≤ hl2Zr x c (1 / x) ∧ hl2Zr x c (1 / x) ≤ (23 * x - 7) / (8 * x) := by
  have hx0 : 0 < x := by linarith
  have e : hl2Zr x c (1 / x) = 2 + c * ((x - 1) / x) := by unfold hl2Zr; field_simp; ring
  have e5 : (21 * x - 5) / (8 * x) = 2 + 5 / 8 * ((x - 1) / x) := by field_simp; ring
  have e7 : (23 * x - 7) / (8 * x) = 2 + 7 / 8 * ((x - 1) / x) := by field_simp; ring
  have : 0 ≤ (x - 1) / x := div_nonneg (by linarith) hx0.le
  rw [e, e5, e7]
  constructor <;> nlinarith

/-- `H₀ < 0` at `α = x`, norm `u_v`: the chord bound between `c = 5/8` and `c = 7/8`. -/
theorem hl2_up_H0 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : hl2H0 x c (hsVbar x) (1 / x) < 0 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨-, -, hZb, hZb', -⟩ := hl2_Zb hx hx2 hc hc2 le_rfl
  obtain ⟨h5, h7⟩ := hl2_up_Zc hx hc hc2
  have hZ5 : 7 / 3 ≤ (21 * x - 5) / (8 * x) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hZ5' : (21 * x - 5) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hZ7' : (23 * x - 7) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hg : 0 ≤ -(2 / 49) * (hl2Zr x c (1 / x) * ((21 * x - 5) / (8 * x)) *
      ((23 * x - 7) / (8 * x))) + 1 := by
    have : hl2Zr x c (1 / x) * ((21 * x - 5) / (8 * x)) * ((23 * x - 7) / (8 * x)) ≤
        8 / 3 * (8 / 3) * (8 / 3) :=
      mul_le_mul (mul_le_mul hZb' hZ5' (by linarith) (by norm_num)) hZ7' (by linarith) (by norm_num)
    linarith
  have hK := hl2_chord (by linarith) h5 h7 hg (hl2_up_K0_5 hx hx2) (hl2_up_K0_7 hx hx2)
  have hZ0 : 0 < hl2Zr x c (1 / x) := by linarith
  have hlog := hl2_log_le_quad (y := 2 * hl2Zr x c (1 / x) / 7) (by positivity) (by linarith)
  unfold hl2H0 hl2Ht
  rw [hl2_Wb_eq hx0.ne', hl2_Eb_eq hx0.ne']
  have e : hl2K0 x (hsVbar x) (hl2Zr x c (1 / x)) = 6 / 7 + (hsVbar x - 1) * hl2Zr x c (1 / x) +
      1 / hl2Zr x c (1 / x) - hl2Eb x (hsVbar x) + (4 - hl2Zr x c (1 / x) / 2) * hl2Wb x (hsVbar x) +
      ((2 * hl2Zr x c (1 / x) / 7 - 1) - (2 * hl2Zr x c (1 / x) / 7 - 1) ^ 2 / 2) := by
    unfold hl2K0; ring
  linarith

/-- `H₁ < 0` at `α = x`, norm `u_v`: the chord bound between `c = 5/8` and `c = 7/8`. -/
theorem hl2_up_H1 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : hl2H1 x c (hsVbar x) (1 / x) < 0 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨-, -, hZb, hZb', -⟩ := hl2_Zb hx hx2 hc hc2 le_rfl
  obtain ⟨h5, h7⟩ := hl2_up_Zc hx hc hc2
  have hZ5 : 7 / 3 ≤ (21 * x - 5) / (8 * x) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hZ5' : (21 * x - 5) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hZ7' : (23 * x - 7) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hW := hl2_Wb_pos hx hx2 (hl2_Vbar_le hx hx2).2.le
  have hg : 0 ≤ -(2 / 49) * (hl2Zr x c (1 / x) * ((21 * x - 5) / (8 * x)) *
      ((23 * x - 7) / (8 * x))) + (1 + 7 * hl2Wb x (hsVbar x)) := by
    have : hl2Zr x c (1 / x) * ((21 * x - 5) / (8 * x)) * ((23 * x - 7) / (8 * x)) ≤
        8 / 3 * (8 / 3) * (8 / 3) :=
      mul_le_mul (mul_le_mul hZb' hZ5' (by linarith) (by norm_num)) hZ7' (by linarith) (by norm_num)
    linarith
  have hK := hl2_chord (by linarith) h5 h7 hg (hl2_up_K1_5 hx hx2) (hl2_up_K1_7 hx hx2)
  have hZ0 : 0 < hl2Zr x c (1 / x) := by linarith
  have hlog := hl2_log_le_quad (y := 2 * hl2Zr x c (1 / x) / 7) (by positivity) (by linarith)
  unfold hl2H1 hl2Ht
  rw [hl2_Wb_eq hx0.ne', hl2_Eb_eq hx0.ne']
  have e : (1 + 7 * hl2Wb x (hsVbar x)) / hl2Zr x c (1 / x) =
      1 / hl2Zr x c (1 / x) + 7 / hl2Zr x c (1 / x) * hl2Wb x (hsVbar x) := by
    field_simp
  linarith

/-! ### The large-shape face sign -/

/-- **The outer sharp-ratio face, large `α`** (the statement of `hs2_outer_sign_large`). -/
theorem hs2_outer_sign_large_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hal : 3 / 2 ≤ al) (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsVbar x) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  obtain ⟨c, hc1, hc2, hbe⟩ := hl2_strip_c hx hx2 (by linarith) hb hb'
  have hal0 : 0 < al := by linarith
  have hB : 0 < al + be := by rw [hbe]; nlinarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hk : 0 < 1 / 7 / hsRA al be := by positivity
  have hτk : τ * (1 / 7 / hsRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    linarith
  obtain ⟨hu, hu'⟩ := hl2_Vbar_le hx hx2
  have hr0 : 1 / x ≤ 1 / al := one_div_le_one_div_of_le hal0 hax
  have hr1 : 1 / al ≤ 2 / 3 := by rw [div_le_iff₀ hal0]; linarith
  rw [hl2_hsF_face]
  refine lt_of_le_of_lt (hl2_tau_outer hk hτ hτk) (max_lt ?_ ?_)
  · rw [hl2_face_H0 hal0 hbe hB]
    refine lt_of_le_of_lt (hl2_H0_le_max hx hx2 hc1 hc2 hu hu'.le le_rfl hr0 hr1 (by norm_num))
      (max_lt (hl2_up_H0 hx hx2 hc1 hc2) (hl2_mid_H0 hx hx2 hc1 hc2))
  · rw [hl2_face_H1 hal0 hbe hB]
    refine lt_of_le_of_lt (hl2_H1_le_max hx hx2 hc1 hc2 hu hu'.le le_rfl hr0 hr1 (by norm_num))
      (max_lt (hl2_up_H1 hx hx2 hc1 hc2) (hl2_mid_H1 hx hx2 hc1 hc2))

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.Reciprocal

/-!
# Smaller-short window, upper ratio: the outer face for large `α`

`ur_outer_sign_large_proof` proves the statement of `ur_outer_sign_large`: with the incoming
norm `u_v = V̄(x)` fixed, both outer tests are convex in `r = 1/α` (`OuterFace/Reciprocal`), so on
`1/x ≤ r ≤ 2/3` they are bounded by their values at two terminal shapes: the middle shape
`α = 3/2` (`log y ≤ y - 1` and the two bivariate polynomials `P₀`, `P₁`) and the upper shape
`α = x` (`D = S²`, `log y ≤ (y - 1) - (y - 1)²/2`, convexity in `Z` between `c = 5/8` and
`c = 7/8`, and four univariate polynomials with positive coefficients).

## Main API

* `ur_Vbar_le`: `3/4 ≤ V̄(x) < 4/5`.
* `ur_mid_H0`, `ur_mid_H1`: both tests are negative at `α = 3/2`, norm `u_v`.
* `ur_up_H0`, `ur_up_H1`: both tests are negative at `α = x`, norm `u_v`.
* `ur_outer_sign_large_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `3/4 ≤ u_v < 4/5`: `u_v - 3/4 = 2(x - 1)²/((x + 1)(35x + 13)) < 1/20`. -/
theorem ur_Vbar_le {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) :
    3 / 4 ≤ ssVbar x ∧ ssVbar x < 4 / 5 := by
  unfold ssVbar
  have hd : 0 < (x + 1) * (35 * x + 13) := by positivity
  constructor
  · have : 0 ≤ 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) := by positivity
    linarith
  · have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) < 1 / 20 := by
      rw [div_lt_iff₀ hd]; nlinarith
    linarith

/-- **Chord bound for `A + BZ + CZ² + g/Z`**: if `CZZ₅Z₇ + g ≥ 0` the function lies below its
chord, so negativity at `Z₅` and `Z₇` gives negativity in between. -/
theorem ur_chord {A B C g Z Z5 Z7 : ℝ} (h5 : 0 < Z5) (h57 : Z5 ≤ Z) (h7 : Z ≤ Z7)
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
noncomputable def urP0 (h t : ℝ) : ℝ :=
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
noncomputable def urP1 (h t : ℝ) : ℝ :=
  (-1851392) * h ^ 7 +
      (-2777088*t - 100117504) * h ^ 6 +
      (-1388544*t^2 - 105794560*t - 848275648) * h ^ 5 +
      (-231424*t^3 - 30706432*t^2 - 767762016*t - 2631801700) * h ^ 4 +
      (-1419264*t^3 - 177395968*t^2 - 2110288736*t - 2736950236) * h ^ 3 +
      (-2791936*t^3 - 430245056*t^2 - 2276207224*t + 1436109239) * h ^ 2 +
      (-1843200*t^3 - 448134656*t^2 - 247508736*t + 3486400264) * h +
      (-386560*t^3 - 154005312*t^2 + 887736184*t + 261744249)

theorem ur_P0_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urP0 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urP0
  linarith [mul_nonneg (tp 1) (hp 7), mul_nonneg (tp 2) (hp 6), mul_nonneg (tp 1) (hp 6), mul_nonneg (tp 3) (hp 5), mul_nonneg (tp 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tp 4) (hp 4), mul_nonneg (tp 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tp 4) (hp 3), mul_nonneg (tp 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tq 3, tq 2, tp 1, hl 8, hl 7, hu 6, hu 5, hu 4, hu 3, hl 2, hl 1]

theorem ur_P1_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urP1 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urP1
  linarith [mul_nonneg (tq 1) (hp 6), mul_nonneg (tq 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tq 3, tq 2, tp 1, hu 7, hu 6, hu 5, hu 4, hu 3, hl 2, hl 1]

/-- `H₀ < 0` at `α = 3/2`, norm `u_v`: `log y ≤ y - 1` and `P₀ > 0`. -/
theorem ur_mid_H0 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : urH0 x c (ssVbar x) (2 / 3) < 0 := by
  have hZ : 0 < urZr x c (2 / 3) := by unfold urZr; nlinarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 2 * urZr x c (2 / 3) / 7 by positivity)
  have hS : 0 < 1 + x := by linarith
  have hB : 0 < c + 2 * x + 3 := by linarith
  have key : -47628 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) * (6 / 7 +
      (ssVbar x - 1) * urZr x c (2 / 3) + 1 / urZr x c (2 / 3) - urELr x c (ssVbar x) (2 / 3) +
      (4 - urZr x c (2 / 3) / 2) * (urWr x c (ssVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * urZr x c (2 / 3) / 7 - 1)) = urP0 (x - 2) (c - 5 / 8) / 2048 := by
    have eZ : urZr x c (2 / 3) = (c + 2 * x + 3) / 3 := by unfold urZr; ring
    have hB' := hB.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    rw [eZ]
    unfold ssVbar urELr urWr urDr urd1 urd2 urJ2 ssE0 urP0
    field_simp
    ring
  have hP := ur_P0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hd : 0 < 47628 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) := by positivity
  have hJ : 6 / 7 + (ssVbar x - 1) * urZr x c (2 / 3) + 1 / urZr x c (2 / 3) -
      urELr x c (ssVbar x) (2 / 3) +
      (4 - urZr x c (2 / 3) / 2) * (urWr x c (ssVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * urZr x c (2 / 3) / 7 - 1) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hd.le h]
  unfold urH0 urHt
  linarith

/-- `H₁ < 0` at `α = 3/2`, norm `u_v`: `log y ≤ y - 1` and `P₁ > 0`. -/
theorem ur_mid_H1 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : urH1 x c (ssVbar x) (2 / 3) < 0 := by
  have hZ : 0 < urZr x c (2 / 3) := by unfold urZr; nlinarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 2 * urZr x c (2 / 3) / 7 by positivity)
  have hS : 0 < 1 + x := by linarith
  have hB : 0 < c + 2 * x + 3 := by linarith
  have key : -31752 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) * (6 / 7 +
      (ssVbar x - 1) * urZr x c (2 / 3) + 1 / urZr x c (2 / 3) - urELr x c (ssVbar x) (2 / 3) +
      (7 / urZr x c (2 / 3) + 1 / 4) * (urWr x c (ssVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * urZr x c (2 / 3) / 7 - 1)) = urP1 (x - 2) (c - 5 / 8) / 256 := by
    have eZ : urZr x c (2 / 3) = (c + 2 * x + 3) / 3 := by unfold urZr; ring
    have hB' := hB.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    rw [eZ]
    unfold ssVbar urELr urWr urDr urd1 urd2 urJ2 ssE0 urP1
    field_simp
    ring
  have hP := ur_P1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hd : 0 < 31752 * (1 + x) * (35 * x + 13) * (c + 2 * x + 3) := by positivity
  have hJ : 6 / 7 + (ssVbar x - 1) * urZr x c (2 / 3) + 1 / urZr x c (2 / 3) -
      urELr x c (ssVbar x) (2 / 3) +
      (7 / urZr x c (2 / 3) + 1 / 4) * (urWr x c (ssVbar x) (2 / 3) / 49 - 3 / 4) +
      (2 * urZr x c (2 / 3) / 7 - 1) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hd.le h]
  unfold urH1 urHt
  linarith

/-! ### The upper shape `α = x` -/

/-- At `r = 1/x`, `D_r = S²/x²` does not depend on `c`. -/
theorem ur_Dr_edge {x : ℝ} (c c' : ℝ) (hx : x ≠ 0) : urDr x c (1 / x) = urDr x c' (1 / x) := by
  unfold urDr urd1 urd2
  field_simp
  ring

/-- `h = w - 3/4` at the upper shape (independent of `c`). -/
noncomputable def urWb (x u : ℝ) : ℝ := urWr x (5 / 8) u (1 / x) / 49 - 3 / 4

/-- `E_L` at the upper shape (independent of `c`). -/
noncomputable def urEb (x u : ℝ) : ℝ := urELr x (5 / 8) u (1 / x)

/-- `K₀` at the upper shape as a function of `Z`, with `q(2Z/7) = 4Z/7 - 2Z²/49 - 3/2` in place
of the logarithm (`log y ≤ (y - 1) - (y - 1)²/2` at `y = 2Z/7`). -/
noncomputable def urK0 (x u Z : ℝ) : ℝ :=
  (6 / 7 - urEb x u + 4 * urWb x u - 3 / 2) + (u - 1 - urWb x u / 2 + 4 / 7) * Z +
    (-(2 / 49)) * Z ^ 2 + 1 / Z

/-- `K₁` at the upper shape as a function of `Z`. -/
noncomputable def urK1 (x u Z : ℝ) : ℝ :=
  (6 / 7 - urEb x u + urWb x u / 4 - 3 / 2) + (u - 1 + 4 / 7) * Z + (-(2 / 49)) * Z ^ 2 +
    (1 + 7 * urWb x u) / Z

theorem ur_Wb_eq {x c u : ℝ} (hx : x ≠ 0) : urWr x c u (1 / x) / 49 - 3 / 4 = urWb x u := by
  unfold urWb urWr; rw [ur_Dr_edge c (5 / 8) hx]

theorem ur_Eb_eq {x c u : ℝ} (hx : x ≠ 0) : urELr x c u (1 / x) = urEb x u := by
  unfold urEb urELr; rw [ur_Dr_edge c (5 / 8) hx]

/-- `w > 3/4` at the upper shape for `u ≤ 4/5`. -/
theorem ur_Wb_pos {x u : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) (hu : u ≤ 4 / 5) :
    0 ≤ urWb x u := by
  have hx0 : 0 < x := by linarith
  have e : 49 * x ^ 3 * (urWb x u + 3 / 4) = 6 * x ^ 4 + 54 * x ^ 3 + 5 * x ^ 2 + 5 * x - 1 -
      u * (6 * x ^ 4 + 17 * x ^ 3 + 15 * x ^ 2 + 3 * x - 1) := by
    unfold urWb urWr urDr urd1 urd2 ssE0
    field_simp
    ring
  have hk : 0 ≤ 6 * x ^ 4 + 17 * x ^ 3 + 15 * x ^ 2 + 3 * x - 1 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hu hk
  have h2 : 0 ≤ 49 * x ^ 3 * urWb x u := by nlinarith
  exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 49 * x ^ 3)

/-- `Q_{0,5}`: `K0` at `c = 5/8` is negative (its cleared form is a polynomial in `x - 2` with
positive coefficients). -/
theorem ur_up_K0_5 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    urK0 x (ssVbar x) ((21 * x - 5) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -3136 * x ^ 4 * (1 + x) * (21 * x - 5) * (35 * x + 13) * urK0 x (ssVbar x) ((21 * x - 5) / (8 * x)) =
      234738 * (x - 2) ^ 8 + 3667214 * (x - 2) ^ 7 + 24648615 * (x - 2) ^ 6 +
        92851363 * (x - 2) ^ 5 + 213716967 * (x - 2) ^ 4 + 306333042 * (x - 2) ^ 3 +
        264962511 * (x - 2) ^ 2 + 124682189 * (x - 2) + 23749793 := by
    have h1 : 21 * x - 5 ≠ 0 := by linarith
    have h1' : x * 21 - 5 ≠ 0 := by linarith
    have h1'' : -5 + x * 21 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold urK0 urWb urEb ssVbar urELr urWr urDr urd1 urd2 urJ2 ssE0
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
theorem ur_up_K0_7 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    urK0 x (ssVbar x) ((23 * x - 7) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -3136 * x ^ 4 * (1 + x) * (23 * x - 7) * (35 * x + 13) * urK0 x (ssVbar x) ((23 * x - 7) / (8 * x)) =
      264546 * (x - 2) ^ 8 + 4135722 * (x - 2) ^ 7 + 27918195 * (x - 2) ^ 6 +
        105942595 * (x - 2) ^ 5 + 246387335 * (x - 2) ^ 4 + 358167934 * (x - 2) ^ 3 +
        315902859 * (x - 2) ^ 2 + 152970501 * (x - 2) + 30522633 := by
    have h1 : 23 * x - 7 ≠ 0 := by linarith
    have h1' : x * 23 - 7 ≠ 0 := by linarith
    have h1'' : -7 + x * 23 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold urK0 urWb urEb ssVbar urELr urWr urDr urd1 urd2 urJ2 ssE0
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
theorem ur_up_K1_5 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    urK1 x (ssVbar x) ((21 * x - 5) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -1568 * x ^ 3 * (1 + x) * (21 * x - 5) * (35 * x + 13) * urK1 x (ssVbar x) ((21 * x - 5) / (8 * x)) =
      111132 * (x - 2) ^ 7 + 1470458 * (x - 2) ^ 6 + 8061427 * (x - 2) ^ 5 +
        23480036 * (x - 2) ^ 4 + 38542410 * (x - 2) ^ 3 + 34349390 * (x - 2) ^ 2 +
        13879207 * (x - 2) + 1100756 := by
    have h1 : 21 * x - 5 ≠ 0 := by linarith
    have h1' : x * 21 - 5 ≠ 0 := by linarith
    have h1'' : -5 + x * 21 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold urK1 urWb urEb ssVbar urELr urWr urDr urd1 urd2 urJ2 ssE0
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
theorem ur_up_K1_7 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    urK1 x (ssVbar x) ((23 * x - 7) / (8 * x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have key : -1568 * x ^ 3 * (1 + x) * (23 * x - 7) * (35 * x + 13) * urK1 x (ssVbar x) ((23 * x - 7) / (8 * x)) =
      128628 * (x - 2) ^ 7 + 1724592 * (x - 2) ^ 6 + 9663133 * (x - 2) ^ 5 +
        29057180 * (x - 2) ^ 4 + 50024402 * (x - 2) ^ 3 + 48266480 * (x - 2) ^ 2 +
        23049277 * (x - 2) + 3623652 := by
    have h1 : 23 * x - 7 ≠ 0 := by linarith
    have h1' : x * 23 - 7 ≠ 0 := by linarith
    have h1'' : -7 + x * 23 ≠ 0 := by linarith
    have hx' : x ≠ 0 := hx0.ne'
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    unfold urK1 urWb urEb ssVbar urELr urWr urDr urd1 urd2 urJ2 ssE0
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
theorem ur_up_Zc {x c : ℝ} (hx : 13 / 6 ≤ x) (hc : 5 / 8 ≤ c) (hc2 : c ≤ 7 / 8) :
    (21 * x - 5) / (8 * x) ≤ urZr x c (1 / x) ∧ urZr x c (1 / x) ≤ (23 * x - 7) / (8 * x) := by
  have hx0 : 0 < x := by linarith
  have e : urZr x c (1 / x) = 2 + c * ((x - 1) / x) := by unfold urZr; field_simp; ring
  have e5 : (21 * x - 5) / (8 * x) = 2 + 5 / 8 * ((x - 1) / x) := by field_simp; ring
  have e7 : (23 * x - 7) / (8 * x) = 2 + 7 / 8 * ((x - 1) / x) := by field_simp; ring
  have : 0 ≤ (x - 1) / x := div_nonneg (by linarith) hx0.le
  rw [e, e5, e7]
  constructor <;> nlinarith

/-- `H₀ < 0` at `α = x`, norm `u_v`: the chord bound between `c = 5/8` and `c = 7/8`. -/
theorem ur_up_H0 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : urH0 x c (ssVbar x) (1 / x) < 0 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨-, -, hZb, hZb', -⟩ := ur_Zb hx hx2 hc hc2 le_rfl
  obtain ⟨h5, h7⟩ := ur_up_Zc hx hc hc2
  have hZ5 : 7 / 3 ≤ (21 * x - 5) / (8 * x) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hZ5' : (21 * x - 5) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hZ7' : (23 * x - 7) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hg : 0 ≤ -(2 / 49) * (urZr x c (1 / x) * ((21 * x - 5) / (8 * x)) *
      ((23 * x - 7) / (8 * x))) + 1 := by
    have : urZr x c (1 / x) * ((21 * x - 5) / (8 * x)) * ((23 * x - 7) / (8 * x)) ≤
        8 / 3 * (8 / 3) * (8 / 3) :=
      mul_le_mul (mul_le_mul hZb' hZ5' (by linarith) (by norm_num)) hZ7' (by linarith) (by norm_num)
    linarith
  have hK := ur_chord (by linarith) h5 h7 hg (ur_up_K0_5 hx hx2) (ur_up_K0_7 hx hx2)
  have hZ0 : 0 < urZr x c (1 / x) := by linarith
  have hlog := ur_log_le_quad (y := 2 * urZr x c (1 / x) / 7) (by positivity) (by linarith)
  unfold urH0 urHt
  rw [ur_Wb_eq hx0.ne', ur_Eb_eq hx0.ne']
  have e : urK0 x (ssVbar x) (urZr x c (1 / x)) = 6 / 7 + (ssVbar x - 1) * urZr x c (1 / x) +
      1 / urZr x c (1 / x) - urEb x (ssVbar x) + (4 - urZr x c (1 / x) / 2) * urWb x (ssVbar x) +
      ((2 * urZr x c (1 / x) / 7 - 1) - (2 * urZr x c (1 / x) / 7 - 1) ^ 2 / 2) := by
    unfold urK0; ring
  linarith

/-- `H₁ < 0` at `α = x`, norm `u_v`: the chord bound between `c = 5/8` and `c = 7/8`. -/
theorem ur_up_H1 {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) : urH1 x c (ssVbar x) (1 / x) < 0 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨-, -, hZb, hZb', -⟩ := ur_Zb hx hx2 hc hc2 le_rfl
  obtain ⟨h5, h7⟩ := ur_up_Zc hx hc hc2
  have hZ5 : 7 / 3 ≤ (21 * x - 5) / (8 * x) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hZ5' : (21 * x - 5) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hZ7' : (23 * x - 7) / (8 * x) ≤ 8 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hW := ur_Wb_pos hx hx2 (ur_Vbar_le hx hx2).2.le
  have hg : 0 ≤ -(2 / 49) * (urZr x c (1 / x) * ((21 * x - 5) / (8 * x)) *
      ((23 * x - 7) / (8 * x))) + (1 + 7 * urWb x (ssVbar x)) := by
    have : urZr x c (1 / x) * ((21 * x - 5) / (8 * x)) * ((23 * x - 7) / (8 * x)) ≤
        8 / 3 * (8 / 3) * (8 / 3) :=
      mul_le_mul (mul_le_mul hZb' hZ5' (by linarith) (by norm_num)) hZ7' (by linarith) (by norm_num)
    linarith
  have hK := ur_chord (by linarith) h5 h7 hg (ur_up_K1_5 hx hx2) (ur_up_K1_7 hx hx2)
  have hZ0 : 0 < urZr x c (1 / x) := by linarith
  have hlog := ur_log_le_quad (y := 2 * urZr x c (1 / x) / 7) (by positivity) (by linarith)
  unfold urH1 urHt
  rw [ur_Wb_eq hx0.ne', ur_Eb_eq hx0.ne']
  have e : (1 + 7 * urWb x (ssVbar x)) / urZr x c (1 / x) =
      1 / urZr x c (1 / x) + 7 / urZr x c (1 / x) * urWb x (ssVbar x) := by
    field_simp
  linarith

/-! ### The large-shape face sign -/

/-- **The outer sharp-ratio face, large `α`** (the statement of `ur_outer_sign_large`). -/
theorem ur_outer_sign_large_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hal : 3 / 2 ≤ al) (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * ssRA al be) :
    ssF x be al (ssVbar x) (1 / 7) τ (log (τ * (1 / 7) / ssRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * ssRA al be)) < 0 := by
  obtain ⟨c, hc1, hc2, hbe⟩ := ur_strip_c hx hx2 (by linarith) hb hb'
  have hal0 : 0 < al := by linarith
  have hB : 0 < al + be := by rw [hbe]; nlinarith
  have hrA : 0 < ssRA al be := by unfold ssRA; positivity
  have hk : 0 < 1 / 7 / ssRA al be := by positivity
  have hτk : τ * (1 / 7 / ssRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    linarith
  obtain ⟨hu, hu'⟩ := ur_Vbar_le hx hx2
  have hr0 : 1 / x ≤ 1 / al := one_div_le_one_div_of_le hal0 hax
  have hr1 : 1 / al ≤ 2 / 3 := by rw [div_le_iff₀ hal0]; linarith
  rw [ur_hsF_face]
  refine lt_of_le_of_lt (ur_tau_outer hk hτ hτk) (max_lt ?_ ?_)
  · rw [ur_face_H0 hal0 hbe hB]
    refine lt_of_le_of_lt (ur_H0_le_max hx hx2 hc1 hc2 hu hu'.le le_rfl hr0 hr1 (by norm_num))
      (max_lt (ur_up_H0 hx hx2 hc1 hc2) (ur_mid_H0 hx hx2 hc1 hc2))
  · rw [ur_face_H1 hal0 hbe hB]
    refine lt_of_le_of_lt (ur_H1_le_max hx hx2 hc1 hc2 hu hu'.le le_rfl hr0 hr1 (by norm_num))
      (max_lt (ur_up_H1 hx hx2 hc1 hc2) (ur_mid_H1 hx hx2 hc1 hc2))

end SmoothedOctagon

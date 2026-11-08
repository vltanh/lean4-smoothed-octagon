module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaDefs
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecipPoly

/-!
# S2 hand signs: the central beta monotonicity, the base face `b = x`

Both beta derivatives are positive at the lower endpoint `b = x` (`B = a + x`) of the enlarged
beta range `x ≤ b ≤ x + 7(a - 1)/8`.

The exact derivatives at `b = x` (moving norm included, through the partial fractions of
`S2HandCenBetaDefs`) are cleared directly:
`19200aB²(x - 1)S²K³ G_b(x) = N_G(x - 2, a - 1)` and
`38400aB²(x - 1)S²K² H_b(x) = N_H(x - 2, a - 1)`, two bivariate polynomials of degrees 12 and 10
(82 and 58 terms in `h = x - 2`, `c = a - 1`), each positive by a termwise bound of its monomials
(lower bounds `2.4·10⁸` and `5.1·10⁷`).

## Main API

* `hl2cbG1`, `hl2cbH1`: the two first derivatives (template forms of `hl2cb_hd`).
* `hl2cbNG`, `hl2cbNH` and `hl2cb_G1_base`, `hl2cb_H1_base`: positivity at `b = x`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `G_b = 3p₃B² + 2p₂B + p₁ - a/B² - p_c/(b - 1)² + 1/B`. -/
noncomputable def hl2cbG1 (x a s : ℝ) : ℝ :=
  3 * hl2cbp3 x a * (a + s) ^ 2 + 2 * hl2cbp2 x a * (a + s) + hl2cbp1 x a - a / (a + s) ^ 2 -
    hl2cbpc x a / (s - 1) ^ 2 + 1 / (a + s)

/-- `H_b = (c₂/2)B + q₁ - A₁/B² - P_c/(b - 1)² + 1/B`. -/
noncomputable def hl2cbH1 (x a s : ℝ) : ℝ :=
  3 * 0 * (a + s) ^ 2 + 2 * (hl2cbc2 x a / 4) * (a + s) + hl2cbq1 x a - hl2cbA1 x a / (a + s) ^ 2 -
    hl2cbPc x a / (s - 1) ^ 2 + 1 / (a + s)

/-- `N_G(h, c) = 19200aB²(x - 1)S²K³ G_b(x)`, `x = 2 + h`, `a = 1 + c`. -/
noncomputable def hl2cbNG (h c : ℝ) : ℝ :=
  (-44500 * h ^ 11 - 685654 * h ^ 10 - 3344404 * h ^ 9 + 3894818 * h ^ 8 + 118880392 * h ^ 7 + 626394692 * h ^ 6 + 1806612888 * h ^ 5 + 3258606228 * h ^ 4 + 3760785644 * h ^ 3 + 2694645106 * h ^ 2 + 1089387996 * h + 189421290) +
    (-39706 * h ^ 11 - 528696 * h ^ 10 - 1600178 * h ^ 9 + 11506184 * h ^ 8 + 113758768 * h ^ 7 + 420611428 * h ^ 6 + 789278336 * h ^ 5 + 599392516 * h ^ 4 - 409074118 * h ^ 3 - 1220657916 * h ^ 2 - 932125342 * h - 250124988) * c +
    (16578 * h ^ 10 - 3034 * h ^ 9 - 5709255 * h ^ 8 - 74744308 * h ^ 7 - 456872632 * h ^ 6 - 1615901592 * h ^ 5 - 3520448402 * h ^ 4 - 4739020252 * h ^ 3 - 3769402162 * h ^ 2 - 1577643390 * h - 254877887) * c ^ 2 +
    (92550 * h ^ 9 + 883728 * h ^ 8 + 3211147 * h ^ 7 + 16692407 * h ^ 6 + 139420839 * h ^ 5 + 662279303 * h ^ 4 + 1670441209 * h ^ 3 + 2280384861 * h ^ 2 + 1579966255 * h + 432917621) * c ^ 3 +
    (-35443 * h ^ 8 + 454716 * h ^ 7 + 14576517 * h ^ 6 + 116286357 * h ^ 5 + 441228166 * h ^ 4 + 885831646 * h ^ 3 + 907524301 * h ^ 2 + 384077857 * h + 23364811) * c ^ 4 +
    (-84371 * h ^ 7 - 500357 * h ^ 6 - 2288008 * h ^ 5 - 25128979 * h ^ 4 - 146103143 * h ^ 3 - 387169943 * h ^ 2 - 467880262 * h - 203562889) * c ^ 5 +
    (-13339 * h ^ 6 - 1065211 * h ^ 5 - 12787846 * h ^ 4 - 63743681 * h ^ 3 - 155866730 * h ^ 2 - 182201688 * h - 78348257) * c ^ 6 +
    (-677 * h ^ 5 - 392054 * h ^ 4 - 3654960 * h ^ 3 - 12518047 * h ^ 2 - 18173769 * h - 8921021) * c ^ 7 +
    (-32273 * h ^ 3 - 217811 * h ^ 2 - 473575 * h - 288277) * c ^ 8 +
    (677 * h ^ 2 + 1342 * h + 653) * c ^ 9

/-- `N_H(h, c) = 38400aB²(x - 1)S²K² H_b(x)`, `x = 2 + h`, `a = 1 + c`. -/
noncomputable def hl2cbNH (h c : ℝ) : ℝ :=
  (-5416 * h ^ 10 - 58018 * h ^ 9 + 191974 * h ^ 8 + 6139812 * h ^ 7 + 42878708 * h ^ 6 + 157885536 * h ^ 5 + 349930944 * h ^ 4 + 479534428 * h ^ 3 + 395543188 * h ^ 2 + 179075778 * h + 34037370) +
    (-21262 * h ^ 9 - 307188 * h ^ 8 - 1867556 * h ^ 7 - 6741444 * h ^ 6 - 19678592 * h ^ 5 - 55279244 * h ^ 4 - 122364860 * h ^ 3 - 166849260 * h ^ 2 - 118045586 * h - 32799184) * c +
    (-622 * h ^ 8 - 126453 * h ^ 7 - 2066269 * h ^ 6 - 15626365 * h ^ 5 - 65317025 * h ^ 4 - 155766887 * h ^ 3 - 205321951 * h ^ 2 - 134917447 * h - 33726869) * c ^ 2 +
    (-10997 * h ^ 7 - 130165 * h ^ 6 - 1391025 * h ^ 5 - 8157369 * h ^ 4 - 22217263 * h ^ 3 - 24944015 * h ^ 2 - 4921355 * h + 4695709) * c ^ 3 +
    (15736 * h ^ 6 + 8405 * h ^ 5 - 363306 * h ^ 4 + 156934 * h ^ 3 + 6597912 * h ^ 2 + 14324909 * h + 8242834) * c ^ 4 +
    (677 * h ^ 5 + 115126 * h ^ 4 + 1079584 * h ^ 3 + 3807178 * h ^ 2 + 5717723 * h + 2876640) * c ^ 5 +
    (17858 * h ^ 3 + 121645 * h ^ 2 + 266744 * h + 163113) * c ^ 6 +
    (-677 * h ^ 2 - 1342 * h - 653) * c ^ 7

theorem hl2cb_NG_id {x a : ℝ} (hx : 1 < x) (ha : 0 < a) :
    19200 * a * (a + x) ^ 2 * (x - 1) * (1 + x) ^ 2 * hl2cK x a ^ 3 * hl2cbG1 x a x =
      hl2cbNG (x - 2) (a - 1) := by
  have hK := (hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)).ne'
  have hS : 1 + x ≠ 0 := by linarith
  have hx1 : x - 1 ≠ 0 := by linarith
  have hB : a + x ≠ 0 := by linarith
  unfold hl2cbG1 hl2cbp3 hl2cbp2 hl2cbp1 hl2cbpc hl2cbl hl2cbc2 hl2cbc1 hl2cbc0 hl2cbcv hl2cbl1
    hl2cbe1 hl2cbcb hl2cbce hl2cbM hl2cbD0 hl2cbEf hl2cbJ hl2cbd
  field_simp
  unfold hl2cbNG hl2cK
  ring

theorem hl2cb_NG_pos {h c : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (hc : 0 ≤ c) (hc' : c ≤ 1 / 3) :
    0 < hl2cbNG h c := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) hc hc'
  unfold hl2cbNG
  linarith [mul_nonneg (tq 1) (hp 11), mul_nonneg (tp 2) (hp 10), mul_nonneg (tq 1) (hp 10), mul_nonneg (tp 3) (hp 9), mul_nonneg (tq 2) (hp 9), mul_nonneg (tq 1) (hp 9), mul_nonneg (tq 4) (hp 8), mul_nonneg (tp 3) (hp 8), mul_nonneg (tq 2) (hp 8), mul_nonneg (tp 1) (hp 8), mul_nonneg (tq 5) (hp 7), mul_nonneg (tp 4) (hp 7), mul_nonneg (tp 3) (hp 7), mul_nonneg (tq 2) (hp 7), mul_nonneg (tp 1) (hp 7), mul_nonneg (tq 6) (hp 6), mul_nonneg (tq 5) (hp 6), mul_nonneg (tp 4) (hp 6), mul_nonneg (tp 3) (hp 6), mul_nonneg (tq 2) (hp 6), mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 7) (hp 5), mul_nonneg (tq 6) (hp 5), mul_nonneg (tq 5) (hp 5), mul_nonneg (tp 4) (hp 5), mul_nonneg (tp 3) (hp 5), mul_nonneg (tq 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 7) (hp 4), mul_nonneg (tq 6) (hp 4), mul_nonneg (tq 5) (hp 4), mul_nonneg (tp 4) (hp 4), mul_nonneg (tp 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tq 8) (hp 3), mul_nonneg (tq 7) (hp 3), mul_nonneg (tq 6) (hp 3), mul_nonneg (tq 5) (hp 3), mul_nonneg (tp 4) (hp 3), mul_nonneg (tp 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tp 9) (hp 2), mul_nonneg (tq 8) (hp 2), mul_nonneg (tq 7) (hp 2), mul_nonneg (tq 6) (hp 2), mul_nonneg (tq 5) (hp 2), mul_nonneg (tp 4) (hp 2), mul_nonneg (tp 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tp 9) (hp 1), mul_nonneg (tq 8) (hp 1), mul_nonneg (tq 7) (hp 1), mul_nonneg (tq 6) (hp 1), mul_nonneg (tq 5) (hp 1), mul_nonneg (tp 4) (hp 1), mul_nonneg (tp 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 9, tq 8, tq 7, tq 6, tq 5, tp 4, tp 3, tq 2, tq 1, hu 11, hu 10, hu 9, hl 8, hl 7, hl 6, hl 5, hl 4, hl 3, hl 2, hl 1]

theorem hl2cb_NH_id {x a : ℝ} (hx : 1 < x) (ha : 0 < a) :
    38400 * a * (a + x) ^ 2 * (x - 1) * (1 + x) ^ 2 * hl2cK x a ^ 2 * hl2cbH1 x a x =
      hl2cbNH (x - 2) (a - 1) := by
  have hK := (hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)).ne'
  have hS : 1 + x ≠ 0 := by linarith
  have hx1 : x - 1 ≠ 0 := by linarith
  have hB : a + x ≠ 0 := by linarith
  unfold hl2cbH1 hl2cbq1 hl2cbA1 hl2cbPc hl2cbc2 hl2cbc1 hl2cbc0 hl2cbcv hl2cbl1 hl2cbe1 hl2cbcb
    hl2cbce hl2cbM hl2cbD0 hl2cbEf hl2cbJ hl2cbd
  field_simp
  unfold hl2cbNH hl2cK
  ring

theorem hl2cb_NH_pos {h c : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (hc : 0 ≤ c) (hc' : c ≤ 1 / 3) :
    0 < hl2cbNH h c := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) hc hc'
  unfold hl2cbNH
  linarith [mul_nonneg (tq 1) (hp 9), mul_nonneg (tq 2) (hp 8), mul_nonneg (tq 1) (hp 8), mul_nonneg (tq 3) (hp 7), mul_nonneg (tq 2) (hp 7), mul_nonneg (tq 1) (hp 7), mul_nonneg (tp 4) (hp 6), mul_nonneg (tq 3) (hp 6), mul_nonneg (tq 2) (hp 6), mul_nonneg (tq 1) (hp 6), mul_nonneg (tp 5) (hp 5), mul_nonneg (tp 4) (hp 5), mul_nonneg (tq 3) (hp 5), mul_nonneg (tq 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tp 5) (hp 4), mul_nonneg (tq 4) (hp 4), mul_nonneg (tq 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tp 6) (hp 3), mul_nonneg (tp 5) (hp 3), mul_nonneg (tp 4) (hp 3), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tq 7) (hp 2), mul_nonneg (tp 6) (hp 2), mul_nonneg (tp 5) (hp 2), mul_nonneg (tp 4) (hp 2), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tq 7) (hp 1), mul_nonneg (tp 6) (hp 1), mul_nonneg (tp 5) (hp 1), mul_nonneg (tp 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tq 7, tp 6, tp 5, tp 4, tp 3, tq 2, tq 1, hu 10, hu 9, hl 8, hl 7, hl 6, hl 5, hl 4, hl 3, hl 2, hl 1]

/-- **The first beta derivative at `b = x`** is positive. -/
theorem hl2cb_G1_base {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) : 0 < hl2cbG1 x a x := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have e := hl2cb_NG_id (a := a) (by linarith : (1 : ℝ) < x) (by linarith)
  have hP := hl2cb_NG_pos (h := x - 2) (c := a - 1) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hx1 : 0 < x - 1 := by linarith
  have h2 : 0 < 19200 * a * (a + x) ^ 2 * (x - 1) * (1 + x) ^ 2 * hl2cK x a ^ 3 := by positivity
  rw [← e] at hP
  exact pos_of_mul_pos_right hP h2.le

/-- **The second beta derivative at `b = x`** is positive. -/
theorem hl2cb_H1_base {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) : 0 < hl2cbH1 x a x := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have e := hl2cb_NH_id (a := a) (by linarith : (1 : ℝ) < x) (by linarith)
  have hP := hl2cb_NH_pos (h := x - 2) (c := a - 1) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hx1 : 0 < x - 1 := by linarith
  have h2 : 0 < 38400 * a * (a + x) ^ 2 * (x - 1) * (1 + x) ^ 2 * hl2cK x a ^ 2 := by positivity
  rw [← e] at hP
  exact pos_of_mul_pos_right hP h2.le

end SmoothedOctagon

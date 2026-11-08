module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaDefs
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecipPoly

/-!
# S2 hand signs: the central beta monotonicity, coefficient signs

The coefficient bounds behind the central beta monotonicity, each through an explicit polynomial
identity and a termwise bound of its monomials: `0 < J < 1/50`, `p_c > 0` (`P_c(r, t)`,
`r = 4/3 - a`, `t = x - 13/6`),
`6p₃B_max + 2p₂ > 1/10` (`P_G`), `A₁ > 9/2` (`P_A`), `P_c > -2J` (`P_H`), the last three in
`c = a - 1`, `h = x - 2`.

## Main API

* `hl2cb_J_pos`, `hl2cb_J_lt`.
* `hl2cbPcc`, `hl2cb_pc_pos`; `hl2cbPG`, `hl2cb_curv`; `hl2cbPA`, `hl2cb_A1`; `hl2cbPH`,
  `hl2cb_Pc`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `J > 0`. -/
theorem hl2cb_J_pos {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) : 0 < hl2cbJ x := by
  unfold hl2cbJ
  apply div_pos _ (by positivity)
  apply mul_pos (by linarith)
  nlinarith

/-- `J < 1/50` (`9600S²(1/50 - J) = 1075 - 843v - 1827v² - 677v³`, `v = x - 2`). -/
theorem hl2cb_J_lt {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) : hl2cbJ x < 1 / 50 := by
  unfold hl2cbJ
  rw [div_lt_iff₀ (by positivity)]
  obtain ⟨hp, -, -, hu, -⟩ := hl2_box (h := x - 2) (t := 0) (hl := 1 / 6) (hu := 2 / 5)
    (tu := 0) (by linarith) (by linarith) (by norm_num) le_rfl le_rfl
  have e : 1 / 50 * (9600 * (1 + x) ^ 2) - (x - 1) * (680 * (x - 1) ^ 2 - 3 * (1 + x) ^ 2) =
      1075 - 843 * (x - 2) - 1827 * (x - 2) ^ 2 - 677 * (x - 2) ^ 3 := by ring
  nlinarith [hu 1, hu 2, hu 3]

/-! ## The beta-pole residue `p_c` -/

/-- `P_c(r, t) = 419904(2aK³p_c/J)`, `r = 4/3 - a`, `t = x - 13/6` (the cleared beta-pole
residue); arguments in the order `(t, r)`. -/
noncomputable def hl2cbPcc (t r : ℝ) : ℝ :=
  (1119744 * t ^ 7 + 26780544 * t ^ 6 + 250387200 * t ^ 5 + 1173100320 * t ^ 4 + 2866310496 * t ^ 3 + 3368723400 * t ^ 2 + 1484854560 * t + 14128078) +
    (-839808 * t ^ 7 - 19455552 * t ^ 6 - 160893216 * t ^ 5 - 552449808 * t ^ 4 - 358646616 * t ^ 3 + 2213193780 * t ^ 2 + 4285560618 * t + 2005349277) * r +
    (-13436928 * t ^ 5 - 210231936 * t ^ 4 - 1244953152 * t ^ 3 - 3211106976 * t ^ 2 - 2832178608 * t - 369824976) * r ^ 2 +
    (1679616 * t ^ 5 + 25754112 * t ^ 4 + 131989824 * t ^ 3 + 128545056 * t ^ 2 - 729806112 * t - 837538056) * r ^ 3 +
    (4898880 * t ^ 3 + 72573408 * t ^ 2 + 312256944 * t + 166238568) * r ^ 4 +
    (-419904 * t ^ 3 - 6508512 * t ^ 2 - 28588464 * t + 20748312) * r ^ 5 +
    (-7698240) * r ^ 6 +
    (419904) * r ^ 7

/-- The identity `419904 · 2aK³p_c = J P_c(4/3 - a, x - 13/6)`. -/
theorem hl2cb_pc_id {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    419904 * (2 * a * hl2cK x a ^ 3 * hl2cbpc x a) =
      hl2cbJ x * hl2cbPcc (x - 13 / 6) (4 / 3 - a) := by
  have hK := (hl2cb_K_pos (a := a) hx).ne'
  unfold hl2cbpc hl2cbcb hl2cbce hl2cbcv hl2cbl
  field_simp
  unfold hl2cbPcc hl2cK
  ring

/-- The termwise bound of the residue: `P_c(r, t) ≥ P_c(0, t) + rL_c(t) > 0`. -/
theorem hl2cb_Pcc_pos {t r : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 7 / 30) (hr : 0 ≤ r) (hr' : r ≤ 1 / 3) :
    0 < hl2cbPcc t r := by
  have hp : ∀ n : ℕ, 0 ≤ t ^ n := fun n => pow_nonneg ht n
  have tq : ∀ n : ℕ, 0 ≤ (7 / 30) ^ n - t ^ n := fun n => sub_nonneg.2 (pow_le_pow_left₀ ht ht' n)
  have rp : ∀ n : ℕ, 0 ≤ r ^ n := fun n => pow_nonneg hr n
  have rr : ∀ n : ℕ, 0 ≤ r * (1 / 3) ^ n - r ^ (n + 1) := fun n => by
    rw [pow_succ']
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hr' n) hr)
  unfold hl2cbPcc
  linarith [hp 7, hp 6, mul_nonneg (rp 3) (hp 5), mul_nonneg (rr 1) (hp 5), hp 5, mul_nonneg (rp 3) (hp 4), mul_nonneg (rr 1) (hp 4), hp 4, mul_nonneg (rr 4) (hp 3), mul_nonneg (rp 4) (hp 3), mul_nonneg (rp 3) (hp 3), mul_nonneg (rr 1) (hp 3), hp 3, mul_nonneg (rr 4) (hp 2), mul_nonneg (rp 4) (hp 2), mul_nonneg (rp 3) (hp 2), mul_nonneg (rr 1) (hp 2), hp 2, mul_nonneg (rr 4) (hp 1), mul_nonneg (rp 4) (hp 1), mul_nonneg (rr 2) (hp 1), mul_nonneg (rr 1) (hp 1), hp 1, rp 7, rr 5, rp 5, rp 4, rr 2, rr 1, mul_nonneg (rp 1) (hp 1), mul_nonneg (rp 1) (hp 2), mul_nonneg (rp 1) (tq 3), mul_nonneg (rp 1) (tq 4), mul_nonneg (rp 1) (tq 5), mul_nonneg (rp 1) (tq 6), mul_nonneg (rp 1) (tq 7), rp 1]

/-- **`p_c > 0`**, from the identity `hl2cb_pc_id` and `P_c > 0`. -/
theorem hl2cb_pc_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    0 < hl2cbpc x a := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have e := hl2cb_pc_id (a := a) (by linarith : (0 : ℝ) < x) (by linarith)
  have hP := hl2cb_Pcc_pos (t := x - 13 / 6) (r := 4 / 3 - a) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hJ := hl2cb_J_pos hx hx2
  have h2 : 0 < 419904 * (2 * a * hl2cK x a ^ 3) := by positivity
  have : 0 < 419904 * (2 * a * hl2cK x a ^ 3) * hl2cbpc x a := by
    rw [mul_assoc, e]; positivity
  exact pos_of_mul_pos_right this h2.le

/-! ## The curvature of the first test -/

/-- `P_G(c, h) = 19200S²K³(6p₃B_max + 2p₂ - 1/10)`, `B_max = a + x + 7(a - 1)/8` (the curvature
identity). -/
noncomputable def hl2cbPG (h c : ℝ) : ℝ :=
  (-1920 * h ^ 8 - 46080 * h ^ 7 + 44268 * h ^ 6 + 3376688 * h ^ 5 + 19886188 * h ^ 4 + 53826080 * h ^ 3 + 78279908 * h ^ 2 + 59575216 * h + 18031940) +
    (55596 * h ^ 6 - 1370620 * h ^ 5 - 18237705 * h ^ 4 - 78889760 * h ^ 3 - 156043642 * h ^ 2 - 145233924 * h - 55231433) * c +
    (-5760 * h ^ 6 - 170796 * h ^ 5 + 148427 * h ^ 4 + 12027610 * h ^ 3 + 57543720 * h ^ 2 + 94427186 * h + 42329773) * c ^ 2 +
    (-23040 * h ^ 4 + 881306 * h ^ 3 + 3633501 * h ^ 2 - 4939536 * h - 21553975) * c ^ 3 +
    (-5760 * h ^ 4 - 69120 * h ^ 3 - 1738665 * h ^ 2 - 9187830 * h - 13315185) * c ^ 4 +
    (-11520 * h ^ 2 - 69120 * h - 103680) * c ^ 5 +
    (-1920 * h ^ 2 - 11520 * h - 17280) * c ^ 6

theorem hl2cb_PG_id {x a : ℝ} (hx : 0 < x) :
    19200 * (1 + x) ^ 2 * hl2cK x a ^ 3 *
        (6 * hl2cbp3 x a * (a + x + 7 * (a - 1) / 8) + 2 * hl2cbp2 x a - 1 / 10) =
      hl2cbPG (x - 2) (a - 1) := by
  have hK := (hl2cb_K_pos (a := a) hx).ne'
  have hS : 1 + x ≠ 0 := by linarith
  unfold hl2cbp3 hl2cbp2 hl2cbl hl2cbc2 hl2cbc1 hl2cbD0 hl2cbEf hl2cbJ hl2cbd
  field_simp
  unfold hl2cbPG hl2cK
  ring

theorem hl2cb_PG_pos {h c : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (hc : 0 ≤ c) (hc' : c ≤ 1 / 3) :
    0 < hl2cbPG h c := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) hc hc'
  unfold hl2cbPG
  linarith [mul_nonneg (tq 2) (hp 6), mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tq 4) (hp 4), mul_nonneg (tq 3) (hp 4), mul_nonneg (tp 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tq 4) (hp 3), mul_nonneg (tp 3) (hp 3), mul_nonneg (tp 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tq 6) (hp 2), mul_nonneg (tq 5) (hp 2), mul_nonneg (tq 4) (hp 2), mul_nonneg (tp 3) (hp 2), mul_nonneg (tp 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tq 6) (hp 1), mul_nonneg (tq 5) (hp 1), mul_nonneg (tq 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tp 2) (hp 1), mul_nonneg (tq 1) (hp 1), tq 6, tq 5, tq 4, tq 3, tp 2, tq 1, hu 8, hu 7, hl 6, hl 5, hl 4, hl 3, hl 2, hl 1]

/-- **The polynomial curvature of the first test**: `6p₃B_max + 2p₂ > 1/10`. -/
theorem hl2cb_curv {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    1 / 10 < 6 * hl2cbp3 x a * (a + x + 7 * (a - 1) / 8) + 2 * hl2cbp2 x a := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have e := hl2cb_PG_id (a := a) (by linarith : (0 : ℝ) < x)
  have hP := hl2cb_PG_pos (h := x - 2) (c := a - 1) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h2 : 0 < 19200 * (1 + x) ^ 2 * hl2cK x a ^ 3 := by positivity
  rw [← e] at hP
  have := pos_of_mul_pos_right hP h2.le
  linarith

/-! ## The coefficients of the second test -/

/-- `P_A(c, h) = 9600aS²K(A₁ - 9/2)`. -/
noncomputable def hl2cbPA (h c : ℝ) : ℝ :=
  (1354 * h ^ 7 + 30920 * h ^ 6 + 300518 * h ^ 5 + 1605372 * h ^ 4 + 4874158 * h ^ 3 + 7942376 * h ^ 2 + 5741954 * h + 801524) +
    (4117 * h ^ 6 + 65884 * h ^ 5 + 456281 * h ^ 4 + 1457140 * h ^ 3 + 1587715 * h ^ 2 - 1403536 * h - 3042225) * c +
    (-2397 * h ^ 5 - 9235 * h ^ 4 - 59520 * h ^ 3 - 574224 * h ^ 2 - 1935619 * h - 2047677) * c ^ 2 +
    (-29489 * h ^ 3 - 237303 * h ^ 2 - 635775 * h - 562361) * c ^ 3 +
    (9603 * h ^ 2 + 57618 * h + 86427) * c ^ 4

theorem hl2cb_PA_id {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    9600 * a * (1 + x) ^ 2 * hl2cK x a * (hl2cbA1 x a - 9 / 2) = hl2cbPA (x - 2) (a - 1) := by
  have hK := (hl2cb_K_pos (a := a) hx).ne'
  have hS : 1 + x ≠ 0 := by linarith
  unfold hl2cbA1 hl2cbc0 hl2cbcv hl2cbM hl2cbD0 hl2cbEf hl2cbJ hl2cbd
  field_simp
  unfold hl2cbPA hl2cK
  ring

theorem hl2cb_PA_pos {h c : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (hc : 0 ≤ c) (hc' : c ≤ 1 / 3) :
    0 < hl2cbPA h c := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) hc hc'
  unfold hl2cbPA
  linarith [mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tp 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tq 3, tq 2, tq 1, hl 7, hl 6, hl 5, hl 4, hl 3, hl 2, hl 1]

/-- **`A₁ > 9/2`**. -/
theorem hl2cb_A1 {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    9 / 2 < hl2cbA1 x a := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have e := hl2cb_PA_id (a := a) (by linarith : (0 : ℝ) < x) (by linarith)
  have hP := hl2cb_PA_pos (h := x - 2) (c := a - 1) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h2 : 0 < 9600 * a * (1 + x) ^ 2 * hl2cK x a := by positivity
  rw [← e] at hP
  have := pos_of_mul_pos_right hP h2.le
  linarith

/-- `P_H(c, h) = 4aK²(P_c/J + 2)`. -/
noncomputable def hl2cbPH (h c : ℝ) : ℝ :=
  (-4 * h ^ 5 - 44 * h ^ 4 - 172 * h ^ 3 - 252 * h ^ 2 + 232) +
    (12 * h ^ 4 + 128 * h ^ 3 + 552 * h ^ 2 + 1152 * h + 1020) * c +
    (-9 * h ^ 3 - 17 * h ^ 2 + 141 * h + 421) * c ^ 2 +
    (-h ^ 3 + 11 * h ^ 2 + 93 * h + 249) * c ^ 3 +
    49 * c ^ 4 +
    9 * c ^ 5

theorem hl2cb_PH_id {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    4 * a * hl2cK x a ^ 2 * (hl2cbPc x a + 2 * hl2cbJ x) = hl2cbJ x * hl2cbPH (x - 2) (a - 1) := by
  have hK := (hl2cb_K_pos (a := a) hx).ne'
  unfold hl2cbPc hl2cbcb hl2cbce hl2cbcv
  field_simp
  unfold hl2cbPH hl2cK
  ring

theorem hl2cb_PH_pos {h c : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (hc : 0 ≤ c) (hc' : c ≤ 1 / 3) :
    0 < hl2cbPH h c := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := hl2_box hh hh' (by norm_num) hc hc'
  unfold hl2cbPH
  linarith [mul_nonneg (tp 1) (hp 4), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tp 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tp 1) (hp 2), mul_nonneg (tp 3) (hp 1), mul_nonneg (tp 2) (hp 1), mul_nonneg (tp 1) (hp 1), tp 5, tp 4, tp 3, tp 2, tp 1, hu 5, hu 4, hu 3, hu 2]

/-- **`P_c > -2J`**. -/
theorem hl2cb_Pc {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    -(2 * hl2cbJ x) < hl2cbPc x a := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have e := hl2cb_PH_id (a := a) (by linarith : (0 : ℝ) < x) (by linarith)
  have hP := hl2cb_PH_pos (h := x - 2) (c := a - 1) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hJ := hl2cb_J_pos hx hx2
  have h2 : 0 < 4 * a * hl2cK x a ^ 2 := by positivity
  have : 0 < 4 * a * hl2cK x a ^ 2 * (hl2cbPc x a + 2 * hl2cbJ x) := by rw [e]; positivity
  have := pos_of_mul_pos_right this h2.le
  linarith

end SmoothedOctagon

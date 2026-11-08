module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOA1

/-!
# Gate S1 by hand, outer face, branch A: the test `F₀`

On `3/2 ≤ x ≤ 2`, `6/5 ≤ α ≤ x`, `24/43 ≤ C ≤ 10/13`:

* norm concavity reduces `u` to `3/4`, `19/25`;
* at these norms the reciprocal-shape curvature of `F₀` is at most `M₀ + 7/648 < 0` for every
  `C` of the interval (`p₄ ≤ 0`, `4p₄/x + p₃ ≤ 0`, `(e/Z)²(1 - 2/Z) ≤ 4/27`), so
  `α ∈ {6/5, x}`;
* at `α = 6/5`, `F₀` decreases in `β` (`hl1o_F0_bmono`): raise `C` to `10/13`;
* at `α = x`, `w` and `E_L` do not depend on `β`: `F₀ = Ψ(x, u) - c[(u - 1)Z + 1/Z + ℓ(2Z/7)]`
  (`hl1o_F0_diag`); `F₀(19/25) ≥ F₀(3/4)`, and at `u = 3/4` the bracket decreases in `Z`
  (`-1/4 - 1/Z² + 1/Z = -(Z - 2)²/(4Z²)`), so `C = 24/43`;
* the three terminal curves are positive.

The curvature bound `M₀ < -7/648` is proved for all `C` at once by a two-variable sign in
`(x, C)`; the terminal curves are cleared and bounded termwise.

## Main API

* `hl1oPsi`, `hl1o_F0_diag`, `hl1_phiZ_anti`, `hl1o_A_recip0`, `hl1o_A_F0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The `β`-independent part of `F₀` on the diagonal `α = x`. -/
noncomputable def hl1oPsi (x u : ℝ) : ℝ :=
  hh1oG x x u - 7 / 96 * (2 * hh1ow x x x u - 1 / 2 - 1 / 7 - hh1oEL x x x u) - 9193 / 50000

/-- On the diagonal `α = x` only `Z = (α + β)/α` depends on `β`. -/
theorem hl1o_F0_diag (x b u : ℝ) :
    hh1oF0 x x b u = hl1oPsi x u - 7 / 96 * ((u - 1) * ((x + b) / x) + x / (x + b) +
      hh1ell (hh1oy x b)) := by
  have hD : hsDg x b x = hsDg x x x := by unfold hsDg; ring
  have hw : hh1ow x x b u = hh1ow x x x u := by simp only [hh1ow, hh1od, hD]
  have hE : hh1oEL x x b u = hh1oEL x x x u := by simp only [hh1oEL, hh1od, hD]
  unfold hh1oF0 hh1oR2 hl1oPsi
  rw [hw, hE]
  ring

/-- The numerator of `-(M₀ + 7/648)` at `u = 3 / 4`, `x = 3/2 + t`, `C = 24/43 + c`. -/
noncomputable def hl1PM0f (t c : ℝ) : ℝ :=
  -1 / 56 * t ^ 7 + 1 / 56 * t ^ 6 * c ^ 2 + 177 / 2408 * t ^ 6 * c - 713113 / 4970112 * t ^ 6 + 9 / 56 * t ^ 5 * c ^ 2 + 9773 / 14448 * t ^ 5 * c - 1654391 / 4970112 * t ^ 5 + 127 / 224 * t ^ 4 * c ^ 2 + 2453 / 1032 * t ^ 4 * c + 57716417 / 536772096 * t ^ 4 + 111 / 112 * t ^ 3 * c ^ 2 + 113969 / 28896 * t ^ 3 * c + 397245365 / 268386048 * t ^ 3 + 799 / 896 * t ^ 2 * c ^ 2 + 346267 / 115584 * t ^ 2 * c + 648060017 / 306726912 * t ^ 2 + 345 / 896 * t * c ^ 2 + 51739 / 77056 * t * c + 781763813 / 715696128 * t + 225 / 3584 * c ^ 2 - 12015 / 77056 * c + 132171779 / 954261504



theorem hl1PM0f_pos {t c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 2 : ℝ)) (hc0 : 0 ≤ c) (hc1 : c ≤ (118 / 559 : ℝ)) :
    (0 : ℝ) < hl1PM0f t c := by
  unfold hl1PM0f
  nlinarith [hc1,
    (by positivity : (0 : ℝ) ≤ c ^ 2),
    (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t * c),
    (by positivity : (0 : ℝ) ≤ t * c ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * c ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 6)]



theorem hl1o_A_M0_f {x C : ℝ} (hx : 3 / 2 ≤ x) :
    12 * hl1p4 x C (3 / 4) / x ^ 2 + 6 * hl1p3 x C (3 / 4) / x + 2 * hl1p2 x C (3 / 4) + 7 / 648 =
      -(hl1PM0f (x - 3 / 2) (C - 24 / 43)) / (x ^ 2 * (x + 1) ^ 2) := by
  have h1 : x ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x + 1 ≠ 0 := by linarith
  simp only [hl1p2, hl1p3, hl1p4, hl1g2, hl1g4, hl1W2, hl1W3, hl1W4, hl1d0, hl1d1, hl1d2, hl1J2, hsE0, hl1PM0f]
  field_simp
  ring


/-- The numerator of `-(M₀ + 7/648)` at `u = 19 / 25`, `x = 3/2 + t`, `C = 24/43 + c`. -/
noncomputable def hl1PM0v (t c : ℝ) : ℝ :=
  -3 / 175 * t ^ 7 + 19 / 1050 * t ^ 6 * c ^ 2 + 332 / 4515 * t ^ 6 * c - 12925001 / 97072500 * t ^ 6 + 57 / 350 * t ^ 5 * c ^ 2 + 12167 / 18060 * t ^ 5 * c - 26458363 / 97072500 * t ^ 5 + 2413 / 4200 * t ^ 4 * c ^ 2 + 141507 / 60200 * t ^ 4 * c + 1533048569 / 5241915000 * t ^ 4 + 703 / 700 * t ^ 3 * c ^ 2 + 46341 / 12040 * t ^ 3 * c + 236286556 / 131047875 * t ^ 3 + 15181 / 16800 * t ^ 2 * c ^ 2 + 340791 / 120400 * t ^ 2 * c + 4086026311 / 1677412800 * t ^ 2 + 437 / 1120 * t * c ^ 2 + 51369 / 96320 * t * c + 17701291 / 13978440 * t + 57 / 896 * c ^ 2 - 7713 / 38528 * c + 2662853 / 14910336



theorem hl1PM0v_pos {t c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 2 : ℝ)) (hc0 : 0 ≤ c) (hc1 : c ≤ (118 / 559 : ℝ)) :
    (0 : ℝ) < hl1PM0v t c := by
  unfold hl1PM0v
  nlinarith [hc1,
    (by positivity : (0 : ℝ) ≤ c ^ 2),
    (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t * c),
    (by positivity : (0 : ℝ) ≤ t * c ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * c ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * c ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * c),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * c ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 6)]



theorem hl1o_A_M0_v {x C : ℝ} (hx : 3 / 2 ≤ x) :
    12 * hl1p4 x C (19 / 25) / x ^ 2 + 6 * hl1p3 x C (19 / 25) / x + 2 * hl1p2 x C (19 / 25) + 7 / 648 =
      -(hl1PM0v (x - 3 / 2) (C - 24 / 43)) / (x ^ 2 * (x + 1) ^ 2) := by
  have h1 : x ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x + 1 ≠ 0 := by linarith
  simp only [hl1p2, hl1p3, hl1p4, hl1g2, hl1g4, hl1W2, hl1W3, hl1W4, hl1d0, hl1d1, hl1d2, hl1J2, hsE0, hl1PM0v]
  field_simp
  ring


theorem hl1o_A_Dpsi_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 49 / 160000 * z ^ 8 + 1247 / 280000 * z ^ 7 + 149707 / 5460000 * z ^ 6 + 680619 / 7280000 * z ^ 5 + 203084057 / 1048320000 * z ^ 4 + 26343637 / 104832000 * z ^ 3 + 844189 / 4193280 * z ^ 2 + 775613 / 8386560 * z + 1021675 / 53673984 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7),
    (by positivity : (0 : ℝ) ≤ z ^ 8)]

theorem hl1o_A_Dpsi_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (hl1oPsi x (19 / 25) - hl1oPsi x (3 / 4) - 7 / 9600 * (2 + 10 / 13 * (x - 1) / x)) - (0 : ℝ) = (49 / 160000 * (x - (3 / 2 : ℝ)) ^ 8 + 1247 / 280000 * (x - (3 / 2 : ℝ)) ^ 7 + 149707 / 5460000 * (x - (3 / 2 : ℝ)) ^ 6 + 680619 / 7280000 * (x - (3 / 2 : ℝ)) ^ 5 + 203084057 / 1048320000 * (x - (3 / 2 : ℝ)) ^ 4 + 26343637 / 104832000 * (x - (3 / 2 : ℝ)) ^ 3 + 844189 / 4193280 * (x - (3 / 2 : ℝ)) ^ 2 + 775613 / 8386560 * (x - (3 / 2 : ℝ)) + 1021675 / 53673984) / ((x + 1) ^ 2 * (x) ^ 4) := by
  simp only [hl1oPsi, hh1oG, hh1ow, hh1oEL, hh1oL, hh1od, hh1ov, hh1oE, hh1oK, hsDg]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : x ≠ 0 := by nlinarith
  have hd6 : x * 1 + 0 ≠ 0 := by nlinarith
  have hd7 : 0 + x * 1 ≠ 0 := by nlinarith
  have hd8 : 0 + 1 * x ≠ 0 := by nlinarith
  have hd9 : x + 0 ≠ 0 := by nlinarith
  field_simp
  ring

theorem hl1o_A_Dpsi {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < (hl1oPsi x (19 / 25) - hl1oPsi x (3 / 4) - 7 / 9600 * (2 + 10 / 13 * (x - 1) / x)) := by
  have hid := hl1o_A_Dpsi_id h0 h1
  have hn := hl1o_A_Dpsi_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < x := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (x) ^ 4 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 4))
  have : 0 < (hl1oPsi x (19 / 25) - hl1oPsi x (3 / 4) - 7 / 9600 * (2 + 10 / 13 * (x - 1) / x)) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem hl1o_A_F0x_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -7778141855 / 256 * z ^ 12 - 507671487803 / 896 * z ^ 11 - 1305297851030702663 / 288960000 * z ^ 10 - 29110092645231066449 / 1444800000 * z ^ 9 - 1891574239335339905449 / 34675200000 * z ^ 8 - 760741472552137074773 / 8668800000 * z ^ 7 - 241090730109821774327 / 3852800000 * z ^ 6 + 1784934342782083547857 / 34675200000 * z ^ 5 + 100666213120195833454343 / 554803200000 * z ^ 4 + 19730475804996935322901 / 92467200000 * z ^ 3 + 396262890765880516269 / 2867200000 * z ^ 2 + 1211682372709283583237 / 24657920000 * z + 297729848195624142729 / 39452672000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem hl1o_A_F0x_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    hh1oF0 x (x) (x + 24 / 43 * (x - 1)) (3 / 4) - (0 : ℝ) = (-7778141855 / 256 * (x - (3 / 2 : ℝ)) ^ 12 - 507671487803 / 896 * (x - (3 / 2 : ℝ)) ^ 11 - 1305297851030702663 / 288960000 * (x - (3 / 2 : ℝ)) ^ 10 - 29110092645231066449 / 1444800000 * (x - (3 / 2 : ℝ)) ^ 9 - 1891574239335339905449 / 34675200000 * (x - (3 / 2 : ℝ)) ^ 8 - 760741472552137074773 / 8668800000 * (x - (3 / 2 : ℝ)) ^ 7 - 241090730109821774327 / 3852800000 * (x - (3 / 2 : ℝ)) ^ 6 + 1784934342782083547857 / 34675200000 * (x - (3 / 2 : ℝ)) ^ 5 + 100666213120195833454343 / 554803200000 * (x - (3 / 2 : ℝ)) ^ 4 + 19730475804996935322901 / 92467200000 * (x - (3 / 2 : ℝ)) ^ 3 + 396262890765880516269 / 2867200000 * (x - (3 / 2 : ℝ)) ^ 2 + 1211682372709283583237 / 24657920000 * (x - (3 / 2 : ℝ)) + 297729848195624142729 / 39452672000) /
      ((55 * x - 12) * (x + 1) ^ 2 * (521 * x - 48) ^ 3 * (x) ^ 4) := by
  rw [hl1o_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (x) + (x + 24 / 43 * (x - 1)) = (55 * x - 12) / (43 / 2 : ℝ) by ring,
    show 2 * ((55 * x - 12) / (43 / 2 : ℝ)) + 7 * (x) = (521 * x - 48) / (43 : ℝ) by ring]
  simp only [hl1oM, hl1oJ, hh1oK, hsE0, hsDg]
  have hd0 : 55 * x - 12 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 521 * x - 48 ≠ 0 := by nlinarith
  have hd3 : x ≠ 0 := by nlinarith
  have hp0 : 55 * x - 12 ≠ 0 := by nlinarith
  have hq0 : 521 * x - 48 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 55 * x - 12 = p at hp0 ⊢
  generalize hq : 521 * x - 48 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem hl1o_A_F0x {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < hh1oF0 x (x) (x + 24 / 43 * (x - 1)) (3 / 4) := by
  have hid := hl1o_A_F0x_id h0 h1
  have hn := hl1o_A_F0x_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 55 * x - 12 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 521 * x - 48 := by nlinarith
  have hP3 : 0 < x := by nlinarith
  have hD : 0 < (55 * x - 12) * (x + 1) ^ 2 * (521 * x - 48) ^ 3 * (x) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < hh1oF0 x (x) (x + 24 / 43 * (x - 1)) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem hl1o_A_F065f_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -11156640625 / 145152 * z ^ 10 - 2051689046875 / 870912 * z ^ 9 - 351683964750625 / 11943936 * z ^ 8 - 2312178863960875 / 11943936 * z ^ 7 - 607307695806831337 / 836075520 * z ^ 6 - 174753814468458940789 / 108689817600 * z ^ 5 - 7827578597775082678039 / 3532419072000 * z ^ 4 - 8647996122389986776293 / 4037050368000 * z ^ 3 - 224105348790354536826097 / 201852518400000 * z ^ 2 + 64273130481907810918931 / 80741007360000 * z + 52682383994788751307181 / 64592805888000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem hl1o_A_F065f_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) - (0 : ℝ) = (-11156640625 / 145152 * (x - (3 / 2 : ℝ)) ^ 10 - 2051689046875 / 870912 * (x - (3 / 2 : ℝ)) ^ 9 - 351683964750625 / 11943936 * (x - (3 / 2 : ℝ)) ^ 8 - 2312178863960875 / 11943936 * (x - (3 / 2 : ℝ)) ^ 7 - 607307695806831337 / 836075520 * (x - (3 / 2 : ℝ)) ^ 6 - 174753814468458940789 / 108689817600 * (x - (3 / 2 : ℝ)) ^ 5 - 7827578597775082678039 / 3532419072000 * (x - (3 / 2 : ℝ)) ^ 4 - 8647996122389986776293 / 4037050368000 * (x - (3 / 2 : ℝ)) ^ 3 - 224105348790354536826097 / 201852518400000 * (x - (3 / 2 : ℝ)) ^ 2 + 64273130481907810918931 / 80741007360000 * (x - (3 / 2 : ℝ)) + 52682383994788751307181 / 64592805888000) /
      ((65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3) := by
  rw [hl1o_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 10 / 13 * (6 / 5 - 1)) = (65 * x + 88) / (65 : ℝ) by ring,
    show 2 * ((65 * x + 88) / (65 : ℝ)) + 7 * (6 / 5) = (65 * x + 361) / (65 / 2 : ℝ) by ring]
  simp only [hl1oM, hl1oJ, hh1oK, hsE0, hsDg]
  have hd0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 65 * x + 361 ≠ 0 := by nlinarith
  have hp0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hq0 : 65 * x + 361 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 65 * x + 88 = p at hp0 ⊢
  generalize hq : 65 * x + 361 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem hl1o_A_F065f {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) := by
  have hid := hl1o_A_F065f_id h0 h1
  have hn := hl1o_A_F065f_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 65 * x + 88 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 65 * x + 361 := by nlinarith
  have hD : 0 < (65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem hl1o_A_F065v_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -8479046875 / 108864 * z ^ 10 - 65112214375 / 27216 * z ^ 9 - 1451805644029 / 48384 * z ^ 8 - 36004664465341 / 181440 * z ^ 7 - 98318092586355121 / 130636800 * z ^ 6 - 28880624606424599 / 16982784 * z ^ 5 - 1790336835888900239467 / 735920640000 * z ^ 4 - 38908834383138038077 / 15769728000 * z ^ 3 - 4387001032259079183523 / 3153945600000 * z ^ 2 + 3070192109139913933 / 4380480000 * z + 7775831293792566613 / 9345024000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem hl1o_A_F065v_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) - (0 : ℝ) = (-8479046875 / 108864 * (x - (3 / 2 : ℝ)) ^ 10 - 65112214375 / 27216 * (x - (3 / 2 : ℝ)) ^ 9 - 1451805644029 / 48384 * (x - (3 / 2 : ℝ)) ^ 8 - 36004664465341 / 181440 * (x - (3 / 2 : ℝ)) ^ 7 - 98318092586355121 / 130636800 * (x - (3 / 2 : ℝ)) ^ 6 - 28880624606424599 / 16982784 * (x - (3 / 2 : ℝ)) ^ 5 - 1790336835888900239467 / 735920640000 * (x - (3 / 2 : ℝ)) ^ 4 - 38908834383138038077 / 15769728000 * (x - (3 / 2 : ℝ)) ^ 3 - 4387001032259079183523 / 3153945600000 * (x - (3 / 2 : ℝ)) ^ 2 + 3070192109139913933 / 4380480000 * (x - (3 / 2 : ℝ)) + 7775831293792566613 / 9345024000) /
      ((65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3) := by
  rw [hl1o_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 10 / 13 * (6 / 5 - 1)) = (65 * x + 88) / (65 : ℝ) by ring,
    show 2 * ((65 * x + 88) / (65 : ℝ)) + 7 * (6 / 5) = (65 * x + 361) / (65 / 2 : ℝ) by ring]
  simp only [hl1oM, hl1oJ, hh1oK, hsE0, hsDg]
  have hd0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 65 * x + 361 ≠ 0 := by nlinarith
  have hp0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hq0 : 65 * x + 361 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 65 * x + 88 = p at hp0 ⊢
  generalize hq : 65 * x + 361 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem hl1o_A_F065v {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) := by
  have hid := hl1o_A_F065v_id h0 h1
  have hn := hl1o_A_F065v_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 65 * x + 88 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 65 * x + 361 := by nlinarith
  have hD : 0 < (65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith

/-- `φ(Z) = -Z/4 + 1/Z + ℓ(2Z/7)` decreases for `Z ≥ 2`. -/
theorem hl1_phiZ_anti {Z1 Z2 : ℝ} (h1 : 2 ≤ Z1) (h12 : Z1 ≤ Z2) :
    -(Z2 / 4) + 1 / Z2 + hh1ell (2 * Z2 / 7) ≤ -(Z1 / 4) + 1 / Z1 + hh1ell (2 * Z1 / 7) := by
  have key := ss_le_of_deriv (f := fun Z => -(-(Z / 4) + 1 / Z + hh1ell (2 * Z / 7)))
    (f' := fun Z => -(-(1 / 4) - 1 / Z ^ 2 + hl1ell1 (2 * Z / 7) * (2 / 7))) h12
    (fun Z hZ => by
      have hZ0 : 0 < Z := by linarith [hZ.1]
      have hy : -1 < 2 * Z / 7 := by linarith
      have hl := (hl1_ell_hasDerivAt hy).comp Z (((hasDerivAt_id' Z).const_mul 2).div_const 7)
      have h := ((((hasDerivAt_id' Z).div_const 4).neg).add ((hasDerivAt_const Z (1 : ℝ)).fun_div
        (hasDerivAt_id' Z) hZ0.ne')).add hl
      convert h.neg using 1
      · funext s; simp only [Function.comp_apply, Pi.add_apply, Pi.neg_apply]
      · field_simp; ring)
    (fun Z hZ => by
      have hZ0 : 0 < Z := by linarith [hZ.1]
      have hy : 0 < 2 * Z / 7 := by positivity
      have hl := hl1_ell1_le hy
      have e : 1 / (2 * Z / 7) * (2 / 7) = 1 / Z := by field_simp
      have h2 : hl1ell1 (2 * Z / 7) * (2 / 7) ≤ 1 / Z := by
        rw [← e]; exact mul_le_mul_of_nonneg_right hl (by norm_num)
      have h3 : 0 ≤ 1 / 4 + 1 / Z ^ 2 - 1 / Z := by
        have : 1 / 4 + 1 / Z ^ 2 - 1 / Z = (Z - 2) ^ 2 / (4 * Z ^ 2) := by field_simp; ring
        rw [this]; positivity
      linarith)
  linarith

/-- **Reciprocal-shape concavity of `F₀` on the large shapes**. -/
theorem hl1o_A_recip0 {x a C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha : 6 / 5 ≤ a) (hax : a ≤ x)
    (hC0 : 24 / 43 ≤ C) (hC1 : C ≤ 10 / 13) (hu : u = 3 / 4 ∨ u = 19 / 25) :
    min (hh1oF0 x x (x + C * (x - 1)) u) (hh1oF0 x (6 / 5) (x + C * (6 / 5 - 1)) u) ≤
      hh1oF0 x a (x + C * (a - 1)) u := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < u := by rcases hu with rfl | rfl <;> norm_num
  have hu1 : u ≤ 19 / 25 := by rcases hu with rfl | rfl <;> norm_num
  have hp4 := hl1o_p4_nonpos hx hx2 hC1 hu0.le hu1
  have hp43 := hl1o_p43_nonpos hx hx2 (by linarith) hC1 hu0 hu1
  have hM : 12 * hl1p4 x C u / x ^ 2 + 6 * hl1p3 x C u / x + 2 * hl1p2 x C u + 7 / 648 < 0 := by
    have hD : 0 < x ^ 2 * (x + 1) ^ 2 := by positivity
    rcases hu with rfl | rfl
    · rw [hl1o_A_M0_f hx]
      have := hl1PM0f_pos (t := x - 3 / 2) (c := C - 24 / 43) (by linarith) (by linarith)
        (by linarith) (by linarith)
      have : 0 < hl1PM0f (x - 3 / 2) (C - 24 / 43) / (x ^ 2 * (x + 1) ^ 2) := div_pos this hD
      rw [neg_div]; linarith
    · rw [hl1o_A_M0_v hx]
      have := hl1PM0v_pos (t := x - 3 / 2) (c := C - 24 / 43) (by linarith) (by linarith)
        (by linarith) (by linarith)
      have : 0 < hl1PM0v (x - 3 / 2) (C - 24 / 43) / (x ^ 2 * (x + 1) ^ 2) := div_pos this hD
      rw [neg_div]; linarith
  have hZ : ∀ a' : ℝ, 6 / 5 ≤ a' → a' ≤ x → 0 < 1 + C + (x - C) * (1 / a') := by
    intro a' h1 h2
    have : 0 < (x - C) * (1 / a') := mul_pos (by linarith) (by positivity)
    linarith
  have hrep : ∀ a' : ℝ, 6 / 5 ≤ a' → a' ≤ x → hh1oF0 x a' (x + C * (a' - 1)) u =
      hl1G (hl1p0 x C u) (hl1p1 x C u) (hl1p2 x C u) (hl1p3 x C u) (hl1p4 x C u) (-(7 / 96))
        (1 + C) (x - C) (1 / a') :=
    fun a' h1 h2 => hl1o_F0_rG hx0 (by linarith) rfl (hZ a' h1 h2)
  rw [hrep a ha hax, hrep x (by linarith) le_rfl, hrep (6 / 5) le_rfl (by linarith)]
  apply hl1G_min (one_div_le_one_div_of_le (by linarith) hax)
    (one_div_le_one_div_of_le (by norm_num) ha)
  · intro s hs
    have h1 : 1 / x ≤ s := hs.1
    have hs1 : s ≤ 5 / 6 := by have := hs.2; norm_num at this; exact this
    have hxs : 1 ≤ x * s := by rw [div_le_iff₀ hx0] at h1; linarith
    constructor
    · nlinarith
    · nlinarith
  · intro s hs
    have h1 : 1 / x ≤ s := hs.1
    have hs1 : s ≤ 5 / 6 := by have := hs.2; norm_num at this; exact this
    have hxs : 1 ≤ x * s := by rw [div_le_iff₀ hx0] at h1; linarith
    have hs0 : 1 / 2 ≤ s := by nlinarith
    set Z := 1 + C + (x - C) * s with hZdef
    have hZ2 : 2 ≤ Z := by nlinarith
    have hZ3 : Z ≤ 3 := by nlinarith
    have hZe : 3 / 2 * (x - C) ≤ Z := by nlinarith
    have hZ0 : 0 < Z := by linarith
    have t1 : 6 * hl1p3 x C u * s + 12 * hl1p4 x C u * s ^ 2 ≤
        6 * hl1p3 x C u / x + 12 * hl1p4 x C u / x ^ 2 := by
      have e1 : 6 * hl1p3 x C u / x + 12 * hl1p4 x C u / x ^ 2 =
          6 * hl1p3 x C u * (1 / x) + 12 * hl1p4 x C u * (1 / x) ^ 2 := by ring
      have e2 : 4 * hl1p4 x C u / x = 4 * hl1p4 x C u * (1 / x) := by ring
      rw [e1]
      rw [e2] at hp43
      have hA : 12 * hl1p4 x C u * (s + 1 / x) + 6 * hl1p3 x C u ≤ 0 := by
        nlinarith [mul_le_mul_of_nonpos_left h1 hp4]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤
        -(12 * hl1p4 x C u * (s + 1 / x) + 6 * hl1p3 x C u))]
    have t2 : 2 * -(7 / 96) * (x - C) ^ 2 / Z ^ 3 + 7 / 96 * (x - C) ^ 2 / Z ^ 2 ≤ 7 / 648 := by
      have e : 2 * -(7 / 96) * (x - C) ^ 2 / Z ^ 3 + 7 / 96 * (x - C) ^ 2 / Z ^ 2 =
          7 / 96 * ((x - C) ^ 2 * (Z - 2)) / Z ^ 3 := by field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      have h4 : (x - C) ^ 2 ≤ 4 / 9 * Z ^ 2 := by nlinarith
      have h5 : (x - C) ^ 2 * (Z - 2) ≤ 4 / 9 * Z ^ 2 * (Z / 3) :=
        mul_le_mul h4 (by linarith) (by linarith) (by positivity)
      nlinarith
    nlinarith

/-- **Branch A, `F₀ > 0`.** -/
theorem hl1o_A_F0 {x a b C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha : 6 / 5 ≤ a) (hax : a ≤ x)
    (hC0 : 24 / 43 ≤ C) (hC1 : C ≤ 10 / 13) (hb : b = x + C * (a - 1)) (hu0 : 3 / 4 ≤ u)
    (hu1 : u ≤ 19 / 25) : 0 < hh1oF0 x a b u := by
  have hx0 : 0 < x := by linarith
  -- the face `α = 6/5`
  have h65 : ∀ u', (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < hh1oF0 x (6 / 5) (x + C * (6 / 5 - 1)) u' := by
    intro u' hu'
    have hm := hl1o_F0_bmono (x := x) (a := 6 / 5) (b1 := x + C * (6 / 5 - 1))
      (b2 := x + 10 / 13 * (6 / 5 - 1)) (u := u') hx hx2 (by norm_num) le_rfl (by nlinarith)
      (by nlinarith) (by nlinarith) (by rcases hu' with rfl | rfl <;> norm_num)
    have ht : 0 < hh1oF0 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) u' := by
      rcases hu' with rfl | rfl
      · exact hl1o_A_F065f hx hx2
      · exact hl1o_A_F065v hx hx2
    nlinarith
  -- the face `α = x`
  have hxx : ∀ u', (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < hh1oF0 x x (x + C * (x - 1)) u' := by
    intro u' hu'
    have hZ1 : (x + (x + 24 / 43 * (x - 1))) / x ≤ (x + (x + C * (x - 1))) / x := by
      apply div_le_div_of_nonneg_right _ hx0.le; nlinarith
    have hZ0 : 2 ≤ (x + (x + 24 / 43 * (x - 1))) / x := by
      rw [le_div_iff₀ hx0]; nlinarith
    have hy : ∀ b, hh1oy x b = 2 * ((x + b) / x) / 7 := fun b => by unfold hh1oy; ring
    have hinv : ∀ b, 0 < x + b → x / (x + b) = 1 / ((x + b) / x) := fun b hb => by
      field_simp
    have hmono := hl1_phiZ_anti hZ0 hZ1
    have hb0 : 0 < x + (x + 24 / 43 * (x - 1)) := by nlinarith
    have hbC : 0 < x + (x + C * (x - 1)) := by nlinarith
    have h34 : hh1oF0 x x (x + 24 / 43 * (x - 1)) (3 / 4) ≤ hh1oF0 x x (x + C * (x - 1)) (3 / 4) := by
      rw [hl1o_F0_diag, hl1o_F0_diag, hy, hy, hinv _ hb0, hinv _ hbC]
      nlinarith
    have hT := hl1o_A_F0x hx hx2
    rcases hu' with rfl | rfl
    · linarith
    · -- `F₀(19/25) - F₀(3/4) = Ψ(19/25) - Ψ(3/4) - (7/9600)Z ≥ 0`
      have hD := hl1o_A_Dpsi hx hx2
      have hZu : (x + (x + C * (x - 1))) / x ≤ 2 + 10 / 13 * (x - 1) / x := by
        rw [div_le_iff₀ hx0]
        have : 10 / 13 * (x - 1) / x * x = 10 / 13 * (x - 1) := by field_simp
        nlinarith
      have e : hh1oF0 x x (x + C * (x - 1)) (19 / 25) - hh1oF0 x x (x + C * (x - 1)) (3 / 4) =
          hl1oPsi x (19 / 25) - hl1oPsi x (3 / 4) - 7 / 9600 * ((x + (x + C * (x - 1))) / x) := by
        rw [hl1o_F0_diag, hl1o_F0_diag]; ring
      nlinarith
  -- shape concavity and norm concavity
  have hshape : ∀ u', (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < hh1oF0 x a b u' := by
    intro u' hu'
    have := hl1o_A_recip0 hx hx2 ha hax hC0 hC1 hu'
    rw [hb]
    exact lt_of_lt_of_le (lt_min (hxx u' hu') (h65 u' hu')) this
  have hm := hl1o_F0_umin (x := x) (a := a) (b := b) hu0 hu1 (by positivity : a ≠ 0)
  exact lt_of_lt_of_le (lt_min (hshape _ (Or.inl rfl)) (hshape _ (Or.inr rfl))) hm

end SmoothedOctagon

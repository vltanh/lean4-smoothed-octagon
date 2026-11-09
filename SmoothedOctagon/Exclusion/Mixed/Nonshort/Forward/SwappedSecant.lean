module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Basic

/-!
# Case M2, forward successor by hand: the quantitative swapped-secant bound

In the coordinates `t = (1 - h)/2`,
`c = (1 + h)/2`, `p = c + j` with `0 < j < h ≤ 1/2`,
`Sec(t, c, p) < Sec(t + p - c, p, c)`: after the rational logarithm bounds the difference is
`j𝒫/(6(1 + j)³AC(A + C)(h + j))` (`A = 1 + 2j`, `C = 1 + h + j`) with the cleared polynomial `𝒫`
(`fhSwapP`), positive by a termwise estimate.

## Main API

* `fhSwapP`, `fh_swapP_pos`: the polynomial `𝒫` and its sign.
* `fh_sec_swap_q`: **the stronger secant comparison**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared numerator `𝒫` of the swapped-secant difference. -/
noncomputable def fhSwapP (h j : ℝ) : ℝ :=
  2 * (1 + h) * (3 * (1 + j) ^ 2 + j ^ 2) * (1 + 2 * j) * (1 + h + j) * ((1 + 2 * j) + (1 + h + j))
    - (1 + 2 * h + j) * (1 + j) ^ 3 * ((1 + h + j) ^ 2 + 10 * (1 + h + j) * (1 + 2 * j) + (1 + 2 * j) ^ 2)
    + 3 * (h + j) * (1 - h ^ 2 + 2 * j) * (1 + j) ^ 3 * ((1 + 2 * j) + (1 + h + j))

/-- **The sign of `𝒫`**: `𝒫 ≥ h²/4 + h(2 + 3h/4)j + (67/16)j³ + j⁴/8 > 0` for `0 < j < h ≤ 1/2`. -/
theorem fh_swapP_pos {h j : ℝ} (hh : h ≤ 1 / 2) (hj : 0 < j) (hjh : j < h) : 0 < fhSwapP h j := by
  have h0 : 0 < h := by linarith
  have e : fhSwapP h j = h ^ 2 * (2 - 2 * h - 3 * h ^ 2) + h * (2 + 9 * h - 12 * h ^ 2 - 9 * h ^ 3) * j
      + h * (10 + 14 * h - 28 * h ^ 2 - 9 * h ^ 3) * j ^ 2
      + (-1 + 20 * h + 8 * h ^ 2 - 28 * h ^ 3 - 3 * h ^ 4) * j ^ 3
      + (-7 + 14 * h - 8 * h ^ 2 - 12 * h ^ 3) * j ^ 4 + (-13 - 9 * h ^ 2) * j ^ 5 - 7 * j ^ 6 := by
    unfold fhSwapP; ring
  rw [e]
  have a1 : h ^ 2 / 4 ≤ h ^ 2 * (2 - 2 * h - 3 * h ^ 2) := by
    have : 1 / 4 ≤ 2 - 2 * h - 3 * h ^ 2 := by nlinarith
    nlinarith [sq_nonneg h]
  have a2 : 0 ≤ h * (9 * h - 12 * h ^ 2 - 9 * h ^ 3 - 3 / 4 * h) * j := by
    have : 0 ≤ 9 * h - 12 * h ^ 2 - 9 * h ^ 3 - 3 / 4 * h := by
      have : 0 ≤ 33 / 4 - 12 * h - 9 * h ^ 2 := by nlinarith
      nlinarith
    positivity
  have hj2 : 0 < j ^ 2 := by positivity
  have hj3 : 0 < j ^ 3 := by positivity
  have hj4 : 0 < j ^ 4 := by positivity
  -- the quadratic term and the negative part of the cubic
  have a3 : 67 / 16 * j ^ 3 ≤ h * (10 + 14 * h - 28 * h ^ 2 - 9 * h ^ 3) * j ^ 2
      - (1 + 28 * h ^ 3 + 3 * h ^ 4) * j ^ 3 := by
    have b1 : 71 / 8 ≤ 10 + 14 * h - 28 * h ^ 2 - 9 * h ^ 3 := by nlinarith
    have b2 : 1 + 28 * h ^ 3 + 3 * h ^ 4 ≤ 75 / 16 := by nlinarith
    have b3 : j ^ 3 ≤ h * j ^ 2 := by nlinarith
    have c1 : 71 / 8 * (h * j ^ 2) ≤ h * (10 + 14 * h - 28 * h ^ 2 - 9 * h ^ 3) * j ^ 2 := by
      have := mul_le_mul_of_nonneg_right b1 (by positivity : (0 : ℝ) ≤ h * j ^ 2)
      linarith
    have c2 : (1 + 28 * h ^ 3 + 3 * h ^ 4) * j ^ 3 ≤ 75 / 16 * j ^ 3 :=
      mul_le_mul_of_nonneg_right b2 hj3.le
    nlinarith
  -- the remaining negative terms against `20hj³`
  have a4 : 1 / 8 * j ^ 4 ≤ 20 * h * j ^ 3 - (7 + 8 * h ^ 2 + 12 * h ^ 3) * j ^ 4
      - (13 + 9 * h ^ 2) * j ^ 5 - 7 * j ^ 6 := by
    have b1 : 20 * j ^ 4 ≤ 20 * h * j ^ 3 := by nlinarith
    have b2 : (7 + 8 * h ^ 2 + 12 * h ^ 3) * j ^ 4 ≤ 21 / 2 * j ^ 4 :=
      mul_le_mul_of_nonneg_right (by nlinarith) hj4.le
    have hj1 : j ≤ 1 / 2 := by linarith
    have b3 : (13 + 9 * h ^ 2) * j ^ 5 ≤ 61 / 8 * j ^ 4 := by
      have : (13 + 9 * h ^ 2) * j ≤ 61 / 8 := by nlinarith
      nlinarith
    have b4 : 7 * j ^ 6 ≤ 7 / 4 * j ^ 4 := by
      have : j ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith
    linarith
  have a5 : 0 ≤ 8 * h ^ 2 * j ^ 3 := by positivity
  have a6 : 0 ≤ 14 * h * j ^ 4 := by positivity
  nlinarith [mul_pos h0 hj]

/-- **The stronger secant comparison**: with
`t = (1 - h)/2`, `c = (1 + h)/2`, `p = c + j`, `0 < j < h ≤ 1/2`:
`Sec(t, c, p) < Sec(t + p - c, p, c)`. -/
theorem fh_sec_swap_q {h j : ℝ} (hh : h ≤ 1 / 2) (hj : 0 < j) (hjh : j < h) :
    m2Sec ((1 - h) / 2) ((1 + h) / 2) ((1 + h) / 2 + j) <
      m2Sec ((1 - h) / 2 + j) ((1 + h) / 2 + j) ((1 + h) / 2) := by
  have h0 : 0 < h := by linarith
  have hA : 0 < 1 + 2 * j := by linarith
  have hC : 0 < 1 + h + j := by linarith
  have hCA : 1 < (1 + h + j) / (1 + 2 * j) := by rw [lt_div_iff₀ hA]; linarith
  rw [m2Sec_of_ne (by linarith), m2Sec_of_ne (by linarith)]
  have e1 : ((1 + h) / 2 + j + (1 + h) / 2) / ((1 - h) / 2 + (1 + h) / 2) = 1 + h + j := by ring
  have e2 : ((1 + h) / 2 + ((1 + h) / 2 + j)) / ((1 - h) / 2 + j + ((1 + h) / 2 + j)) =
      (1 + h + j) / (1 + 2 * j) := by ring
  rw [e1, e2]
  have hlogC : Real.log (1 + h + j) = Real.log (1 + 2 * j) + Real.log ((1 + h + j) / (1 + 2 * j)) := by
    rw [Real.log_div hC.ne' hA.ne']; ring
  rw [hlogC]
  have hlA := nh_log_one_add_gt (x := 2 * j) (by linarith)
  have hlR := nh_log_lt_Lp hCA
  set lA := Real.log (1 + 2 * j)
  set lR := Real.log ((1 + h + j) / (1 + 2 * j))
  -- the coefficient of `log(C/A)` is negative
  have hcoef : (1 + h) / 2 / ((1 + h) / 2 + j - (1 - h) / 2) <
      ((1 + h) / 2 + j) / ((1 + h) / 2 - ((1 - h) / 2 + j)) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hc1 : 0 < (1 + h) / 2 / ((1 + h) / 2 + j - (1 - h) / 2) := by
    apply div_pos (by linarith) (by linarith)
  -- the rational lower bound
  have hLp : nhLp ((1 + h + j) / (1 + 2 * j)) = (h - j) * ((1 + h + j) ^ 2
      + 10 * (1 + h + j) * (1 + 2 * j) + (1 + 2 * j) ^ 2) /
      (6 * (1 + 2 * j) * (1 + h + j) * ((1 + h + j) + (1 + 2 * j))) := by
    unfold nhLp; field_simp; ring
  have r1 : (1 + h) / 2 / ((1 + h) / 2 + j - (1 - h) / 2) = (1 + h) / (2 * (h + j)) := by
    rw [show (1 + h) / 2 + j - (1 - h) / 2 = h + j by ring]; field_simp
  have r2 : ((1 + h) / 2 + j) / ((1 + h) / 2 - ((1 - h) / 2 + j)) = (1 + h + 2 * j) / (2 * (h - j)) := by
    rw [show (1 + h) / 2 - ((1 - h) / 2 + j) = h - j by ring]; field_simp
  have r3 : 2 * (2 * j) / (2 * j + 2) + 2 * (2 * j) ^ 3 / (3 * (2 * j + 2) ^ 3) =
      2 * j / (1 + j) + 2 * j ^ 3 / (3 * (1 + j) ^ 3) := by
    have : (1 + j) ≠ 0 := by linarith
    field_simp; ring
  have r4 : ((1 + h) / 2 + j) ^ 2 / (((1 - h) / 2 + j + ((1 + h) / 2 + j)) *
        ((1 + h) / 2 + ((1 + h) / 2 + j))) = (1 + h + 2 * j) ^ 2 / (4 * ((1 + 2 * j) * (1 + h + j))) := by
    rw [show (1 - h) / 2 + j + ((1 + h) / 2 + j) = 1 + 2 * j by ring,
      show (1 + h) / 2 + ((1 + h) / 2 + j) = 1 + h + j by ring]
    field_simp; ring
  have r5 : ((1 + h) / 2) ^ 2 / (((1 - h) / 2 + (1 + h) / 2) * ((1 + h) / 2 + j + (1 + h) / 2)) =
      (1 + h) ^ 2 / (4 * (1 + h + j)) := by
    rw [show (1 - h) / 2 + (1 + h) / 2 = 1 by ring, show (1 + h) / 2 + j + (1 + h) / 2 = 1 + h + j by ring]
    field_simp; ring
  rw [r1, r2] at hcoef
  rw [r1] at hc1
  rw [r1, r2, r4, r5]
  rw [r3] at hlA
  rw [hLp] at hlR
  have key : (1 + h + 2 * j) ^ 2 / (4 * ((1 + 2 * j) * (1 + h + j))) - (1 + h) ^ 2 / (4 * (1 + h + j))
      + (1 + h) / (2 * (h + j)) * (2 * j / (1 + j) + 2 * j ^ 3 / (3 * (1 + j) ^ 3))
      + ((1 + h) / (2 * (h + j)) - (1 + h + 2 * j) / (2 * (h - j))) *
        ((h - j) * ((1 + h + j) ^ 2 + 10 * (1 + h + j) * (1 + 2 * j) + (1 + 2 * j) ^ 2) /
          (6 * (1 + 2 * j) * (1 + h + j) * ((1 + h + j) + (1 + 2 * j)))) =
      j * fhSwapP h j / (6 * (1 + j) ^ 3 * (1 + 2 * j) * (1 + h + j) *
        ((1 + 2 * j) + (1 + h + j)) * (h + j)) := by
    have h1 : h - j ≠ 0 := by linarith
    have h2 : h + j ≠ 0 := by linarith
    have h3 : (1 + j) ≠ 0 := by linarith
    unfold fhSwapP
    field_simp
    ring
  have hpos : 0 < j * fhSwapP h j / (6 * (1 + j) ^ 3 * (1 + 2 * j) * (1 + h + j) *
      ((1 + 2 * j) + (1 + h + j)) * (h + j)) := by
    have := fh_swapP_pos hh hj hjh
    apply div_pos (mul_pos hj this)
    have : 0 < 1 + j := by linarith
    positivity
  have m1 := mul_lt_mul_of_pos_left hlA hc1
  have m2 := mul_lt_mul_of_neg_left hlR (by linarith : (1 + h) / (2 * (h + j)) - (1 + h + 2 * j) / (2 * (h - j)) < 0)
  nlinarith

end SmoothedOctagon

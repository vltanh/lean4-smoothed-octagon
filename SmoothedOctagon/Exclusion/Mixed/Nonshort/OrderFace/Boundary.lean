module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The boundary of the reverse order face

The coordinates `h = 1 - 2t` and `s = 2t + x - 1` measure the two order gaps.
After clearing the positive denominators, the boundary residual is `nsrOP h s`.
Its terms of order at least two in `s` are nonnegative: the only negative terms
are absorbed by the fourth and fifth order terms. The remaining affine function
of `s` is positive by two explicit factorizations, on either side of `h = 1/4`.
-/

@[expose] public section

namespace SmoothedOctagon


/-- The cleared boundary residual, grouped by the order gap `s`. -/
noncomputable def nsrOP (h s : ℝ) : ℝ :=
  h ^ 3 * (1 + h) ^ 2 *
    (-16 + 24 * h + 120 * h ^ 2 + 140 * h ^ 3 + 78 * h ^ 4 + 23 * h ^ 5 + 3 * h ^ 6) +
  h ^ 3 * (1 + h) *
    (8 + 396 * h + 1020 * h ^ 2 + 1080 * h ^ 3 + 597 * h ^ 4 + 179 * h ^ 5 + 24 * h ^ 6) * s +
  (48 * h + 144 * h ^ 2 + 420 * h ^ 3 + 1718 * h ^ 4 + 3455 * h ^ 5 +
    3498 * h ^ 6 + 1946 * h ^ 7 + 594 * h ^ 8 + 81 * h ^ 9) * s ^ 2 +
  (16 + 216 * h + 396 * h ^ 2 + 824 * h ^ 3 + 2440 * h ^ 4 + 3562 * h ^ 5 +
    2558 * h ^ 6 + 942 * h ^ 7 + 150 * h ^ 8) * s ^ 3 +
  (40 + 316 * h + 268 * h ^ 2 + 510 * h ^ 3 + 1643 * h ^ 4 + 1833 * h ^ 5 +
    873 * h ^ 6 + 165 * h ^ 7) * s ^ 4 +
  (40 + 184 * h - 70 * h ^ 2 + 117 * h ^ 3 + 638 * h ^ 4 + 471 * h ^ 5 +
    108 * h ^ 6) * s ^ 5 +
  (18 + 29 * h - 108 * h ^ 2 + 46 * h ^ 3 + 136 * h ^ 4 + 39 * h ^ 5) * s ^ 6 +
  (2 - 4 * h - 20 * h ^ 2 + 16 * h ^ 3 + 6 * h ^ 4) * s ^ 7

private noncomputable def orderF (h : ℝ) : ℝ :=
  -16 + 24 * h + 120 * h ^ 2 + 140 * h ^ 3 + 78 * h ^ 4 + 23 * h ^ 5 + 3 * h ^ 6

private noncomputable def orderG (h : ℝ) : ℝ :=
  8 + 396 * h + 1020 * h ^ 2 + 1080 * h ^ 3 + 597 * h ^ 4 + 179 * h ^ 5 + 24 * h ^ 6

private noncomputable def orderQ (h : ℝ) : ℝ :=
  -56 + 396 * h + 12 * h ^ 2 - 1960 * h ^ 3 - 2851 * h ^ 4 - 1805 * h ^ 5 -
    588 * h ^ 6 - 84 * h ^ 7

/-- The negative tail is absorbed without estimating the other positive terms. -/
private theorem order_affine_le {h s : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 4 / 3) :
    h ^ 3 * (1 + h) ^ 2 * orderF h + h ^ 3 * (1 + h) * orderG h * s ≤ nsrOP h s := by
  have hs2 : s ^ 2 ≤ 16 / 9 := by nlinarith only [hs, hs1, sq_nonneg (s - 4 / 3)]
  have hs3 : s ^ 3 ≤ 64 / 27 := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ ≤ (16 / 9) * (4 / 3) := mul_le_mul hs2 hs1 hs (by norm_num)
      _ = 64 / 27 := by norm_num
  have hhs2 : h * s ^ 2 ≤ 16 / 9 :=
    (mul_le_mul_of_nonneg_right hh1 (sq_nonneg s)).trans (by simpa using hs2)
  have hhs3 : (4 + 20 * h) * s ^ 3 ≤ 24 * (64 / 27) := by
    calc
      (4 + 20 * h) * s ^ 3 ≤ 24 * s ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith only [hh1]) (pow_nonneg hs 3)
      _ ≤ 24 * (64 / 27) := mul_le_mul_of_nonneg_left hs3 (by norm_num)
  have hfour : 0 ≤ h * s ^ 4 * (316 - 108 * h * s ^ 2 - (4 + 20 * h) * s ^ 3) :=
    mul_nonneg (by positivity) (by linarith only [hhs2, hhs3])
  have hfive : 0 ≤ h * s ^ 5 * (184 - 70 * h) :=
    mul_nonneg (by positivity) (by linarith only [hh1])
  have hrest : 0 ≤ nsrOP h s -
      (h ^ 3 * (1 + h) ^ 2 * orderF h + h ^ 3 * (1 + h) * orderG h * s) -
      h * s ^ 4 * (316 - 108 * h * s ^ 2 - (4 + 20 * h) * s ^ 3) -
      h * s ^ 5 * (184 - 70 * h) := by
    unfold nsrOP orderF orderG
    ring_nf
    positivity
  linarith only [hfour, hfive, hrest]

/-- On the short interval, the high powers can be absorbed before factoring. -/
private theorem orderQ_pos {h : ℝ} (hh : 1 / 5 ≤ h) (hh1 : h ≤ 1 / 4) : 0 < orderQ h := by
  have hh0 : 0 < h := by linarith only [hh]
  have hh2 : h ^ 2 ≤ 1 / 16 := by nlinarith only [hh0, hh1, sq_nonneg (h - 1 / 4)]
  have hh3 : h ^ 3 ≤ 1 / 64 := by
    calc
      h ^ 3 = h ^ 2 * h := by ring
      _ ≤ (1 / 16) * (1 / 4) := mul_le_mul hh2 hh1 hh0.le (by norm_num)
      _ = 1 / 64 := by norm_num
  have hh4 : h ^ 4 ≤ 1 / 256 := by
    calc
      h ^ 4 = h ^ 2 * h ^ 2 := by ring
      _ ≤ (1 / 16) * (1 / 16) := mul_le_mul hh2 hh2 (sq_nonneg h) (by norm_num)
      _ = 1 / 256 := by norm_num
  have hhigh : 0 ≤ 836 - 2851 * h - 1805 * h ^ 2 - 588 * h ^ 3 - 84 * h ^ 4 := by
    linarith only [hh1, hh2, hh3, hh4]
  have hquad : 0 ≤ 175 * h ^ 2 + 43 * h - 14 := by
    nlinarith only [hh, sq_nonneg (h - 1 / 5)]
  have heq : orderQ h = 4 * h ^ 3 + 16 * (1 / 4 - h) * (175 * h ^ 2 + 43 * h - 14) +
      h ^ 3 * (836 - 2851 * h - 1805 * h ^ 2 - 588 * h ^ 3 - 84 * h ^ 4) := by
    unfold orderQ
    ring
  rw [heq]
  have : 0 ≤ 1 / 4 - h := sub_nonneg.mpr hh1
  positivity

/-- Above one quarter, the constant term has a positive factorization. -/
private theorem orderF_pos {h : ℝ} (hh : 1 / 4 ≤ h) : 0 < orderF h := by
  have hh0 : 0 < h := by linarith only [hh]
  have hbracket : 0 ≤ 78 * h + 23 * h ^ 2 - 20 := by
    nlinarith only [hh, sq_nonneg (h - 1 / 4)]
  have heq : orderF h = 8 * (4 * h - 1) * (5 * h ^ 2 + 5 * h + 2) +
      h ^ 3 * (78 * h + 23 * h ^ 2 - 20) + 3 * h ^ 6 := by
    unfold orderF
    ring
  rw [heq]
  have : 0 ≤ 4 * h - 1 := by linarith only [hh]
  positivity

/-- Positivity at the boundary follows from the two order gaps and positive factors. -/
theorem nsrOP_pos {h s : ℝ} (hh : 1 / 5 ≤ h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 4 / 3) (hshape : 1 / 4 - h ≤ s) : 0 < nsrOP h s := by
  have hh0 : 0 < h := by linarith only [hh]
  have hG : 0 < orderG h := by unfold orderG; positivity
  have htail := order_affine_le hh0.le hh1 hs hs1
  by_cases hquarter : 1 / 4 ≤ h
  · have hFpos := orderF_pos hquarter
    have hconstant : 0 < h ^ 3 * (1 + h) ^ 2 * orderF h := by positivity
    have hslope : 0 ≤ h ^ 3 * (1 + h) * orderG h * s := by positivity
    linarith only [htail, hconstant, hslope]
  · have hQ := orderQ_pos hh (le_of_not_ge hquarter)
    have hboundary : 0 < h ^ 3 * (1 + h) ^ 2 * orderF h +
        h ^ 3 * (1 + h) * orderG h * (1 / 4 - h) := by
      have heq : h ^ 3 * (1 + h) ^ 2 * orderF h +
          h ^ 3 * (1 + h) * orderG h * (1 / 4 - h) =
          h ^ 3 * (1 + h) / 4 * orderQ h := by
        unfold orderF orderG orderQ
        ring
      rw [heq]
      positivity
    have hmove := mul_le_mul_of_nonneg_left hshape
      (show 0 ≤ h ^ 3 * (1 + h) * orderG h by positivity)
    linarith only [htail, hboundary, hmove]

end SmoothedOctagon

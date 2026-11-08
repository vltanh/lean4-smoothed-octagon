module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandTermDefs

/-!
# S2 hand signs: the lower-shape terminal curve, component signs

The univariate component signs of `archive/lighter-proofs/SHORT_RATIO_OUTER_TERMINAL_ALGEBRA.md`
§2-§4 on `3/4 ≤ r ≤ 49/60`, each stated for the cleared numerator of the bounded quantity (the
positive clearing factor of the table in §2 is already divided out): for `n = 49/20` and
`n = 63/25`, `0 < A_n < 5`, `-17 < A_n' < 0`, `A_n'' < 53`, `L_n'' < -1`, `Q_n'' < -17/10`; the
`F` bounds `K₀`-`K₃` and the logarithm-pole bound `T`. Each is proved by the termwise rule in the
shifted variable `s = r - 3/4 ∈ [0, 1/15]` (positive terms at `s = 0`, negative terms at
`s = 1/15`).
Route: the notes' monotonicity arguments for `P₁, P₂, P₄, P₅, P₆, K₁, T` and the `n`-derivatives
`J₀`-`J₂` are replaced by the termwise rule at the left endpoint, applied to each `n` separately.

## Main API

* `hl2_rbox`, and `hl2_bAl_pos`, …, `hl2_bT` (19 signs).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The monomial facts of the termwise rule in `s = r - 3/4 ∈ [0, 1/15]`. -/
theorem hl2_rbox {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    (∀ n : ℕ, 0 ≤ (r - 3 / 4) ^ n) ∧ (∀ n : ℕ, (r - 3 / 4) ^ n ≤ (1 / 15) ^ n) :=
  ⟨fun n => pow_nonneg (by linarith) n, fun n => pow_le_pow_left₀ (by linarith) (by linarith) n⟩

theorem hl2_bAl_pos {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < hl2Asl r := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Asl
  linarith [hp 6, hu 5, hp 4, hp 3, hu 2, hu 1]

theorem hl2_bAl_lt5 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 5 * 60197437440 * r ^ 2 - hl2Asl r := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Asl
  linarith [hu 6, hp 5, hu 4, hu 3, hp 2, hp 1]

theorem hl2_bAdl_gt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 17 * 60197437440 * r ^ 3 + (r * hl2Asl1 r - 2 * hl2Asl r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Asl hl2Asl1
  linarith [hp 6, hu 5, hu 4, hp 3, hp 2, hp 1]

theorem hl2_bAdl_neg {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(r * hl2Asl1 r - 2 * hl2Asl r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Asl hl2Asl1
  linarith [hu 6, hp 5, hp 4, hu 3, hu 2, hp 1]

theorem hl2_bAddl_lt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 53 * 60197437440 * r ^ 4 - (r ^ 2 * hl2Asl2 r - 4 * r * hl2Asl1 r + 6 * hl2Asl r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Asl hl2Asl1 hl2Asl2
  linarith [hu 6, hp 5, hp 4, hp 3, hp 2, hp 1]

theorem hl2_bLddl {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(80263249920 * r ^ 4) - (r ^ 2 * hl2Lsl2 r - 4 * r * hl2Lsl1 r + 6 * hl2Lsl r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Lsl hl2Lsl1 hl2Lsl2
  linarith [hu 6, hu 5, hu 4, hu 3, hu 2, hu 1]

theorem hl2_bQddl {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(17 / 10) * (887040 * r + 6773760) ^ 3 - (hl2Qsl2 r * (887040 * r + 6773760) ^ 2 - 2 * 887040 * hl2Qsl1 r * (887040 * r + 6773760) + 2 * 887040 ^ 2 * hl2Qsl r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Qsl hl2Qsl1 hl2Qsl2
  linarith [hu 5, hu 4, hu 3, hp 2, hu 1]

theorem hl2_bAh_pos {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < hl2Ash r := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Ash
  linarith [hp 6, hu 5, hp 4, hp 3, hu 2, hu 1]

theorem hl2_bAh_lt5 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 5 * 8360755200 * r ^ 2 - hl2Ash r := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Ash
  linarith [hu 6, hp 5, hu 4, hu 3, hp 2, hp 1]

theorem hl2_bAdh_gt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 17 * 8360755200 * r ^ 3 + (r * hl2Ash1 r - 2 * hl2Ash r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Ash hl2Ash1
  linarith [hp 6, hu 5, hu 4, hp 3, hp 2, hp 1]

theorem hl2_bAdh_neg {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(r * hl2Ash1 r - 2 * hl2Ash r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Ash hl2Ash1
  linarith [hu 6, hp 5, hp 4, hu 3, hu 2, hp 1]

theorem hl2_bAddh_lt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 53 * 8360755200 * r ^ 4 - (r ^ 2 * hl2Ash2 r - 4 * r * hl2Ash1 r + 6 * hl2Ash r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Ash hl2Ash1 hl2Ash2
  linarith [hu 6, hp 5, hp 4, hp 3, hp 2, hp 1]

theorem hl2_bLddh {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(11147673600 * r ^ 4) - (r ^ 2 * hl2Lsh2 r - 4 * r * hl2Lsh1 r + 6 * hl2Lsh r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Lsh hl2Lsh2 hl2Lsh1
  linarith [hu 6, hu 5, hu 4, hu 3, hu 2, hu 1]

theorem hl2_bQddh {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(17 / 10) * (123200 * r + 940800) ^ 3 - (hl2Qsh2 r * (123200 * r + 940800) ^ 2 - 2 * 123200 * hl2Qsh1 r * (123200 * r + 940800) + 2 * 123200 ^ 2 * hl2Qsh r) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  unfold hl2Qsh hl2Qsh2 hl2Qsh1
  linarith [hu 5, hu 4, hu 3, hp 2, hu 1]

theorem hl2_bK0 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 11 / 400 * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  linarith [hu 2, hu 1]

theorem hl2_bK1 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < ((84 - 122 * r) * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (2493 - 4522 * r)) - 7 / 500 * (504 + 2493 * r - 2261 * r ^ 2) ^ 2 := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  linarith [hu 4, hu 3, hp 2, hp 1]

theorem hl2_bK2 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 1 / 50 * (504 + 2493 * r - 2261 * r ^ 2) ^ 2 - ((84 - 122 * r) * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (2493 - 4522 * r)) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  linarith [hp 4, hp 3, hu 2, hu 1]

theorem hl2_bK3 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 1 / 12 * (504 + 2493 * r - 2261 * r ^ 2) ^ 3 - ((-122 * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (-4522)) * (504 + 2493 * r - 2261 * r ^ 2) - 2 * (2493 - 4522 * r) * ((84 - 122 * r) * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (2493 - 4522 * r))) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  linarith [hu 6, hu 5, hp 4, hp 3, hu 2, hu 1]

theorem hl2_bT {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 7 / 20 * r ^ 2 * (504 + 3645 * r - 1109 * r ^ 2) ^ 3 - (1152 * (-r * (-2218) * (504 + 3645 * r - 1109 * r ^ 2) - 2 * (3645 - 2218 * r) * ((504 + 3645 * r - 1109 * r ^ 2) - r * (3645 - 2218 * r))) * r ^ 2 + (((-2218) * (504 + 3645 * r - 1109 * r ^ 2) - (3645 - 2218 * r) ^ 2) * (504 + 3645 * r - 1109 * r ^ 2) * r ^ 2 + (504 + 3645 * r - 1109 * r ^ 2) ^ 3)) := by
  obtain ⟨hp, hu⟩ := hl2_rbox h0 h1
  linarith [hu 8, hp 7, hp 6, hu 5, hu 4, hp 3, hp 2, hp 1]


end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LowerTerminal.Defs

/-!
# Smaller-short window, upper ratio: the lower-shape terminal curve, component signs

The univariate component signs of the lower-shape terminal curve on `3/4 ≤ r ≤ 49/60`, each
stated for the cleared numerator of the bounded quantity (with its positive clearing factor
divided out): for `n = 49/20` and `n = 63/25`, `0 < A_n < 5`, `-17 < A_n' < 0`, `A_n'' < 53`,
`L_n'' < -1`, `Q_n'' < -17/10`; the `F` bounds `K₀`-`K₃` and the logarithm-pole bound `T`. Each
is proved by a termwise rule in the shifted variable `s = r - 3/4 ∈ [0, 1/15]` (positive terms
at `s = 0`, negative terms at `s = 1/15`).
The rule is applied to each `n` separately.

## Main API

* `ur_rbox`, and `ur_bAl_pos`, …, `ur_bT` (19 signs).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The monomial facts of the termwise rule in `s = r - 3/4 ∈ [0, 1/15]`. -/
theorem ur_rbox {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    (∀ n : ℕ, 0 ≤ (r - 3 / 4) ^ n) ∧ (∀ n : ℕ, (r - 3 / 4) ^ n ≤ (1 / 15) ^ n) :=
  ⟨fun n => pow_nonneg (by linarith) n, fun n => pow_le_pow_left₀ (by linarith) (by linarith) n⟩

theorem ur_bAl_pos {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < urAsl r := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsl
  linarith [hp 6, hu 5, hp 4, hp 3, hu 2, hu 1]

theorem ur_bAl_lt5 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 5 * 60197437440 * r ^ 2 - urAsl r := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsl
  linarith [hu 6, hp 5, hu 4, hu 3, hp 2, hp 1]

theorem ur_bAdl_gt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 17 * 60197437440 * r ^ 3 + (r * urAsl1 r - 2 * urAsl r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsl urAsl1
  linarith [hp 6, hu 5, hu 4, hp 3, hp 2, hp 1]

theorem ur_bAdl_neg {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(r * urAsl1 r - 2 * urAsl r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsl urAsl1
  linarith [hu 6, hp 5, hp 4, hu 3, hu 2, hp 1]

theorem ur_bAddl_lt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 53 * 60197437440 * r ^ 4 - (r ^ 2 * urAsl2 r - 4 * r * urAsl1 r + 6 * urAsl r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsl urAsl1 urAsl2
  linarith [hu 6, hp 5, hp 4, hp 3, hp 2, hp 1]

theorem ur_bLddl {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(80263249920 * r ^ 4) - (r ^ 2 * urLsl2 r - 4 * r * urLsl1 r + 6 * urLsl r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urLsl urLsl1 urLsl2
  linarith [hu 6, hu 5, hu 4, hu 3, hu 2, hu 1]

theorem ur_bQddl {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(17 / 10) * (887040 * r + 6773760) ^ 3 - (urQsl2 r * (887040 * r + 6773760) ^ 2 - 2 * 887040 * urQsl1 r * (887040 * r + 6773760) + 2 * 887040 ^ 2 * urQsl r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urQsl urQsl1 urQsl2
  linarith [hu 5, hu 4, hu 3, hp 2, hu 1]

theorem ur_bAh_pos {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < urAsh r := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsh
  linarith [hp 6, hu 5, hp 4, hp 3, hu 2, hu 1]

theorem ur_bAh_lt5 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 5 * 8360755200 * r ^ 2 - urAsh r := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsh
  linarith [hu 6, hp 5, hu 4, hu 3, hp 2, hp 1]

theorem ur_bAdh_gt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 17 * 8360755200 * r ^ 3 + (r * urAsh1 r - 2 * urAsh r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsh urAsh1
  linarith [hp 6, hu 5, hu 4, hp 3, hp 2, hp 1]

theorem ur_bAdh_neg {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(r * urAsh1 r - 2 * urAsh r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsh urAsh1
  linarith [hu 6, hp 5, hp 4, hu 3, hu 2, hp 1]

theorem ur_bAddh_lt {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 53 * 8360755200 * r ^ 4 - (r ^ 2 * urAsh2 r - 4 * r * urAsh1 r + 6 * urAsh r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urAsh urAsh1 urAsh2
  linarith [hu 6, hp 5, hp 4, hp 3, hp 2, hp 1]

theorem ur_bLddh {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(11147673600 * r ^ 4) - (r ^ 2 * urLsh2 r - 4 * r * urLsh1 r + 6 * urLsh r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urLsh urLsh2 urLsh1
  linarith [hu 6, hu 5, hu 4, hu 3, hu 2, hu 1]

theorem ur_bQddh {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < -(17 / 10) * (123200 * r + 940800) ^ 3 - (urQsh2 r * (123200 * r + 940800) ^ 2 - 2 * 123200 * urQsh1 r * (123200 * r + 940800) + 2 * 123200 ^ 2 * urQsh r) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  unfold urQsh urQsh2 urQsh1
  linarith [hu 5, hu 4, hu 3, hp 2, hu 1]

theorem ur_bK0 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 11 / 400 * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  linarith [hu 2, hu 1]

theorem ur_bK1 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < ((84 - 122 * r) * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (2493 - 4522 * r)) - 7 / 500 * (504 + 2493 * r - 2261 * r ^ 2) ^ 2 := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  linarith [hu 4, hu 3, hp 2, hp 1]

theorem ur_bK2 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 1 / 50 * (504 + 2493 * r - 2261 * r ^ 2) ^ 2 - ((84 - 122 * r) * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (2493 - 4522 * r)) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  linarith [hp 4, hp 3, hu 2, hu 1]

theorem ur_bK3 {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 1 / 12 * (504 + 2493 * r - 2261 * r ^ 2) ^ 3 - ((-122 * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (-4522)) * (504 + 2493 * r - 2261 * r ^ 2) - 2 * (2493 - 4522 * r) * ((84 - 122 * r) * (504 + 2493 * r - 2261 * r ^ 2) - (r * (84 - 61 * r)) * (2493 - 4522 * r))) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  linarith [hu 6, hu 5, hp 4, hp 3, hu 2, hu 1]

theorem ur_bT {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < 7 / 20 * r ^ 2 * (504 + 3645 * r - 1109 * r ^ 2) ^ 3 - (1152 * (-r * (-2218) * (504 + 3645 * r - 1109 * r ^ 2) - 2 * (3645 - 2218 * r) * ((504 + 3645 * r - 1109 * r ^ 2) - r * (3645 - 2218 * r))) * r ^ 2 + (((-2218) * (504 + 3645 * r - 1109 * r ^ 2) - (3645 - 2218 * r) ^ 2) * (504 + 3645 * r - 1109 * r ^ 2) * r ^ 2 + (504 + 3645 * r - 1109 * r ^ 2) ^ 3)) := by
  obtain ⟨hp, hu⟩ := ur_rbox h0 h1
  linarith [hu 8, hp 7, hp 6, hu 5, hu 4, hp 3, hp 2, hp 1]


end SmoothedOctagon

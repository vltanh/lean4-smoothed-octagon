module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenStage
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenLinkG
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenLinkA
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenLinkD
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL0
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL1
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL2
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL3
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL4

/-!
# S2 heavy face signs: the central face

`hs2_central_sign_proof` proves the statement of `hs2_central_sign` (`CENTRAL_RATIO_HAND_SIGN` (5);
inventory HS-S2 R23): for `13/6 ≤ x ≤ 12/5`, `1 ≤ α`, `6α² ≤ x(x + 2)`, `β` in the strip, `q = q_c`,
`u = u_C(x, β)` and `2 ≤ τ ≤ T`, `G_τ < 0`.

Proof. Duration: `G(τ) - G(2) = (τ - 2)A + log(τ/2) - (τ² - 4)/(4τ)` and
`log z ≤ (z - 1/z)/2 - (z - 1)³/(6z²)` give `G(τ) ≤ G₂ + (τ - 2)A - (τ - 2)³/(12τ²)`
(`hh2_tau_cubic`); since `k ≥ 2/7`, `τ ≤ 7/2`, and the upper envelope of
`A ↦ (τ - 2)A - (τ - 2)³/(12τ²)` over `τ ∈ [2, 7/2]` is below the piecewise-linear chords
`ℓ₀, …, ℓ₄` (`hh2_chord0`-`4`, breakpoints `A = 0, 1/250, 3/250, 9/196`; each chord is checked at its
two endpoints by a cubic in `τ`). Each sign `G₂ + ℓᵢ(A) < 0` (with the log majorant) is a polynomial
sign on `t ∈ [0, 229/1024]`, `x ∈ [13/6, 12/5]`, `α ∈ [1, 4/3]` (`t = c₊(x) - c`, `c = (β - x)/(α - 1)`),
proved by the nested Bernstein certificates `hh2CnL{i}_pos` after the two-stage clearing
`hh2_cen_stage1_*` (abstract atoms) and `hh2_cen_stage2_*` (expansion).

Route: the notes' cubic loss `8TA² + TA/18` with the `β`-monotonicities (App. A), the exact-log
`x`-derivatives `Q₀`, `Q₁` (App. B) and the terminal polynomials `P₀`, `P₁` (App. C) are replaced by
the chord bounds of the exact cubic loss and five trivariate Bernstein certificates (no derivative
in `x` or `β`).

## Main API

* `hh2_tau_cubic`, `hh2_chord0`-`hh2_chord4`, `hh2_strip_t`, `hh2_cen_line0`-`hh2_cen_line4`.
* `hs2_central_sign_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

private theorem hh2_chord_e1_0_bp0 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 1866447 * b ^ (3 : ℕ) + 3742317 * a * b ^ (2 : ℕ) + 1474245 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e1_0_l0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (35 / 16)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 1728000000 : ℝ) * hh2_chord_e1_0_bp0 (16 * τ - 32) (35 - 16 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e1_0_bp1 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 3907701 * b ^ (3 : ℕ) + 5826123 * a * b ^ (2 : ℕ) + 1516797 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e1_0_l1 (τ : ℝ) (h0 : (35 / 16) ≤ τ) (h1 : τ ≤ (73 / 32)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 13824000000 : ℝ) * hh2_chord_e1_0_bp1 (32 * τ - 70) (73 - 32 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e1_0_bp2 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 12777336 * b ^ (7 : ℕ) + 46971036 * a * b ^ (6 : ℕ) + 52597566 * a ^ (2 : ℕ) * b ^ (5 : ℕ) + 8440425 * a ^ (3 : ℕ) * b ^ (4 : ℕ) + 39091626 * a ^ (5 : ℕ) * b ^ (2 : ℕ) + 41341986 * a ^ (6 : ℕ) * b + 12213801 * a ^ (7 : ℕ) := by positivity

private theorem hh2_chord_e1_0_l2 (τ : ℝ) (h0 : (73 / 32) ≤ τ) (h1 : τ ≤ (149 / 64)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 62705664000000 : ℝ) * hh2_chord_e1_0_bp2 (64 * τ - 146) (149 - 64 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e1_0_bp3 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 6307803 * a * b ^ (2 : ℕ) + 19405539 * a ^ (2 : ℕ) * b + 13499361 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e1_0_l3 (τ : ℝ) (h0 : (149 / 64) ≤ τ) (h1 : τ ≤ (19 / 8)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 110592000000 : ℝ) * hh2_chord_e1_0_bp3 (64 * τ - 149) (152 - 64 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e1_0_bp4 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 329571 * a * b ^ (2 : ℕ) + 1658493 * a ^ (2 : ℕ) * b + 1730547 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e1_0_l4 (τ : ℝ) (h0 : (19 / 8) ≤ τ) (h1 : τ ≤ (11 / 4)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 216000000 : ℝ) * hh2_chord_e1_0_bp4 (8 * τ - 19) (22 - 8 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e1_0_bp5 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 883287 * a * b ^ (2 : ℕ) + 2868687 * a ^ (2 : ℕ) * b + 2387025 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e1_0_l5 (τ : ℝ) (h0 : (11 / 4) ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 27000000 : ℝ) * hh2_chord_e1_0_bp5 (4 * τ - 11) (14 - 4 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e1_0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  rcases le_total τ (35 / 16) with hc0 | hc0
  · exact hh2_chord_e1_0_l0 τ h0 hc0
  rcases le_total τ (73 / 32) with hc1 | hc1
  · exact hh2_chord_e1_0_l1 τ hc0 hc1
  rcases le_total τ (149 / 64) with hc2 | hc2
  · exact hh2_chord_e1_0_l2 τ hc1 hc2
  rcases le_total τ (19 / 8) with hc3 | hc3
  · exact hh2_chord_e1_0_l3 τ hc2 hc3
  rcases le_total τ (11 / 4) with hc4 | hc4
  · exact hh2_chord_e1_0_l4 τ hc3 hc4
  exact hh2_chord_e1_0_l5 τ hc4 h1

private theorem hh2_chord_e2_1_bp0 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 1866447 * b ^ (3 : ℕ) + 3742317 * a * b ^ (2 : ℕ) + 1474245 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e2_1_l0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (35 / 16)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 1728000000 : ℝ) * hh2_chord_e2_1_bp0 (16 * τ - 32) (35 - 16 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_1_bp1 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 3907701 * b ^ (3 : ℕ) + 5826123 * a * b ^ (2 : ℕ) + 1516797 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e2_1_l1 (τ : ℝ) (h0 : (35 / 16) ≤ τ) (h1 : τ ≤ (73 / 32)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 13824000000 : ℝ) * hh2_chord_e2_1_bp1 (32 * τ - 70) (73 - 32 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_1_bp2 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 12777336 * b ^ (7 : ℕ) + 46971036 * a * b ^ (6 : ℕ) + 52597566 * a ^ (2 : ℕ) * b ^ (5 : ℕ) + 8440425 * a ^ (3 : ℕ) * b ^ (4 : ℕ) + 39091626 * a ^ (5 : ℕ) * b ^ (2 : ℕ) + 41341986 * a ^ (6 : ℕ) * b + 12213801 * a ^ (7 : ℕ) := by positivity

private theorem hh2_chord_e2_1_l2 (τ : ℝ) (h0 : (73 / 32) ≤ τ) (h1 : τ ≤ (149 / 64)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 62705664000000 : ℝ) * hh2_chord_e2_1_bp2 (64 * τ - 146) (149 - 64 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_1_bp3 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 6307803 * a * b ^ (2 : ℕ) + 19405539 * a ^ (2 : ℕ) * b + 13499361 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e2_1_l3 (τ : ℝ) (h0 : (149 / 64) ≤ τ) (h1 : τ ≤ (19 / 8)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 110592000000 : ℝ) * hh2_chord_e2_1_bp3 (64 * τ - 149) (152 - 64 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_1_bp4 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 329571 * a * b ^ (2 : ℕ) + 1658493 * a ^ (2 : ℕ) * b + 1730547 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e2_1_l4 (τ : ℝ) (h0 : (19 / 8) ≤ τ) (h1 : τ ≤ (11 / 4)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 216000000 : ℝ) * hh2_chord_e2_1_bp4 (8 * τ - 19) (22 - 8 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_1_bp5 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 883287 * a * b ^ (2 : ℕ) + 2868687 * a ^ (2 : ℕ) * b + 2387025 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e2_1_l5 (τ : ℝ) (h0 : (11 / 4) ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 27000000 : ℝ) * hh2_chord_e2_1_bp5 (4 * τ - 11) (14 - 4 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_1 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3 := by
  rcases le_total τ (35 / 16) with hc0 | hc0
  · exact hh2_chord_e2_1_l0 τ h0 hc0
  rcases le_total τ (73 / 32) with hc1 | hc1
  · exact hh2_chord_e2_1_l1 τ hc0 hc1
  rcases le_total τ (149 / 64) with hc2 | hc2
  · exact hh2_chord_e2_1_l2 τ hc1 hc2
  rcases le_total τ (19 / 8) with hc3 | hc3
  · exact hh2_chord_e2_1_l3 τ hc2 hc3
  rcases le_total τ (11 / 4) with hc4 | hc4
  · exact hh2_chord_e2_1_l4 τ hc3 hc4
  exact hh2_chord_e2_1_l5 τ hc4 h1

private theorem hh2_chord_e2_2_bp0 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 6492195 * b ^ (3 : ℕ) + 14111721 * a * b ^ (2 : ℕ) + 5813901 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e2_2_l0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (19 / 8)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 1080000000 : ℝ) * hh2_chord_e2_2_bp0 (8 * τ - 16) (19 - 8 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_2_bp1 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 16482141 * b ^ (3 : ℕ) + 26190819 * a * b ^ (2 : ℕ) + 7903053 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e2_2_l1 (τ : ℝ) (h0 : (19 / 8) ≤ τ) (h1 : τ ≤ (41 / 16)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 8640000000 : ℝ) * hh2_chord_e2_2_bp1 (16 * τ - 38) (41 - 16 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_2_bp2 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 83104371 * b ^ (3 : ℕ) + 122864265 * a * b ^ (2 : ℕ) + 37954269 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e2_2_l2 (τ : ℝ) (h0 : (41 / 16) ≤ τ) (h1 : τ ≤ (167 / 64)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 552960000000 : ℝ) * hh2_chord_e2_2_bp2 (64 * τ - 164) (167 - 64 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_2_bp3 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 47605206 * b ^ (6 : ℕ) + 95859891 * a * b ^ (5 : ℕ) + 2533335 * a ^ (3 : ℕ) * b ^ (3 : ℕ) + 252120825 * a ^ (4 : ℕ) * b ^ (2 : ℕ) + 302973426 * a ^ (5 : ℕ) * b + 101640621 * a ^ (6 : ℕ) := by positivity

private theorem hh2_chord_e2_2_l3 (τ : ℝ) (h0 : (167 / 64) ≤ τ) (h1 : τ ≤ (85 / 32)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 74649600000000 : ℝ) * hh2_chord_e2_2_bp3 (64 * τ - 167) (170 - 64 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_2_bp4 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 15343515 * a * b ^ (2 : ℕ) + 56873331 * a ^ (2 : ℕ) * b + 43335441 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e2_2_l4 (τ : ℝ) (h0 : (85 / 32) ≤ τ) (h1 : τ ≤ (11 / 4)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 69120000000 : ℝ) * hh2_chord_e2_2_bp4 (32 * τ - 85) (88 - 32 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_2_bp5 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 1142703 * a * b ^ (2 : ℕ) + 6235803 * a ^ (2 : ℕ) * b + 6898725 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e2_2_l5 (τ : ℝ) (h0 : (11 / 4) ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 135000000 : ℝ) * hh2_chord_e2_2_bp5 (4 * τ - 11) (14 - 4 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e2_2 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  rcases le_total τ (19 / 8) with hc0 | hc0
  · exact hh2_chord_e2_2_l0 τ h0 hc0
  rcases le_total τ (41 / 16) with hc1 | hc1
  · exact hh2_chord_e2_2_l1 τ hc0 hc1
  rcases le_total τ (167 / 64) with hc2 | hc2
  · exact hh2_chord_e2_2_l2 τ hc1 hc2
  rcases le_total τ (85 / 32) with hc3 | hc3
  · exact hh2_chord_e2_2_l3 τ hc2 hc3
  rcases le_total τ (11 / 4) with hc4 | hc4
  · exact hh2_chord_e2_2_l4 τ hc3 hc4
  exact hh2_chord_e2_2_l5 τ hc4 h1

private theorem hh2_chord_e3_3_bp0 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 634742955 * b ^ (3 : ℕ) + 1379836449 * a * b ^ (2 : ℕ) + 568142244 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e3_3_l0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (19 / 8)) :
    0 < 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 105840000000 : ℝ) * hh2_chord_e3_3_bp0 (8 * τ - 16) (19 - 8 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e3_3_bp1 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 804256902 * b ^ (3 : ℕ) + 1276486218 * a * b ^ (2 : ℕ) + 383753691 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e3_3_l1 (τ : ℝ) (h0 : (19 / 8) ≤ τ) (h1 : τ ≤ (41 / 16)) :
    0 < 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 423360000000 : ℝ) * hh2_chord_e3_3_bp1 (16 * τ - 38) (41 - 16 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e3_3_bp2 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 469929873 * b ^ (6 : ℕ) + 900810783 * a * b ^ (5 : ℕ) + 832867755 * a ^ (3 : ℕ) * b ^ (3 : ℕ) + 4457763000 * a ^ (4 : ℕ) * b ^ (2 : ℕ) + 4732448058 * a ^ (5 : ℕ) * b + 1538433723 * a ^ (6 : ℕ) := by positivity

private theorem hh2_chord_e3_3_l2 (τ : ℝ) (h0 : (41 / 16) ≤ τ) (h1 : τ ≤ (11 / 4)) :
    0 < 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 57153600000000 : ℝ) * hh2_chord_e3_3_bp2 (16 * τ - 41) (44 - 16 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e3_3_bp3 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 224907714 * a * b ^ (2 : ℕ) + 1224221139 * a ^ (2 : ℕ) * b + 1353215925 * a ^ (3 : ℕ) := by positivity

private theorem hh2_chord_e3_3_l3 (τ : ℝ) (h0 : (11 / 4) ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 26460000000 : ℝ) * hh2_chord_e3_3_bp3 (4 * τ - 11) (14 - 4 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e3_3 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3 := by
  rcases le_total τ (19 / 8) with hc0 | hc0
  · exact hh2_chord_e3_3_l0 τ h0 hc0
  rcases le_total τ (41 / 16) with hc1 | hc1
  · exact hh2_chord_e3_3_l1 τ hc0 hc1
  rcases le_total τ (11 / 4) with hc2 | hc2
  · exact hh2_chord_e3_3_l2 τ hc1 hc2
  exact hh2_chord_e3_3_l3 τ hc2 h1

private theorem hh2_chord_e3_4_bp0 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 5395149 * b ^ (3 : ℕ) + 16188975 * a * b ^ (2 : ℕ) + 7081326 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e3_4_l0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (9 / 196) - (τ - 2) * (9 / 196)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 66150000 : ℝ) * hh2_chord_e3_4_bp0 (2 * τ - 4) (7 - 2 * τ) (by linarith) (by linarith)

private theorem hh2_chord_e4_5_bp0 (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ 5395149 * b ^ (3 : ℕ) + 16188975 * a * b ^ (2 : ℕ) + 7081326 * a ^ (2 : ℕ) * b := by positivity

private theorem hh2_chord_e4_5_l0 (τ : ℝ) (h0 : 2 ≤ τ) (h1 : τ ≤ (7 / 2)) :
    0 < 12 * τ ^ 2 * (((-56201) / 2450000) + (3 / 2) * (9 / 196) - (τ - 2) * (9 / 196)) + (τ - 2) ^ 3 := by
  linear_combination (1 / 66150000 : ℝ) * hh2_chord_e4_5_bp0 (2 * τ - 4) (7 - 2 * τ) (by linarith) (by linarith)

/-- Chord 0 (`A ≤ 0`). -/
theorem hh2_chord0 {τ A : ℝ} (h2 : 2 ≤ τ) (hA : A ≤ 0) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ 0 + 0 * A := by
  have h1 : (τ - 2) * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hA
  have h3 : 0 ≤ (τ - 2) ^ 3 / (12 * τ ^ 2) := by
    have : 0 ≤ τ - 2 := by linarith
    positivity
  linarith

/-- Chord 1 (`0 ≤ A ≤ 1/250`). -/
theorem hh2_chord1 {τ A : ℝ} (h2 : 2 ≤ τ) (h7 : τ ≤ 7 / 2) (hA0 : 0 ≤ A) (hA1 : A ≤ (1 / 250)) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ 0 + (97 / 500) * A := by
  have e0 : (0 : ℝ) ≤ (τ - 2) ^ 3 := pow_nonneg (by linarith) 3
  have e1 := (hh2_chord_e1_0 τ h2 h7).le
  have hτ2 : 0 < 12 * τ ^ 2 := by positivity
  have key : 0 ≤ 12 * τ ^ 2 * (0 + (97 / 500) * A - (τ - 2) * A) + (τ - 2) ^ 3 := by
    have hc : ((1 / 250) - 0) * (12 * τ ^ 2 * (0 + (97 / 500) * A - (τ - 2) * A) + (τ - 2) ^ 3) =
        ((1 / 250) - A) * ((τ - 2) ^ 3) + (A - 0) * (12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3) := by ring
    have hp : 0 ≤ ((1 / 250) - A) * ((τ - 2) ^ 3) + (A - 0) * (12 * τ ^ 2 * (0 + (97 / 500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3) :=
      add_nonneg (mul_nonneg (by linarith) e0) (mul_nonneg (by linarith) e1)
    nlinarith
  have hg : (τ - 2) ^ 3 / (12 * τ ^ 2) * (12 * τ ^ 2) = (τ - 2) ^ 3 := div_mul_cancel₀ _ (ne_of_gt hτ2)
  nlinarith

/-- Chord 2 (`1/250 ≤ A ≤ 3/250`). -/
theorem hh2_chord2 {τ A : ℝ} (h2 : 2 ≤ τ) (h7 : τ ≤ 7 / 2) (hA0 : (1 / 250) ≤ A) (hA1 : A ≤ (3 / 250)) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ ((-347) / 312500) + (1179 / 2500) * A := by
  have e0 := (hh2_chord_e2_1 τ h2 h7).le
  have e1 := (hh2_chord_e2_2 τ h2 h7).le
  have hτ2 : 0 < 12 * τ ^ 2 := by positivity
  have key : 0 ≤ 12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * A - (τ - 2) * A) + (τ - 2) ^ 3 := by
    have hc : ((3 / 250) - (1 / 250)) * (12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * A - (τ - 2) * A) + (τ - 2) ^ 3) =
        ((3 / 250) - A) * (12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3) + (A - (1 / 250)) * (12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3) := by ring
    have hp : 0 ≤ ((3 / 250) - A) * (12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (1 / 250) - (τ - 2) * (1 / 250)) + (τ - 2) ^ 3) + (A - (1 / 250)) * (12 * τ ^ 2 * (((-347) / 312500) + (1179 / 2500) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3) :=
      add_nonneg (mul_nonneg (by linarith) e0) (mul_nonneg (by linarith) e1)
    nlinarith
  have hg : (τ - 2) ^ 3 / (12 * τ ^ 2) * (12 * τ ^ 2) = (τ - 2) ^ 3 := div_mul_cancel₀ _ (ne_of_gt hτ2)
  nlinarith

/-- Chord 3 (`3/250 ≤ A ≤ 9/196`). -/
theorem hh2_chord3 {τ A : ℝ} (h2 : 2 ≤ τ) (h7 : τ ≤ 7 / 2) (hA0 : (3 / 250) ≤ A) (hA1 : A ≤ (9 / 196)) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ ((-98669) / 9800000) + (12197 / 10000) * A := by
  have e0 := (hh2_chord_e3_3 τ h2 h7).le
  have e1 := (hh2_chord_e3_4_l0 τ h2 h7).le
  have hτ2 : 0 < 12 * τ ^ 2 := by positivity
  have key : 0 ≤ 12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * A - (τ - 2) * A) + (τ - 2) ^ 3 := by
    have hc : ((9 / 196) - (3 / 250)) * (12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * A - (τ - 2) * A) + (τ - 2) ^ 3) =
        ((9 / 196) - A) * (12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3) + (A - (3 / 250)) * (12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (9 / 196) - (τ - 2) * (9 / 196)) + (τ - 2) ^ 3) := by ring
    have hp : 0 ≤ ((9 / 196) - A) * (12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (3 / 250) - (τ - 2) * (3 / 250)) + (τ - 2) ^ 3) + (A - (3 / 250)) * (12 * τ ^ 2 * (((-98669) / 9800000) + (12197 / 10000) * (9 / 196) - (τ - 2) * (9 / 196)) + (τ - 2) ^ 3) :=
      add_nonneg (mul_nonneg (by linarith) e0) (mul_nonneg (by linarith) e1)
    nlinarith
  have hg : (τ - 2) ^ 3 / (12 * τ ^ 2) * (12 * τ ^ 2) = (τ - 2) ^ 3 := div_mul_cancel₀ _ (ne_of_gt hτ2)
  nlinarith

/-- Chord 4 (`A ≥ 9/196`, the endpoint `τ = 7/2`). -/
theorem hh2_chord4 {τ A : ℝ} (h2 : 2 ≤ τ) (h7 : τ ≤ 7 / 2) (hA0 : (9 / 196) ≤ A) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ ((-56201) / 2450000) + (3 / 2) * A := by
  have e1 := (hh2_chord_e4_5_l0 τ h2 h7).le
  have hτ2 : 0 < 12 * τ ^ 2 := by positivity
  have hm : 0 ≤ (7 / 2 - τ) * (A - (9 / 196)) := mul_nonneg (by linarith) (by linarith)
  have key : 0 ≤ 12 * τ ^ 2 * (((-56201) / 2450000) + (3 / 2) * A - (τ - 2) * A) + (τ - 2) ^ 3 := by
    have hc : 12 * τ ^ 2 * (((-56201) / 2450000) + (3 / 2) * A - (τ - 2) * A) + (τ - 2) ^ 3 =
        (12 * τ ^ 2 * (((-56201) / 2450000) + (3 / 2) * (9 / 196) - (τ - 2) * (9 / 196)) + (τ - 2) ^ 3) + 12 * τ ^ 2 * ((7 / 2 - τ) * (A - (9 / 196))) := by ring
    rw [hc]
    have : 0 ≤ 12 * τ ^ 2 * ((7 / 2 - τ) * (A - (9 / 196))) := mul_nonneg hτ2.le hm
    linarith
  have hg : (τ - 2) ^ 3 / (12 * τ ^ 2) * (12 * τ ^ 2) = (τ - 2) ^ 3 := div_mul_cancel₀ _ (ne_of_gt hτ2)
  nlinarith

/-- The central face against chord `0`: `G₂ + ℓ0(A) < 0` for any `ℓ` below the log majorant
(`hh2CnL0_pos`). -/
theorem hh2_cen_line0 {x al be t ℓ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 4 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 229 / 1024)
    (hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1)) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + ℓ + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (0 + 0 * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) < 0 := by
  calc _ ≤ (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (0 + 0 * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) := by gcongr
    _ < 0 := by
      have hS : (0 : ℝ) < 1 + x := by linarith
      have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      rw [hh2_Ws_central _ _ _ _ hal0.ne' hS.ne' hK.ne', hh2_ELs_central _ _ _ _ hal0.ne' hS.ne' hK.ne']
      unfold hsQc hsRA
      have hc := hh2CnL0_pos t x al ht0 ht1 hx hx2 hal hal'
      rw [hh2CnL0_eq] at hc
      exact hh2_combine (M := ((x * (x + 2) + al ^ 2) ^ 3 * (al) * (al + be))) (Ud := (9600 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_cen_stage1_G (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_stage1_A (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_uC x be hS.ne' hbe1.ne') (hh2_cen_stage2_G t x al be hbe) (hh2_cen_stage2_A t x al be hbe)
        (hh2_cen_stage2_D t x al be hbe) hc

/-- The central face against chord `1`: `G₂ + ℓ1(A) < 0` for any `ℓ` below the log majorant
(`hh2CnL1_pos`). -/
theorem hh2_cen_line1 {x al be t ℓ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 4 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 229 / 1024)
    (hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1)) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + ℓ + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (0 + (97 / 500) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) < 0 := by
  calc _ ≤ (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (0 + (97 / 500) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) := by gcongr
    _ < 0 := by
      have hS : (0 : ℝ) < 1 + x := by linarith
      have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      rw [hh2_Ws_central _ _ _ _ hal0.ne' hS.ne' hK.ne', hh2_ELs_central _ _ _ _ hal0.ne' hS.ne' hK.ne']
      unfold hsQc hsRA
      have hc := hh2CnL1_pos t x al ht0 ht1 hx hx2 hal hal'
      rw [hh2CnL1_eq] at hc
      exact hh2_combine (M := ((x * (x + 2) + al ^ 2) ^ 3 * (al) * (al + be))) (Ud := (9600 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_cen_stage1_G (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_stage1_A (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_uC x be hS.ne' hbe1.ne') (hh2_cen_stage2_G t x al be hbe) (hh2_cen_stage2_A t x al be hbe)
        (hh2_cen_stage2_D t x al be hbe) hc

/-- The central face against chord `2`: `G₂ + ℓ2(A) < 0` for any `ℓ` below the log majorant
(`hh2CnL2_pos`). -/
theorem hh2_cen_line2 {x al be t ℓ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 4 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 229 / 1024)
    (hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1)) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + ℓ + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (((-347) / 312500) + (1179 / 2500) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) < 0 := by
  calc _ ≤ (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (((-347) / 312500) + (1179 / 2500) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) := by gcongr
    _ < 0 := by
      have hS : (0 : ℝ) < 1 + x := by linarith
      have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      rw [hh2_Ws_central _ _ _ _ hal0.ne' hS.ne' hK.ne', hh2_ELs_central _ _ _ _ hal0.ne' hS.ne' hK.ne']
      unfold hsQc hsRA
      have hc := hh2CnL2_pos t x al ht0 ht1 hx hx2 hal hal'
      rw [hh2CnL2_eq] at hc
      exact hh2_combine (M := ((x * (x + 2) + al ^ 2) ^ 3 * (al) * (al + be))) (Ud := (9600 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_cen_stage1_G (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_stage1_A (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_uC x be hS.ne' hbe1.ne') (hh2_cen_stage2_G t x al be hbe) (hh2_cen_stage2_A t x al be hbe)
        (hh2_cen_stage2_D t x al be hbe) hc

/-- The central face against chord `3`: `G₂ + ℓ3(A) < 0` for any `ℓ` below the log majorant
(`hh2CnL3_pos`). -/
theorem hh2_cen_line3 {x al be t ℓ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 4 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 229 / 1024)
    (hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1)) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + ℓ + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (((-98669) / 9800000) + (12197 / 10000) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) < 0 := by
  calc _ ≤ (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (((-98669) / 9800000) + (12197 / 10000) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) := by gcongr
    _ < 0 := by
      have hS : (0 : ℝ) < 1 + x := by linarith
      have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      rw [hh2_Ws_central _ _ _ _ hal0.ne' hS.ne' hK.ne', hh2_ELs_central _ _ _ _ hal0.ne' hS.ne' hK.ne']
      unfold hsQc hsRA
      have hc := hh2CnL3_pos t x al ht0 ht1 hx hx2 hal hal'
      rw [hh2CnL3_eq] at hc
      exact hh2_combine (M := ((x * (x + 2) + al ^ 2) ^ 3 * (al) * (al + be))) (Ud := (9600 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_cen_stage1_G (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_stage1_A (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_uC x be hS.ne' hbe1.ne') (hh2_cen_stage2_G t x al be hbe) (hh2_cen_stage2_A t x al be hbe)
        (hh2_cen_stage2_D t x al be hbe) hc

/-- The central face against chord `4`: `G₂ + ℓ4(A) < 0` for any `ℓ` below the log majorant
(`hh2CnL4_pos`). -/
theorem hh2_cen_line4 {x al be t ℓ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 4 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 229 / 1024)
    (hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1)) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + ℓ + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (((-56201) / 2450000) + (3 / 2) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) < 0 := by
  calc _ ≤ (hsWs x be al (hsUC x be) (hsQc x al) - 1) * 2 + 1 / 2 + ((hsUC x be - 1) / hsRA al be + hsRA al be + 1 - hsQc x al - hsELs x be al (hsUC x be) (hsQc x al)) + (-296 / 1029 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) - (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (hsQc x al / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4) + (((-56201) / 2450000) + (3 / 2) * ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4))) := by gcongr
    _ < 0 := by
      have hS : (0 : ℝ) < 1 + x := by linarith
      have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      rw [hh2_Ws_central _ _ _ _ hal0.ne' hS.ne' hK.ne', hh2_ELs_central _ _ _ _ hal0.ne' hS.ne' hK.ne']
      unfold hsQc hsRA
      have hc := hh2CnL4_pos t x al ht0 ht1 hx hx2 hal hal'
      rw [hh2CnL4_eq] at hc
      exact hh2_combine (M := ((x * (x + 2) + al ^ 2) ^ 3 * (al) * (al + be))) (Ud := (9600 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_cen_stage1_G (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_stage1_A (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_uC x be hS.ne' hbe1.ne') (hh2_cen_stage2_G t x al be hbe) (hh2_cen_stage2_A t x al be hbe)
        (hh2_cen_stage2_D t x al be hbe) hc

/-- Duration elimination with the cubic loss (`CENTRAL_RATIO_HAND_SIGN` (9)-(10), with `τ` in
place of `T` in the loss): `G(τ) ≤ G(2) + ((τ - 2)A - (τ - 2)³/(12τ²))` for `τ ≥ 2`. -/
theorem hh2_tau_cubic {W c k τ : ℝ} (hk : 0 < k) (h2 : 2 ≤ τ) :
    (W - 1) * τ + 1 / τ + c + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      (W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4) +
        ((τ - 2) * ((1 - 7 * k / 4) * (W - 3 / 4)) - (τ - 2) ^ 3 / (12 * τ ^ 2)) := by
  have hτ0 : 0 < τ := by linarith
  have hlog : log (τ * k) = log (2 * k) + log (τ / 2) := by
    rw [← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hcl := hh2_log_le_cubic_loss (z := τ / 2) (by linarith)
  have e1 : (τ / 2 - 1 / (τ / 2)) / 2 - (τ / 2 - 1) ^ 3 / (6 * (τ / 2) ^ 2) =
      τ / 4 - 1 / τ - (τ - 2) ^ 3 / (12 * τ ^ 2) := by field_simp; ring
  rw [e1] at hcl
  rw [hlog]
  nlinarith [hcl]

/-- The strip coordinate `t = c₊(x) - (β - x)/(α - 1) ∈ [0, 229/1024]` (`CENTRAL_RATIO_HAND_SIGN` (6)-(7);
`t = 0` when `α = 1`). -/
theorem hh2_strip_t {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 229 / 1024 ∧ be = x + ((24 * x + 51) / 128 - t) * (al - 1) := by
  rcases eq_or_lt_of_le hal with h | h
  · subst h
    refine ⟨0, le_refl _, by norm_num, ?_⟩
    simp only [sub_self, mul_zero, zero_div, add_zero] at hb hb' ⊢
    linarith
  · have ha : 0 < al - 1 := by linarith
    refine ⟨(24 * x + 51) / 128 - (be - x) / (al - 1), ?_, ?_, ?_⟩
    · have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ (24 * x + 51) / 128 * (al - 1) := by
        rw [div_le_iff₀ (by positivity)]
        have hq : 0 ≤ (24 * x + 51) * (4 * x ^ 2 + 11 * x + 1) - 128 * x * (7 * x + 1) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), sq_nonneg (x - 9 / 4),
            mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx)]
        nlinarith [mul_nonneg ha.le hq]
      have : (be - x) / (al - 1) ≤ (24 * x + 51) / 128 := by
        rw [div_le_iff₀ ha]; linarith
      linarith
    · have h1 : 5 / 8 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      have : 5 / 8 ≤ (be - x) / (al - 1) := by
        rw [le_div_iff₀ ha]; linarith
      linarith
    · field_simp
      ring

/-- **The central sharp-ratio face** (`hs2_central_sign`). -/
theorem hs2_central_sign_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ * hsQc x al ≤ hsRA al be) :
    hsF x be al (hsUC x be) (hsQc x al) τ (log (τ * hsQc x al / hsRA al be))
      (2 - 7 * τ * hsQc x al / (4 * hsRA al be)) < 0 := by
  have hal' : al ≤ 4 / 3 := by
    nlinarith [sq_nonneg (al - 4 / 3), mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  obtain ⟨t, ht0, ht1, hbe⟩ := hh2_strip_t hx hx2 hal hb hb'
  have hal0 : 0 < al := by linarith
  have hbx : x ≤ be := by
    rw [hbe]
    have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hB : 0 < al + be := by linarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hq : 0 < hsQc x al := by unfold hsQc; positivity
  have hk : 0 < hsQc x al / hsRA al be := by positivity
  have hτk : τ * (hsQc x al / hsRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    exact hτT
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hk27 : 2 / 7 ≤ hsQc x al / hsRA al be := by
    have e : hsQc x al / hsRA al be = al * (al + be) / (x * (x + 2) + al ^ 2) := by
      unfold hsQc hsRA
      field_simp
    rw [e, le_div_iff₀ hK]
    have h1 : 1 * x ≤ al * be := mul_le_mul hal hbx (by linarith) hal0.le
    nlinarith
  have hτ7 : τ ≤ 7 / 2 := by
    have := mul_le_mul_of_nonneg_left hk27 (by linarith : (0 : ℝ) ≤ τ)
    linarith
  rw [hh2_hsF_face]
  have hl := hh2_log_le_bound (y := 2 * (hsQc x al / hsRA al be)) (by positivity)
  refine lt_of_le_of_lt (hh2_tau_cubic hk hτ) ?_
  by_cases h0 : ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4)) ≤ 0
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord0 hτ h0))
      (hh2_cen_line0 hx hx2 hal hal' ht0 ht1 hbe hl)
  by_cases h1 : ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4)) ≤ (1 / 250)
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord1 hτ hτ7 (by linarith) h1))
      (hh2_cen_line1 hx hx2 hal hal' ht0 ht1 hbe hl)
  by_cases h2 : ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4)) ≤ (3 / 250)
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord2 hτ hτ7 (by linarith) h2))
      (hh2_cen_line2 hx hx2 hal hal' ht0 ht1 hbe hl)
  by_cases h3 : ((1 - 7 * (hsQc x al / hsRA al be) / 4) * (hsWs x be al (hsUC x be) (hsQc x al) - 3 / 4)) ≤ (9 / 196)
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord3 hτ hτ7 (by linarith) h3))
      (hh2_cen_line3 hx hx2 hal hal' ht0 ht1 hbe hl)
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord4 hτ hτ7 (by linarith)))
      (hh2_cen_line4 hx hx2 hal hal' ht0 ht1 hbe hl)

end SmoothedOctagon

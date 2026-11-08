module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOuter

/-!
# Gate S1 by hand, central face: the norm and beta reductions

`SHORT_CENTRAL_REDUCTION`, `SHORT_CENTRAL_NORM_MONOTONICITY`. On the central face
(`x(x + 2) ≥ 6α²`, so `x ≥ √7 - 1 > 41/25` and `α ≤ α_U(x) = (1013x + 676)/2340`), with the
order strip `x + (α - 1)/2 ≤ β ≤ x + (10/13)(α - 1)`:

* both tests are concave quadratics in `u`, with `(F₀)_u ≤ (F₁)_u` (`T ≥ 2`, `w_u ≤ 0`) and
  `(F₁)_u(3/4) = Ψ = Γ_u - cH < 0`, where `H = α′B/(αK) + η′/(αK) + γ′/(αKB)` increases in `B`
  (`α′ > 0`, `γ′ = D₀(D₀ - S³) < 0`; `NORM_MONOTONICITY` (2)-(3)), so `Ψ ≤ Ψ(x + (α - 1)/2) < 0`;
  hence both tests decrease in `u ≥ 3/4` (`hl1c_F1_ustep`, `hl1c_F0_ustep`);
* `(F₀)_u ≥ -1/5` for `u ≤ 19/25` (concave in `β`, two endpoint signs; `REDUCTION` (2));
* `(r₀)_β ≥ 1/40 + 1/1000` (increasing in `β` by `B³ ≥ 27α²(β - α)`, `18α(x - α) > K`, and in `u`;
  `REDUCTION` (3), sign `P₀`) and `(r₁)_β ≥ 1/40 + 1/1000` at `u = 19/25`
  (`(r₁)_β = (u - 1)/α + 4uηx/(αK) + 1/B - Q₀/B²` with `Q₀ ≥ 3α/2 ≥ B/2`, sign `P₁`, `P_Q`);
  hence `F₀` decreases in `β` along the ceiling `u_ℓ(x, β)` (`|(u_ℓ)_β| ≤ 15/1992`) and `F₁`
  decreases in `β` at `u = 19/25` (`hl1c_F0_bstep`, `hl1c_F1_bstep`).

Route: the two-variable signs are bounded termwise on boxes in `(x, α)` (or below the tangent
chord `α_U` of the cap) instead of the shape derivative `P_a` and the univariate residual of
`NORM_MONOTONICITY` §§3-5; the cubic logarithm majorant of the Lean tests is kept, its defect
`ε(y) ≤ 1/625` absorbed by the `1/1000` slack.

## Main API

* `hl1c_F0_uquad`, `hl1c_F1_uquad`, `hl1c_Psi_neg`, `hl1c_F1_ustep`, `hl1c_F0_ustep`,
  `hl1c_F0u_ge`, `hl1c_R2b_ge`, `hl1c_R1b_ge`, `hl1c_F1_bstep`, `hl1c_F0_bstep`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `Q₀ = (α²K + M + uD₀² - D₀E - 3K²/4)/(αK)` (`SHORT_CENTRAL_REDUCTION` §2). -/
noncomputable def hl1cQ0 (x a u : ℝ) : ℝ :=
  (a ^ 2 * hh1cK x a + (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + u * hl1oD0 x a ^ 2 -
    hl1oD0 x a * ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1) - 3 / 4 * hh1cK x a ^ 2) / (a * hh1cK x a)

/-- `(r₁)_β = (u - 1)/α + 4uηx/(αK) + 1/B - Q₀/B²` (`SHORT_CENTRAL_REDUCTION` §2). -/
noncomputable def hl1cR1bf (x a b u : ℝ) : ℝ :=
  (u - 1) / a + 4 * u * (x - a) * x / (a * hh1cK x a) + 1 / (a + b) - hl1cQ0 x a u / (a + b) ^ 2

theorem hl1c_R1b_eq {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : 0 < a + b) :
    hh1cR1b x a b u = hl1cR1bf x a b u := by
  have hK : hh1cK x a ≠ 0 := by unfold hh1cK; positivity
  have hS : 1 + x ≠ 0 := by linarith
  have hab0 : a + b ≠ 0 := hab.ne'
  have hD : hsDg x b a = hl1oD0 x a - 2 * (x - a) * (a + b) := by unfold hsDg hl1oD0; ring
  simp only [hh1cR1b, hh1cR2b, hh1cTb, hh1cwb, hh1cdb, hh1cw, hh1cT, hh1cd, hh1cL, hh1cv, hh1cE,
    hl1cR1bf, hl1cQ0, hD]
  unfold hh1cK at hK ⊢
  field_simp
  ring

/-- Numerator of `-Ψ(x, α, x + (α - 1)/2)` (`SHORT_CENTRAL_NORM_MONOTONICITY` (2)-(7)). -/
noncomputable def hl1cPphix (x a : ℝ) : ℝ :=
  -1 / 16 * x ^ 11 * a + 7 / 24 * x ^ 11 - 3 / 32 * x ^ 10 * a ^ 2 - 19 / 32 * x ^ 10 * a + 35 / 12 * x ^ 10 - 1 / 8 * x ^ 9 * a ^ 3 - 23 / 32 * x ^ 9 * a ^ 2 - 155 / 96 * x ^ 9 * a + 133 / 16 * x ^ 9 - 3 / 16 * x ^ 8 * a ^ 4 - 15 / 16 * x ^ 8 * a ^ 3 - 373 / 192 * x ^ 8 * a ^ 2 + 115 / 96 * x ^ 8 * a + 427 / 192 * x ^ 8 - 1 / 16 * x ^ 7 * a ^ 5 - 151 / 96 * x ^ 7 * a ^ 4 - 179 / 96 * x ^ 7 * a ^ 3 - 367 / 96 * x ^ 7 * a ^ 2 + 405 / 32 * x ^ 7 * a - 91 / 4 * x ^ 7 - 3 / 32 * x ^ 6 * a ^ 6 - 11 / 32 * x ^ 6 * a ^ 5 - 19 / 4 * x ^ 6 * a ^ 4 + 175 / 96 * x ^ 6 * a ^ 3 - 517 / 96 * x ^ 6 * a ^ 2 + 56 / 3 * x ^ 6 * a - 231 / 8 * x ^ 6 - 9 / 16 * x ^ 5 * a ^ 6 - 1 / 2 * x ^ 5 * a ^ 5 - 389 / 96 * x ^ 5 * a ^ 4 + 827 / 96 * x ^ 5 * a ^ 3 + 121 / 48 * x ^ 5 * a ^ 2 + 187 / 48 * x ^ 5 * a - 7 * x ^ 5 - 191 / 192 * x ^ 4 * a ^ 6 + 13 / 48 * x ^ 4 * a ^ 5 + 1105 / 192 * x ^ 4 * a ^ 4 + 137 / 32 * x ^ 4 * a ^ 3 + 1123 / 96 * x ^ 4 * a ^ 2 - 231 / 32 * x ^ 4 * a + 7 / 12 * x ^ 4 + 7 / 48 * x ^ 3 * a ^ 6 + 25 / 48 * x ^ 3 * a ^ 5 + 491 / 48 * x ^ 3 * a ^ 4 - 33 / 8 * x ^ 3 * a ^ 3 + 73 / 24 * x ^ 3 * a ^ 2 - 35 / 24 * x ^ 3 * a + 131 / 96 * x ^ 2 * a ^ 6 - 31 / 96 * x ^ 2 * a ^ 5 + 5 / 2 * x ^ 2 * a ^ 4 - 59 / 48 * x ^ 2 * a ^ 3 - 3 / 8 * x ^ 2 * a ^ 2 + 1 / 8 * x ^ 2 * a + 9 / 16 * x * a ^ 6 - 1 / 4 * x * a ^ 5 - 3 / 8 * x * a ^ 4 + 1 / 8 * x * a ^ 3 - 3 / 32 * a ^ 6 + 1 / 32 * a ^ 5

/-- Its shift to the domain variables. -/
noncomputable def hl1cPphis (t s : ℝ) : ℝ :=
  -1 / 16 * t ^ 11 * s + 11 / 48 * t ^ 11 - 3 / 32 * t ^ 10 * s ^ 2 - 1527 / 800 * t ^ 10 * s + 1909 / 300 * t ^ 10 - 1 / 8 * t ^ 9 * s ^ 3 - 421 / 160 * t ^ 9 * s ^ 2 - 305821 / 12000 * t ^ 9 * s + 114469 / 1500 * t ^ 9 - 3 / 16 * t ^ 8 * s ^ 4 - 1413 / 400 * t ^ 8 * s ^ 3 - 800897 / 24000 * t ^ 8 * s ^ 2 - 9843893 / 50000 * t ^ 8 * s + 9812831 / 18750 * t ^ 8 - 1 / 16 * t ^ 7 * s ^ 5 - 10429 / 2400 * t ^ 7 * s ^ 4 - 860489 / 20000 * t ^ 7 * s ^ 3 - 12607681 / 50000 * t ^ 7 * s ^ 2 - 1229678851 / 1250000 * t ^ 7 * s + 1425661281 / 625000 * t ^ 7 - 3 / 32 * t ^ 6 * s ^ 6 - 1299 / 800 * t ^ 6 * s ^ 5 - 2618399 / 60000 * t ^ 6 * s ^ 4 - 111261317 / 375000 * t ^ 6 * s ^ 3 - 9355398883 / 7500000 * t ^ 6 * s ^ 2 - 787568649793 / 234375000 * t ^ 6 * s + 517133631497 / 78125000 * t ^ 6 - 297 / 200 * t ^ 5 * s ^ 6 - 81613 / 5000 * t ^ 5 * s ^ 5 - 11497774 / 46875 * t ^ 5 * s ^ 4 - 7949307447 / 6250000 * t ^ 5 * s ^ 3 - 1302055412581 / 312500000 * t ^ 5 * s ^ 2 - 188347700721677 / 23437500000 * t ^ 5 * s + 19014314689139 / 1464843750 * t ^ 5 - 225349 / 24000 * t ^ 4 * s ^ 6 - 12552541 / 150000 * t ^ 4 * s ^ 5 - 65192032 / 78125 * t ^ 4 * s ^ 4 - 102239150216 / 29296875 * t ^ 4 * s ^ 3 - 87888955599121 / 9375000000 * t ^ 4 * s ^ 2 - 262019282531021 / 19531250000 * t ^ 4 * s + 124775440732307 / 7324218750 * t ^ 4 - 93061 / 3125 * t ^ 3 * s ^ 6 - 147485701 / 625000 * t ^ 3 * s ^ 5 - 1627543586483 / 937500000 * t ^ 3 * s ^ 4 - 47365293311201 / 7812500000 * t ^ 3 * s ^ 3 - 134812757343783 / 9765625000 * t ^ 3 * s ^ 2 - 922441581765921 / 61035156250 * t ^ 3 * s + 2639681527299031 / 183105468750 * t ^ 3 - 367168247 / 7500000 * t ^ 2 * s ^ 6 - 84855528019 / 234375000 * t ^ 2 * s ^ 5 - 16549876635413 / 7812500000 * t ^ 2 * s ^ 4 - 231652355215687 / 36621093750 * t ^ 2 * s ^ 3 - 4570242976111697 / 366210937500 * t ^ 2 * s ^ 2 - 32373100675415549 / 3051757812500 * t ^ 2 * s + 16608189496661366 / 2288818359375 * t ^ 2 - 2996534717 / 78125000 * t * s ^ 6 - 66779271757 / 244140625 * t * s ^ 5 - 394676611014707 / 292968750000 * t * s ^ 4 - 532977954008458 / 152587890625 * t * s ^ 3 - 9237274867947201 / 1525878906250 * t * s ^ 2 - 2223686048760842951 / 572204589843750 * t * s + 174259749816138602 / 95367431640625 * t - 494598400913 / 46875000000 * s ^ 6 - 21947334682793 / 292968750000 * s ^ 5 - 2372506168490039 / 7324218750000 * s ^ 4 - 33395623863650479 / 45776367187500 * s ^ 3 - 1272917019304185373 / 1144409179687500 * s ^ 2 - 3142515575063088028 / 7152557373046875 * s + 343361369485386912 / 2384185791015625

theorem hl1cPphis_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) ≤ hl1cPphis t s := by
  unfold hl1cPphis
  have q0 := hs1
  have q1 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s)
  have q2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q3 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 3)
  have q4 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 4)
  have q5 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 5)
  have q6 := (by positivity : (0 : ℝ) ≤ t)
  have q7 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t)
  have q8 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s)
  have q9 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q10 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 3)
  have q11 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 4)
  have q12 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 5)
  have q13 := (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q14 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q15 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s)
  have q16 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q17 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3)
  have q18 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q19 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 5)
  have q20 := (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q21 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q22 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s)
  have q23 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q24 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3)
  have q25 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q26 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 5)
  have q27 := (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q28 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q29 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s)
  have q30 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2)
  have q31 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 3)
  have q32 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q33 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 5)
  have q34 := (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q35 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q36 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q37 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q38 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 3)
  have q39 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q40 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 5)
  have q41 := (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q42 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q43 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s)
  have q44 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q45 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 3)
  have q46 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q47 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 5)
  have q48 := (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q49 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q50 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s)
  have q51 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q52 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 3)
  have q53 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 4)
  have q54 := (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q55 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q56 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s)
  have q57 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q58 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 3)
  have q59 := (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q60 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q61 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 9 * s)
  have q62 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 9 * s ^ 2)
  have q63 := (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q64 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q65 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 10 * s)
  have q66 := (by positivity : (0 : ℝ) ≤ t ^ 11)
  have q67 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 11)
  ring_nf at *
  linarith

theorem hl1cPphix_eq (x a : ℝ) : hl1cPphix x a = hl1cPphis (x - 41 / 25) (a - 1) := by
  unfold hl1cPphix hl1cPphis
  ring

theorem hl1cPphi_id {x a : ℝ} (hx : 41 / 25 ≤ x) (ha : 1 ≤ a) :
    -(hh1cGu x (3 / 4) - 7 / 96 * (hh1cR2u x a (x + (a - 1) / 2) + (hh1cT x a (x + (a - 1) / 2) - 2) * hh1cwu x a (x + (a - 1) / 2))) = hl1cPphix x a / ((a) * (x) ^ 2 * (2 * x + 3 * a - 1) * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hx2' : x + 2 ≠ 0 := by linarith
  have hKn : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  simp only [hh1cGu, hh1cR2u, hh1cwu, hh1cd, hh1cL, hh1cv, hh1cE, hsDg, hh1cK, hh1cT, hl1cPphix]
  rw [show a + (x + (a - 1) / 2) = (2 * x + 3 * a - 1) / 2 by ring]
  have hB : 2 * x + 3 * a - 1 ≠ 0 := by linarith
  generalize hBq : 2 * x + 3 * a - 1 = Bq at hB ⊢
  field_simp
  subst hBq
  ring

/-- Numerator of `(F₀)_u(19/25) + 1/5` at `β = x + (α - 1)/2` (`SHORT_CENTRAL_REDUCTION` (2)). -/
noncomputable def hl1cPu0x (x a : ℝ) : ℝ :=
  3 / 100 * x ^ 10 * a - 31 / 480 * x ^ 9 * a - 7 / 96 * x ^ 9 + 3 / 50 * x ^ 8 * a ^ 3 + 7 / 48 * x ^ 8 * a ^ 2 - 9023 / 4800 * x ^ 8 * a - 35 / 64 * x ^ 8 + 559 / 800 * x ^ 7 * a ^ 3 + 35 / 24 * x ^ 7 * a ^ 2 - 9397 / 2400 * x ^ 7 * a - 35 / 24 * x ^ 7 + 3 / 100 * x ^ 6 * a ^ 5 + 1231 / 300 * x ^ 6 * a ^ 3 + 245 / 96 * x ^ 6 * a ^ 2 + 577 / 160 * x ^ 6 * a - 35 / 24 * x ^ 6 + 9 / 50 * x ^ 5 * a ^ 5 - 49 / 96 * x ^ 5 * a ^ 4 + 4867 / 480 * x ^ 5 * a ^ 3 - 119 / 48 * x ^ 5 * a ^ 2 + 14561 / 1200 * x ^ 5 * a + 119 / 960 * x ^ 4 * a ^ 5 - 301 / 192 * x ^ 4 * a ^ 4 + 1351 / 160 * x ^ 4 * a ^ 3 - 259 / 48 * x ^ 4 * a ^ 2 + 109 / 24 * x ^ 4 * a + 7 / 12 * x ^ 4 - 199 / 240 * x ^ 3 * a ^ 5 - 7 / 48 * x ^ 3 * a ^ 4 - 367 / 300 * x ^ 3 * a ^ 3 + 7 / 6 * x ^ 3 * a ^ 2 - 23 / 300 * x ^ 3 * a - 59 / 48 * x ^ 2 * a ^ 5 + 91 / 48 * x ^ 2 * a ^ 4 - 1307 / 600 * x ^ 2 * a ^ 3 + 7 / 12 * x ^ 2 * a ^ 2 + 3 / 25 * x ^ 2 * a - 39 / 200 * x * a ^ 5 + 3 / 25 * x * a ^ 3 + 3 / 100 * a ^ 5

/-- Its shift to the domain variables. -/
noncomputable def hl1cPu0s (t s : ℝ) : ℝ :=
  42822549131042693 / 2338611238080000000 * t ^ 11 - 13792131060241 / 199881302400000 * t ^ 10 * s + 23916048672868624243 / 58465280952000000000 * t ^ 10 + 4367578877 / 42709680000 * t ^ 9 * s ^ 2 - 837929704814791 / 499703256000000 * t ^ 9 * s + 162165806919771609206347 / 42095002285440000000000 * t ^ 9 - 2121289 / 18252000 * t ^ 8 * s ^ 3 + 499963055473 / 177957000000 * t ^ 8 * s ^ 2 - 67161287492326472711 / 3597863443200000000 * t ^ 8 * s + 21277991024656510038851831 / 1052375057136000000000000 * t ^ 8 + 1013 / 15600 * t ^ 7 * s ^ 4 - 1202787167 / 456300000 * t ^ 7 * s ^ 3 + 131472016957847183 / 3843871200000000 * t ^ 7 * s ^ 2 - 2840654320104240863999 / 22486646520000000000 * t ^ 7 * s + 54996850940404679246904631 / 822168013387500000000000 * t ^ 7 - 3 / 100 * t ^ 6 * s ^ 5 + 459581 / 390000 * t ^ 6 * s ^ 4 - 41782019250763 / 1642680000000 * t ^ 6 * s ^ 3 + 2513919878839471573 / 10677420000000000 * t ^ 6 * s ^ 2 - 323495161087062834391217 / 562166163000000000000 * t ^ 6 * s + 3590985983460137970997088491 / 22838000371875000000000000 * t ^ 6 - 297 / 625 * t ^ 5 * s ^ 5 + 11155894247 / 1404000000 * t ^ 5 * s ^ 4 - 2789473581846283 / 20533500000000 * t ^ 5 * s ^ 3 + 2397646469273890477943 / 2402419500000000000 * t ^ 5 * s ^ 2 - 128536650223138785563086727 / 70270770375000000000000 * t ^ 5 * s + 12960262336808074324349617205107 / 41108400669375000000000000000 * t ^ 5 - 1686167 / 600000 * t ^ 4 * s ^ 5 + 171675564859 / 7020000000 * t ^ 4 * s ^ 4 - 89938518616888489 / 205335000000000 * t ^ 4 * s ^ 3 + 161805057622218135091013 / 60060487500000000000 * t ^ 4 * s ^ 2 - 2853548867484868138949896109 / 702707703750000000000000 * t ^ 4 * s + 125780544099512014042997005536491 / 205542003346875000000000000000 * t ^ 4 - 583738 / 78125 * t ^ 3 * s ^ 5 + 2652618810497 / 87750000000 * t ^ 3 * s ^ 4 - 5588771636011096799 / 6416718750000000 * t ^ 3 * s ^ 3 + 6964903621177876493475797 / 1501512187500000000000 * t ^ 3 * s ^ 2 - 53997689299979752752158013349 / 8783846296875000000000000 * t ^ 3 * s + 434544758947995259594117009088819 / 428212506972656250000000000000 * t ^ 3 - 1478756101 / 187500000 * t ^ 2 * s ^ 5 - 81478782572519 / 10968750000000 * t ^ 2 * s ^ 4 - 667992789959364276893 / 641671875000000000 * t ^ 2 * s ^ 3 + 14230416793886393757437291 / 2887523437500000000000 * t ^ 2 * s ^ 2 - 101741886449376468695451839393 / 16892012109375000000000000 * t ^ 2 * s + 37288566177153241441010096614080679 / 32115938022949218750000000000000 * t ^ 2 + 163942889 / 1953125000 * t * s ^ 5 - 27077776253972161 / 548437500000000 * t * s ^ 4 - 5474756167506642232159 / 8020898437500000000 * t * s ^ 3 + 23596934988834359366535521 / 8020898437500000000000 * t * s ^ 2 - 18840743526072693368375300087177 / 5489903935546875000000000000 * t * s + 24589216910951204049382678081242229387 / 32115938022949218750000000000000000 * t + 4262474925821 / 1171875000000 * s ^ 5 - 426493768533685993 / 13710937500000000 * s ^ 4 - 75234555539653020460411 / 401044921875000000000 * s ^ 3 + 17694252793152593889540866543 / 23461127929687500000000000 * s ^ 2 - 2365053727391946710097198994870579 / 2744951967773437500000000000000 * s + 174135066787602007454938967132512733447 / 802898450573730468750000000000000000

theorem hl1cPu0s_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (31 / 200 : ℝ)) :
    (0 : ℝ) ≤ hl1cPu0s t s := by
  unfold hl1cPu0s
  have q0 := hs1
  have q1 := (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q3 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 3)
  have q4 := (by positivity : (0 : ℝ) ≤ s ^ 5)
  have q5 := (by positivity : (0 : ℝ) ≤ t)
  have q6 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t)
  have q7 := (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q8 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q9 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 3)
  have q10 := (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q11 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q12 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q13 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q14 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3)
  have q15 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s ^ 5)
  have q16 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q17 := (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q18 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q19 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q20 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q21 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q22 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q23 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q24 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q25 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2)
  have q26 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2)
  have q27 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q28 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q29 := (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q30 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q31 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q32 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q33 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q34 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q35 := (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q36 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q37 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q38 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q39 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q40 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q41 := (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q42 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q43 := (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q44 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q45 := (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 4)
  have q46 := (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q47 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q48 := (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q49 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q50 := (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q51 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q52 := (by positivity : (0 : ℝ) ≤ t ^ 9 * s ^ 2)
  have q53 := (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q54 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q55 := (by positivity : (0 : ℝ) ≤ t ^ 11)
  ring_nf at *
  linarith

theorem hl1cPu0x_eq (x a : ℝ) : hl1cPu0x x a = hl1cPu0s (x - 41 / 25) ((1013 * x + 676) / 2340 - a) := by
  unfold hl1cPu0x hl1cPu0s
  ring

theorem hl1cPu0_id {x a : ℝ} (hx : 41 / 25 ≤ x) (ha : 1 ≤ a) :
    hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a (x + (a - 1) / 2) + 1 / 5 = hl1cPu0x x a / ((a) * (x) ^ 2 * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hx2' : x + 2 ≠ 0 := by linarith
  have hKn : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  simp only [hh1cGu, hh1cR2u, hh1cwu, hh1cd, hh1cL, hh1cv, hh1cE, hsDg, hh1cK, hh1cT, hl1cPu0x]
  field_simp
  ring

/-- Numerator of `(F₀)_u(19/25) + 1/5` at `β = x + (10/13)(α - 1)`. -/
noncomputable def hl1cPu1x (x a : ℝ) : ℝ :=
  3 / 100 * x ^ 10 * a - 31 / 480 * x ^ 9 * a - 7 / 96 * x ^ 9 + 3 / 50 * x ^ 8 * a ^ 3 + 7 / 104 * x ^ 8 * a ^ 2 - 14203 / 7800 * x ^ 8 * a - 329 / 624 * x ^ 8 + 24251 / 31200 * x ^ 7 * a ^ 3 + 7 / 16 * x ^ 7 * a ^ 2 - 97661 / 31200 * x ^ 7 * a - 203 / 156 * x ^ 7 + 3 / 100 * x ^ 6 * a ^ 5 + 692379 / 135200 * x ^ 6 * a ^ 3 - 4753 / 4056 * x ^ 6 * a ^ 2 + 473839 / 81120 * x ^ 6 * a - 77 / 78 * x ^ 6 + 9 / 50 * x ^ 5 * a ^ 5 - 5635 / 16224 * x ^ 5 * a ^ 4 + 343591 / 27040 * x ^ 5 * a ^ 3 - 9681 / 1352 * x ^ 5 * a ^ 2 + 682271 / 50700 * x ^ 5 * a + 49 / 78 * x ^ 5 - 14077 / 81120 * x ^ 4 * a ^ 5 - 3395 / 8112 * x ^ 4 * a ^ 4 + 236159 / 27040 * x ^ 4 * a ^ 3 - 11641 / 2028 * x ^ 4 * a ^ 2 + 13913 / 4056 * x ^ 4 * a + 35 / 39 * x ^ 4 - 10237 / 5070 * x ^ 3 * a ^ 5 + 10115 / 4056 * x ^ 3 * a ^ 4 - 116149 / 25350 * x ^ 3 * a ^ 3 + 3437 / 1014 * x ^ 3 * a ^ 2 - 127 / 325 * x ^ 3 * a - 2453 / 1014 * x ^ 2 * a ^ 5 + 2625 / 676 * x ^ 2 * a ^ 4 - 333583 / 101400 * x ^ 2 * a ^ 3 + 35 / 39 * x ^ 2 * a ^ 2 + 3 / 25 * x ^ 2 * a - 39 / 200 * x * a ^ 5 + 3 / 25 * x * a ^ 3 + 3 / 100 * a ^ 5

/-- Its shift to the domain variables. -/
noncomputable def hl1cPu1s (t s : ℝ) : ℝ :=
  42822549131042693 / 2338611238080000000 * t ^ 11 - 13792131060241 / 199881302400000 * t ^ 10 * s + 23428125131257436743 / 58465280952000000000 * t ^ 10 + 4367578877 / 42709680000 * t ^ 9 * s ^ 2 - 826017010953541 / 499703256000000 * t ^ 9 * s + 12899869625406572247297259 / 3557027693119680000000000 * t ^ 9 - 2121289 / 18252000 * t ^ 8 * s ^ 3 + 252068698049 / 88978500000 * t ^ 8 * s ^ 2 - 5495650351057161716267 / 304019460950400000000 * t ^ 8 * s + 1575568394070612731568759407 / 88925692327992000000000000 * t ^ 8 + 1013 / 15600 * t ^ 7 * s ^ 4 - 1238618417 / 456300000 * t ^ 7 * s ^ 3 + 11310396820605004151 / 324807116400000000 * t ^ 7 * s ^ 2 - 114213994272250885888489 / 950060815470000000000 * t ^ 7 * s + 28705636809852978502683739931 / 555785577049950000000000000 * t ^ 7 - 3 / 100 * t ^ 6 * s ^ 5 + 459581 / 390000 * t ^ 6 * s ^ 4 - 3758803374512911 / 138806460000000 * t ^ 6 * s ^ 3 + 653298780215250010943 / 2706725970000000000 * t ^ 6 * s ^ 2 - 25655614618241914252923149 / 47503040773500000000000 * t ^ 6 * s + 1159267596001845853666633989937 / 11578866188540625000000000000 * t ^ 6 - 297 / 625 * t ^ 5 * s ^ 5 + 885627493559 / 118638000000 * t ^ 5 * s ^ 4 - 259159973026515601 / 1735080750000000 * t ^ 5 * s ^ 3 + 208397511740615625978371 / 203004447750000000000 * t ^ 5 * s ^ 2 - 10101155903218781885146814369 / 5937880096687500000000000 * t ^ 5 * s + 616609606250308382778882684823729 / 3473659856562187500000000000000 * t ^ 5 - 127398299 / 50700000 * t ^ 4 * s ^ 5 + 11066617941523 / 593190000000 * t ^ 4 * s ^ 4 - 8594813804225760133 / 17350807500000000 * t ^ 4 * s ^ 3 + 14068589980925530238479661 / 5075111193750000000000 * t ^ 4 * s ^ 2 - 223090156242877629392511601523 / 59378800966875000000000000 * t ^ 4 * s + 6888017653052868161273329855931927 / 17368299282810937500000000000000 * t ^ 4 - 457391901 / 105625000 * t ^ 3 * s ^ 5 + 25691807901059 / 7414875000000 * t ^ 3 * s ^ 4 - 136637101445357531207 / 135553183593750000 * t ^ 3 * s ^ 3 + 604471203304291928748968909 / 126877779843750000000000 * t ^ 3 * s ^ 2 - 1052607908871483007053935774107 / 185558753021484375000000000 * t ^ 3 * s + 58130321707334273102542852448747911 / 72367913678378906250000000000000 * t ^ 3 + 62720545403 / 15843750000 * t ^ 2 * s ^ 5 - 61605048741557543 / 926859375000000 * t ^ 2 * s ^ 4 - 66542136623584923149021 / 54221273437500000000 * t ^ 2 * s ^ 3 + 16004191589640712210798781351 / 3171944496093750000000000 * t ^ 2 * s ^ 2 - 103002308182054584140220465654773 / 18555875302148437500000000000 * t ^ 2 * s + 2828264393878581294684758648597140813 / 2713796762939208984375000000000000 * t ^ 2 + 239147824091 / 12695312500 * t * s ^ 5 - 399218583333670609 / 3564843750000000 * t * s ^ 4 - 42596441640756761707471 / 52135839843750000000 * t * s ^ 3 + 677845297403007772788907279 / 225921972656250000000000 * t * s ^ 2 - 112802512484482844483747624258213 / 35684375581054687500000000000 * t * s + 153747212624242433883920434261436858203 / 208753597149169921875000000000000000 * t + 8343018376973 / 585937500000 * s ^ 5 - 389500555028225809 / 6855468750000000 * s ^ 4 - 45659959528891049103643 / 200522460937500000000 * s ^ 3 + 8987053394506162623951387959 / 11730563964843750000000000 * s ^ 2 - 1089127178516722464680876863796227 / 1372475983886718750000000000000 * s + 87098815982841471696969458358653358911 / 401449225286865234375000000000000000

theorem hl1cPu1s_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (31 / 200 : ℝ)) :
    (0 : ℝ) ≤ hl1cPu1s t s := by
  unfold hl1cPu1s
  have q0 := hs1
  have q1 := (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q3 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 3)
  have q4 := (by positivity : (0 : ℝ) ≤ s ^ 5)
  have q5 := (by positivity : (0 : ℝ) ≤ t)
  have q6 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t)
  have q7 := (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q8 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q9 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 3)
  have q10 := (by positivity : (0 : ℝ) ≤ t * s ^ 5)
  have q11 := (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q12 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q13 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q14 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q15 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3)
  have q16 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 5)
  have q17 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q18 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q19 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q20 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q21 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q22 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 5)
  have q23 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q24 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q25 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2)
  have q26 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2)
  have q27 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q28 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q29 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q30 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q31 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q32 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q33 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q34 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q35 := (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q36 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q37 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q38 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q39 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q40 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q41 := (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q42 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q43 := (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q44 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q45 := (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 4)
  have q46 := (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q47 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q48 := (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q49 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q50 := (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q51 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q52 := (by positivity : (0 : ℝ) ≤ t ^ 9 * s ^ 2)
  have q53 := (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q54 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q55 := (by positivity : (0 : ℝ) ≤ t ^ 11)
  ring_nf at *
  linarith

theorem hl1cPu1x_eq (x a : ℝ) : hl1cPu1x x a = hl1cPu1s (x - 41 / 25) ((1013 * x + 676) / 2340 - a) := by
  unfold hl1cPu1x hl1cPu1s
  ring

theorem hl1cPu1_id {x a : ℝ} (hx : 41 / 25 ≤ x) (ha : 1 ≤ a) :
    hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a (x + 10 / 13 * (a - 1)) + 1 / 5 = hl1cPu1x x a / ((a) * (x) ^ 2 * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hx2' : x + 2 ≠ 0 := by linarith
  have hKn : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  simp only [hh1cGu, hh1cR2u, hh1cwu, hh1cd, hh1cL, hh1cv, hh1cE, hsDg, hh1cK, hh1cT, hl1cPu1x]
  field_simp
  ring

/-- Numerator of `(r₀)_β - 1/40 - 1/1000` at `β = x`, `u = 3/4` (`SHORT_CENTRAL_REDUCTION` (3), `P₀`). -/
noncomputable def hl1cPb0x (x a : ℝ) : ℝ :=
  -513 / 500 * x ^ 6 * a - 1 / 4 * x ^ 6 - 263 / 250 * x ^ 5 * a ^ 2 + 3099 / 250 * x ^ 5 * a - x ^ 5 + 461 / 500 * x ^ 4 * a ^ 3 - 479 / 500 * x ^ 4 * a ^ 2 + 612 / 125 * x ^ 4 * a - x ^ 4 + 112 / 125 * x ^ 3 * a ^ 4 - 3276 / 125 * x ^ 3 * a ^ 3 + 99 / 125 * x ^ 3 * a ^ 2 + 3 * x ^ 3 * a - 39 / 500 * x ^ 2 * a ^ 5 - 1979 / 500 * x ^ 2 * a ^ 4 - 138 / 125 * x ^ 2 * a ^ 3 - 13 / 250 * x * a ^ 6 + 3849 / 250 * x * a ^ 5 - 4 * x * a ^ 4 - x * a ^ 3 - 13 / 500 * a ^ 7 + 11 / 4 * a ^ 6 - a ^ 4

/-- Its shift to the domain variables. -/
noncomputable def hl1cPb0s (t s : ℝ) : ℝ :=
  -513 / 500 * t ^ 6 * s - 319 / 250 * t ^ 6 - 263 / 250 * t ^ 5 * s ^ 2 + 613 / 3125 * t ^ 5 * s - 6912 / 3125 * t ^ 5 + 461 / 500 * t ^ 4 * s ^ 3 - 8523 / 1250 * t ^ 4 * s ^ 2 + 761679 / 15625 * t ^ 4 * s + 581279 / 15625 * t ^ 4 + 112 / 125 * t ^ 3 * s ^ 4 - 51799 / 3125 * t ^ 3 * s ^ 3 - 1388908 / 15625 * t ^ 3 * s ^ 2 + 59976102 / 390625 * t ^ 3 * s + 66190052 / 390625 * t ^ 3 - 39 / 500 * t ^ 2 * s ^ 5 + 377 / 6250 * t ^ 2 * s ^ 4 - 8917751 / 78125 * t ^ 2 * s ^ 3 - 156855418 / 390625 * t ^ 2 * s ^ 2 + 675713124 / 9765625 * t ^ 2 * s + 2627763824 / 9765625 * t ^ 2 - 13 / 250 * t * s ^ 6 + 46338 / 3125 * t * s ^ 5 + 5091266 / 78125 * t * s ^ 4 - 172791894 / 1953125 * t * s ^ 3 - 5428894464 / 9765625 * t * s ^ 2 - 212758260232 / 1220703125 * t * s + 209058474768 / 1220703125 * t - 13 / 500 * s ^ 7 + 15517 / 6250 * s ^ 6 + 3162654 / 78125 * s ^ 5 + 292980127 / 1953125 * s ^ 4 + 6456364724 / 48828125 * s ^ 3 - 185840124844 / 1220703125 * s ^ 2 - 3439870663152 / 30517578125 * s + 1091143622448 / 30517578125

theorem hl1cPb0s_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) ≤ hl1cPb0s t s := by
  unfold hl1cPb0s
  have q0 := hs1
  have q1 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s)
  have q2 := (by positivity : (0 : ℝ) ≤ s ^ 3)
  have q3 := (by positivity : (0 : ℝ) ≤ s ^ 4)
  have q4 := (by positivity : (0 : ℝ) ≤ s ^ 5)
  have q5 := (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q6 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q7 := (by positivity : (0 : ℝ) ≤ t)
  have q8 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t)
  have q9 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s)
  have q10 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ s ^ 3)
  have q11 := (by positivity : (0 : ℝ) ≤ t * s ^ 4)
  have q12 := (by positivity : (0 : ℝ) ≤ t * s ^ 5)
  have q13 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q14 := (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q15 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q16 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s)
  have q17 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q18 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q19 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s ^ 5)
  have q20 := (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q21 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s)
  have q22 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s)
  have q23 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q24 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q25 := (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q26 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s)
  have q27 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s)
  have q28 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 3)
  have q29 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q30 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q31 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q32 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q33 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 6)
  ring_nf at *
  linarith

theorem hl1cPb0x_eq (x a : ℝ) : hl1cPb0x x a = hl1cPb0s (x - 41 / 25) (a - 1) := by
  unfold hl1cPb0x hl1cPb0s
  ring

theorem hl1cPb0_id {x a : ℝ} (hx : 41 / 25 ≤ x) (ha : 1 ≤ a) :
    hh1cR2b x a x (3 / 4) - 1 / 40 - 1 / 1000 = hl1cPb0x x a / ((a) * (x + a) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hx2' : x + 2 ≠ 0 := by linarith
  have hKn : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hax : a + x ≠ 0 := by linarith
  have hxa : x + a ≠ 0 := by linarith
  simp only [hh1cR2b, hh1cwb, hh1cdb, hh1cd, hh1cL, hh1cE, hsDg, hh1cK, hl1cPb0x]
  field_simp
  ring

/-- Numerator of `(r₁)_β - 1/40 - 1/1000` at `β = x`, `u = 19/25` (`SHORT_CENTRAL_REDUCTION` (3), `P₁`). -/
noncomputable def hl1cPb1x (x a : ℝ) : ℝ :=
  -253 / 500 * x ^ 4 * a + 207 / 100 * x ^ 4 + 47 / 250 * x ^ 3 * a ^ 2 + 517 / 250 * x ^ 3 * a - 54 / 25 * x ^ 3 - 13 / 250 * x ^ 2 * a ^ 3 - 1111 / 250 * x ^ 2 * a ^ 2 - 12 / 25 * x ^ 2 * a - 1 / 5 * x ^ 2 - 13 / 250 * x * a ^ 4 + 117 / 250 * x * a ^ 3 + 82 / 25 * x * a ^ 2 + 12 / 25 * x * a - 6 / 25 * x - 13 / 500 * a ^ 5 - 1 / 4 * a ^ 4 - 6 / 25 * a ^ 2

/-- Its shift to the domain variables. -/
noncomputable def hl1cPb1s (t s : ℝ) : ℝ :=
  -253 / 500 * t ^ 4 * s + 391 / 250 * t ^ 4 + 47 / 250 * t ^ 3 * s ^ 2 - 5471 / 6250 * t ^ 3 * s + 32362 / 3125 * t ^ 3 - 13 / 250 * t ^ 2 * s ^ 3 - 22969 / 6250 * t ^ 2 * s ^ 2 - 885179 / 156250 * t ^ 2 * s + 1604338 / 78125 * t ^ 2 - 13 / 250 * t * s ^ 4 + 559 / 6250 * t * s ^ 3 - 718677 / 78125 * t * s ^ 2 - 23848288 / 1953125 * t * s + 29937872 / 1953125 * t - 13 / 500 * s ^ 5 - 1454 / 3125 * s ^ 4 - 152103 / 156250 * s ^ 3 - 12446919 / 1953125 * s ^ 2 - 322204152 / 48828125 * s + 183350388 / 48828125

theorem hl1cPb1s_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) ≤ hl1cPb1s t s := by
  unfold hl1cPb1s
  nlinarith [hs1,
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 3),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 4),
    (by positivity : (0 : ℝ) ≤ t),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s),
    (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 4),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4)]

theorem hl1cPb1x_eq (x a : ℝ) : hl1cPb1x x a = hl1cPb1s (x - 41 / 25) (a - 1) := by
  unfold hl1cPb1x hl1cPb1s
  ring

theorem hl1cPb1_id {x a : ℝ} (hx : 41 / 25 ≤ x) (ha : 1 ≤ a) :
    hl1cR1bf x a x (19 / 25) - 1 / 40 - 1 / 1000 = hl1cPb1x x a / ((a) * (x + a) ^ 2 * (x * (x + 2) + a ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hx2' : x + 2 ≠ 0 := by linarith
  have hKn : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  have hax : a + x ≠ 0 := by linarith
  have hxa : x + a ≠ 0 := by linarith
  simp only [hl1cR1bf, hl1cQ0, hl1oD0, hh1cK, hl1cPb1x]
  field_simp
  ring

/-- Numerator of `Q₀ - 3α/2` at `u = 19/25` (`SHORT_CENTRAL_REDUCTION` §2, `P_Q`). -/
noncomputable def hl1cPQx (x a : ℝ) : ℝ :=
  12 / 25 * x ^ 4 * a + 73 / 100 * x ^ 4 - 6 / 25 * x ^ 3 * a ^ 2 + 36 / 25 * x ^ 3 * a + 42 / 25 * x ^ 3 + 8 / 25 * x ^ 2 * a ^ 2 + 38 / 25 * x ^ 2 * a + 1 / 5 * x ^ 2 - 76 / 25 * x * a ^ 3 - 119 / 25 * x * a ^ 2 - 12 / 25 * x * a + 6 / 25 * x - 49 / 100 * a ^ 4 + 6 / 25 * a ^ 2

/-- Its shift to the domain variables. -/
noncomputable def hl1cPQs (t s : ℝ) : ℝ :=
  12 / 25 * t ^ 4 * s + 121 / 100 * t ^ 4 - 6 / 25 * t ^ 3 * s ^ 2 + 2568 / 625 * t ^ 3 * s + 6761 / 625 * t ^ 3 - 538 / 625 * t ^ 2 * s ^ 2 + 228582 / 15625 * t ^ 2 * s + 1116753 / 31250 * t ^ 2 - 76 / 25 * t * s ^ 3 - 230733 / 15625 * t * s ^ 2 + 1632758 / 390625 * t * s + 16889966 / 390625 * t - 49 / 100 * s ^ 4 - 4341 / 625 * s ^ 3 - 20047777 / 781250 * s ^ 2 - 188676393 / 9765625 * s + 131911914 / 9765625

theorem hl1cPQs_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) ≤ hl1cPQs t s := by
  unfold hl1cPQs
  nlinarith [hs1,
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 3),
    (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s)]

theorem hl1cPQx_eq (x a : ℝ) : hl1cPQx x a = hl1cPQs (x - 41 / 25) (a - 1) := by
  unfold hl1cPQx hl1cPQs
  ring

theorem hl1cPQ_id {x a : ℝ} (hx : 41 / 25 ≤ x) (ha : 1 ≤ a) :
    hl1cQ0 x a (19 / 25) - 3 / 2 * a = hl1cPQx x a / ((a) * (x * (x + 2) + a ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hx2' : x + 2 ≠ 0 := by linarith
  have hKn : x * (x + 2) + a ^ 2 ≠ 0 := by positivity
  simp only [hl1cQ0, hl1oD0, hh1cK, hl1cPQx]
  field_simp
  ring
/-! ### Norm quadratics -/

theorem hl1c_F0_uquad (x a b u1 u2 : ℝ) :
    hh1cF0 x a b u1 - hh1cF0 x a b u2 = (u1 - u2) * (hh1cGu x u2 - 7 / 96 * hh1cR2u x a b) -
      (u1 - u2) ^ 2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) := by
  simp only [hh1cF0, hh1cR2, hh1cw, hh1cEL, hh1cG, hh1cGu, hh1cR2u, hh1cwu, hh1cE]
  ring

theorem hl1c_F1_uquad (x a b u1 u2 : ℝ) :
    hh1cF1 x a b u1 - hh1cF1 x a b u2 = (u1 - u2) * (hh1cGu x u2 - 7 / 96 * (hh1cR2u x a b +
      (hh1cT x a b - 2) * hh1cwu x a b)) - (u1 - u2) ^ 2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) := by
  simp only [hh1cF1, hh1cF0, hh1cR2, hh1cw, hh1cEL, hh1cG, hh1cGu, hh1cR2u, hh1cwu, hh1cE]
  ring

theorem hl1c_Gu_diff (x u u' : ℝ) :
    hh1cGu x u - hh1cGu x u' = (u' - u) * (2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2)) := by
  simp only [hh1cGu, hh1cE]
  ring

/-- The central domain facts used repeatedly. -/
theorem hl1c_dom {x a b : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 7 / 6)
    (hb0 : x ≤ b) (hb1 : b ≤ x + 10 / 13 * (a - 1)) :
    0 < hsDg x b a ∧ hsDg x b a < (1 + x) ^ 3 ∧ 2 * a * (a + b) ≤ hh1cK x a ∧
      hh1cK x a ≤ 18 * a * (x - a) := by
  unfold hsDg hh1cK
  have h1 : 0 ≤ (b - x) * (x - a) := mul_nonneg (by linarith) (by linarith)
  have h2 : (66 / 25 : ℝ) ^ 3 ≤ (1 + x) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-! ### `Ψ ≤ 0` and the norm steps -/

theorem hl1c_H_sep {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : 0 < a + b) :
    hh1cR2u x a b + (hh1cT x a b - 2) * hh1cwu x a b =
      (a ^ 2 - 4 * a * x + 5 * x ^ 2 + 2 * x) * (a + b) / (a * hh1cK x a) +
        (2 * x - a) * ((1 + x) ^ 3 - 2 * hl1oD0 x a) / (a * hh1cK x a) +
          hl1oD0 x a * (hl1oD0 x a - (1 + x) ^ 3) / (a * hh1cK x a * (a + b)) := by
  have hK : hh1cK x a ≠ 0 := by unfold hh1cK; positivity
  have hD : hsDg x b a = hl1oD0 x a - 2 * (x - a) * (a + b) := by unfold hsDg hl1oD0; ring
  simp only [hh1cR2u, hh1cwu, hh1cT, hh1cd, hh1cL, hD]
  have : a + b ≠ 0 := hab.ne'
  unfold hh1cK at hK ⊢
  field_simp
  ring

theorem hl1c_Psi_neg {x a b : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 7 / 6)
    (hb0 : x + (a - 1) / 2 ≤ b) :
    hh1cGu x (3 / 4) - 7 / 96 * (hh1cR2u x a b + (hh1cT x a b - 2) * hh1cwu x a b) ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hK : 0 < hh1cK x a := by unfold hh1cK; positivity
  have hD0 : 0 < hl1oD0 x a := by unfold hl1oD0; nlinarith
  have hD1 : hl1oD0 x a < (1 + x) ^ 3 := by
    have h2 : (66 / 25 : ℝ) ^ 3 ≤ (1 + x) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    unfold hl1oD0; nlinarith
  have hal : 0 < a ^ 2 - 4 * a * x + 5 * x ^ 2 + 2 * x := by nlinarith [sq_nonneg (a - 2 * x)]
  have hB0 : 0 < a + (x + (a - 1) / 2) := by linarith
  have hB : 0 < a + b := by linarith
  have hmono : hh1cR2u x a (x + (a - 1) / 2) + (hh1cT x a (x + (a - 1) / 2) - 2) *
      hh1cwu x a (x + (a - 1) / 2) ≤ hh1cR2u x a b + (hh1cT x a b - 2) * hh1cwu x a b := by
    rw [hl1c_H_sep hx0 ha0 hB0, hl1c_H_sep hx0 ha0 hB]
    have hk : 0 < a * hh1cK x a := mul_pos ha0 hK
    have h1 : (a ^ 2 - 4 * a * x + 5 * x ^ 2 + 2 * x) * (a + (x + (a - 1) / 2)) / (a * hh1cK x a) ≤
        (a ^ 2 - 4 * a * x + 5 * x ^ 2 + 2 * x) * (a + b) / (a * hh1cK x a) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hal.le) hk.le
    have h2 : hl1oD0 x a * (hl1oD0 x a - (1 + x) ^ 3) / (a * hh1cK x a * (a + (x + (a - 1) / 2))) ≤
        hl1oD0 x a * (hl1oD0 x a - (1 + x) ^ 3) / (a * hh1cK x a * (a + b)) := by
      have hn : hl1oD0 x a * (hl1oD0 x a - (1 + x) ^ 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hD0.le (by linarith)
      rw [div_le_div_iff₀ (mul_pos hk hB0) (mul_pos hk hB)]
      have : a * hh1cK x a * (a + (x + (a - 1) / 2)) ≤ a * hh1cK x a * (a + b) :=
        mul_le_mul_of_nonneg_left (by linarith) hk.le
      nlinarith [mul_le_mul_of_nonpos_left this hn]
    linarith
  have hid := hl1cPphi_id hx ha1
  have hP := hl1cPphis_pos (t := x - 41 / 25) (s := a - 1) (by linarith) (by linarith)
    (by linarith) (by linarith)
  rw [← hl1cPphix_eq] at hP
  have hden : 0 < a * x ^ 2 * (2 * x + 3 * a - 1) * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2 := by
    have : 0 < 2 * x + 3 * a - 1 := by linarith
    positivity
  have : 0 ≤ hl1cPphix x a / (a * x ^ 2 * (2 * x + 3 * a - 1) * (x + 2) ^ 2 *
      (x * (x + 2) + a ^ 2) ^ 2) := div_nonneg hP hden.le
  linarith

theorem hl1c_wu_nonpos {x a b : ℝ} (hx : 0 < x) (h0 : 0 < hsDg x b a) (h1 : hsDg x b a < (1 + x) ^ 3) :
    hh1cwu x a b ≤ 0 := by
  have hK : 0 < hh1cK x a := by unfold hh1cK; positivity
  have e : hh1cwu x a b = hsDg x b a * (hsDg x b a - (1 + x) ^ 3) / hh1cK x a ^ 2 := by
    simp only [hh1cwu, hh1cd, hh1cL]; field_simp
  rw [e]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h0.le (by linarith))
    (by positivity)

theorem hl1c_T_ge {x a b : ℝ} (ha : 0 < a) (hab : 0 < a + b) (h : 2 * a * (a + b) ≤ hh1cK x a) :
    2 ≤ hh1cT x a b := by
  unfold hh1cT; rw [le_div_iff₀ (by positivity)]; linarith

/-- `(F₀)_u ≤ (F₁)_u ≤ 0` for `u ≥ 3/4` on the strip. -/
theorem hl1c_Fu_nonpos {x a b u : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 7 / 6)
    (hb0 : x + (a - 1) / 2 ≤ b) (hb1 : b ≤ x + 10 / 13 * (a - 1)) (hu : 3 / 4 ≤ u) :
    hh1cGu x u - 7 / 96 * hh1cR2u x a b ≤ 0 ∧
      hh1cGu x u - 7 / 96 * (hh1cR2u x a b + (hh1cT x a b - 2) * hh1cwu x a b) ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨hD0, hD1, hT, -⟩ := hl1c_dom hx hx2 ha1 ha2 (by linarith) hb1
  have hP := hl1c_Psi_neg hx hx2 ha1 ha2 hb0
  have hG := hl1c_Gu_diff x u (3 / 4)
  have hG0 : (3 / 4 - u) * (2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hw := hl1c_wu_nonpos hx0 hD0 hD1
  have hT2 := hl1c_T_ge ha0 (by linarith) hT
  have : 0 ≤ (hh1cT x a b - 2) * -hh1cwu x a b := mul_nonneg (by linarith) (by linarith)
  constructor <;> nlinarith

theorem hl1c_F1_ustep {x a b u1 u2 : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 7 / 6) (hb0 : x + (a - 1) / 2 ≤ b) (hb1 : b ≤ x + 10 / 13 * (a - 1))
    (h1 : 3 / 4 ≤ u1) (h12 : u1 ≤ u2) : hh1cF1 x a b u2 ≤ hh1cF1 x a b u1 := by
  have hq := hl1c_F1_uquad x a b u2 u1
  have hF := (hl1c_Fu_nonpos hx hx2 ha1 ha2 hb0 hb1 h1).2
  have : 0 ≤ (u2 - u1) ^ 2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ u2 - u1) hF]

theorem hl1c_F0_ustep {x a b u1 u2 : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 7 / 6) (hb0 : x + (a - 1) / 2 ≤ b) (hb1 : b ≤ x + 10 / 13 * (a - 1))
    (h1 : 3 / 4 ≤ u1) (h12 : u1 ≤ u2) : hh1cF0 x a b u2 ≤ hh1cF0 x a b u1 := by
  have hq := hl1c_F0_uquad x a b u2 u1
  have hF := (hl1c_Fu_nonpos hx hx2 ha1 ha2 hb0 hb1 h1).1
  have : 0 ≤ (u2 - u1) ^ 2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ u2 - u1) hF]

/-! ### `(F₀)_u ≥ -1/5` -/

/-- The tangent chord `α_U(x) = (1013x + 676)/2340` lies above the cap `√(x(x + 2)/6)`. -/
theorem hl1c_aU {x a : ℝ} (hx : 1 ≤ x) (ha : 0 < a) (hqc : 6 * a ^ 2 ≤ x * (x + 2)) :
    a ≤ (1013 * x + 676) / 2340 := by
  have h1 : a ^ 2 ≤ ((1013 * x + 676) / 2340) ^ 2 := by nlinarith [sq_nonneg (337 * x - 676)]
  have h2 : 0 ≤ (1013 * x + 676) / 2340 := by positivity
  nlinarith [sq_nonneg (a - (1013 * x + 676) / 2340), sq_nonneg (a + (1013 * x + 676) / 2340)]

theorem hl1c_F0u_ge {x a b u : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (haU : a ≤ (1013 * x + 676) / 2340) (hb0 : x + (a - 1) / 2 ≤ b)
    (hb1 : b ≤ x + 10 / 13 * (a - 1)) (hu : u ≤ 19 / 25) :
    -(1 / 5) ≤ hh1cGu x u - 7 / 96 * hh1cR2u x a b := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hK : hh1cK x a ≠ 0 := by unfold hh1cK; positivity
  have hG := hl1c_Gu_diff x u (19 / 25)
  have hG0 : 0 ≤ (19 / 25 - u) * (2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2)) :=
    mul_nonneg (by linarith) (by positivity)
  have hid : ∀ s, (x + 10 / 13 * (a - 1) - (x + (a - 1) / 2)) *
      (hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a s) -
      (x + 10 / 13 * (a - 1) - s) * (hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a (x + (a - 1) / 2)) -
      (s - (x + (a - 1) / 2)) * (hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a (x + 10 / 13 * (a - 1))) =
      7 / 12 * (x - a) ^ 2 / hh1cK x a ^ 2 * (s - (x + (a - 1) / 2)) *
        (x + 10 / 13 * (a - 1) - s) * (x + 10 / 13 * (a - 1) - (x + (a - 1) / 2)) := by
    intro s
    simp only [hh1cR2u, hh1cwu, hh1cd, hsDg]
    generalize hh1cGu x (19 / 25) = G
    generalize hh1cL x a = L
    field_simp
    ring
  have hm := hl1_conc3 (f := fun s => hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a s) hb0 hb1
    (by positivity) hid
  have hs0 : 0 ≤ (1013 * x + 676) / 2340 - a := by linarith
  have hs1 : (1013 * x + 676) / 2340 - a ≤ 31 / 200 := by linarith
  have hden : 0 < a * x ^ 2 * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2 := by positivity
  have e1 : -(1 / 5) ≤ hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a (x + (a - 1) / 2) := by
    have hP := hl1cPu0s_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - a) (by linarith)
      (by linarith) hs0 hs1
    rw [← hl1cPu0x_eq] at hP
    have := hl1cPu0_id hx ha1
    have : 0 ≤ hl1cPu0x x a / (a * x ^ 2 * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) :=
      div_nonneg hP hden.le
    linarith
  have e2 : -(1 / 5) ≤ hh1cGu x (19 / 25) - 7 / 96 * hh1cR2u x a (x + 10 / 13 * (a - 1)) := by
    have hP := hl1cPu1s_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - a) (by linarith)
      (by linarith) hs0 hs1
    rw [← hl1cPu1x_eq] at hP
    have := hl1cPu1_id hx ha1
    have : 0 ≤ hl1cPu1x x a / (a * x ^ 2 * (x + 2) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) :=
      div_nonneg hP hden.le
    linarith
  have := le_trans (le_min e1 e2) hm
  linarith

end SmoothedOctagon

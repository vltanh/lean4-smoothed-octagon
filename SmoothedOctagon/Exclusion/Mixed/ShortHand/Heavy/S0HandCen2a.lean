module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen

/-!
# Hand proof of the smaller-short case, gate S0: the `τ = 2` test at the upper faces (rows 0, 1)

`archive/lighter-proofs/SHORT_DURATION_CENTRAL_TAU_TWO.md` (algebra in `SHORT_DURATION_CENTRAL_TAU_TWO_ALGEBRA.md`). The upper beta endpoint is enlarged to a
constant slope `c_j` on each `x`-interval; the cleared numerator (`hl0N2`) there is a polynomial
of degree ten in `(x, α)`, computed in Lean from its factored source formula (`hl0FNc`; it is never
printed). On each rectangle `∂²_x N > 0` (the coefficient bound, the note's (6)-(8)), `∂_x N > 0` and
`N > 0` on the left edge `x = l_j` (the note's (9)-(11)); beyond `α = t_j` the slanted edge `x = 2α - o_j` carries the sign (§4, `hl0_face_slant`; the same rule replaces the third derivatives (13)-(17)).

Route: the edge polynomials are taken exactly at `x = l_j` (no Taylor bound at `x = 2`), and every
one-variable sign uses the coefficient bound after a Taylor shift on a few fixed pieces (`hl0Cov`)
instead of the midpoint quadratic bound.

## Main API

* `hl0U2_0_neg`, `hl0U2_1_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Row 0 of the `τ = 2` test: the cleared numerator at `β = x + (7 / 8)(α - 1)` as a list in `X = x - (12 / 5)`,
`A = α - 1`, computed from the source formula. -/
noncomputable def hl0U2_0 : List (List ℝ) :=
  hl0FNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[(12 / 5)], [1]] [[1, 1]] [[(12 / 5), (7 / 8)], [1]]

theorem hl0U2_0_link (x a : ℝ) :
    hl0N2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (7 / 8) * (a - 1))) (hl0Uc x (x + (7 / 8) * (a - 1)))
      (hl0Vc x (x + (7 / 8) * (a - 1))) (hsDg x (x + (7 / 8) * (a - 1)) a) = hl0H2 hl0U2_0 (x - (12 / 5)) (a - 1) := by
  unfold hl0U2_0
  rw [hl0_H2_FN2, (hl0_H2_base (12 / 5) x a).1, (hl0_H2_base (12 / 5) x a).2, hl0_H2_lin]

/-- The signs of row 0: curvature, edge derivative, edge value. -/
theorem hl0U2_0_signs :
    0 ≤ hl0Low2 (3 / 8) (1 / 10) (hl0D2 (hl0D2 hl0U2_0)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0U2_0)) (3 / 8) [0, (3 / 16)] ∧
      hl0Cov (hl0Eval 0 hl0U2_0) (3 / 8) [0, (3 / 32), (3 / 16), (9 / 32)] := by
  norm_num [hl0U2_0, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift]

/-- **Row 0 of the `τ = 2` test**: negative on `(12 / 5) ≤ x ≤ (5 / 2)`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0U2_0_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ (5 / 2)) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0G2 x a (x + (7 / 8) * (a - 1)) < 0 := by
  have hb : 1 < (x + (7 / 8) * (a - 1)) := by nlinarith
  apply hl0_G2_neg (by linarith) (by linarith) hb
  rw [hl0U2_0_link]
  obtain ⟨h1, h2, h3⟩ := hl0U2_0_signs
  exact hl0_face_rect hl0U2_0 (HA := (3 / 8)) (W := (1 / 10)) h1 (hl0_cov_pos _ _ _ _ h2)
    (hl0_cov_pos _ _ _ _ h3) (by linarith) (by linarith) (by linarith) (by linarith)

/-- Row 1 of the `τ = 2` test: the cleared numerator at `β = x + 1(α - 1)` as a list in `X = x - (5 / 2)`,
`A = α - 1`, computed from the source formula. -/
noncomputable def hl0U2_1 : List (List ℝ) :=
  hl0FNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[(5 / 2)], [1]] [[1, 1]] [[(5 / 2), 1], [1]]

theorem hl0U2_1_link (x a : ℝ) :
    hl0N2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + 1 * (a - 1))) (hl0Uc x (x + 1 * (a - 1)))
      (hl0Vc x (x + 1 * (a - 1))) (hsDg x (x + 1 * (a - 1)) a) = hl0H2 hl0U2_1 (x - (5 / 2)) (a - 1) := by
  unfold hl0U2_1
  rw [hl0_H2_FN2, (hl0_H2_base (5 / 2) x a).1, (hl0_H2_base (5 / 2) x a).2, hl0_H2_lin]

/-- The signs of row 1: curvature, edge derivative, edge value, slanted edge. -/
theorem hl0U2_1_signs :
    0 ≤ hl0Low2 (7 / 12) (1 / 2) (hl0D2 (hl0D2 hl0U2_1)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0U2_1)) (7 / 12) [0, (7 / 24)] ∧
      hl0Cov (hl0Eval 0 hl0U2_1) (5 / 12) [0, (5 / 48), (5 / 24), (5 / 16)] ∧
      hl0Cov (hl0Slant 2 (-5 / 6) hl0U2_1) (7 / 12) [(5 / 12)] := by
  norm_num [hl0U2_1, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift, hl0Slant]

/-- **Row 1 of the `τ = 2` test**: negative on `(5 / 2) ≤ x ≤ 3`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0U2_1_neg {x a : ℝ} (hx : (5 / 2) ≤ x) (hxh : x ≤ 3) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0G2 x a (x + 1 * (a - 1)) < 0 := by
  have hb : 1 < (x + 1 * (a - 1)) := by nlinarith
  apply hl0_G2_neg (by linarith) (by linarith) hb
  rw [hl0U2_1_link]
  obtain ⟨h1, h2, h3, h4⟩ := hl0U2_1_signs
  apply hl0_face_slant hl0U2_1 (HA := (7 / 12)) (W := (1 / 2)) (T := (5 / 12)) (α := 2) (β := (-5 / 6)) h1
    (hl0_cov_pos _ _ _ _ h2) (hl0_cov_pos _ _ _ _ h3) (hl0_cov_pos _ _ _ _ h4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt a (17 / 12) with h | h
  · left; linarith
  · right; constructor <;> linarith

end SmoothedOctagon

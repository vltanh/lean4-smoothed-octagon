module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen

/-!
# Hand proof of the smaller-short case, gate S0: the `τ = T` test at the upper faces (rows 2, 3)

`archive/lighter-proofs/SHORT_DURATION_CENTRAL_UPPER_FACES.md` (algebra in `SHORT_DURATION_CENTRAL_UPPER_ALGEBRA.md`). The upper beta endpoint is enlarged to a
constant slope `c_j` on each `x`-interval; the cleared numerator (`hl0NT`) there is a polynomial
of degree ten in `(x, α)`, computed in Lean from its factored source formula (`hl0FNc`; it is never
printed). On each rectangle `∂²_x N > 0` (the coefficient bound, the note's (6)-(8)), `∂_x N > 0` and
`N > 0` on the left edge `x = l_j` (the note's (9)-(11)).

Route: the edge polynomials are taken exactly at `x = l_j` (no Taylor bound at `x = 2`), and every
one-variable sign uses the coefficient bound after a Taylor shift on a few fixed pieces (`hl0Cov`)
instead of the midpoint quadratic bound.

## Main API

* `hl0UT_2_neg`, `hl0UT_3_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Row 2 of the `τ = T` test: the cleared numerator at `β = x + (6 / 5)(α - 1)` as a list in `X = x - 3`,
`A = α - 1`, computed from the source formula. -/
noncomputable def hl0UT_2 : List (List ℝ) :=
  hl0FNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) [[3], [1]] [[1, 1]] [[3, (6 / 5)], [1]]

theorem hl0UT_2_link (x a : ℝ) :
    hl0NT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (6 / 5) * (a - 1))) (hl0Uc x (x + (6 / 5) * (a - 1)))
      (hl0Vc x (x + (6 / 5) * (a - 1))) (hsDg x (x + (6 / 5) * (a - 1)) a) = hl0H2 hl0UT_2 (x - 3) (a - 1) := by
  unfold hl0UT_2
  rw [hl0_H2_FNT, (hl0_H2_base 3 x a).1, (hl0_H2_base 3 x a).2, hl0_H2_lin]

/-- The signs of row 2: curvature, edge derivative, edge value. -/
theorem hl0UT_2_signs :
    0 ≤ hl0Low2 (17 / 12) 2 (hl0D2 (hl0D2 hl0UT_2)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0UT_2)) (17 / 12) [0, (17 / 24)] ∧
      hl0Cov (hl0Eval 0 hl0UT_2) (17 / 12) [0, (17 / 24)] := by
  norm_num [hl0UT_2, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift]

/-- **Row 2 of the `τ = T` test**: negative on `3 ≤ x ≤ 5`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0UT_2_neg {x a : ℝ} (hx : 3 ≤ x) (hxh : x ≤ 5) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0GT x a (x + (6 / 5) * (a - 1)) < 0 := by
  have hb : 1 < (x + (6 / 5) * (a - 1)) := by nlinarith
  apply hl0_GT_neg (by linarith) (by linarith) hb
  rw [hl0UT_2_link]
  obtain ⟨h1, h2, h3⟩ := hl0UT_2_signs
  exact hl0_face_rect hl0UT_2 (HA := (17 / 12)) (W := 2) h1 (hl0_cov_pos _ _ _ _ h2)
    (hl0_cov_pos _ _ _ _ h3) (by linarith) (by linarith) (by linarith) (by linarith)

/-- Row 3 of the `τ = T` test: the cleared numerator at `β = x + (3 / 2)(α - 1)` as a list in `X = x - 5`,
`A = α - 1`, computed from the source formula. -/
noncomputable def hl0UT_3 : List (List ℝ) :=
  hl0FNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) [[5], [1]] [[1, 1]] [[5, (3 / 2)], [1]]

theorem hl0UT_3_link (x a : ℝ) :
    hl0NT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (3 / 2) * (a - 1))) (hl0Uc x (x + (3 / 2) * (a - 1)))
      (hl0Vc x (x + (3 / 2) * (a - 1))) (hsDg x (x + (3 / 2) * (a - 1)) a) = hl0H2 hl0UT_3 (x - 5) (a - 1) := by
  unfold hl0UT_3
  rw [hl0_H2_FNT, (hl0_H2_base 5 x a).1, (hl0_H2_base 5 x a).2, hl0_H2_lin]

/-- The signs of row 3: curvature, edge derivative, edge value. -/
theorem hl0UT_3_signs :
    0 ≤ hl0Low2 (37 / 12) 4 (hl0D2 (hl0D2 hl0UT_3)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0UT_3)) (37 / 12) [0] ∧
      hl0Cov (hl0Eval 0 hl0UT_3) (37 / 12) [0, (37 / 24)] := by
  norm_num [hl0UT_3, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift]

/-- **Row 3 of the `τ = T` test**: negative on `5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0UT_3_neg {x a : ℝ} (hx : 5 ≤ x) (hxh : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0GT x a (x + (3 / 2) * (a - 1)) < 0 := by
  have hb : 1 < (x + (3 / 2) * (a - 1)) := by nlinarith
  apply hl0_GT_neg (by linarith) (by linarith) hb
  rw [hl0UT_3_link]
  obtain ⟨h1, h2, h3⟩ := hl0UT_3_signs
  exact hl0_face_rect hl0UT_3 (HA := (37 / 12)) (W := 4) h1 (hl0_cov_pos _ _ _ _ h2)
    (hl0_cov_pos _ _ _ _ h3) (by linarith) (by linarith) (by linarith) (by linarith)

end SmoothedOctagon

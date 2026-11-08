module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen

/-!
# Hand proof of the smaller-short case, gate S0: the `τ = T` test at the upper faces (rows 0, 1)

The upper beta endpoint is enlarged to a constant slope
`c_j` on each `x`-interval; the cleared numerator (`hl0NT`) there is a polynomial of degree ten in
`(x, α)`, computed in Lean from its factored formula (`hl0FNc`; it is never printed). On each
rectangle `∂²_x N > 0` (the coefficient bound `hl0Low2`), `∂_x N > 0` and `N > 0` on the
left edge `x = l_j`.

The edge polynomials are taken exactly at `x = l_j`, and every one-variable sign uses the
coefficient bound after a Taylor shift on a few fixed pieces (`hl0Cov`).

## Main API

* `hl0UT_0_neg`, `hl0UT_1_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Row 0 of the `τ = T` test: the cleared numerator at `β = x + (7 / 8)(α - 1)` as a list in `X = x - (12 / 5)`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def hl0UT_0 : List (List ℝ) :=
  hl0FNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) [[(12 / 5)], [1]] [[1, 1]] [[(12 / 5), (7 / 8)], [1]]

theorem hl0UT_0_link (x a : ℝ) :
    hl0NT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (7 / 8) * (a - 1))) (hl0Uc x (x + (7 / 8) * (a - 1)))
      (hl0Vc x (x + (7 / 8) * (a - 1))) (hsDg x (x + (7 / 8) * (a - 1)) a) = hl0H2 hl0UT_0 (x - (12 / 5)) (a - 1) := by
  unfold hl0UT_0
  rw [hl0_H2_FNT, (hl0_H2_base (12 / 5) x a).1, (hl0_H2_base (12 / 5) x a).2, hl0_H2_lin]

/-- The signs of row 0: curvature, edge derivative, edge value. -/
theorem hl0UT_0_signs :
    0 ≤ hl0Low2 (3 / 8) (1 / 10) (hl0D2 (hl0D2 hl0UT_0)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0UT_0)) (3 / 8) [0] ∧
      hl0Cov (hl0Eval 0 hl0UT_0) (3 / 8) [0] := by
  norm_num [hl0UT_0, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift]

/-- **Row 0 of the `τ = T` test**: negative on `(12 / 5) ≤ x ≤ (5 / 2)`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0UT_0_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ (5 / 2)) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0GT x a (x + (7 / 8) * (a - 1)) < 0 := by
  have hb : 1 < (x + (7 / 8) * (a - 1)) := by nlinarith
  apply hl0_GT_neg (by linarith) (by linarith) hb
  rw [hl0UT_0_link]
  obtain ⟨h1, h2, h3⟩ := hl0UT_0_signs
  exact hl0_face_rect hl0UT_0 (HA := (3 / 8)) (W := (1 / 10)) h1 (hl0_cov_pos _ _ _ _ h2)
    (hl0_cov_pos _ _ _ _ h3) (by linarith) (by linarith) (by linarith) (by linarith)

/-- Row 1 of the `τ = T` test: the cleared numerator at `β = x + 1(α - 1)` as a list in `X = x - (5 / 2)`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def hl0UT_1 : List (List ℝ) :=
  hl0FNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) [[(5 / 2)], [1]] [[1, 1]] [[(5 / 2), 1], [1]]

theorem hl0UT_1_link (x a : ℝ) :
    hl0NT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + 1 * (a - 1))) (hl0Uc x (x + 1 * (a - 1)))
      (hl0Vc x (x + 1 * (a - 1))) (hsDg x (x + 1 * (a - 1)) a) = hl0H2 hl0UT_1 (x - (5 / 2)) (a - 1) := by
  unfold hl0UT_1
  rw [hl0_H2_FNT, (hl0_H2_base (5 / 2) x a).1, (hl0_H2_base (5 / 2) x a).2, hl0_H2_lin]

/-- The signs of row 1: curvature, edge derivative, edge value. -/
theorem hl0UT_1_signs :
    0 ≤ hl0Low2 (7 / 12) (1 / 2) (hl0D2 (hl0D2 hl0UT_1)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0UT_1)) (7 / 12) [0] ∧
      hl0Cov (hl0Eval 0 hl0UT_1) (7 / 12) [0, (7 / 24)] := by
  norm_num [hl0UT_1, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift]

/-- **Row 1 of the `τ = T` test**: negative on `(5 / 2) ≤ x ≤ 3`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0UT_1_neg {x a : ℝ} (hx : (5 / 2) ≤ x) (hxh : x ≤ 3) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0GT x a (x + 1 * (a - 1)) < 0 := by
  have hb : 1 < (x + 1 * (a - 1)) := by nlinarith
  apply hl0_GT_neg (by linarith) (by linarith) hb
  rw [hl0UT_1_link]
  obtain ⟨h1, h2, h3⟩ := hl0UT_1_signs
  exact hl0_face_rect hl0UT_1 (HA := (7 / 12)) (W := (1 / 2)) h1 (hl0_cov_pos _ _ _ _ h2)
    (hl0_cov_pos _ _ _ _ h3) (by linarith) (by linarith) (by linarith) (by linarith)

end SmoothedOctagon

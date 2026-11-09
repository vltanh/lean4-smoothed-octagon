module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen

/-!
# Hand proof of the smaller-short case, gate S0: the `τ = 2` test at the upper faces (rows 2, 3)

The upper beta endpoint is enlarged to a constant
slope `c_j` on each `x`-interval; the cleared numerator (`hl0N2`) there is a polynomial of degree
ten in `(x, α)`, computed in Lean from its factored formula (`hl0FNc`; it is never printed).
On each rectangle `∂²_x N > 0` (the coefficient bound `hl0Low2`), `∂_x N > 0` and `N > 0`
on the left edge `x = l_j`; beyond `α = t_j` the slanted edge `x = 2α - o_j`
carries the sign (`hl0_face_slant`, by the same bound).

The edge polynomials are taken exactly at `x = l_j`, and every one-variable sign uses the
coefficient bound after a Taylor shift on a few fixed pieces (`hl0Cov`).

## Main API

* `hl0U2_2_neg`, `hl0U2_3_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Row 2 of the `τ = 2` test: the cleared numerator at `β = x + (5 / 4)(α - 1)` as a list in `X = x - 3`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def hl0U2_2 : List (List ℝ) :=
  hl0FNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[3], [1]] [[1, 1]] [[3, (5 / 4)], [1]]

theorem hl0U2_2_link (x a : ℝ) :
    hl0N2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (5 / 4) * (a - 1))) (hl0Uc x (x + (5 / 4) * (a - 1)))
      (hl0Vc x (x + (5 / 4) * (a - 1))) (hsDg x (x + (5 / 4) * (a - 1)) a) = hl0H2 hl0U2_2 (x - 3) (a - 1) := by
  unfold hl0U2_2
  rw [hl0_H2_FN2, (hl0_H2_base 3 x a).1, (hl0_H2_base 3 x a).2, hl0_H2_lin]

/-- The signs of row 2: curvature, edge derivative, edge value, slanted edge. -/
theorem hl0U2_2_signs :
    0 ≤ hl0Low2 (17 / 12) 2 (hl0D2 (hl0D2 hl0U2_2)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0U2_2)) (17 / 12) [0, (17 / 24), (17 / 16)] ∧
      hl0Cov (hl0Eval 0 hl0U2_2) (3 / 4) [0, (3 / 8)] ∧
      hl0Cov (hl0Slant 2 (-3 / 2) hl0U2_2) (17 / 12) [(3 / 4)] := by
  norm_num [hl0U2_2, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift, hl0Slant]

/-- **Row 2 of the `τ = 2` test**: negative on `3 ≤ x ≤ 5`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0U2_2_neg {x a : ℝ} (hx : 3 ≤ x) (hxh : x ≤ 5) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0G2 x a (x + (5 / 4) * (a - 1)) < 0 := by
  have hb : 1 < (x + (5 / 4) * (a - 1)) := by nlinarith
  apply hl0_G2_neg (by linarith) (by linarith) hb
  rw [hl0U2_2_link]
  obtain ⟨h1, h2, h3, h4⟩ := hl0U2_2_signs
  apply hl0_face_slant hl0U2_2 (HA := (17 / 12)) (W := 2) (T := (3 / 4)) (α := 2) (β := (-3 / 2)) h1
    (hl0_cov_pos _ _ _ _ h2) (hl0_cov_pos _ _ _ _ h3) (hl0_cov_pos _ _ _ _ h4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt a (7 / 4) with h | h
  · left; linarith
  · right; constructor <;> linarith

/-- Row 3 of the `τ = 2` test: the cleared numerator at `β = x + (3 / 2)(α - 1)` as a list in `X = x - 5`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def hl0U2_3 : List (List ℝ) :=
  hl0FNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[5], [1]] [[1, 1]] [[5, (3 / 2)], [1]]

theorem hl0U2_3_link (x a : ℝ) :
    hl0N2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (3 / 2) * (a - 1))) (hl0Uc x (x + (3 / 2) * (a - 1)))
      (hl0Vc x (x + (3 / 2) * (a - 1))) (hsDg x (x + (3 / 2) * (a - 1)) a) = hl0H2 hl0U2_3 (x - 5) (a - 1) := by
  unfold hl0U2_3
  rw [hl0_H2_FN2, (hl0_H2_base 5 x a).1, (hl0_H2_base 5 x a).2, hl0_H2_lin]

/-- The signs of row 3: curvature, edge derivative, edge value, slanted edge. -/
theorem hl0U2_3_signs :
    0 ≤ hl0Low2 (37 / 12) 4 (hl0D2 (hl0D2 hl0U2_3)) ∧
      hl0Cov (hl0Eval 0 (hl0D2 hl0U2_3)) (37 / 12) [0, (37 / 24)] ∧
      hl0Cov (hl0Eval 0 hl0U2_3) (3 / 2) [0] ∧
      hl0Cov (hl0Slant 2 (-3) hl0U2_3) (37 / 12) [(3 / 2)] := by
  norm_num [hl0U2_3, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D2, hl0Low, hl0Neg, hl0Cov, hl0Eval, hl0Shift, hl0Slant]

/-- **Row 3 of the `τ = 2` test**: negative on `5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem hl0U2_3_neg {x a : ℝ} (hx : 5 ≤ x) (hxh : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0G2 x a (x + (3 / 2) * (a - 1)) < 0 := by
  have hb : 1 < (x + (3 / 2) * (a - 1)) := by nlinarith
  apply hl0_G2_neg (by linarith) (by linarith) hb
  rw [hl0U2_3_link]
  obtain ⟨h1, h2, h3, h4⟩ := hl0U2_3_signs
  apply hl0_face_slant hl0U2_3 (HA := (37 / 12)) (W := 4) (T := (3 / 2)) (α := 2) (β := (-3)) h1
    (hl0_cov_pos _ _ _ _ h2) (hl0_cov_pos _ _ _ _ h3) (hl0_cov_pos _ _ _ _ h4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt a (5 / 2) with h | h
  · left; linarith
  · right; constructor <;> linarith

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace

/-!
# Smaller-short window, large ratio: the `τ = 2` test at the upper faces (rows 2, 3)

The upper beta endpoint is enlarged to a constant
slope `c_j` on each `x`-interval; the cleared numerator (`lgrN2`) there is a polynomial of degree
ten in `(x, α)`, computed in Lean from its factored formula (`lgrFNc`; it is never printed).
On each rectangle `∂²_x N > 0` (the coefficient bound `lgrLow2`), `∂_x N > 0` and `N > 0`
on the left edge `x = l_j`; beyond `α = t_j` the slanted edge `x = 2α - o_j`
carries the sign (`lgr_face_slant`, by the same bound).

The edge polynomials are taken exactly at `x = l_j`, and every one-variable sign uses the
coefficient bound after a Taylor shift on a few fixed pieces (`lgrCov`).

## Main API

* `lgrU2_2_neg`, `lgrU2_3_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Row 2 of the `τ = 2` test: the cleared numerator at `β = x + (5 / 4)(α - 1)` as a list in `X = x - 3`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def lgrU2_2 : List (List ℝ) :=
  lgrFNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[3], [1]] [[1, 1]] [[3, (5 / 4)], [1]]

theorem lgrU2_2_link (x a : ℝ) :
    lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (5 / 4) * (a - 1))) (lgrUc x (x + (5 / 4) * (a - 1)))
      (lgrVc x (x + (5 / 4) * (a - 1))) (ssDg x (x + (5 / 4) * (a - 1)) a) = lgrH2 lgrU2_2 (x - 3) (a - 1) := by
  unfold lgrU2_2
  rw [lgr_H2_FN2, (lgr_H2_base 3 x a).1, (lgr_H2_base 3 x a).2, lgr_H2_lin]

/-- The signs of row 2: curvature, edge derivative, edge value, slanted edge. -/
theorem lgrU2_2_signs :
    0 ≤ lgrLow2 (17 / 12) 2 (lgrD2 (lgrD2 lgrU2_2)) ∧
      lgrCov (lgrEval 0 (lgrD2 lgrU2_2)) (17 / 12) [0, (17 / 24), (17 / 16)] ∧
      lgrCov (lgrEval 0 lgrU2_2) (3 / 4) [0, (3 / 8)] ∧
      lgrCov (lgrSlant 2 (-3 / 2) lgrU2_2) (17 / 12) [(3 / 4)] := by
  norm_num [lgrU2_2, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD2, lgrLow, lgrNeg, lgrCov, lgrEval, lgrShift, lgrSlant]

/-- **Row 2 of the `τ = 2` test**: negative on `3 ≤ x ≤ 5`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem lgrU2_2_neg {x a : ℝ} (hx : 3 ≤ x) (hxh : x ≤ 5) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG2 x a (x + (5 / 4) * (a - 1)) < 0 := by
  have hb : 1 < (x + (5 / 4) * (a - 1)) := by nlinarith
  apply lgr_G2_neg (by linarith) (by linarith) hb
  rw [lgrU2_2_link]
  obtain ⟨h1, h2, h3, h4⟩ := lgrU2_2_signs
  apply lgr_face_slant lgrU2_2 (HA := (17 / 12)) (W := 2) (T := (3 / 4)) (α := 2) (β := (-3 / 2)) h1
    (lgr_cov_pos _ _ _ _ h2) (lgr_cov_pos _ _ _ _ h3) (lgr_cov_pos _ _ _ _ h4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt a (7 / 4) with h | h
  · left; linarith
  · right; constructor <;> linarith

/-- Row 3 of the `τ = 2` test: the cleared numerator at `β = x + (3 / 2)(α - 1)` as a list in `X = x - 5`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def lgrU2_3 : List (List ℝ) :=
  lgrFNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[5], [1]] [[1, 1]] [[5, (3 / 2)], [1]]

theorem lgrU2_3_link (x a : ℝ) :
    lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (3 / 2) * (a - 1))) (lgrUc x (x + (3 / 2) * (a - 1)))
      (lgrVc x (x + (3 / 2) * (a - 1))) (ssDg x (x + (3 / 2) * (a - 1)) a) = lgrH2 lgrU2_3 (x - 5) (a - 1) := by
  unfold lgrU2_3
  rw [lgr_H2_FN2, (lgr_H2_base 5 x a).1, (lgr_H2_base 5 x a).2, lgr_H2_lin]

/-- The signs of row 3: curvature, edge derivative, edge value, slanted edge. -/
theorem lgrU2_3_signs :
    0 ≤ lgrLow2 (37 / 12) 4 (lgrD2 (lgrD2 lgrU2_3)) ∧
      lgrCov (lgrEval 0 (lgrD2 lgrU2_3)) (37 / 12) [0, (37 / 24)] ∧
      lgrCov (lgrEval 0 lgrU2_3) (3 / 2) [0] ∧
      lgrCov (lgrSlant 2 (-3) lgrU2_3) (37 / 12) [(3 / 2)] := by
  norm_num [lgrU2_3, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD2, lgrLow, lgrNeg, lgrCov, lgrEval, lgrShift, lgrSlant]

/-- **Row 3 of the `τ = 2` test**: negative on `5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem lgrU2_3_neg {x a : ℝ} (hx : 5 ≤ x) (hxh : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG2 x a (x + (3 / 2) * (a - 1)) < 0 := by
  have hb : 1 < (x + (3 / 2) * (a - 1)) := by nlinarith
  apply lgr_G2_neg (by linarith) (by linarith) hb
  rw [lgrU2_3_link]
  obtain ⟨h1, h2, h3, h4⟩ := lgrU2_3_signs
  apply lgr_face_slant lgrU2_3 (HA := (37 / 12)) (W := 4) (T := (3 / 2)) (α := 2) (β := (-3)) h1
    (lgr_cov_pos _ _ _ _ h2) (lgr_cov_pos _ _ _ _ h3) (lgr_cov_pos _ _ _ _ h4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt a (5 / 2) with h | h
  · left; linarith
  · right; constructor <;> linarith

end SmoothedOctagon

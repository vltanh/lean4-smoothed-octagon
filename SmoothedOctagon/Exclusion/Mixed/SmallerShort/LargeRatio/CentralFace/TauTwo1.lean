module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace

/-!
# Smaller-short window, large ratio: the `τ = 2` test at the upper faces (rows 0, 1)

The upper beta endpoint is enlarged to a constant
slope `c_j` on each `x`-interval; the cleared numerator (`lgrN2`) there is a polynomial of degree
ten in `(x, α)`, computed in Lean from its factored formula (`lgrFNc`; it is never printed).
On each rectangle `∂²_x N > 0` (the coefficient bound `lgrLow2`), `∂_x N > 0` and `N > 0`
on the left edge `x = l_j`; beyond `α = t_j` the slanted edge `x = 2α - o_j`
carries the sign (`lgr_face_slant`, by the same bound).

The edge polynomials are taken exactly at `x = l_j`, and every one-variable sign uses the
coefficient bound after a Taylor shift on a few fixed pieces (`lgrCov`).

## Main API

* `lgrU2_0_neg`, `lgrU2_1_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Row 0 of the `τ = 2` test: the cleared numerator at `β = x + (7 / 8)(α - 1)` as a list in `X = x - (12 / 5)`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def lgrU2_0 : List (List ℝ) :=
  lgrFNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[(12 / 5)], [1]] [[1, 1]] [[(12 / 5), (7 / 8)], [1]]

theorem lgrU2_0_link (x a : ℝ) :
    lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + (7 / 8) * (a - 1))) (lgrUc x (x + (7 / 8) * (a - 1)))
      (lgrVc x (x + (7 / 8) * (a - 1))) (ssDg x (x + (7 / 8) * (a - 1)) a) = lgrH2 lgrU2_0 (x - (12 / 5)) (a - 1) := by
  unfold lgrU2_0
  rw [lgr_H2_FN2, (lgr_H2_base (12 / 5) x a).1, (lgr_H2_base (12 / 5) x a).2, lgr_H2_lin]

/-- The signs of row 0: curvature, edge derivative, edge value. -/
theorem lgrU2_0_signs :
    0 ≤ lgrLow2 (3 / 8) (1 / 10) (lgrD2 (lgrD2 lgrU2_0)) ∧
      lgrCov (lgrEval 0 (lgrD2 lgrU2_0)) (3 / 8) [0, (3 / 16)] ∧
      lgrCov (lgrEval 0 lgrU2_0) (3 / 8) [0, (3 / 32), (3 / 16), (9 / 32)] := by
  norm_num [lgrU2_0, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD2, lgrLow, lgrNeg, lgrCov, lgrEval, lgrShift]

/-- **Row 0 of the `τ = 2` test**: negative on `(12 / 5) ≤ x ≤ (5 / 2)`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem lgrU2_0_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ (5 / 2)) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG2 x a (x + (7 / 8) * (a - 1)) < 0 := by
  have hb : 1 < (x + (7 / 8) * (a - 1)) := by nlinarith
  apply lgr_G2_neg (by linarith) (by linarith) hb
  rw [lgrU2_0_link]
  obtain ⟨h1, h2, h3⟩ := lgrU2_0_signs
  exact lgr_face_rect lgrU2_0 (HA := (3 / 8)) (W := (1 / 10)) h1 (lgr_cov_pos _ _ _ _ h2)
    (lgr_cov_pos _ _ _ _ h3) (by linarith) (by linarith) (by linarith) (by linarith)

/-- Row 1 of the `τ = 2` test: the cleared numerator at `β = x + 1(α - 1)` as a list in `X = x - (5 / 2)`,
`A = α - 1`, computed from the factored formula. -/
noncomputable def lgrU2_1 : List (List ℝ) :=
  lgrFNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[(5 / 2)], [1]] [[1, 1]] [[(5 / 2), 1], [1]]

theorem lgrU2_1_link (x a : ℝ) :
    lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + (x + 1 * (a - 1))) (lgrUc x (x + 1 * (a - 1)))
      (lgrVc x (x + 1 * (a - 1))) (ssDg x (x + 1 * (a - 1)) a) = lgrH2 lgrU2_1 (x - (5 / 2)) (a - 1) := by
  unfold lgrU2_1
  rw [lgr_H2_FN2, (lgr_H2_base (5 / 2) x a).1, (lgr_H2_base (5 / 2) x a).2, lgr_H2_lin]

/-- The signs of row 1: curvature, edge derivative, edge value, slanted edge. -/
theorem lgrU2_1_signs :
    0 ≤ lgrLow2 (7 / 12) (1 / 2) (lgrD2 (lgrD2 lgrU2_1)) ∧
      lgrCov (lgrEval 0 (lgrD2 lgrU2_1)) (7 / 12) [0, (7 / 24)] ∧
      lgrCov (lgrEval 0 lgrU2_1) (5 / 12) [0, (5 / 48), (5 / 24), (5 / 16)] ∧
      lgrCov (lgrSlant 2 (-5 / 6) lgrU2_1) (7 / 12) [(5 / 12)] := by
  norm_num [lgrU2_1, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD2, lgrLow, lgrNeg, lgrCov, lgrEval, lgrShift, lgrSlant]

/-- **Row 1 of the `τ = 2` test**: negative on `(5 / 2) ≤ x ≤ 3`, `1 ≤ α ≤ (5x + 4)/12`. -/
theorem lgrU2_1_neg {x a : ℝ} (hx : (5 / 2) ≤ x) (hxh : x ≤ 3) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG2 x a (x + 1 * (a - 1)) < 0 := by
  have hb : 1 < (x + 1 * (a - 1)) := by nlinarith
  apply lgr_G2_neg (by linarith) (by linarith) hb
  rw [lgrU2_1_link]
  obtain ⟨h1, h2, h3, h4⟩ := lgrU2_1_signs
  apply lgr_face_slant lgrU2_1 (HA := (7 / 12)) (W := (1 / 2)) (T := (5 / 12)) (α := 2) (β := (-5 / 6)) h1
    (lgr_cov_pos _ _ _ _ h2) (lgr_cov_pos _ _ _ _ h3) (lgr_cov_pos _ _ _ _ h4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rcases le_or_gt a (17 / 12) with h | h
  · left; linarith
  · right; constructor <;> linarith

end SmoothedOctagon

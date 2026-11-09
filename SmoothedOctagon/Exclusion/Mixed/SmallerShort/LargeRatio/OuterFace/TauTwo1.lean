module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip

/-!
# Smaller-short window, large ratio: the outer `τ = 2` test at the strip faces 0, 1, 2

On the strip `(22x + 20)/55 ≤ α ≤ (2x + 3)/5` with
`u = û`, the beta faces are `β = x + c_j(α - 1)`, `c₀ = 3/5` (the common lower face, `x ∈ [12/5, 9]`)
and `c_j = 7/8, 11/12, 13/12, 3/2` on `x ∈ [12/5, 5/2], [5/2, 14/5], [14/5, 4], [4, 9]`. On each
face the cleared numerator (`lgrNo2`, a polynomial of degree ten, computed in Lean from its factored
formula by `lgrFNo`, never printed) increases with `α` (the coefficient bound
on the rectangle in `X = x - l_j`, `A = α - α_f(x)`) and is positive on the lower edge `α = α_f(x)`
(by the coefficient bound on the whole edge; `lgr_strip_face`).

## Main API

* `lgrS2_0_neg`, `lgrS2_1_neg`, `lgrS2_2_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Face 0 of the outer `τ = 2` test on the strip: the cleared numerator at `β = x + (3 / 5)(α - 1)`, `u = û`,
as a list in `X = x - (12 / 5)`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def lgrS2_0 : List (List ℝ) :=
  lgrFNo 504 180 0 3528 2268 7903 (-3528) [[(12 / 5)], [1]] [[(364 / 275), 1], [(2 / 5)]]
    [[(3567 / 1375), (3 / 5)], [(31 / 25)]]

theorem lgrS2_0_link (x a : ℝ) :
    lgrNo2 (x + 1) a (a + (x + (3 / 5) * (a - 1))) (lgrUc x (x + (3 / 5) * (a - 1))) (lgrVc x (x + (3 / 5) * (a - 1)))
      (ssDg x (x + (3 / 5) * (a - 1)) a) = lgrH2 lgrS2_0 (x - (12 / 5)) (a - (22 * x + 20) / 55) := by
  have ex : lgrH2 [[(12 / 5)], [1]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = x := by
    simp [lgrH2, polyHorner]
  have ea : lgrH2 [[(364 / 275), 1], [(2 / 5)]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = a := by
    simp [lgrH2, polyHorner]; ring
  have eb : lgrH2 [[(3567 / 1375), (3 / 5)], [(31 / 25)]] (x - (12 / 5))
      (a - (22 * x + 20) / 55) = (x + (3 / 5) * (a - 1)) := by
    simp [lgrH2, polyHorner]; ring
  unfold lgrS2_0
  rw [lgr_H2_FNo2, ex, ea, eb]

/-- The signs of face 0: the `A`-derivative on the rectangle and the lower edge. -/
theorem lgrS2_0_signs :
    0 < lgrLow2 (13 / 55) (33 / 5) (lgrS2_0.map lgrD) ∧ lgrCov (lgrS2_0.map (lgrLow 0)) (33 / 5) [0] := by
  norm_num [lgrS2_0, lgrFNo, lgrNoL, lgrWoNL, lgrLoNL, lgrcS, lgrcSM, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD, lgrLow, lgrNeg, lgrCov, lgrShift]

/-- **Face 0 of the outer `τ = 2` test** is negative on `(12 / 5) ≤ x ≤ 9`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem lgrS2_0_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : lgrO2 x a (x + (3 / 5) * (a - 1)) (ssUhat x (x + (3 / 5) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (3 / 5) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (3 / 5) * (a - 1)) - 1 := by linarith
  have hV : 0 < lgrVc x (x + (3 / 5) * (a - 1)) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb]
  apply lgr_O2_neg (by linarith) (by linarith) (by linarith) hV
  rw [lgrS2_0_link]
  obtain ⟨h1, h2⟩ := lgrS2_0_signs
  exact lgr_strip_face lgrS2_0 h1 (lgr_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Face 1 of the outer `τ = 2` test on the strip: the cleared numerator at `β = x + (7 / 8)(α - 1)`, `u = û`,
as a list in `X = x - (12 / 5)`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def lgrS2_1 : List (List ℝ) :=
  lgrFNo 504 180 0 3528 2268 7903 (-3528) [[(12 / 5)], [1]] [[(364 / 275), 1], [(2 / 5)]]
    [[(5903 / 2200), (7 / 8)], [(27 / 20)]]

theorem lgrS2_1_link (x a : ℝ) :
    lgrNo2 (x + 1) a (a + (x + (7 / 8) * (a - 1))) (lgrUc x (x + (7 / 8) * (a - 1))) (lgrVc x (x + (7 / 8) * (a - 1)))
      (ssDg x (x + (7 / 8) * (a - 1)) a) = lgrH2 lgrS2_1 (x - (12 / 5)) (a - (22 * x + 20) / 55) := by
  have ex : lgrH2 [[(12 / 5)], [1]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = x := by
    simp [lgrH2, polyHorner]
  have ea : lgrH2 [[(364 / 275), 1], [(2 / 5)]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = a := by
    simp [lgrH2, polyHorner]; ring
  have eb : lgrH2 [[(5903 / 2200), (7 / 8)], [(27 / 20)]] (x - (12 / 5))
      (a - (22 * x + 20) / 55) = (x + (7 / 8) * (a - 1)) := by
    simp [lgrH2, polyHorner]; ring
  unfold lgrS2_1
  rw [lgr_H2_FNo2, ex, ea, eb]

/-- The signs of face 1: the `A`-derivative on the rectangle and the lower edge. -/
theorem lgrS2_1_signs :
    0 < lgrLow2 (13 / 55) (1 / 10) (lgrS2_1.map lgrD) ∧ lgrCov (lgrS2_1.map (lgrLow 0)) (1 / 10) [0] := by
  norm_num [lgrS2_1, lgrFNo, lgrNoL, lgrWoNL, lgrLoNL, lgrcS, lgrcSM, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD, lgrLow, lgrNeg, lgrCov, lgrShift]

/-- **Face 1 of the outer `τ = 2` test** is negative on `(12 / 5) ≤ x ≤ (5 / 2)`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem lgrS2_1_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ (5 / 2)) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : lgrO2 x a (x + (7 / 8) * (a - 1)) (ssUhat x (x + (7 / 8) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (7 / 8) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (7 / 8) * (a - 1)) - 1 := by linarith
  have hV : 0 < lgrVc x (x + (7 / 8) * (a - 1)) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb]
  apply lgr_O2_neg (by linarith) (by linarith) (by linarith) hV
  rw [lgrS2_1_link]
  obtain ⟨h1, h2⟩ := lgrS2_1_signs
  exact lgr_strip_face lgrS2_1 h1 (lgr_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Face 2 of the outer `τ = 2` test on the strip: the cleared numerator at `β = x + (11 / 12)(α - 1)`, `u = û`,
as a list in `X = x - (5 / 2)`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def lgrS2_2 : List (List ℝ) :=
  lgrFNo 504 180 0 3528 2268 7903 (-3528) [[(5 / 2)], [1]] [[(15 / 11), 1], [(2 / 5)]]
    [[(17 / 6), (11 / 12)], [(41 / 30)]]

theorem lgrS2_2_link (x a : ℝ) :
    lgrNo2 (x + 1) a (a + (x + (11 / 12) * (a - 1))) (lgrUc x (x + (11 / 12) * (a - 1))) (lgrVc x (x + (11 / 12) * (a - 1)))
      (ssDg x (x + (11 / 12) * (a - 1)) a) = lgrH2 lgrS2_2 (x - (5 / 2)) (a - (22 * x + 20) / 55) := by
  have ex : lgrH2 [[(5 / 2)], [1]] (x - (5 / 2)) (a - (22 * x + 20) / 55) = x := by
    simp [lgrH2, polyHorner]
  have ea : lgrH2 [[(15 / 11), 1], [(2 / 5)]] (x - (5 / 2)) (a - (22 * x + 20) / 55) = a := by
    simp [lgrH2, polyHorner]; ring
  have eb : lgrH2 [[(17 / 6), (11 / 12)], [(41 / 30)]] (x - (5 / 2))
      (a - (22 * x + 20) / 55) = (x + (11 / 12) * (a - 1)) := by
    simp [lgrH2, polyHorner]; ring
  unfold lgrS2_2
  rw [lgr_H2_FNo2, ex, ea, eb]

/-- The signs of face 2: the `A`-derivative on the rectangle and the lower edge. -/
theorem lgrS2_2_signs :
    0 < lgrLow2 (13 / 55) (3 / 10) (lgrS2_2.map lgrD) ∧ lgrCov (lgrS2_2.map (lgrLow 0)) (3 / 10) [0] := by
  norm_num [lgrS2_2, lgrFNo, lgrNoL, lgrWoNL, lgrLoNL, lgrcS, lgrcSM, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD, lgrLow, lgrNeg, lgrCov, lgrShift]

/-- **Face 2 of the outer `τ = 2` test** is negative on `(5 / 2) ≤ x ≤ (14 / 5)`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem lgrS2_2_neg {x a : ℝ} (hx : (5 / 2) ≤ x) (hxh : x ≤ (14 / 5)) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : lgrO2 x a (x + (11 / 12) * (a - 1)) (ssUhat x (x + (11 / 12) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (11 / 12) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (11 / 12) * (a - 1)) - 1 := by linarith
  have hV : 0 < lgrVc x (x + (11 / 12) * (a - 1)) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb]
  apply lgr_O2_neg (by linarith) (by linarith) (by linarith) hV
  rw [lgrS2_2_link]
  obtain ⟨h1, h2⟩ := lgrS2_2_signs
  exact lgr_strip_face lgrS2_2 h1 (lgr_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

end SmoothedOctagon

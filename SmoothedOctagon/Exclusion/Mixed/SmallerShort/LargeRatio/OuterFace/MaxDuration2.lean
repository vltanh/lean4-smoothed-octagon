module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip

/-!
# Smaller-short window, large ratio: the outer `τ = T` test at the strip faces 3, 4

On the strip `(22x + 20)/55 ≤ α ≤ (2x + 3)/5` with
`u = û`, the beta faces are `β = x + c_j(α - 1)`, `c₀ = 3/5` (the common lower face, `x ∈ [12/5, 9]`)
and `c_j = 7/8, 11/12, 13/12, 3/2` on `x ∈ [12/5, 5/2], [5/2, 14/5], [14/5, 4], [4, 9]`. On each
face the cleared numerator (`lgrNoT`, a polynomial of degree ten, computed in Lean from its factored
formula by `lgrFNo`, never printed) increases with `α` (the coefficient bound
on the rectangle in `X = x - l_j`, `A = α - α_f(x)`) and is positive on the lower edge `α = α_f(x)`
(by the coefficient bound on the whole edge; `lgr_strip_face`).

## Main API

* `lgrST_3_neg`, `lgrST_4_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Face 3 of the outer `τ = T` test on the strip: the cleared numerator at `β = x + (13 / 12)(α - 1)`, `u = û`,
as a list in `X = x - (14 / 5)`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def lgrST_3 : List (List ℝ) :=
  lgrFNo 56 4 56 392 336 (-189) 2352 [[(14 / 5)], [1]] [[(408 / 275), 1], [(2 / 5)]]
    [[(10969 / 3300), (13 / 12)], [(43 / 30)]]

theorem lgrST_3_link (x a : ℝ) :
    lgrNoT (x + 1) a (a + (x + (13 / 12) * (a - 1))) (lgrUc x (x + (13 / 12) * (a - 1))) (lgrVc x (x + (13 / 12) * (a - 1)))
      (ssDg x (x + (13 / 12) * (a - 1)) a) = lgrH2 lgrST_3 (x - (14 / 5)) (a - (22 * x + 20) / 55) := by
  have ex : lgrH2 [[(14 / 5)], [1]] (x - (14 / 5)) (a - (22 * x + 20) / 55) = x := by
    simp [lgrH2, polyHorner]
  have ea : lgrH2 [[(408 / 275), 1], [(2 / 5)]] (x - (14 / 5)) (a - (22 * x + 20) / 55) = a := by
    simp [lgrH2, polyHorner]; ring
  have eb : lgrH2 [[(10969 / 3300), (13 / 12)], [(43 / 30)]] (x - (14 / 5))
      (a - (22 * x + 20) / 55) = (x + (13 / 12) * (a - 1)) := by
    simp [lgrH2, polyHorner]; ring
  unfold lgrST_3
  rw [lgr_H2_FNoT, ex, ea, eb]

/-- The signs of face 3: the `A`-derivative on the rectangle and the lower edge. -/
theorem lgrST_3_signs :
    0 < lgrLow2 (13 / 55) (6 / 5) (lgrST_3.map lgrD) ∧ lgrCov (lgrST_3.map (lgrLow 0)) (6 / 5) [0] := by
  norm_num [lgrST_3, lgrFNo, lgrNoL, lgrWoNL, lgrLoNL, lgrcS, lgrcSM, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD, lgrLow, lgrNeg, lgrCov, lgrShift]

/-- **Face 3 of the outer `τ = T` test** is negative on `(14 / 5) ≤ x ≤ 4`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem lgrST_3_neg {x a : ℝ} (hx : (14 / 5) ≤ x) (hxh : x ≤ 4) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : lgrOT x a (x + (13 / 12) * (a - 1)) (ssUhat x (x + (13 / 12) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (13 / 12) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (13 / 12) * (a - 1)) - 1 := by linarith
  have hV : 0 < lgrVc x (x + (13 / 12) * (a - 1)) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb]
  apply lgr_OT_neg (by linarith) (by linarith) (by linarith) hV
  rw [lgrST_3_link]
  obtain ⟨h1, h2⟩ := lgrST_3_signs
  exact lgr_strip_face lgrST_3 h1 (lgr_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Face 4 of the outer `τ = T` test on the strip: the cleared numerator at `β = x + (3 / 2)(α - 1)`, `u = û`,
as a list in `X = x - 4`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def lgrST_4 : List (List ℝ) :=
  lgrFNo 56 4 56 392 336 (-189) 2352 [[4], [1]] [[(108 / 55), 1], [(2 / 5)]]
    [[(599 / 110), (3 / 2)], [(8 / 5)]]

theorem lgrST_4_link (x a : ℝ) :
    lgrNoT (x + 1) a (a + (x + (3 / 2) * (a - 1))) (lgrUc x (x + (3 / 2) * (a - 1))) (lgrVc x (x + (3 / 2) * (a - 1)))
      (ssDg x (x + (3 / 2) * (a - 1)) a) = lgrH2 lgrST_4 (x - 4) (a - (22 * x + 20) / 55) := by
  have ex : lgrH2 [[4], [1]] (x - 4) (a - (22 * x + 20) / 55) = x := by
    simp [lgrH2, polyHorner]
  have ea : lgrH2 [[(108 / 55), 1], [(2 / 5)]] (x - 4) (a - (22 * x + 20) / 55) = a := by
    simp [lgrH2, polyHorner]; ring
  have eb : lgrH2 [[(599 / 110), (3 / 2)], [(8 / 5)]] (x - 4)
      (a - (22 * x + 20) / 55) = (x + (3 / 2) * (a - 1)) := by
    simp [lgrH2, polyHorner]; ring
  unfold lgrST_4
  rw [lgr_H2_FNoT, ex, ea, eb]

/-- The signs of face 4: the `A`-derivative on the rectangle and the lower edge. -/
theorem lgrST_4_signs :
    0 < lgrLow2 (13 / 55) 5 (lgrST_4.map lgrD) ∧ lgrCov (lgrST_4.map (lgrLow 0)) 5 [0] := by
  norm_num [lgrST_4, lgrFNo, lgrNoL, lgrWoNL, lgrLoNL, lgrcS, lgrcSM, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrLow2, lgrD, lgrLow, lgrNeg, lgrCov, lgrShift]

/-- **Face 4 of the outer `τ = T` test** is negative on `4 ≤ x ≤ 9`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem lgrST_4_neg {x a : ℝ} (hx : 4 ≤ x) (hxh : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : lgrOT x a (x + (3 / 2) * (a - 1)) (ssUhat x (x + (3 / 2) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (3 / 2) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (3 / 2) * (a - 1)) - 1 := by linarith
  have hV : 0 < lgrVc x (x + (3 / 2) * (a - 1)) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb]
  apply lgr_OT_neg (by linarith) (by linarith) (by linarith) hV
  rw [lgrST_4_link]
  obtain ⟨h1, h2⟩ := lgrST_4_signs
  exact lgr_strip_face lgrST_4 h1 (lgr_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

end SmoothedOctagon

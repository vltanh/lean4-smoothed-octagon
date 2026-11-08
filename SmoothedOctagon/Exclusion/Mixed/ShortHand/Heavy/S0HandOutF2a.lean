module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutS

/-!
# Hand proof of the smaller-short case, gate S0: the outer `τ = 2` test at the strip faces 0, 1, 2

`archive/lighter-proofs/SHORT_SCALE_OUTER_LARGE_RATIO.md` §5 (algebra in
`SHORT_SCALE_OUTER_BOUNDARY_ALGEBRA.md`). On the strip `(22x + 20)/55 ≤ α ≤ (2x + 3)/5` with
`u = û`, the beta faces are `β = x + c_j(α - 1)`, `c₀ = 3/5` (the common lower face, `x ∈ [12/5, 9]`)
and `c_j = 7/8, 11/12, 13/12, 3/2` on `x ∈ [12/5, 5/2], [5/2, 14/5], [14/5, 4], [4, 9]`. On each
face the cleared numerator (`hl0No2`, a polynomial of degree ten, computed in Lean from its source
formula by `hl0FNo`, never printed) increases with `α` (the note's (29)-(31): the coefficient bound
on the rectangle in `X = x - l_j`, `A = α - α_f(x)`) and is positive on the lower edge `α = α_f(x)`
(the note's (32), by the coefficient bound on the whole edge instead of the boundary derivative and
the initial value).

## Main API

* `hl0S2_0_neg`, `hl0S2_1_neg`, `hl0S2_2_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Face 0 of the outer `τ = 2` test on the strip: the cleared numerator at `β = x + (3 / 5)(α - 1)`, `u = û`,
as a list in `X = x - (12 / 5)`, `A = α - (22x + 20)/55`, computed from the source formula. -/
noncomputable def hl0S2_0 : List (List ℝ) :=
  hl0FNo 504 180 0 3528 2268 7903 (-3528) [[(12 / 5)], [1]] [[(364 / 275), 1], [(2 / 5)]]
    [[(3567 / 1375), (3 / 5)], [(31 / 25)]]

theorem hl0S2_0_link (x a : ℝ) :
    hl0No2 (x + 1) a (a + (x + (3 / 5) * (a - 1))) (hl0Uc x (x + (3 / 5) * (a - 1))) (hl0Vc x (x + (3 / 5) * (a - 1)))
      (hsDg x (x + (3 / 5) * (a - 1)) a) = hl0H2 hl0S2_0 (x - (12 / 5)) (a - (22 * x + 20) / 55) := by
  have ex : hl0H2 [[(12 / 5)], [1]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = x := by
    simp [hl0H2, lrhHorner]
  have ea : hl0H2 [[(364 / 275), 1], [(2 / 5)]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = a := by
    simp [hl0H2, lrhHorner]; ring
  have eb : hl0H2 [[(3567 / 1375), (3 / 5)], [(31 / 25)]] (x - (12 / 5))
      (a - (22 * x + 20) / 55) = (x + (3 / 5) * (a - 1)) := by
    simp [hl0H2, lrhHorner]; ring
  unfold hl0S2_0
  rw [hl0_H2_FNo2, ex, ea, eb]

/-- The signs of face 0: the `A`-derivative on the rectangle and the lower edge. -/
theorem hl0S2_0_signs :
    0 < hl0Low2 (13 / 55) (33 / 5) (hl0S2_0.map hl0D) ∧ hl0Cov (hl0S2_0.map (hl0Low 0)) (33 / 5) [0] := by
  norm_num [hl0S2_0, hl0FNo, hl0NoL, hl0WoNL, hl0LoNL, hl0cS, hl0cSM, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D, hl0Low, hl0Neg, hl0Cov, hl0Shift]

/-- **Face 0 of the outer `τ = 2` test** is negative on `(12 / 5) ≤ x ≤ 9`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem hl0S2_0_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : hl0O2 x a (x + (3 / 5) * (a - 1)) (hsUhat x (x + (3 / 5) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (3 / 5) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (3 / 5) * (a - 1)) - 1 := by linarith
  have hV : 0 < hl0Vc x (x + (3 / 5) * (a - 1)) := by unfold hl0Vc; positivity
  rw [hl0_uhat_UV hx1 hb]
  apply hl0_O2_neg (by linarith) (by linarith) (by linarith) hV
  rw [hl0S2_0_link]
  obtain ⟨h1, h2⟩ := hl0S2_0_signs
  exact hl0_strip_face hl0S2_0 h1 (hl0_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Face 1 of the outer `τ = 2` test on the strip: the cleared numerator at `β = x + (7 / 8)(α - 1)`, `u = û`,
as a list in `X = x - (12 / 5)`, `A = α - (22x + 20)/55`, computed from the source formula. -/
noncomputable def hl0S2_1 : List (List ℝ) :=
  hl0FNo 504 180 0 3528 2268 7903 (-3528) [[(12 / 5)], [1]] [[(364 / 275), 1], [(2 / 5)]]
    [[(5903 / 2200), (7 / 8)], [(27 / 20)]]

theorem hl0S2_1_link (x a : ℝ) :
    hl0No2 (x + 1) a (a + (x + (7 / 8) * (a - 1))) (hl0Uc x (x + (7 / 8) * (a - 1))) (hl0Vc x (x + (7 / 8) * (a - 1)))
      (hsDg x (x + (7 / 8) * (a - 1)) a) = hl0H2 hl0S2_1 (x - (12 / 5)) (a - (22 * x + 20) / 55) := by
  have ex : hl0H2 [[(12 / 5)], [1]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = x := by
    simp [hl0H2, lrhHorner]
  have ea : hl0H2 [[(364 / 275), 1], [(2 / 5)]] (x - (12 / 5)) (a - (22 * x + 20) / 55) = a := by
    simp [hl0H2, lrhHorner]; ring
  have eb : hl0H2 [[(5903 / 2200), (7 / 8)], [(27 / 20)]] (x - (12 / 5))
      (a - (22 * x + 20) / 55) = (x + (7 / 8) * (a - 1)) := by
    simp [hl0H2, lrhHorner]; ring
  unfold hl0S2_1
  rw [hl0_H2_FNo2, ex, ea, eb]

/-- The signs of face 1: the `A`-derivative on the rectangle and the lower edge. -/
theorem hl0S2_1_signs :
    0 < hl0Low2 (13 / 55) (1 / 10) (hl0S2_1.map hl0D) ∧ hl0Cov (hl0S2_1.map (hl0Low 0)) (1 / 10) [0] := by
  norm_num [hl0S2_1, hl0FNo, hl0NoL, hl0WoNL, hl0LoNL, hl0cS, hl0cSM, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D, hl0Low, hl0Neg, hl0Cov, hl0Shift]

/-- **Face 1 of the outer `τ = 2` test** is negative on `(12 / 5) ≤ x ≤ (5 / 2)`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem hl0S2_1_neg {x a : ℝ} (hx : (12 / 5) ≤ x) (hxh : x ≤ (5 / 2)) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : hl0O2 x a (x + (7 / 8) * (a - 1)) (hsUhat x (x + (7 / 8) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (7 / 8) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (7 / 8) * (a - 1)) - 1 := by linarith
  have hV : 0 < hl0Vc x (x + (7 / 8) * (a - 1)) := by unfold hl0Vc; positivity
  rw [hl0_uhat_UV hx1 hb]
  apply hl0_O2_neg (by linarith) (by linarith) (by linarith) hV
  rw [hl0S2_1_link]
  obtain ⟨h1, h2⟩ := hl0S2_1_signs
  exact hl0_strip_face hl0S2_1 h1 (hl0_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Face 2 of the outer `τ = 2` test on the strip: the cleared numerator at `β = x + (11 / 12)(α - 1)`, `u = û`,
as a list in `X = x - (5 / 2)`, `A = α - (22x + 20)/55`, computed from the source formula. -/
noncomputable def hl0S2_2 : List (List ℝ) :=
  hl0FNo 504 180 0 3528 2268 7903 (-3528) [[(5 / 2)], [1]] [[(15 / 11), 1], [(2 / 5)]]
    [[(17 / 6), (11 / 12)], [(41 / 30)]]

theorem hl0S2_2_link (x a : ℝ) :
    hl0No2 (x + 1) a (a + (x + (11 / 12) * (a - 1))) (hl0Uc x (x + (11 / 12) * (a - 1))) (hl0Vc x (x + (11 / 12) * (a - 1)))
      (hsDg x (x + (11 / 12) * (a - 1)) a) = hl0H2 hl0S2_2 (x - (5 / 2)) (a - (22 * x + 20) / 55) := by
  have ex : hl0H2 [[(5 / 2)], [1]] (x - (5 / 2)) (a - (22 * x + 20) / 55) = x := by
    simp [hl0H2, lrhHorner]
  have ea : hl0H2 [[(15 / 11), 1], [(2 / 5)]] (x - (5 / 2)) (a - (22 * x + 20) / 55) = a := by
    simp [hl0H2, lrhHorner]; ring
  have eb : hl0H2 [[(17 / 6), (11 / 12)], [(41 / 30)]] (x - (5 / 2))
      (a - (22 * x + 20) / 55) = (x + (11 / 12) * (a - 1)) := by
    simp [hl0H2, lrhHorner]; ring
  unfold hl0S2_2
  rw [hl0_H2_FNo2, ex, ea, eb]

/-- The signs of face 2: the `A`-derivative on the rectangle and the lower edge. -/
theorem hl0S2_2_signs :
    0 < hl0Low2 (13 / 55) (3 / 10) (hl0S2_2.map hl0D) ∧ hl0Cov (hl0S2_2.map (hl0Low 0)) (3 / 10) [0] := by
  norm_num [hl0S2_2, hl0FNo, hl0NoL, hl0WoNL, hl0LoNL, hl0cS, hl0cSM, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D, hl0Low, hl0Neg, hl0Cov, hl0Shift]

/-- **Face 2 of the outer `τ = 2` test** is negative on `(5 / 2) ≤ x ≤ (14 / 5)`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem hl0S2_2_neg {x a : ℝ} (hx : (5 / 2) ≤ x) (hxh : x ≤ (14 / 5)) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : hl0O2 x a (x + (11 / 12) * (a - 1)) (hsUhat x (x + (11 / 12) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (11 / 12) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (11 / 12) * (a - 1)) - 1 := by linarith
  have hV : 0 < hl0Vc x (x + (11 / 12) * (a - 1)) := by unfold hl0Vc; positivity
  rw [hl0_uhat_UV hx1 hb]
  apply hl0_O2_neg (by linarith) (by linarith) (by linarith) hV
  rw [hl0S2_2_link]
  obtain ⟨h1, h2⟩ := hl0S2_2_signs
  exact hl0_strip_face hl0S2_2 h1 (hl0_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

end SmoothedOctagon

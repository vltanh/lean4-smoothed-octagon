module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutS

/-!
# Hand proof of the smaller-short case, gate S0: the outer `τ = 8T/9` test at the strip faces 3, 4

On the strip `(22x + 20)/55 ≤ α ≤ (2x + 3)/5` with
`u = û`, the beta faces are `β = x + c_j(α - 1)`, `c₀ = 3/5` (the common lower face, `x ∈ [12/5, 9]`)
and `c_j = 7/8, 11/12, 13/12, 3/2` on `x ∈ [12/5, 5/2], [5/2, 14/5], [14/5, 4], [4, 9]`. On each
face the cleared numerator (`hl0No8`, a polynomial of degree ten, computed in Lean from its factored
formula by `hl0FNo`, never printed) increases with `α` (the coefficient bound
on the rectangle in `X = x - l_j`, `A = α - α_f(x)`) and is positive on the lower edge `α = α_f(x)`
(by the coefficient bound on the whole edge; `hl0_strip_face`).

## Main API

* `hl0S8_3_neg`, `hl0S8_4_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Face 3 of the outer `τ = 8T/9` test on the strip: the cleared numerator at `β = x + (13 / 12)(α - 1)`, `u = û`,
as a list in `X = x - (14 / 5)`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def hl0S8_3 : List (List ℝ) :=
  hl0FNo 1008 72 896 7056 5922 (-2618) 36848 [[(14 / 5)], [1]] [[(408 / 275), 1], [(2 / 5)]]
    [[(10969 / 3300), (13 / 12)], [(43 / 30)]]

theorem hl0S8_3_link (x a : ℝ) :
    hl0No8 (x + 1) a (a + (x + (13 / 12) * (a - 1))) (hl0Uc x (x + (13 / 12) * (a - 1))) (hl0Vc x (x + (13 / 12) * (a - 1)))
      (hsDg x (x + (13 / 12) * (a - 1)) a) = hl0H2 hl0S8_3 (x - (14 / 5)) (a - (22 * x + 20) / 55) := by
  have ex : hl0H2 [[(14 / 5)], [1]] (x - (14 / 5)) (a - (22 * x + 20) / 55) = x := by
    simp [hl0H2, lrhHorner]
  have ea : hl0H2 [[(408 / 275), 1], [(2 / 5)]] (x - (14 / 5)) (a - (22 * x + 20) / 55) = a := by
    simp [hl0H2, lrhHorner]; ring
  have eb : hl0H2 [[(10969 / 3300), (13 / 12)], [(43 / 30)]] (x - (14 / 5))
      (a - (22 * x + 20) / 55) = (x + (13 / 12) * (a - 1)) := by
    simp [hl0H2, lrhHorner]; ring
  unfold hl0S8_3
  rw [hl0_H2_FNo8, ex, ea, eb]

/-- The signs of face 3: the `A`-derivative on the rectangle and the lower edge. -/
theorem hl0S8_3_signs :
    0 < hl0Low2 (13 / 55) (6 / 5) (hl0S8_3.map hl0D) ∧ hl0Cov (hl0S8_3.map (hl0Low 0)) (6 / 5) [0] := by
  norm_num [hl0S8_3, hl0FNo, hl0NoL, hl0WoNL, hl0LoNL, hl0cS, hl0cSM, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D, hl0Low, hl0Neg, hl0Cov, hl0Shift]

/-- **Face 3 of the outer `τ = 8T/9` test** is negative on `(14 / 5) ≤ x ≤ 4`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem hl0S8_3_neg {x a : ℝ} (hx : (14 / 5) ≤ x) (hxh : x ≤ 4) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : hl0O8 x a (x + (13 / 12) * (a - 1)) (hsUhat x (x + (13 / 12) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (13 / 12) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (13 / 12) * (a - 1)) - 1 := by linarith
  have hV : 0 < hl0Vc x (x + (13 / 12) * (a - 1)) := by unfold hl0Vc; positivity
  rw [hl0_uhat_UV hx1 hb]
  apply hl0_O8_neg (by linarith) (by linarith) (by linarith) hV
  rw [hl0S8_3_link]
  obtain ⟨h1, h2⟩ := hl0S8_3_signs
  exact hl0_strip_face hl0S8_3 h1 (hl0_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Face 4 of the outer `τ = 8T/9` test on the strip: the cleared numerator at `β = x + (3 / 2)(α - 1)`, `u = û`,
as a list in `X = x - 4`, `A = α - (22x + 20)/55`, computed from the factored formula. -/
noncomputable def hl0S8_4 : List (List ℝ) :=
  hl0FNo 1008 72 896 7056 5922 (-2618) 36848 [[4], [1]] [[(108 / 55), 1], [(2 / 5)]]
    [[(599 / 110), (3 / 2)], [(8 / 5)]]

theorem hl0S8_4_link (x a : ℝ) :
    hl0No8 (x + 1) a (a + (x + (3 / 2) * (a - 1))) (hl0Uc x (x + (3 / 2) * (a - 1))) (hl0Vc x (x + (3 / 2) * (a - 1)))
      (hsDg x (x + (3 / 2) * (a - 1)) a) = hl0H2 hl0S8_4 (x - 4) (a - (22 * x + 20) / 55) := by
  have ex : hl0H2 [[4], [1]] (x - 4) (a - (22 * x + 20) / 55) = x := by
    simp [hl0H2, lrhHorner]
  have ea : hl0H2 [[(108 / 55), 1], [(2 / 5)]] (x - 4) (a - (22 * x + 20) / 55) = a := by
    simp [hl0H2, lrhHorner]; ring
  have eb : hl0H2 [[(599 / 110), (3 / 2)], [(8 / 5)]] (x - 4)
      (a - (22 * x + 20) / 55) = (x + (3 / 2) * (a - 1)) := by
    simp [hl0H2, lrhHorner]; ring
  unfold hl0S8_4
  rw [hl0_H2_FNo8, ex, ea, eb]

/-- The signs of face 4: the `A`-derivative on the rectangle and the lower edge. -/
theorem hl0S8_4_signs :
    0 < hl0Low2 (13 / 55) 5 (hl0S8_4.map hl0D) ∧ hl0Cov (hl0S8_4.map (hl0Low 0)) 5 [0] := by
  norm_num [hl0S8_4, hl0FNo, hl0NoL, hl0WoNL, hl0LoNL, hl0cS, hl0cSM, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0Low2, hl0D, hl0Low, hl0Neg, hl0Cov, hl0Shift]

/-- **Face 4 of the outer `τ = 8T/9` test** is negative on `4 ≤ x ≤ 9`, `(22x + 20)/55 ≤ α ≤ (2x + 3)/5`. -/
theorem hl0S8_4_neg {x a : ℝ} (hx : 4 ≤ x) (hxh : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : hl0O8 x a (x + (3 / 2) * (a - 1)) (hsUhat x (x + (3 / 2) * (a - 1))) < 0 := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 < a := by linarith
  have hb : 1 < (x + (3 / 2) * (a - 1)) := by nlinarith
  have hb1 : 0 < (x + (3 / 2) * (a - 1)) - 1 := by linarith
  have hV : 0 < hl0Vc x (x + (3 / 2) * (a - 1)) := by unfold hl0Vc; positivity
  rw [hl0_uhat_UV hx1 hb]
  apply hl0_O8_neg (by linarith) (by linarith) (by linarith) hV
  rw [hl0S8_4_link]
  obtain ⟨h1, h2⟩ := hl0S8_4_signs
  exact hl0_strip_face hl0S8_4 h1 (hl0_cov_pos _ _ _ _ h2)
    (by linarith) (by linarith) (by linarith) (by linarith)

end SmoothedOctagon

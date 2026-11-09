module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace

/-!
# Smaller-short window, large ratio: the central tests at the lower face `β = x`

At `β = x` the three central tests
(`τ = T`, `8T/9`, `2`) are negative on `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`. The cleared numerator
`N` (`lgrNT`, `lgrN8`, `lgrN2` at `β = x`) is
computed in Lean from its factored formula (`lgrLFT`, …; never printed). `∂_α N > 0` on the shape
domain (by the coefficient bound on three pieces, `lgr_trap_pos`) and `N(x, 1) > 0`
(all its coefficients in `x - 12/5` are positive), so `N(x, α) ≥ N(x, 1) > 0` (`lgr_low_gen`).

The sign of `∂_α N` uses two coordinate systems (split at `α = 4/3`, the first piece split once
more at `α = 7/6`), and every coefficient is bounded by the uniform coefficient bound `lgrLow`.

## Main API

* `lgr_lowT`, `lgr_low8`, `lgr_low2`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Monotonicity in `α` on the lower face**: a positive `α`-derivative on the shape domain and
a positive value at `α = 1` give positivity. -/
theorem lgr_low_gen (P : List (List ℝ)) (h1 : lgrPosL ((P.map lgrD).map (lgrLow (1 / 6))))
    (h2 : lgrPosL (((P.map lgrD).map (lgrShift (1 / 6))).map (lgrLow (1 / 6))))
    (h3 : lgrPosL ((lgrShear (12 / 5) ((P.map lgrD).map (lgrShift (1 / 3)))).map (lgrLow (11 / 4))))
    (h0 : lgrPosL (P.map (lgrLow 0))) {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : 0 < lgrH2 P (x - 12 / 5) (a - 1) := by
  have hd : ∀ A, 0 ≤ A → A ≤ a - 1 → 0 ≤ lgrH2 (P.map lgrD) (x - 12 / 5) A := by
    intro A hA hAa
    have := lgr_trap_pos (P.map lgrD) h1 h2 h3 (a := A + 1) hx hx9 (by linarith) (by linarith)
    rw [add_sub_cancel_right] at this
    exact this.le
  have hm := lgr_mono_A (P := P) (X := x - 12 / 5) hd (by linarith : (0 : ℝ) ≤ a - 1)
  have h00 := lgr_pos_unb (HA := 0) le_rfl le_rfl (by linarith : (0 : ℝ) ≤ x - 12 / 5) P h0
  linarith

/-- The lower-face numerator of the `τ = T` test (`β = x`) as a list in `X = x - 12/5`, `A = α - 1`,
computed from the factored formula. -/
noncomputable def lgrLFT : List (List ℝ) :=
  lgrFNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) [[12 / 5], [1]] [[1, 1]] [[12 / 5], [1]]

theorem lgr_low_linkT (x a : ℝ) :
    lgrNT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x) (lgrUc x x) (lgrVc x x) (ssDg x x a) =
      lgrH2 lgrLFT (x - 12 / 5) (a - 1) := by
  unfold lgrLFT
  rw [lgr_H2_FNT, (lgr_H2_base (12 / 5) x a).1, (lgr_H2_base (12 / 5) x a).2]

/-- The signs of the lower face of the `τ = T` test: `∂_α N` on the three pieces of the shape domain and
`N(x, 1)`. -/
theorem lgr_low_signsT :
    lgrPosL ((lgrLFT.map lgrD).map (lgrLow (1 / 6))) ∧
      lgrPosL (((lgrLFT.map lgrD).map (lgrShift (1 / 6))).map (lgrLow (1 / 6))) ∧
      lgrPosL ((lgrShear (12 / 5) ((lgrLFT.map lgrD).map (lgrShift (1 / 3)))).map (lgrLow (11 / 4))) ∧
      lgrPosL (lgrLFT.map (lgrLow 0)) := by
  norm_num [lgrLFT, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrPosL, lgrLow, lgrNeg, lgrD, lgrShift, lgrShear]

/-- **The lower face of the `τ = T` test**: negative at `β = x` (`lgr_low_gen`). -/
theorem lgr_lowT {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrGT x a x < 0 := by
  have hx1 : 1 < x := by linarith
  apply lgr_GT_neg hx1 (by linarith) hx1
  rw [lgr_low_linkT]
  obtain ⟨h1, h2, h3, h0⟩ := lgr_low_signsT
  exact lgr_low_gen lgrLFT h1 h2 h3 h0 hx hx9 ha ha'

/-- The lower-face numerator of the `τ = 8T/9` test (`β = x`) as a list in `X = x - 12/5`, `A = α - 1`,
computed from the factored formula. -/
noncomputable def lgrLF8 : List (List ℝ) :=
  lgrFNc 72 36 64 72 72 (-81) (-37) 72 64 (-72) [[12 / 5], [1]] [[1, 1]] [[12 / 5], [1]]

theorem lgr_low_link8 (x a : ℝ) :
    lgrN8 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x) (lgrUc x x) (lgrVc x x) (ssDg x x a) =
      lgrH2 lgrLF8 (x - 12 / 5) (a - 1) := by
  unfold lgrLF8
  rw [lgr_H2_FN8, (lgr_H2_base (12 / 5) x a).1, (lgr_H2_base (12 / 5) x a).2]

/-- The signs of the lower face of the `τ = 8T/9` test: `∂_α N` on the three pieces of the shape domain and
`N(x, 1)`. -/
theorem lgr_low_signs8 :
    lgrPosL ((lgrLF8.map lgrD).map (lgrLow (1 / 6))) ∧
      lgrPosL (((lgrLF8.map lgrD).map (lgrShift (1 / 6))).map (lgrLow (1 / 6))) ∧
      lgrPosL ((lgrShear (12 / 5) ((lgrLF8.map lgrD).map (lgrShift (1 / 3)))).map (lgrLow (11 / 4))) ∧
      lgrPosL (lgrLF8.map (lgrLow 0)) := by
  norm_num [lgrLF8, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrPosL, lgrLow, lgrNeg, lgrD, lgrShift, lgrShear]

/-- **The lower face of the `τ = 8T/9` test**: negative at `β = x` (`lgr_low_gen`). -/
theorem lgr_low8 {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG8 x a x < 0 := by
  have hx1 : 1 < x := by linarith
  apply lgr_G8_neg hx1 (by linarith) hx1
  rw [lgr_low_link8]
  obtain ⟨h1, h2, h3, h0⟩ := lgr_low_signs8
  exact lgr_low_gen lgrLF8 h1 h2 h3 h0 hx hx9 ha ha'

/-- The lower-face numerator of the `τ = 2` test (`β = x`) as a list in `X = x - 12/5`, `A = α - 1`,
computed from the factored formula. -/
noncomputable def lgrLF2 : List (List ℝ) :=
  lgrFNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[12 / 5], [1]] [[1, 1]] [[12 / 5], [1]]

theorem lgr_low_link2 (x a : ℝ) :
    lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x) (lgrUc x x) (lgrVc x x) (ssDg x x a) =
      lgrH2 lgrLF2 (x - 12 / 5) (a - 1) := by
  unfold lgrLF2
  rw [lgr_H2_FN2, (lgr_H2_base (12 / 5) x a).1, (lgr_H2_base (12 / 5) x a).2]

/-- The signs of the lower face of the `τ = 2` test: `∂_α N` on the three pieces of the shape domain and
`N(x, 1)`. -/
theorem lgr_low_signs2 :
    lgrPosL ((lgrLF2.map lgrD).map (lgrLow (1 / 6))) ∧
      lgrPosL (((lgrLF2.map lgrD).map (lgrShift (1 / 6))).map (lgrLow (1 / 6))) ∧
      lgrPosL ((lgrShear (12 / 5) ((lgrLF2.map lgrD).map (lgrShift (1 / 3)))).map (lgrLow (11 / 4))) ∧
      lgrPosL (lgrLF2.map (lgrLow 0)) := by
  norm_num [lgrLF2, lgrFNc, lgrNcL, lgrBrL, lgrWNL, lgrLNL, lgrcS, lgrcSM, lgrcK, lgrcU, lgrcV, lgrcD, lgrMul2, lgrMul, lgrSmul2, lgrAdd2, lgrAdd, lgrSmul, lgrPosL, lgrLow, lgrNeg, lgrD, lgrShift, lgrShear]

/-- **The lower face of the `τ = 2` test**: negative at `β = x` (`lgr_low_gen`). -/
theorem lgr_low2 {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG2 x a x < 0 := by
  have hx1 : 1 < x := by linarith
  apply lgr_G2_neg hx1 (by linarith) hx1
  rw [lgr_low_link2]
  obtain ⟨h1, h2, h3, h0⟩ := lgr_low_signs2
  exact lgr_low_gen lgrLF2 h1 h2 h3 h0 hx hx9 ha ha'

end SmoothedOctagon

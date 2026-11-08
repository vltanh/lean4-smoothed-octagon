module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen

/-!
# Hand proof of the smaller-short case, gate S0: the central tests at the lower face `β = x`

At `β = x` the three central tests
(`τ = T`, `8T/9`, `2`) are negative on `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`. The cleared numerator
`N` (`hl0NT`, `hl0N8`, `hl0N2` at `β = x`) is
computed in Lean from its factored formula (`hl0LFT`, …; never printed). `∂_α N > 0` on the shape
domain (by the coefficient bound on three pieces, `hl0_trap_pos`) and `N(x, 1) > 0`
(all its coefficients in `x - 12/5` are positive), so `N(x, α) ≥ N(x, 1) > 0` (`hl0_low_gen`).

The sign of `∂_α N` uses two coordinate systems (split at `α = 4/3`, the first piece split once
more at `α = 7/6`), and every coefficient is bounded by the uniform coefficient bound `hl0Low`.

## Main API

* `hl0_lowT`, `hl0_low8`, `hl0_low2`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Monotonicity in `α` on the lower face**: a positive `α`-derivative on the shape domain and
a positive value at `α = 1` give positivity. -/
theorem hl0_low_gen (P : List (List ℝ)) (h1 : hl0PosL ((P.map hl0D).map (hl0Low (1 / 6))))
    (h2 : hl0PosL (((P.map hl0D).map (hl0Shift (1 / 6))).map (hl0Low (1 / 6))))
    (h3 : hl0PosL ((hl0Shear (12 / 5) ((P.map hl0D).map (hl0Shift (1 / 3)))).map (hl0Low (11 / 4))))
    (h0 : hl0PosL (P.map (hl0Low 0))) {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : 0 < hl0H2 P (x - 12 / 5) (a - 1) := by
  have hd : ∀ A, 0 ≤ A → A ≤ a - 1 → 0 ≤ hl0H2 (P.map hl0D) (x - 12 / 5) A := by
    intro A hA hAa
    have := hl0_trap_pos (P.map hl0D) h1 h2 h3 (a := A + 1) hx hx9 (by linarith) (by linarith)
    rw [add_sub_cancel_right] at this
    exact this.le
  have hm := hl0_mono_A (P := P) (X := x - 12 / 5) hd (by linarith : (0 : ℝ) ≤ a - 1)
  have h00 := hl0_pos_unb (HA := 0) le_rfl le_rfl (by linarith : (0 : ℝ) ≤ x - 12 / 5) P h0
  linarith

/-- The lower-face numerator of the `τ = T` test (`β = x`) as a list in `X = x - 12/5`, `A = α - 1`,
computed from the factored formula. -/
noncomputable def hl0LFT : List (List ℝ) :=
  hl0FNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) [[12 / 5], [1]] [[1, 1]] [[12 / 5], [1]]

theorem hl0_low_linkT (x a : ℝ) :
    hl0NT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x) (hl0Uc x x) (hl0Vc x x) (hsDg x x a) =
      hl0H2 hl0LFT (x - 12 / 5) (a - 1) := by
  unfold hl0LFT
  rw [hl0_H2_FNT, (hl0_H2_base (12 / 5) x a).1, (hl0_H2_base (12 / 5) x a).2]

/-- The signs of the lower face of the `τ = T` test: `∂_α N` on the three pieces of the shape domain and
`N(x, 1)`. -/
theorem hl0_low_signsT :
    hl0PosL ((hl0LFT.map hl0D).map (hl0Low (1 / 6))) ∧
      hl0PosL (((hl0LFT.map hl0D).map (hl0Shift (1 / 6))).map (hl0Low (1 / 6))) ∧
      hl0PosL ((hl0Shear (12 / 5) ((hl0LFT.map hl0D).map (hl0Shift (1 / 3)))).map (hl0Low (11 / 4))) ∧
      hl0PosL (hl0LFT.map (hl0Low 0)) := by
  norm_num [hl0LFT, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0PosL, hl0Low, hl0Neg, hl0D, hl0Shift, hl0Shear]

/-- **The lower face of the `τ = T` test**: negative at `β = x` (`hl0_low_gen`). -/
theorem hl0_lowT {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0GT x a x < 0 := by
  have hx1 : 1 < x := by linarith
  apply hl0_GT_neg hx1 (by linarith) hx1
  rw [hl0_low_linkT]
  obtain ⟨h1, h2, h3, h0⟩ := hl0_low_signsT
  exact hl0_low_gen hl0LFT h1 h2 h3 h0 hx hx9 ha ha'

/-- The lower-face numerator of the `τ = 8T/9` test (`β = x`) as a list in `X = x - 12/5`, `A = α - 1`,
computed from the factored formula. -/
noncomputable def hl0LF8 : List (List ℝ) :=
  hl0FNc 72 36 64 72 72 (-81) (-37) 72 64 (-72) [[12 / 5], [1]] [[1, 1]] [[12 / 5], [1]]

theorem hl0_low_link8 (x a : ℝ) :
    hl0N8 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x) (hl0Uc x x) (hl0Vc x x) (hsDg x x a) =
      hl0H2 hl0LF8 (x - 12 / 5) (a - 1) := by
  unfold hl0LF8
  rw [hl0_H2_FN8, (hl0_H2_base (12 / 5) x a).1, (hl0_H2_base (12 / 5) x a).2]

/-- The signs of the lower face of the `τ = 8T/9` test: `∂_α N` on the three pieces of the shape domain and
`N(x, 1)`. -/
theorem hl0_low_signs8 :
    hl0PosL ((hl0LF8.map hl0D).map (hl0Low (1 / 6))) ∧
      hl0PosL (((hl0LF8.map hl0D).map (hl0Shift (1 / 6))).map (hl0Low (1 / 6))) ∧
      hl0PosL ((hl0Shear (12 / 5) ((hl0LF8.map hl0D).map (hl0Shift (1 / 3)))).map (hl0Low (11 / 4))) ∧
      hl0PosL (hl0LF8.map (hl0Low 0)) := by
  norm_num [hl0LF8, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0PosL, hl0Low, hl0Neg, hl0D, hl0Shift, hl0Shear]

/-- **The lower face of the `τ = 8T/9` test**: negative at `β = x` (`hl0_low_gen`). -/
theorem hl0_low8 {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0G8 x a x < 0 := by
  have hx1 : 1 < x := by linarith
  apply hl0_G8_neg hx1 (by linarith) hx1
  rw [hl0_low_link8]
  obtain ⟨h1, h2, h3, h0⟩ := hl0_low_signs8
  exact hl0_low_gen hl0LF8 h1 h2 h3 h0 hx hx9 ha ha'

/-- The lower-face numerator of the `τ = 2` test (`β = x`) as a list in `X = x - 12/5`, `A = α - 1`,
computed from the factored formula. -/
noncomputable def hl0LF2 : List (List ℝ) :=
  hl0FNc 72 180 0 72 72 (-180) 151 72 0 (-72) [[12 / 5], [1]] [[1, 1]] [[12 / 5], [1]]

theorem hl0_low_link2 (x a : ℝ) :
    hl0N2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x) (hl0Uc x x) (hl0Vc x x) (hsDg x x a) =
      hl0H2 hl0LF2 (x - 12 / 5) (a - 1) := by
  unfold hl0LF2
  rw [hl0_H2_FN2, (hl0_H2_base (12 / 5) x a).1, (hl0_H2_base (12 / 5) x a).2]

/-- The signs of the lower face of the `τ = 2` test: `∂_α N` on the three pieces of the shape domain and
`N(x, 1)`. -/
theorem hl0_low_signs2 :
    hl0PosL ((hl0LF2.map hl0D).map (hl0Low (1 / 6))) ∧
      hl0PosL (((hl0LF2.map hl0D).map (hl0Shift (1 / 6))).map (hl0Low (1 / 6))) ∧
      hl0PosL ((hl0Shear (12 / 5) ((hl0LF2.map hl0D).map (hl0Shift (1 / 3)))).map (hl0Low (11 / 4))) ∧
      hl0PosL (hl0LF2.map (hl0Low 0)) := by
  norm_num [hl0LF2, hl0FNc, hl0NcL, hl0BrL, hl0WNL, hl0LNL, hl0cS, hl0cSM, hl0cK, hl0cU, hl0cV, hl0cD, hl0Mul2, hl0Mul, hl0Smul2, hl0Add2, hl0Add, hl0Smul, hl0PosL, hl0Low, hl0Neg, hl0D, hl0Shift, hl0Shear]

/-- **The lower face of the `τ = 2` test**: negative at `β = x` (`hl0_low_gen`). -/
theorem hl0_low2 {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : hl0G2 x a x < 0 := by
  have hx1 : 1 < x := by linarith
  apply hl0_G2_neg hx1 (by linarith) hx1
  rw [hl0_low_link2]
  obtain ⟨h1, h2, h3, h0⟩ := hl0_low_signs2
  exact hl0_low_gen hl0LF2 h1 h2 h3 h0 hx hx9 ha ha'

end SmoothedOctagon

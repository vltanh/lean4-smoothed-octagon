module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOut

/-!
# Hand proof of the smaller-short case, gate S0: the outer face, beta convexity on the strip

On the strip
`(22x + 20)/55 ≤ α ≤ (2x + 3)/5` with `u = û = u_∞ + J/(β - 1)`, each outer test is
`kη² + lη + m + r/η + s/(η + α + 1)` in `η = β - 1` (`hl0_pfo_g`, `hl0_pfo_2`): `k = q₀, q₀, 5q₀`,
`r = J·U_i` (`U_i` the coefficient of `u` at `β = 1`) and `s = R_i` (`R_T = α(7w₋ - 6)`,
`R₈ = (8/9)R_T + α/9`, `R₂ = α`). The residue signs `U_T > -5/2`, `U₂ > 0`, `R_T > x²/3`
(`hl0_strip_rT`, `hl0_strip_r2`, `hl0_strip_sT`) give the convexity margin
`k + min(r, 0)/(β₀ - 1)³ + s/B₁³ ≥ 0` (`hl0_strip_hk`) of `hl0_chord2`, with
`β - 1 ≥ x - 1` and `B ≤ 2x` on the strip (`hl0_strip_chord_T`, `_8`, `_2`).

The three residue signs are proved by the coefficient bound on the strip coordinates
`X = x - 12/5`, `A = α - (22x + 20)/55` (`hl0QTf`, `hl0Q2f`, `hl0SRf`, their lists computed in
Lean; one split at `x = 57/10`), and `R_T > x²/3` directly at the continued value `û(-α)`.

## Main API

* `hl0_strip_chord_T`, `hl0_strip_chord_8`, `hl0_strip_chord_2`.
-/

@[expose] public section

namespace SmoothedOctagon

theorem hl0_J_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ hl0J x := by
  unfold hl0J
  have : 0 ≤ x - 1 := by linarith
  positivity

/-! ### Partial fractions of the outer tests -/

/-- `Q₀ = M₀S`. -/
noncomputable def hl0oQ0 (S a : ℝ) : ℝ := (6 * a ^ 2 + 1) * S
/-- `P₀ = M₀(1/S - S) + 2S - 1`. -/
noncomputable def hl0oP0 (S a : ℝ) : ℝ := (6 * a ^ 2 + 1) * (1 / S - S) + 2 * S - 1
/-- `C₀ = M₀² - M₀S + S²`. -/
noncomputable def hl0oC0 (S a : ℝ) : ℝ := (6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2
/-- Coefficient of `η` in `W`. -/
noncomputable def hl0oWl (S a ui J D1 δ : ℝ) : ℝ :=
  ui * δ * (2 * D1 - hl0oQ0 S a) + J * δ ^ 2 - δ * hl0oP0 S a
/-- Constant term of `W`. -/
noncomputable def hl0oWm (S a ui J D1 δ : ℝ) : ℝ :=
  hl0oC0 S a - D1 * hl0oP0 S a + ui * D1 * (D1 - hl0oQ0 S a) + J * δ * (2 * D1 - hl0oQ0 S a)
/-- Residue of `W` at `η = 0`. -/
noncomputable def hl0oWr (S a J D1 : ℝ) : ℝ := J * D1 * (D1 - hl0oQ0 S a)
/-- Constant term of `L`. -/
noncomputable def hl0oLm (S a ui J D1 δ : ℝ) : ℝ := ui * (2 * D1 - hl0oQ0 S a) + 2 * J * δ - hl0oP0 S a
/-- Residue of `L` at `η = 0`. -/
noncomputable def hl0oLr (S a J D1 : ℝ) : ℝ := J * (2 * D1 - hl0oQ0 S a)

theorem hl0_Wo_pf {S a ui J D1 δ η : ℝ} (hS : S ≠ 0) (hη : η ≠ 0) :
    hl0Wo S a (ui + J / η) (D1 + δ * η) = hl0Wk ui δ * η ^ 2 + hl0oWl S a ui J D1 δ * η +
      hl0oWm S a ui J D1 δ + hl0oWr S a J D1 / η := by
  unfold hl0Wo hl0Wk hl0oWl hl0oWm hl0oWr hl0oQ0 hl0oP0 hl0oC0
  field_simp
  ring

theorem hl0_Lo_pf {S a ui J D1 δ η : ℝ} (hS : S ≠ 0) (hη : η ≠ 0) :
    hl0Lo S a (ui + J / η) (D1 + δ * η) = hl0Ll ui δ * η + hl0oLm S a ui J D1 δ +
      hl0oLr S a J D1 / η := by
  unfold hl0Lo hl0Ll hl0oLm hl0oLr hl0oQ0 hl0oP0
  field_simp
  ring

/-- `Q = W_k c² - W_l c + W_m - 49α⁴ - W_r/c`: `Q/(49α⁴) = w₋ - 1`. -/
noncomputable def hl0oQd (S a ui J D1 δ c : ℝ) : ℝ :=
  hl0Wk ui δ * c ^ 2 - hl0oWl S a ui J D1 δ * c + hl0oWm S a ui J D1 δ - 49 * a ^ 4 -
    hl0oWr S a J D1 / c

/-- **The tests `τ = gα/B` in partial fractions** (`g = 7`: `τ = T`; `g = 56/9`: `τ = 8T/9`). -/
theorem hl0_pfo_g {S a c ui J D1 δ η g ℓ : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hg : g ≠ 0) (hη : η ≠ 0) (hB : c + η ≠ 0) :
    hl0Go S a (c + η) (ui + J / η) (D1 + δ * η) (g * (a / (c + η))) ℓ =
      (hl0Wk ui δ / (2 * (49 * a ^ 4))) * η ^ 2 +
      (g * a * hl0Wk ui δ / (49 * a ^ 4) + 1 / (g * a) + (ui - 1) / a - hl0Ll ui δ / (7 * a ^ 2) +
        hl0oWl S a ui J D1 δ / (2 * (49 * a ^ 4))) * η +
      (g * a * (hl0oWl S a ui J D1 δ - hl0Wk ui δ * c) / (49 * a ^ 4) + c / (g * a) +
        ((ui - 1) * c + J) / a + 6 / 7 - hl0oLm S a ui J D1 δ / (7 * a ^ 2) + ℓ +
        hl0oWm S a ui J D1 δ / (2 * (49 * a ^ 4)) - 3 / 8) +
      (g * a * hl0oWr S a J D1 / (c * (49 * a ^ 4)) + J * c / a - hl0oLr S a J D1 / (7 * a ^ 2) +
        hl0oWr S a J D1 / (2 * (49 * a ^ 4))) / (η - 0) +
      (g * a * hl0oQd S a ui J D1 δ c / (49 * a ^ 4) + a) / (η - -c) := by
  unfold hl0Go hl0oQd
  rw [hl0_Wo_pf hS hη, hl0_Lo_pf hS hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring

/-- **The test `τ = 2` in partial fractions**. -/
theorem hl0_pfo_2 {S a c ui J D1 δ η : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hη : η ≠ 0)
    (hB : c + η ≠ 0) :
    hl0Go S a (c + η) (ui + J / η) (D1 + δ * η) 2 (5 / (2 * (7 * (a / (c + η)))) - 11 / 9) =
      (5 / 2 * hl0Wk ui δ / (49 * a ^ 4)) * η ^ 2 +
      (5 / 2 * hl0oWl S a ui J D1 δ / (49 * a ^ 4) + (ui - 1) / a - hl0Ll ui δ / (7 * a ^ 2) +
        5 / (14 * a)) * η +
      (5 / 2 * hl0oWm S a ui J D1 δ / (49 * a ^ 4) + ((ui - 1) * c + J) / a -
        hl0oLm S a ui J D1 δ / (7 * a ^ 2) + 5 * c / (14 * a) + 6 / 7 - 2 + 1 / 2 - 11 / 9 - 3 / 8) +
      (5 / 2 * hl0oWr S a J D1 / (49 * a ^ 4) + J * c / a - hl0oLr S a J D1 / (7 * a ^ 2)) / (η - 0) +
      a / (η - -c) := by
  unfold hl0Go
  rw [hl0_Wo_pf hS hη, hl0_Lo_pf hS hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring

/-! ### The coefficients at the actual shape -/

/-- `k = δ²u_∞/(98α⁴) = q₀`. -/
noncomputable def hl0okd (x a : ℝ) : ℝ := hl0Wk (hl0ui x) (2 * (a - x)) / (2 * (49 * a ^ 4))
/-- `l` for `τ = gα/B`. -/
noncomputable def hl0old (x a g : ℝ) : ℝ :=
  g * a * hl0Wk (hl0ui x) (2 * (a - x)) / (49 * a ^ 4) + 1 / (g * a) + (hl0ui x - 1) / a -
    hl0Ll (hl0ui x) (2 * (a - x)) / (7 * a ^ 2) +
    hl0oWl (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (49 * a ^ 4))
/-- `m` for `τ = gα/B`. -/
noncomputable def hl0omd (x a g ℓ : ℝ) : ℝ :=
  g * a * (hl0oWl (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) -
      hl0Wk (hl0ui x) (2 * (a - x)) * (a + 1)) / (49 * a ^ 4) + (a + 1) / (g * a) +
    ((hl0ui x - 1) * (a + 1) + hl0J x) / a + 6 / 7 -
    hl0oLm (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (7 * a ^ 2) + ℓ +
    hl0oWm (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (49 * a ^ 4)) - 3 / 8
/-- The residue `r = J·U` at `β = 1` for `τ = gα/B`. -/
noncomputable def hl0ord (x a g : ℝ) : ℝ :=
  g * a * hl0oWr (x + 1) a (hl0J x) ((a + 1) ^ 2) / ((a + 1) * (49 * a ^ 4)) +
    hl0J x * (a + 1) / a - hl0oLr (x + 1) a (hl0J x) ((a + 1) ^ 2) / (7 * a ^ 2) +
    hl0oWr (x + 1) a (hl0J x) ((a + 1) ^ 2) / (2 * (49 * a ^ 4))
/-- The residue `s = (gα)(w₋ - 1) + α` at `β = -α`. -/
noncomputable def hl0osd (x a g : ℝ) : ℝ :=
  g * a * hl0oQd (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) (a + 1) / (49 * a ^ 4) + a
/-- `k` for `τ = 2`. -/
noncomputable def hl0ok2 (x a : ℝ) : ℝ := 5 / 2 * hl0Wk (hl0ui x) (2 * (a - x)) / (49 * a ^ 4)
/-- `l` for `τ = 2`. -/
noncomputable def hl0ol2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0oWl (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (49 * a ^ 4) +
    (hl0ui x - 1) / a - hl0Ll (hl0ui x) (2 * (a - x)) / (7 * a ^ 2) + 5 / (14 * a)
/-- `m` for `τ = 2`. -/
noncomputable def hl0om2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0oWm (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (49 * a ^ 4) +
    ((hl0ui x - 1) * (a + 1) + hl0J x) / a -
    hl0oLm (x + 1) a (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (7 * a ^ 2) +
    5 * (a + 1) / (14 * a) + 6 / 7 - 2 + 1 / 2 - 11 / 9 - 3 / 8
/-- The residue `r = J·U₂` at `β = 1` for `τ = 2`. -/
noncomputable def hl0or2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0oWr (x + 1) a (hl0J x) ((a + 1) ^ 2) / (49 * a ^ 4) + hl0J x * (a + 1) / a -
    hl0oLr (x + 1) a (hl0J x) ((a + 1) ^ 2) / (7 * a ^ 2)

/-- The outer tests with `u = û` as functions of `β`, `τ = gα/B`. -/
theorem hl0_Og_pf {x a b g ℓ : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) (hg : g ≠ 0) :
    hsF x b a (hsUhat x b) (1 / 7) (g * hsRA a b) ℓ (1 / 2) =
      hl0okd x a * (b - 1) ^ 2 + hl0old x a g * (b - 1) + hl0omd x a g ℓ +
      hl0ord x a g / ((b - 1) - 0) + hl0osd x a g / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have e : hsF x b a (hsUhat x b) (1 / 7) (g * hsRA a b) ℓ (1 / 2) =
      hl0Go (x + 1) a ((a + 1) + (b - 1)) (hl0ui x + hl0J x / (b - 1))
        ((a + 1) ^ 2 + 2 * (a - x) * (b - 1)) (g * (a / ((a + 1) + (b - 1)))) ℓ := by
    rw [hl0_out_F hx0 ha hB, hl0_uhat_pole hx hb, hl0_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1]; rfl
  rw [e, hl0_pfo_g (by linarith) ha.ne' (by linarith) hg (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold hl0okd hl0old hl0omd hl0ord hl0osd
  ring

theorem hl0_OTs_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    hl0OT x a b (hsUhat x b) = hl0okd x a * (b - 1) ^ 2 + hl0old x a 7 * (b - 1) + hl0omd x a 7 0 +
      hl0ord x a 7 / ((b - 1) - 0) + hl0osd x a 7 / ((b - 1) - -(a + 1)) :=
  hl0_Og_pf hx ha hb (by norm_num)

theorem hl0_O8s_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    hl0O8 x a b (hsUhat x b) = hl0okd x a * (b - 1) ^ 2 + hl0old x a (56 / 9) * (b - 1) +
      hl0omd x a (56 / 9) (-1 / 9) + hl0ord x a (56 / 9) / ((b - 1) - 0) +
      hl0osd x a (56 / 9) / ((b - 1) - -(a + 1)) := by
  rw [← hl0_Og_pf hx ha hb (by norm_num)]
  unfold hl0O8
  congr 1
  ring

theorem hl0_O2s_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    hl0O2 x a b (hsUhat x b) = hl0ok2 x a * (b - 1) ^ 2 + hl0ol2 x a * (b - 1) + hl0om2 x a +
      hl0or2 x a / ((b - 1) - 0) + a / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have e : hl0O2 x a b (hsUhat x b) =
      hl0Go (x + 1) a ((a + 1) + (b - 1)) (hl0ui x + hl0J x / (b - 1))
        ((a + 1) ^ 2 + 2 * (a - x) * (b - 1)) 2
        (5 / (2 * (7 * (a / ((a + 1) + (b - 1))))) - 11 / 9) := by
    unfold hl0O2 hsRA
    rw [hl0_out_F hx0 ha hB, hl0_uhat_pole hx hb, hl0_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1]
  rw [e, hl0_pfo_2 (by linarith) ha.ne' (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold hl0ok2 hl0ol2 hl0om2 hl0or2
  ring

/-! ### The residue signs on the strip -/

/-- `98α⁴(U_T + 5/2) = (14αc + c²)(c² - Q₀) + 98α³c - 14α²(2c² - Q₀) + 245α⁴`, `c = α + 1`,
`Q₀ = M₀S`. -/
noncomputable def hl0QTf (x a : ℝ) : ℝ :=
  (14 * a * (a + 1) + (a + 1) ^ 2) * ((a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1)) + 98 * a ^ 3 * (a + 1) -
    14 * a ^ 2 * (2 * (a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1)) + 245 * a ^ 4

/-- `98α⁴U₂ = 5c²(c² - Q₀) + 98α³c - 14α²(2c² - Q₀)`. -/
noncomputable def hl0Q2f (x a : ℝ) : ℝ :=
  5 * (a + 1) ^ 2 * ((a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1)) + 98 * a ^ 3 * (a + 1) -
    14 * a ^ 2 * (2 * (a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1))

/-- `84α³SM(R_T - x²/3)` at the continued value `û(-α)`: `3·4SM·Q + 84α⁴SM - 28α³SMx²`, the
continued norm `4SM·Q` cleared with `U_I = 4SMu_∞`, `J_J = 4SMJ`, `P₀' = 4SM·P₀`. -/
noncomputable def hl0SRf (x a : ℝ) : ℝ :=
  let S := x + 1
  let F4 := 4 * (x + 1) * (35 * x + 13)
  let UI := 3 * (x + 1) * (35 * x + 13) + (x - 1) ^ 2
  let JJ := 7 * (x - 1) ^ 3
  let c := a + 1
  let δ := 2 * (a - x)
  let M0 := 6 * a ^ 2 + 1
  let Q0 := M0 * S
  let P0 := 4 * (35 * x + 13) * (M0 * (1 - S ^ 2) + (2 * S - 1) * S)
  let C0 := M0 ^ 2 - M0 * S + S ^ 2
  3 * (UI * δ ^ 2 * c ^ 2 - c * (UI * δ * (2 * c ^ 2 - Q0) + JJ * δ ^ 2 - δ * P0) +
      (F4 * C0 - c ^ 2 * P0 + UI * c ^ 2 * (c ^ 2 - Q0) + JJ * δ * (2 * c ^ 2 - Q0)) -
      F4 * (49 * a ^ 4) - JJ * c * (c ^ 2 - Q0)) +
    84 * a ^ 4 * (x + 1) * (35 * x + 13) - 28 * a ^ 3 * (x + 1) * (35 * x + 13) * x ^ 2

/-- `hl0QTf` on coefficient lists. -/
noncomputable def hl0QTL (x a : List (List ℝ)) : List (List ℝ) :=
  let c := hl0Add2 a [[1]]
  let c2 := hl0Mul2 c c
  let Q0 := hl0Mul2 (hl0Add2 (hl0Smul2 6 (hl0Mul2 a a)) [[1]]) (hl0Add2 x [[1]])
  let a2 := hl0Mul2 a a
  hl0Add2 (hl0Mul2 (hl0Add2 (hl0Smul2 14 (hl0Mul2 a c)) c2) (hl0Add2 c2 (hl0Smul2 (-1) Q0)))
    (hl0Add2 (hl0Smul2 98 (hl0Mul2 (hl0Mul2 a2 a) c))
      (hl0Add2 (hl0Smul2 (-14) (hl0Mul2 a2 (hl0Add2 (hl0Smul2 2 c2) (hl0Smul2 (-1) Q0))))
        (hl0Smul2 245 (hl0Mul2 a2 a2))))

/-- `hl0Q2f` on coefficient lists. -/
noncomputable def hl0Q2L (x a : List (List ℝ)) : List (List ℝ) :=
  let c := hl0Add2 a [[1]]
  let c2 := hl0Mul2 c c
  let Q0 := hl0Mul2 (hl0Add2 (hl0Smul2 6 (hl0Mul2 a a)) [[1]]) (hl0Add2 x [[1]])
  let a2 := hl0Mul2 a a
  hl0Add2 (hl0Smul2 5 (hl0Mul2 c2 (hl0Add2 c2 (hl0Smul2 (-1) Q0))))
    (hl0Add2 (hl0Smul2 98 (hl0Mul2 (hl0Mul2 a2 a) c))
      (hl0Smul2 (-14) (hl0Mul2 a2 (hl0Add2 (hl0Smul2 2 c2) (hl0Smul2 (-1) Q0)))))

/-- `hl0SRf` on coefficient lists. -/
noncomputable def hl0SRL (x a : List (List ℝ)) : List (List ℝ) :=
  let S := hl0Add2 x [[1]]
  let M := hl0Add2 (hl0Smul2 35 x) [[13]]
  let SM := hl0Mul2 S M
  let F4 := hl0Smul2 4 SM
  let xm := hl0Add2 x [[-1]]
  let UI := hl0Add2 (hl0Smul2 3 SM) (hl0Mul2 xm xm)
  let JJ := hl0Smul2 7 (hl0Mul2 (hl0Mul2 xm xm) xm)
  let c := hl0Add2 a [[1]]
  let c2 := hl0Mul2 c c
  let δ := hl0Smul2 2 (hl0Add2 a (hl0Smul2 (-1) x))
  let δ2 := hl0Mul2 δ δ
  let a2 := hl0Mul2 a a
  let M0 := hl0Add2 (hl0Smul2 6 a2) [[1]]
  let Q0 := hl0Mul2 M0 S
  let S2 := hl0Mul2 S S
  let P0 := hl0Smul2 4 (hl0Mul2 M (hl0Add2 (hl0Mul2 M0 (hl0Add2 [[1]] (hl0Smul2 (-1) S2)))
    (hl0Mul2 (hl0Add2 (hl0Smul2 2 S) [[-1]]) S)))
  let C0 := hl0Add2 (hl0Mul2 M0 M0) (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 M0 S)) S2)
  let E2 := hl0Add2 (hl0Smul2 2 c2) (hl0Smul2 (-1) Q0)
  let E1 := hl0Add2 c2 (hl0Smul2 (-1) Q0)
  hl0Add2 (hl0Smul2 3 (hl0Add2 (hl0Mul2 (hl0Mul2 UI δ2) c2)
      (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 c (hl0Add2 (hl0Mul2 (hl0Mul2 UI δ) E2)
        (hl0Add2 (hl0Mul2 JJ δ2) (hl0Smul2 (-1) (hl0Mul2 δ P0))))))
      (hl0Add2 (hl0Add2 (hl0Mul2 F4 C0) (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 c2 P0))
          (hl0Add2 (hl0Mul2 (hl0Mul2 UI c2) E1) (hl0Mul2 (hl0Mul2 JJ δ) E2))))
        (hl0Add2 (hl0Smul2 (-49) (hl0Mul2 F4 (hl0Mul2 a2 a2)))
          (hl0Smul2 (-1) (hl0Mul2 (hl0Mul2 JJ c) E1)))))))
    (hl0Add2 (hl0Smul2 84 (hl0Mul2 (hl0Mul2 a2 a2) SM))
      (hl0Smul2 (-28) (hl0Mul2 (hl0Mul2 (hl0Mul2 a2 a) SM) (hl0Mul2 x x))))

theorem hl0_H2_QTL (x a : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0QTL x a) X A = hl0QTf (hl0H2 x X A) (hl0H2 a X A) := by
  unfold hl0QTL hl0QTf
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

theorem hl0_H2_Q2L (x a : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0Q2L x a) X A = hl0Q2f (hl0H2 x X A) (hl0H2 a X A) := by
  unfold hl0Q2L hl0Q2f
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

theorem hl0_H2_SRL (x a : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0SRL x a) X A = hl0SRf (hl0H2 x X A) (hl0H2 a X A) := by
  unfold hl0SRL hl0SRf
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

/-- The strip coordinates `X = x - 12/5`, `A = α - (22x + 20)/55`. -/
theorem hl0_H2_strip (x a : ℝ) :
    hl0H2 [[12 / 5], [1]] (x - 12 / 5) (a - (22 * x + 20) / 55) = x ∧
      hl0H2 [[364 / 275, 1], [2 / 5]] (x - 12 / 5) (a - (22 * x + 20) / 55) = a := by
  refine ⟨by simp [hl0H2, lrhHorner], by simp [hl0H2, lrhHorner]; ring⟩

/-- Positivity of a formula on the strip from its list by the bivariate cover. -/
theorem hl0_strip_pos {f : ℝ → ℝ → ℝ} {L : List (List ℝ) → List (List ℝ) → List (List ℝ)}
    (hL : ∀ x a X A, hl0H2 (L x a) X A = f (hl0H2 x X A) (hl0H2 a X A)) (r : List ℝ)
    (hc : hl0Cov2 (L [[12 / 5], [1]] [[364 / 275, 1], [2 / 5]]) (13 / 55) (33 / 5) (0 :: r))
    {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : 0 < f x a := by
  have e := hL [[12 / 5], [1]] [[364 / 275, 1], [2 / 5]] (x - 12 / 5) (a - (22 * x + 20) / 55)
  rw [(hl0_H2_strip x a).1, (hl0_H2_strip x a).2] at e
  rw [← e]
  exact hl0_cov2_pos _ _ _ 0 r hc _ _ (by linarith) (by linarith) (by linarith) (by linarith)

theorem hl0_strip_rT {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : -(5 / 2) * hl0J x ≤ hl0ord x a 7 := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  have e : hl0ord x a 7 + 5 / 2 * hl0J x = hl0J x * hl0QTf x a / (98 * a ^ 4) := by
    unfold hl0ord hl0oWr hl0oLr hl0oQ0 hl0J hl0QTf
    field_simp
    ring
  have hP := hl0_strip_pos hl0_H2_QTL [33 / 10] (by norm_num [hl0QTL, hl0Mul2, hl0Mul, hl0Smul2,
    hl0Cov2, hl0Low2, hl0Shift2, hl0Add2, hl0Add, hl0Smul, hl0Low, hl0Neg]) hx hx9 ha ham
  have hJ : 0 ≤ hl0J x := hl0_J_nonneg (by linarith)
  have : 0 ≤ hl0J x * hl0QTf x a / (98 * a ^ 4) := by positivity
  linarith

theorem hl0_strip_r2 {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : 0 ≤ hl0or2 x a := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have e : hl0or2 x a = hl0J x * hl0Q2f x a / (98 * a ^ 4) := by
    unfold hl0or2 hl0oWr hl0oLr hl0oQ0 hl0J hl0Q2f
    field_simp
    ring
  have hP := hl0_strip_pos hl0_H2_Q2L [] (by norm_num [hl0Q2L, hl0Mul2, hl0Mul, hl0Smul2,
    hl0Cov2, hl0Low2, hl0Shift2, hl0Add2, hl0Add, hl0Smul, hl0Low, hl0Neg]) hx hx9 ha ham
  have hJ : 0 ≤ hl0J x := hl0_J_nonneg (by linarith)
  rw [e]; positivity

theorem hl0_strip_sT {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : x ^ 2 / 3 ≤ hl0osd x a 7 := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  have e : hl0osd x a 7 - x ^ 2 / 3 = hl0SRf x a / (84 * a ^ 3 * (x + 1) * (35 * x + 13)) := by
    unfold hl0osd hl0oQd hl0Wk hl0oWl hl0oWm hl0oWr hl0oQ0 hl0oP0 hl0oC0 hl0ui hl0J hl0SRf
    field_simp
    ring
  have hP := hl0_strip_pos hl0_H2_SRL [] (by norm_num [hl0SRL, hl0Mul2, hl0Mul, hl0Smul2,
    hl0Cov2, hl0Low2, hl0Shift2, hl0Add2, hl0Add, hl0Smul, hl0Low, hl0Neg]) hx hx9 ha ham
  have : 0 ≤ hl0SRf x a / (84 * a ^ 3 * (x + 1) * (35 * x + 13)) := by positivity
  linarith

theorem hl0_strip_r8 {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a) : hl0ord x a 7 ≤ hl0ord x a (56 / 9) := by
  have ha0 : 0 < a := by linarith
  have hJ : 0 ≤ hl0J x := hl0_J_nonneg (by linarith)
  have hD : (a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1) ≤ 0 := by nlinarith
  have e : hl0ord x a (56 / 9) - hl0ord x a 7 =
      7 / 9 * a * hl0J x * (a + 1) ^ 2 * ((6 * a ^ 2 + 1) * (x + 1) - (a + 1) ^ 2) /
        ((a + 1) * (49 * a ^ 4)) := by
    unfold hl0ord hl0oWr hl0oQ0
    field_simp
    ring
  have : 0 ≤ 7 / 9 * a * hl0J x * (a + 1) ^ 2 * ((6 * a ^ 2 + 1) * (x + 1) - (a + 1) ^ 2) /
      ((a + 1) * (49 * a ^ 4)) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity) (by linarith)
  linarith

theorem hl0_osd8 (x a : ℝ) (ha : a ≠ 0) : hl0osd x a (56 / 9) = 8 / 9 * hl0osd x a 7 + a / 9 := by
  unfold hl0osd; field_simp; ring

/-! ### The chord bounds on the strip -/

/-- The convexity margin: `k + min(r, 0)/(β₀ - 1)³ + s/B₁³ ≥ 0` once `r ≥ -(5/2)J`,
`s ≥ σ ≥ 0`, `β₀ - 1 ≥ x - 1`, `B₁ ≤ 2x` and `σ/(2x)³ ≥ (5/2)J/(x - 1)³`. -/
theorem hl0_strip_hk {k r s J σ x b₀ B₁ : ℝ} (hk : 0 ≤ k) (hJ : 0 ≤ J) (hx1 : 0 < x - 1)
    (hb₀ : x - 1 ≤ b₀) (hB₁ : 0 < B₁) (hB₁x : B₁ ≤ 2 * x) (hr : -(5 / 2) * J ≤ r) (hs : σ ≤ s)
    (hσ : 0 ≤ σ) (key : 0 ≤ -(5 / 2) * J / (x - 1) ^ 3 + σ / (2 * x) ^ 3) :
    0 ≤ k + min r 0 / b₀ ^ 3 + s / B₁ ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b₀ := by linarith
  have h1 : -(5 / 2) * J / (x - 1) ^ 3 ≤ min r 0 / b₀ ^ 3 := by
    have hm : -(5 / 2) * J ≤ min r 0 := le_min hr (by linarith)
    have hm0 : min r 0 ≤ 0 := min_le_right _ _
    have hp : (x - 1) ^ 3 ≤ b₀ ^ 3 := pow_le_pow_left₀ hx1.le hb₀ 3
    have s1 : min r 0 / (x - 1) ^ 3 ≤ min r 0 / b₀ ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have s2 : -(5 / 2) * J / (x - 1) ^ 3 ≤ min r 0 / (x - 1) ^ 3 :=
      div_le_div_of_nonneg_right hm (by positivity)
    linarith
  have h2 : σ / (2 * x) ^ 3 ≤ s / B₁ ^ 3 := by
    have hp : B₁ ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hB₁.le hB₁x 3
    have s1 : σ / (2 * x) ^ 3 ≤ σ / B₁ ^ 3 := div_le_div_of_nonneg_left hσ (by positivity) hp
    have s2 : σ / B₁ ^ 3 ≤ s / B₁ ^ 3 := div_le_div_of_nonneg_right hs (by positivity)
    linarith
  linarith

theorem hl0_J_ratio {x : ℝ} (hx : 1 < x) :
    hl0J x / (x - 1) ^ 3 = 7 / (4 * (x + 1) * (35 * x + 13)) := by
  have : x - 1 ≠ 0 := by linarith
  have : (x + 1) * (35 * x + 13) ≠ 0 := by nlinarith
  unfold hl0J; field_simp

/-- **Beta convexity on the strip, `τ = T`**: the test is at most the larger of its values at
`β = x + (3/5)(α - 1)` and at `β₁` (`hl0_chord2`). -/
theorem hl0_strip_chord_T {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hbb : b ≤ b₁) (hb₁ : b₁ + a ≤ 2 * x) :
    hl0OT x a b (hsUhat x b) ≤ max (hl0OT x a (x + 3 / 5 * (a - 1)) (hsUhat x (x + 3 / 5 * (a - 1))))
      (hl0OT x a b₁ (hsUhat x b₁)) := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 1 < x + 3 / 5 * (a - 1) := by linarith
  rw [hl0_OTs_pf hx1 ha0 (by linarith), hl0_OTs_pf hx1 ha0 hb0, hl0_OTs_pf hx1 ha0 (by linarith)]
  have hsT := hl0_strip_sT hx hx9 ha ham
  apply hl0_chord2 (by linarith) (by linarith) (by linarith) (by linarith)
    (by nlinarith)
  have e : b₁ - 1 - -(a + 1) = b₁ + a := by ring
  rw [e]
  have hJ : 0 ≤ hl0J x := hl0_J_nonneg (by linarith)
  apply hl0_strip_hk (J := hl0J x) (σ := x ^ 2 / 3) (by unfold hl0okd hl0Wk hl0ui; positivity) hJ
    (by linarith) (by linarith) (by linarith) hb₁ (hl0_strip_rT hx hx9 ha ham) hsT (by positivity)
  have e2 : -(5 / 2) * hl0J x / (x - 1) ^ 3 = -(5 / 2) * (hl0J x / (x - 1) ^ 3) := by ring
  rw [e2, hl0_J_ratio hx1]
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  rw [show x ^ 2 / 3 / (2 * x) ^ 3 = 1 / (24 * x) by field_simp; ring]
  have : 35 / (8 * ((x + 1) * (35 * x + 13))) ≤ 1 / (24 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e3 : -(5 / 2) * (7 / (4 * (x + 1) * (35 * x + 13))) = -(35 / (8 * ((x + 1) * (35 * x + 13)))) := by
    field_simp; ring
  linarith

/-- **Beta convexity on the strip, `τ = 8T/9`**: the test is at most the larger of its values at
`β = x + (3/5)(α - 1)` and at `β₁` (`hl0_chord2`). -/
theorem hl0_strip_chord_8 {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hbb : b ≤ b₁) (hb₁ : b₁ + a ≤ 2 * x) :
    hl0O8 x a b (hsUhat x b) ≤ max (hl0O8 x a (x + 3 / 5 * (a - 1)) (hsUhat x (x + 3 / 5 * (a - 1))))
      (hl0O8 x a b₁ (hsUhat x b₁)) := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 1 < x + 3 / 5 * (a - 1) := by linarith
  rw [hl0_O8s_pf hx1 ha0 (by linarith), hl0_O8s_pf hx1 ha0 hb0, hl0_O8s_pf hx1 ha0 (by linarith)]
  have hsT := hl0_strip_sT hx hx9 ha ham
  have hs8 : 8 * x ^ 2 / 27 ≤ hl0osd x a (56 / 9) := by rw [hl0_osd8 x a ha0.ne']; linarith
  apply hl0_chord2 (by linarith) (by linarith) (by linarith) (by linarith) (by nlinarith)
  have e : b₁ - 1 - -(a + 1) = b₁ + a := by ring
  rw [e]
  have hJ : 0 ≤ hl0J x := hl0_J_nonneg (by linarith)
  apply hl0_strip_hk (J := hl0J x) (σ := 8 * x ^ 2 / 27) (by unfold hl0okd hl0Wk hl0ui; positivity)
    hJ (by linarith) (by linarith) (by linarith) hb₁
    ((hl0_strip_rT hx hx9 ha ham).trans (hl0_strip_r8 hx ha1)) hs8 (by positivity)
  have e2 : -(5 / 2) * hl0J x / (x - 1) ^ 3 = -(5 / 2) * (hl0J x / (x - 1) ^ 3) := by ring
  rw [e2, hl0_J_ratio hx1]
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  rw [show 8 * x ^ 2 / 27 / (2 * x) ^ 3 = 1 / (27 * x) by field_simp; ring]
  have : 35 / (8 * ((x + 1) * (35 * x + 13))) ≤ 1 / (27 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e3 : -(5 / 2) * (7 / (4 * (x + 1) * (35 * x + 13))) = -(35 / (8 * ((x + 1) * (35 * x + 13)))) := by
    field_simp; ring
  linarith

/-- **Beta convexity on the strip, `τ = 2`**: the test is at most the larger of its values at
`β = x + (3/5)(α - 1)` and at `β₁` (`hl0_chord2`). -/
theorem hl0_strip_chord_2 {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hbb : b ≤ b₁) :
    hl0O2 x a b (hsUhat x b) ≤ max (hl0O2 x a (x + 3 / 5 * (a - 1)) (hsUhat x (x + 3 / 5 * (a - 1))))
      (hl0O2 x a b₁ (hsUhat x b₁)) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 1 < x + 3 / 5 * (a - 1) := by linarith
  rw [hl0_O2s_pf hx1 ha0 (by linarith), hl0_O2s_pf hx1 ha0 hb0, hl0_O2s_pf hx1 ha0 (by linarith)]
  apply hl0_chord2 (by linarith) (by linarith) (by linarith) (by linarith) ha0.le
  have hr := hl0_strip_r2 hx hx9 ha ham
  rw [min_eq_right hr, zero_div, add_zero]
  have hk : 0 ≤ hl0ok2 x a := by unfold hl0ok2 hl0Wk hl0ui; positivity
  have : 0 < b₁ - 1 - -(a + 1) := by linarith
  positivity

/-! ### Strip faces -/

theorem hl0_horner_zero (l : List ℝ) : lrhHorner l 0 = hl0Low 0 l := by
  cases l with
  | nil => simp [lrhHorner, hl0Low]
  | cons c p => simp [lrhHorner, hl0Low]

/-- **A strip face**: a positive `A`-derivative on the rectangle `0 ≤ X ≤ W`,
`0 ≤ A ≤ 13/55` (`A = α - α_f(x)`) and a positive value on the lower edge `A = 0` (`α = α_f(x)`)
give positivity. -/
theorem hl0_strip_face (P : List (List ℝ)) {W : ℝ} (hd : 0 < hl0Low2 (13 / 55) W (P.map hl0D))
    (hv : ∀ X, 0 ≤ X → X ≤ W → 0 < lrhHorner (P.map (hl0Low 0)) X) {X A : ℝ} (hX : 0 ≤ X)
    (hXW : X ≤ W) (hA : 0 ≤ A) (hA' : A ≤ 13 / 55) : 0 < hl0H2 P X A := by
  have h0 : hl0H2 P X 0 = lrhHorner (P.map (hl0Low 0)) X := by
    unfold hl0H2; congr 1; exact List.map_congr_left (fun l _ => hl0_horner_zero l)
  have hm := hl0_mono_A (P := P) (X := X) (A₁ := 0) (A₂ := A)
    (fun A'' h1 h2 => (hd.le.trans (hl0_low2_le h1 (h2.trans hA') hX hXW _))) hA
  have := hv X hX hXW
  linarith

/-- **An outer face numerator on lists** (`u = û`), from lists for `x`, `α`, `β`. -/
noncomputable def hl0FNo (e₁ e₂ e₃ e₄ c₁ c₂ c₃ : ℝ) (x a b : List (List ℝ)) : List (List ℝ) :=
  hl0NoL e₁ e₂ e₃ e₄ c₁ c₂ c₃ (hl0cS x) a (hl0Add2 a b) (hl0cU x b) (hl0cV x b) (hl0cD x a b)

theorem hl0_H2_FNoT (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0FNo 56 4 56 392 336 (-189) 2352 x a b) X A =
      hl0NoT (hl0H2 x X A + 1) (hl0H2 a X A) (hl0H2 a X A + hl0H2 b X A)
        (hl0Uc (hl0H2 x X A) (hl0H2 b X A)) (hl0Vc (hl0H2 x X A) (hl0H2 b X A))
        (hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A)) := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hl0_H2_atoms x a b X A
  unfold hl0FNo; rw [hl0_H2_NoTL, h1, h3, h4, h5, h6]

theorem hl0_H2_FNo8 (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0FNo 1008 72 896 7056 5922 (-2618) 36848 x a b) X A =
      hl0No8 (hl0H2 x X A + 1) (hl0H2 a X A) (hl0H2 a X A + hl0H2 b X A)
        (hl0Uc (hl0H2 x X A) (hl0H2 b X A)) (hl0Vc (hl0H2 x X A) (hl0H2 b X A))
        (hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A)) := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hl0_H2_atoms x a b X A
  unfold hl0FNo; rw [hl0_H2_No8L, h1, h3, h4, h5, h6]

theorem hl0_H2_FNo2 (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0FNo 504 180 0 3528 2268 7903 (-3528) x a b) X A =
      hl0No2 (hl0H2 x X A + 1) (hl0H2 a X A) (hl0H2 a X A + hl0H2 b X A)
        (hl0Uc (hl0H2 x X A) (hl0H2 b X A)) (hl0Vc (hl0H2 x X A) (hl0H2 b X A))
        (hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A)) := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hl0_H2_atoms x a b X A
  unfold hl0FNo; rw [hl0_H2_No2L, h1, h3, h4, h5, h6]

end SmoothedOctagon

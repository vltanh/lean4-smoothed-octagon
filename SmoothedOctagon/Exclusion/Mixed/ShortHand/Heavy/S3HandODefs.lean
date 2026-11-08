module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S3Leaves

/-!
# Gate S3, the outer face by hand: the reciprocal-shape decomposition

Proof of the leaf `hs3_outer_face`, first part. At `q = 1/7`, with the beta slope
`β = x + C(α - 1)`, `r = 1/α` and a constant duration weight `n`, the rational outer test
`R_n = J + n(w - 3/4)` (the logarithm replaced by its rational majorant) is
`R_n = P_n(r) + (u - 3/4)A_n(r) + 1/Z - 56/K` (`hl3o_decomp`), where
`49A_i = nα_i + β_i`, `49SB_i = nγ_i + δ_i`, `P_i = 3A_i/4 + B_i` with the coefficient polynomials
`hl3oα0`, …, `hl3oδ2` printed below, `Z = 1 + C + (x - C)r`, `K = 5Z + 14`. The
incoming ceiling is `ū = 3/4 + V(r)`, `V = c + c(x - 1)r/(C + (x - C - 1)r)`,
`c = (x - 1)²/(S(35x + 13))` (`hl3o_UO`).

The identity is checked as one polynomial identity in `x, C, n, u, r` with 115 monomials (after
the substitution `D/α² = d₀ + d₁r + d₂r²`).

## Main API

* `hl3oα0`-`hl3oα4`, `hl3oβ0`-`hl3oβ2`, `hl3oγ0`-`hl3oγ4`, `hl3oδ0`-`hl3oδ2`: the printed
  coefficient polynomials; `hl3oA`, `hl3oP`: the quartics `A_n(r)`, `P_n(r)`.
* `hl3oV`, `hl3oPhi`, `hl3oG = P + V·A + Φ`.
* `hl3o_decomp`, `hl3o_UO`, `hl3o_G_eq`: the test in this form.
* Calculus: `hl3_hd_quartic`, `hl3_hd_cubic`, `hl3_neg_of_convex`, the tactic `hl3_deriv`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The printed coefficient polynomials -/

noncomputable def hl3oα0 (x C : ℝ) : ℝ := x * (-12 * C - 6) + (4 * C ^ 2 - 8 * C - 5)
noncomputable def hl3oα1 (x C : ℝ) : ℝ :=
  x ^ 2 * (12 * C - 12) + x * (-8 * C ^ 2 + 28 * C - 8) + (-8 * C ^ 2 + 8 * C)
noncomputable def hl3oα2 (x C : ℝ) : ℝ :=
  x ^ 3 * 12 + x ^ 2 * (4 * C ^ 2 - 28 * C) + x * (16 * C ^ 2 - 10 * C - 15) + (4 * C ^ 2 + 2 * C - 5)
noncomputable def hl3oα3 (x C : ℝ) : ℝ :=
  x ^ 3 * (8 * C - 8) + x ^ 2 * (-8 * C ^ 2 + 10 * C + 6) + x * (-8 * C ^ 2 - 8 * C + 2) + (-2 * C)
noncomputable def hl3oα4 (x C : ℝ) : ℝ :=
  x ^ 4 * 4 + x ^ 3 * (-8 * C - 6) + x ^ 2 * (4 * C ^ 2 + 6 * C) + x * (2 * C + 1)
noncomputable def hl3oβ0 (x C : ℝ) : ℝ := x * 42 + (21 * C + 77)
noncomputable def hl3oβ1 (x C : ℝ) : ℝ := x * (28 * C + 21) + (-21 * C)
noncomputable def hl3oβ2 (x C : ℝ) : ℝ := x ^ 2 * 28 + x * (-28 * C - 21) + (-7)
noncomputable def hl3oγ0 (x C : ℝ) : ℝ := x ^ 2 * (12 * C + 6) + x * (24 * C + 45 / 4) + (-3 / 4)
noncomputable def hl3oγ1 (x C : ℝ) : ℝ :=
  x ^ 3 * (-12 * C + 12) + x ^ 2 * (-36 * C + 24) + x * (-24 * C)
noncomputable def hl3oγ2 (x C : ℝ) : ℝ :=
  x ^ 4 * (-12) + x ^ 3 * (12 * C - 12) + x ^ 2 * (22 * C + 23) + x * (-2 * C + 11) + (-2 * C + 5)
noncomputable def hl3oγ3 (x C : ℝ) : ℝ :=
  x ^ 3 * (2 * C - 2) + x ^ 2 * (4 * C - 2) + x * (4 * C - 2) + 2 * C
noncomputable def hl3oγ4 (x C : ℝ) : ℝ :=
  x ^ 4 * 2 + x ^ 3 * (-2 * C + 1) + x ^ 2 * (-2 * C + 1) + x * (-2 * C - 1)
noncomputable def hl3oδ0 (x C : ℝ) : ℝ :=
  x ^ 2 * (-42) + x * (-49 * C - 707497 / 180000) + (-49 * C + 14412503 / 180000)
noncomputable def hl3oδ1 (x C : ℝ) : ℝ := x ^ 2 * (-49) + x * (49 * C - 49) + 49 * C
noncomputable def hl3oδ2 (x : ℝ) : ℝ := x ^ 2 * 7 + x * 7 + 7

/-- `A_i = (nα_i + β_i)/49`. -/
noncomputable def hl3oAc0 (x C n : ℝ) : ℝ := (n * hl3oα0 x C + hl3oβ0 x C) / 49
noncomputable def hl3oAc1 (x C n : ℝ) : ℝ := (n * hl3oα1 x C + hl3oβ1 x C) / 49
noncomputable def hl3oAc2 (x C n : ℝ) : ℝ := (n * hl3oα2 x C + hl3oβ2 x C) / 49
noncomputable def hl3oAc3 (x C n : ℝ) : ℝ := n * hl3oα3 x C / 49
noncomputable def hl3oAc4 (x C n : ℝ) : ℝ := n * hl3oα4 x C / 49

/-- `P_i = 3A_i/4 + B_i`, `B_i = (nγ_i + δ_i)/(49S)`. -/
noncomputable def hl3oPc0 (x C n : ℝ) : ℝ :=
  3 / 4 * hl3oAc0 x C n + (n * hl3oγ0 x C + hl3oδ0 x C) / (49 * (x + 1))
noncomputable def hl3oPc1 (x C n : ℝ) : ℝ :=
  3 / 4 * hl3oAc1 x C n + (n * hl3oγ1 x C + hl3oδ1 x C) / (49 * (x + 1))
noncomputable def hl3oPc2 (x C n : ℝ) : ℝ :=
  3 / 4 * hl3oAc2 x C n + (n * hl3oγ2 x C + hl3oδ2 x) / (49 * (x + 1))
noncomputable def hl3oPc3 (x C n : ℝ) : ℝ := 3 / 4 * hl3oAc3 x C n + n * hl3oγ3 x C / (49 * (x + 1))
noncomputable def hl3oPc4 (x C n : ℝ) : ℝ := 3 / 4 * hl3oAc4 x C n + n * hl3oγ4 x C / (49 * (x + 1))

/-- `A_n(r) = Σ A_i rⁱ`: the coefficient of the incoming norm. -/
noncomputable def hl3oA (x C n r : ℝ) : ℝ :=
  hl3oAc0 x C n + hl3oAc1 x C n * r + hl3oAc2 x C n * r ^ 2 + hl3oAc3 x C n * r ^ 3 +
    hl3oAc4 x C n * r ^ 4
/-- `A_n'(r)`. -/
noncomputable def hl3oA1 (x C n r : ℝ) : ℝ :=
  hl3oAc1 x C n + 2 * hl3oAc2 x C n * r + 3 * hl3oAc3 x C n * r ^ 2 + 4 * hl3oAc4 x C n * r ^ 3
/-- `A_n''(r)`. -/
noncomputable def hl3oA2 (x C n r : ℝ) : ℝ :=
  2 * hl3oAc2 x C n + 6 * hl3oAc3 x C n * r + 12 * hl3oAc4 x C n * r ^ 2

/-- `P_n(r) = Σ P_i rⁱ`: the polynomial part at `u = 3/4`. -/
noncomputable def hl3oP (x C n r : ℝ) : ℝ :=
  hl3oPc0 x C n + hl3oPc1 x C n * r + hl3oPc2 x C n * r ^ 2 + hl3oPc3 x C n * r ^ 3 +
    hl3oPc4 x C n * r ^ 4
/-- `P_n'(r)`. -/
noncomputable def hl3oP1 (x C n r : ℝ) : ℝ :=
  hl3oPc1 x C n + 2 * hl3oPc2 x C n * r + 3 * hl3oPc3 x C n * r ^ 2 + 4 * hl3oPc4 x C n * r ^ 3
/-- `P_n''(r)`. -/
noncomputable def hl3oP2 (x C n r : ℝ) : ℝ :=
  2 * hl3oPc2 x C n + 6 * hl3oPc3 x C n * r + 12 * hl3oPc4 x C n * r ^ 2

/-- `c = (x - 1)²/(S(35x + 13))`. -/
noncomputable def hl3oc (x : ℝ) : ℝ := (x - 1) ^ 2 / ((x + 1) * (35 * x + 13))

/-- `V = ū - 3/4 = c + c(x - 1)r/H`, `H = C + (x - C - 1)r`. -/
noncomputable def hl3oV (x C r : ℝ) : ℝ := hl3oc x + hl3oc x * (x - 1) * r / (C + (x - C - 1) * r)

/-- `Φ = 1/Z - 56/(5Z + 14)`, `Z = 1 + C + (x - C)r`. -/
noncomputable def hl3oPhi (x C r : ℝ) : ℝ :=
  1 / (1 + C + (x - C) * r) - 56 / (5 * (1 + C + (x - C) * r) + 14)

/-- **The outer test in reciprocal shape** `R_n = P_n + V·A_n + Φ` at `u = ū`. -/
noncomputable def hl3oG (x C n r : ℝ) : ℝ := hl3oP x C n r + hl3oV x C r * hl3oA x C n r + hl3oPhi x C r

/-- `f(z) = -1/z² + 280/(5z + 14)²`, so that `Φ' = (x - C)f(Z)`. -/
noncomputable def hl3of (z : ℝ) : ℝ := -1 / z ^ 2 + 280 / (5 * z + 14) ^ 2
/-- `f'(z) = 2/z³ - 2800/(5z + 14)³`. -/
noncomputable def hl3of1 (z : ℝ) : ℝ := 2 / z ^ 3 - 2800 / (5 * z + 14) ^ 3
/-- `V' = c(x - 1)C/H²`. -/
noncomputable def hl3oV1 (x C r : ℝ) : ℝ := hl3oc x * (x - 1) * C / (C + (x - C - 1) * r) ^ 2
/-- `V'' = -2c(x - 1)C(x - C - 1)/H³`. -/
noncomputable def hl3oV2 (x C r : ℝ) : ℝ :=
  -2 * hl3oc x * (x - 1) * C * (x - C - 1) / (C + (x - C - 1) * r) ^ 3
/-- `G' = P' + V'A + VA' + (x - C)f(Z)`. -/
noncomputable def hl3oG1 (x C n r : ℝ) : ℝ :=
  hl3oP1 x C n r + hl3oV1 x C r * hl3oA x C n r + hl3oV x C r * hl3oA1 x C n r +
    (x - C) * hl3of (1 + C + (x - C) * r)
/-- `G'' = P'' + V''A + 2V'A' + VA'' + (x - C)²f'(Z)`. -/
noncomputable def hl3oG2 (x C n r : ℝ) : ℝ :=
  hl3oP2 x C n r + hl3oV2 x C r * hl3oA x C n r + 2 * hl3oV1 x C r * hl3oA1 x C n r +
    hl3oV x C r * hl3oA2 x C n r + (x - C) ^ 2 * hl3of1 (1 + C + (x - C) * r)

/-! ### The decomposition -/

/-- **The reciprocal-shape decomposition** `R_n = P_n(r) + (u - 3/4)A_n(r) + 1/Z - 56/K`, one
polynomial identity in `x, C, n, u, r`. -/
theorem hl3o_decomp {x C a u n : ℝ} (hx : 0 < x) (ha : 0 < a) (hC : 0 ≤ C) (hCx : C ≤ x) :
    hs3Fn x (x + C * (a - 1)) a u (1 / 7) n
        (319847 / 180000 - 56 * a / (19 * a + 5 * (x + C * (a - 1)))) =
      hl3oP x C n (1 / a) + (u - 3 / 4) * hl3oA x C n (1 / a) + hl3oPhi x C (1 / a) := by
  obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ a = 1 / r := ⟨1 / a, by positivity, by field_simp⟩
  rw [one_div_one_div]
  have hr : r ≠ 0 := hr0.ne'
  have hZ : 0 < 1 + C + (x - C) * r := by nlinarith
  have hZ' : 1 + C + (x - C) * r ≠ 0 := hZ.ne'
  have hab : 1 / r + (x + C * (1 / r - 1)) = (1 + C + (x - C) * r) / r := by field_simp; ring
  have hRA : hsRA (1 / r) (x + C * (1 / r - 1)) = 1 / (1 + C + (x - C) * r) := by
    unfold hsRA; rw [hab]; field_simp
  have h19 : 19 * (1 / r) + 5 * (x + C * (1 / r - 1)) = (5 * (1 + C + (x - C) * r) + 14) / r := by
    field_simp; ring
  have hlog : 56 * (1 / r) / (19 * (1 / r) + 5 * (x + C * (1 / r - 1))) =
      56 / (5 * (1 + C + (x - C) * r) + 14) := by
    rw [h19]
    have : 5 * (1 + C + (x - C) * r) + 14 ≠ 0 := by positivity
    field_simp
  have hD : hsDg x (x + C * (1 / r - 1)) (1 / r) =
      ((1 + 2 * C) + 2 * (x - C * (x + 1)) * r + (1 + 2 * x - 2 * x ^ 2 + 2 * C * x) * r ^ 2) / r ^ 2 := by
    unfold hsDg; field_simp; ring
  have hRA' : (u - 1) / hsRA (1 / r) (x + C * (1 / r - 1)) = (u - 1) * (1 + C + (x - C) * r) := by
    rw [hRA]; field_simp
  unfold hs3Fn hsELs hsWs hsA1 hsA2 hsA3
  rw [hRA', hRA, hlog, hD]
  unfold hsE0 hl3oP hl3oA hl3oPhi hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2
    hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0
    hl3oγ1 hl3oγ2 hl3oγ3 hl3oγ4 hl3oδ0 hl3oδ1 hl3oδ2
  have hS : x + 1 ≠ 0 := by linarith
  have hS' : 1 + x ≠ 0 := by linarith
  generalize 1 / (1 + C + (x - C) * r) = w1
  generalize 56 / (5 * (1 + C + (x - C) * r) + 14) = w2
  field_simp
  ring

/-- The outer ceiling `ū = 3/4 + V(1/α)`. -/
theorem hl3o_UO {x C a : ℝ} (hx : 1 < x) (ha : 1 < a) (hC : 0 < C) :
    hsUO x (x + C * (a - 1)) = 3 / 4 + hl3oV x C (1 / a) := by
  unfold hsUO hl3oV hl3oc
  have hb : 0 < x + C * (a - 1) - 1 := by nlinarith
  have hH : C + (x - C - 1) * (1 / a) = (x + C * (a - 1) - 1) / a := by field_simp; ring
  rw [hH]
  have ha0 : a ≠ 0 := by linarith
  have hS : x + 1 ≠ 0 := by linarith
  have h35 : 35 * x + 13 ≠ 0 := by linarith
  generalize hB : x + C * (a - 1) - 1 = B at hb hH
  have hB' : x + C * (a - 1) = B + 1 := by linarith
  rw [hB']
  have hB0 : B ≠ 0 := hb.ne'
  field_simp
  ring

/-- **The outer test at `ū`** is `hl3oG` at `r = 1/α`. -/
theorem hl3o_G_eq {x C a n : ℝ} (hx : 1 < x) (ha : 1 < a) (hC : 0 < C) (hCx : C ≤ x) :
    hs3Fn x (x + C * (a - 1)) a (hsUO x (x + C * (a - 1))) (1 / 7) n
        (319847 / 180000 - 56 * a / (19 * a + 5 * (x + C * (a - 1)))) = hl3oG x C n (1 / a) := by
  rw [hl3o_decomp (by linarith) (by linarith) hC.le hCx, hl3o_UO hx ha hC]
  unfold hl3oG
  ring

/-! ### Calculus helpers -/

theorem hl3_hd_quartic (c0 c1 c2 c3 c4 t : ℝ) :
    HasDerivAt (fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 + c4 * s ^ 4)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3) t := by
  have := (((((hasDerivAt_id t).const_mul c1).const_add c0).add ((hasDerivAt_pow 2 t).const_mul c2)).add
    ((hasDerivAt_pow 3 t).const_mul c3)).add ((hasDerivAt_pow 4 t).const_mul c4)
  refine this.congr_deriv ?_
  push_cast
  ring

theorem hl3_hd_cubic (c1 c2 c3 c4 t : ℝ) :
    HasDerivAt (fun s => c1 + 2 * c2 * s + 3 * c3 * s ^ 2 + 4 * c4 * s ^ 3)
      (2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2) t := by
  have := ((((hasDerivAt_id t).const_mul (2 * c2)).const_add c1).add
    ((hasDerivAt_pow 2 t).const_mul (3 * c3))).add ((hasDerivAt_pow 3 t).const_mul (4 * c4))
  refine this.congr_deriv ?_
  push_cast
  ring

/-- **Convexity keeps the sign of the endpoints**: if `g'' ≥ 0` on `[r₁, r₂]` and `g < 0` at both
ends, then `g < 0` on `[r₁, r₂]`. -/
theorem hl3_neg_of_convex {g g' g'' : ℝ → ℝ} {r₁ r₂ s : ℝ}
    (hg : ∀ t ∈ Icc r₁ r₂, HasDerivAt g (g' t) t) (hg' : ∀ t ∈ Icc r₁ r₂, HasDerivAt g' (g'' t) t)
    (hpos : ∀ t ∈ Icc r₁ r₂, 0 ≤ g'' t) (h1 : g r₁ < 0) (h2 : g r₂ < 0) (hs : s ∈ Icc r₁ r₂) :
    g s < 0 := by
  rcases le_or_gt 0 (g' s) with h0 | h0
  · -- `g' ≥ g'(s) ≥ 0` on `[s, r₂]`
    have hmono : ∀ t ∈ Icc s r₂, g' s ≤ g' t := fun t ht =>
      ss_le_of_deriv ht.1 (fun z hz => hg' z ⟨hs.1.trans hz.1, hz.2.trans ht.2⟩)
        (fun z hz => hpos z ⟨hs.1.trans hz.1.le, hz.2.le.trans ht.2⟩)
    have := ss_le_of_deriv hs.2 (fun z hz => hg z ⟨hs.1.trans hz.1, hz.2⟩)
      (fun z hz => le_trans h0 (hmono z ⟨hz.1.le, hz.2.le⟩))
    linarith
  · -- `g' ≤ g'(s) < 0` on `[r₁, s]`
    have hmono : ∀ t ∈ Icc r₁ s, g' t ≤ g' s := fun t ht =>
      ss_le_of_deriv ht.2 (fun z hz => hg' z ⟨ht.1.trans hz.1, hz.2.trans hs.2⟩)
        (fun z hz => hpos z ⟨ht.1.trans hz.1.le, hz.2.le.trans hs.2⟩)
    have := ss_le_of_deriv (f := fun t => -g t) (f' := fun t => -g' t) hs.1
      (fun z hz => (hg z ⟨hz.1, hz.2.trans hs.2⟩).neg)
      (fun z hz => by linarith [hmono z ⟨hz.1.le, hz.2.le⟩])
    linarith

/-! ### The two `r`-derivatives of `G` -/

section Deriv

variable {x C n t : ℝ}

theorem hl3o_hd_A : HasDerivAt (fun s => hl3oA x C n s) (hl3oA1 x C n t) t := by
  unfold hl3oA hl3oA1; exact hl3_hd_quartic _ _ _ _ _ t

theorem hl3o_hd_A1 : HasDerivAt (fun s => hl3oA1 x C n s) (hl3oA2 x C n t) t := by
  unfold hl3oA1 hl3oA2; exact hl3_hd_cubic _ _ _ _ t

theorem hl3o_hd_P : HasDerivAt (fun s => hl3oP x C n s) (hl3oP1 x C n t) t := by
  unfold hl3oP hl3oP1; exact hl3_hd_quartic _ _ _ _ _ t

theorem hl3o_hd_P1 : HasDerivAt (fun s => hl3oP1 x C n s) (hl3oP2 x C n t) t := by
  unfold hl3oP1 hl3oP2; exact hl3_hd_cubic _ _ _ _ t

theorem hl3o_hd_V (hH : C + (x - C - 1) * t ≠ 0) :
    HasDerivAt (fun s => hl3oV x C s) (hl3oV1 x C t) t := by
  have := (((hasDerivAt_id t).const_mul (hl3oc x * (x - 1))).fun_div
    (((hasDerivAt_id t).const_mul (x - C - 1)).const_add C) hH).const_add (hl3oc x)
  unfold hl3oV hl3oV1
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem hl3o_hd_V1 (hH : C + (x - C - 1) * t ≠ 0) :
    HasDerivAt (fun s => hl3oV1 x C s) (hl3oV2 x C t) t := by
  have := (hasDerivAt_const t (hl3oc x * (x - 1) * C)).fun_div
    ((((hasDerivAt_id t).const_mul (x - C - 1)).const_add C).fun_pow 2) (pow_ne_zero 2 hH)
  unfold hl3oV1 hl3oV2
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem hl3o_hd_Phi (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => hl3oPhi x C s) ((x - C) * hl3of (1 + C + (x - C) * t)) t := by
  have hZd : HasDerivAt (fun s => 1 + C + (x - C) * s) (x - C) t := by
    simpa using ((hasDerivAt_id t).const_mul (x - C)).const_add (1 + C)
  have hK : (5 * (1 + C + (x - C) * t) + 14) ≠ 0 := by positivity
  have := ((hasDerivAt_const t (1 : ℝ)).fun_div hZd hZ.ne').sub
    ((hasDerivAt_const t (56 : ℝ)).fun_div ((hZd.const_mul 5).add_const 14) hK)
  unfold hl3oPhi hl3of
  refine this.congr_deriv ?_
  field_simp
  ring

theorem hl3o_hd_Phi1 (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => (x - C) * hl3of (1 + C + (x - C) * s))
      ((x - C) ^ 2 * hl3of1 (1 + C + (x - C) * t)) t := by
  have hZd : HasDerivAt (fun s => 1 + C + (x - C) * s) (x - C) t := by
    simpa using ((hasDerivAt_id t).const_mul (x - C)).const_add (1 + C)
  have hK : (5 * (1 + C + (x - C) * t) + 14) ≠ 0 := by positivity
  have := (((hasDerivAt_const t (-1 : ℝ)).fun_div (hZd.fun_pow 2) (pow_ne_zero 2 hZ.ne')).add
    ((hasDerivAt_const t (280 : ℝ)).fun_div (((hZd.const_mul 5).add_const 14).fun_pow 2)
      (pow_ne_zero 2 hK))).const_mul (x - C)
  unfold hl3of hl3of1
  refine this.congr_deriv ?_
  push_cast
  field_simp
  ring

theorem hl3o_hd_G (hH : C + (x - C - 1) * t ≠ 0) (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => hl3oG x C n s) (hl3oG1 x C n t) t := by
  have := ((hl3o_hd_P (x := x) (C := C) (n := n) (t := t)).add
    ((hl3o_hd_V hH).mul (hl3o_hd_A (x := x) (C := C) (n := n) (t := t)))).add (hl3o_hd_Phi hZ)
  unfold hl3oG hl3oG1
  exact this.congr_deriv (by ring)

theorem hl3o_hd_G1 (hH : C + (x - C - 1) * t ≠ 0) (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => hl3oG1 x C n s) (hl3oG2 x C n t) t := by
  have := (((hl3o_hd_P1 (x := x) (C := C) (n := n) (t := t)).add
    ((hl3o_hd_V1 hH).mul (hl3o_hd_A (x := x) (C := C) (n := n) (t := t)))).add
    ((hl3o_hd_V hH).mul (hl3o_hd_A1 (x := x) (C := C) (n := n) (t := t)))).add (hl3o_hd_Phi1 hZ)
  unfold hl3oG1 hl3oG2
  exact this.congr_deriv (by ring)

end Deriv

/-- Expand the derivative of an explicit rational expression by the chain rule (`deriv_fun_*`),
discharging differentiability by `fun_prop` and nonvanishing denominators by hypotheses or
`positivity`. -/
macro "hl3_deriv" : tactic =>
  `(tactic| simp (disch := first
      | fun_prop (disch := first | assumption | positivity)
      | assumption
      | positivity) only [deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_fun_div, deriv_fun_pow,
      deriv_div_const, deriv_id'', deriv_const, deriv_add_const, deriv_sub_const, deriv_const_sub,
      deriv_const_add, deriv_const_mul_id])

end SmoothedOctagon

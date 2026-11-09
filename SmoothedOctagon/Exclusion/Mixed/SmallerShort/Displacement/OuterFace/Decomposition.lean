module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.Faces

/-!
# Smaller-short window, displacement, outer face: the reciprocal-shape decomposition

The outer face sign `dsp_outer_face_proof`, first part. At `q = 1/7`, with the beta slope
`β = x + C(α - 1)`, `r = 1/α` and a constant duration weight `n`, the rational outer test
`R_n = J + n(w - 3/4)` (the logarithm replaced by its rational majorant) is
`R_n = P_n(r) + (u - 3/4)A_n(r) + 1/Z - 56/K` (`dspo_decomp`), where
`49A_i = nα_i + β_i`, `49SB_i = nγ_i + δ_i`, `P_i = 3A_i/4 + B_i` with the coefficient polynomials
`dspoα0`, …, `dspoδ2` printed below, `Z = 1 + C + (x - C)r`, `K = 5Z + 14`. The
incoming ceiling is `ū = 3/4 + V(r)`, `V = c + c(x - 1)r/(C + (x - C - 1)r)`,
`c = (x - 1)²/(S(35x + 13))` (`dspo_UO`).

The identity is checked as one polynomial identity in `x, C, n, u, r` with 115 monomials (after
the substitution `D/α² = d₀ + d₁r + d₂r²`).

## Main API

* `dspoα0`-`dspoα4`, `dspoβ0`-`dspoβ2`, `dspoγ0`-`dspoγ4`, `dspoδ0`-`dspoδ2`: the printed
  coefficient polynomials; `dspoA`, `dspoP`: the quartics `A_n(r)`, `P_n(r)`.
* `dspoV`, `dspoPhi`, `dspoG = P + V·A + Φ`.
* `dspo_decomp`, `dspo_UO`, `dspo_G_eq`: the test in this form.
* Calculus: `dsp_hd_quartic`, `dsp_hd_cubic`, `dsp_neg_of_convex`, the tactic `dsp_deriv`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The printed coefficient polynomials -/

noncomputable def dspoα0 (x C : ℝ) : ℝ := x * (-12 * C - 6) + (4 * C ^ 2 - 8 * C - 5)
noncomputable def dspoα1 (x C : ℝ) : ℝ :=
  x ^ 2 * (12 * C - 12) + x * (-8 * C ^ 2 + 28 * C - 8) + (-8 * C ^ 2 + 8 * C)
noncomputable def dspoα2 (x C : ℝ) : ℝ :=
  x ^ 3 * 12 + x ^ 2 * (4 * C ^ 2 - 28 * C) + x * (16 * C ^ 2 - 10 * C - 15) + (4 * C ^ 2 + 2 * C - 5)
noncomputable def dspoα3 (x C : ℝ) : ℝ :=
  x ^ 3 * (8 * C - 8) + x ^ 2 * (-8 * C ^ 2 + 10 * C + 6) + x * (-8 * C ^ 2 - 8 * C + 2) + (-2 * C)
noncomputable def dspoα4 (x C : ℝ) : ℝ :=
  x ^ 4 * 4 + x ^ 3 * (-8 * C - 6) + x ^ 2 * (4 * C ^ 2 + 6 * C) + x * (2 * C + 1)
noncomputable def dspoβ0 (x C : ℝ) : ℝ := x * 42 + (21 * C + 77)
noncomputable def dspoβ1 (x C : ℝ) : ℝ := x * (28 * C + 21) + (-21 * C)
noncomputable def dspoβ2 (x C : ℝ) : ℝ := x ^ 2 * 28 + x * (-28 * C - 21) + (-7)
noncomputable def dspoγ0 (x C : ℝ) : ℝ := x ^ 2 * (12 * C + 6) + x * (24 * C + 45 / 4) + (-3 / 4)
noncomputable def dspoγ1 (x C : ℝ) : ℝ :=
  x ^ 3 * (-12 * C + 12) + x ^ 2 * (-36 * C + 24) + x * (-24 * C)
noncomputable def dspoγ2 (x C : ℝ) : ℝ :=
  x ^ 4 * (-12) + x ^ 3 * (12 * C - 12) + x ^ 2 * (22 * C + 23) + x * (-2 * C + 11) + (-2 * C + 5)
noncomputable def dspoγ3 (x C : ℝ) : ℝ :=
  x ^ 3 * (2 * C - 2) + x ^ 2 * (4 * C - 2) + x * (4 * C - 2) + 2 * C
noncomputable def dspoγ4 (x C : ℝ) : ℝ :=
  x ^ 4 * 2 + x ^ 3 * (-2 * C + 1) + x ^ 2 * (-2 * C + 1) + x * (-2 * C - 1)
noncomputable def dspoδ0 (x C : ℝ) : ℝ :=
  x ^ 2 * (-42) + x * (-49 * C - 707497 / 180000) + (-49 * C + 14412503 / 180000)
noncomputable def dspoδ1 (x C : ℝ) : ℝ := x ^ 2 * (-49) + x * (49 * C - 49) + 49 * C
noncomputable def dspoδ2 (x : ℝ) : ℝ := x ^ 2 * 7 + x * 7 + 7

/-- `A_i = (nα_i + β_i)/49`. -/
noncomputable def dspoAc0 (x C n : ℝ) : ℝ := (n * dspoα0 x C + dspoβ0 x C) / 49
noncomputable def dspoAc1 (x C n : ℝ) : ℝ := (n * dspoα1 x C + dspoβ1 x C) / 49
noncomputable def dspoAc2 (x C n : ℝ) : ℝ := (n * dspoα2 x C + dspoβ2 x C) / 49
noncomputable def dspoAc3 (x C n : ℝ) : ℝ := n * dspoα3 x C / 49
noncomputable def dspoAc4 (x C n : ℝ) : ℝ := n * dspoα4 x C / 49

/-- `P_i = 3A_i/4 + B_i`, `B_i = (nγ_i + δ_i)/(49S)`. -/
noncomputable def dspoPc0 (x C n : ℝ) : ℝ :=
  3 / 4 * dspoAc0 x C n + (n * dspoγ0 x C + dspoδ0 x C) / (49 * (x + 1))
noncomputable def dspoPc1 (x C n : ℝ) : ℝ :=
  3 / 4 * dspoAc1 x C n + (n * dspoγ1 x C + dspoδ1 x C) / (49 * (x + 1))
noncomputable def dspoPc2 (x C n : ℝ) : ℝ :=
  3 / 4 * dspoAc2 x C n + (n * dspoγ2 x C + dspoδ2 x) / (49 * (x + 1))
noncomputable def dspoPc3 (x C n : ℝ) : ℝ := 3 / 4 * dspoAc3 x C n + n * dspoγ3 x C / (49 * (x + 1))
noncomputable def dspoPc4 (x C n : ℝ) : ℝ := 3 / 4 * dspoAc4 x C n + n * dspoγ4 x C / (49 * (x + 1))

/-- `A_n(r) = Σ A_i rⁱ`: the coefficient of the incoming norm. -/
noncomputable def dspoA (x C n r : ℝ) : ℝ :=
  dspoAc0 x C n + dspoAc1 x C n * r + dspoAc2 x C n * r ^ 2 + dspoAc3 x C n * r ^ 3 +
    dspoAc4 x C n * r ^ 4
/-- `A_n'(r)`. -/
noncomputable def dspoA1 (x C n r : ℝ) : ℝ :=
  dspoAc1 x C n + 2 * dspoAc2 x C n * r + 3 * dspoAc3 x C n * r ^ 2 + 4 * dspoAc4 x C n * r ^ 3
/-- `A_n''(r)`. -/
noncomputable def dspoA2 (x C n r : ℝ) : ℝ :=
  2 * dspoAc2 x C n + 6 * dspoAc3 x C n * r + 12 * dspoAc4 x C n * r ^ 2

/-- `P_n(r) = Σ P_i rⁱ`: the polynomial part at `u = 3/4`. -/
noncomputable def dspoP (x C n r : ℝ) : ℝ :=
  dspoPc0 x C n + dspoPc1 x C n * r + dspoPc2 x C n * r ^ 2 + dspoPc3 x C n * r ^ 3 +
    dspoPc4 x C n * r ^ 4
/-- `P_n'(r)`. -/
noncomputable def dspoP1 (x C n r : ℝ) : ℝ :=
  dspoPc1 x C n + 2 * dspoPc2 x C n * r + 3 * dspoPc3 x C n * r ^ 2 + 4 * dspoPc4 x C n * r ^ 3
/-- `P_n''(r)`. -/
noncomputable def dspoP2 (x C n r : ℝ) : ℝ :=
  2 * dspoPc2 x C n + 6 * dspoPc3 x C n * r + 12 * dspoPc4 x C n * r ^ 2

/-- `c = (x - 1)²/(S(35x + 13))`. -/
noncomputable def dspoc (x : ℝ) : ℝ := (x - 1) ^ 2 / ((x + 1) * (35 * x + 13))

/-- `V = ū - 3/4 = c + c(x - 1)r/H`, `H = C + (x - C - 1)r`. -/
noncomputable def dspoV (x C r : ℝ) : ℝ := dspoc x + dspoc x * (x - 1) * r / (C + (x - C - 1) * r)

/-- `Φ = 1/Z - 56/(5Z + 14)`, `Z = 1 + C + (x - C)r`. -/
noncomputable def dspoPhi (x C r : ℝ) : ℝ :=
  1 / (1 + C + (x - C) * r) - 56 / (5 * (1 + C + (x - C) * r) + 14)

/-- **The outer test in reciprocal shape** `R_n = P_n + V·A_n + Φ` at `u = ū`. -/
noncomputable def dspoG (x C n r : ℝ) : ℝ := dspoP x C n r + dspoV x C r * dspoA x C n r + dspoPhi x C r

/-- `f(z) = -1/z² + 280/(5z + 14)²`, so that `Φ' = (x - C)f(Z)`. -/
noncomputable def dspof (z : ℝ) : ℝ := -1 / z ^ 2 + 280 / (5 * z + 14) ^ 2
/-- `f'(z) = 2/z³ - 2800/(5z + 14)³`. -/
noncomputable def dspof1 (z : ℝ) : ℝ := 2 / z ^ 3 - 2800 / (5 * z + 14) ^ 3
/-- `V' = c(x - 1)C/H²`. -/
noncomputable def dspoV1 (x C r : ℝ) : ℝ := dspoc x * (x - 1) * C / (C + (x - C - 1) * r) ^ 2
/-- `V'' = -2c(x - 1)C(x - C - 1)/H³`. -/
noncomputable def dspoV2 (x C r : ℝ) : ℝ :=
  -2 * dspoc x * (x - 1) * C * (x - C - 1) / (C + (x - C - 1) * r) ^ 3
/-- `G' = P' + V'A + VA' + (x - C)f(Z)`. -/
noncomputable def dspoG1 (x C n r : ℝ) : ℝ :=
  dspoP1 x C n r + dspoV1 x C r * dspoA x C n r + dspoV x C r * dspoA1 x C n r +
    (x - C) * dspof (1 + C + (x - C) * r)
/-- `G'' = P'' + V''A + 2V'A' + VA'' + (x - C)²f'(Z)`. -/
noncomputable def dspoG2 (x C n r : ℝ) : ℝ :=
  dspoP2 x C n r + dspoV2 x C r * dspoA x C n r + 2 * dspoV1 x C r * dspoA1 x C n r +
    dspoV x C r * dspoA2 x C n r + (x - C) ^ 2 * dspof1 (1 + C + (x - C) * r)

/-! ### The decomposition -/

/-- **The reciprocal-shape decomposition** `R_n = P_n(r) + (u - 3/4)A_n(r) + 1/Z - 56/K`, one
polynomial identity in `x, C, n, u, r`. -/
theorem dspo_decomp {x C a u n : ℝ} (hx : 0 < x) (ha : 0 < a) (hC : 0 ≤ C) (hCx : C ≤ x) :
    dspFn x (x + C * (a - 1)) a u (1 / 7) n
        (319847 / 180000 - 56 * a / (19 * a + 5 * (x + C * (a - 1)))) =
      dspoP x C n (1 / a) + (u - 3 / 4) * dspoA x C n (1 / a) + dspoPhi x C (1 / a) := by
  obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ a = 1 / r := ⟨1 / a, by positivity, by field_simp⟩
  rw [one_div_one_div]
  have hr : r ≠ 0 := hr0.ne'
  have hZ : 0 < 1 + C + (x - C) * r := by nlinarith
  have hZ' : 1 + C + (x - C) * r ≠ 0 := hZ.ne'
  have hab : 1 / r + (x + C * (1 / r - 1)) = (1 + C + (x - C) * r) / r := by field_simp; ring
  have hRA : ssRA (1 / r) (x + C * (1 / r - 1)) = 1 / (1 + C + (x - C) * r) := by
    unfold ssRA; rw [hab]; field_simp
  have h19 : 19 * (1 / r) + 5 * (x + C * (1 / r - 1)) = (5 * (1 + C + (x - C) * r) + 14) / r := by
    field_simp; ring
  have hlog : 56 * (1 / r) / (19 * (1 / r) + 5 * (x + C * (1 / r - 1))) =
      56 / (5 * (1 + C + (x - C) * r) + 14) := by
    rw [h19]
    have : 5 * (1 + C + (x - C) * r) + 14 ≠ 0 := by positivity
    field_simp
  have hD : ssDg x (x + C * (1 / r - 1)) (1 / r) =
      ((1 + 2 * C) + 2 * (x - C * (x + 1)) * r + (1 + 2 * x - 2 * x ^ 2 + 2 * C * x) * r ^ 2) / r ^ 2 := by
    unfold ssDg; field_simp; ring
  have hRA' : (u - 1) / ssRA (1 / r) (x + C * (1 / r - 1)) = (u - 1) * (1 + C + (x - C) * r) := by
    rw [hRA]; field_simp
  unfold dspFn ssELs ssWs ssA1 ssA2 ssA3
  rw [hRA', hRA, hlog, hD]
  unfold ssE0 dspoP dspoA dspoPhi dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0 dspoAc1 dspoAc2
    dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2 dspoγ0
    dspoγ1 dspoγ2 dspoγ3 dspoγ4 dspoδ0 dspoδ1 dspoδ2
  have hS : x + 1 ≠ 0 := by linarith
  have hS' : 1 + x ≠ 0 := by linarith
  generalize 1 / (1 + C + (x - C) * r) = w1
  generalize 56 / (5 * (1 + C + (x - C) * r) + 14) = w2
  field_simp
  ring

/-- The outer ceiling `ū = 3/4 + V(1/α)`. -/
theorem dspo_UO {x C a : ℝ} (hx : 1 < x) (ha : 1 < a) (hC : 0 < C) :
    ssUO x (x + C * (a - 1)) = 3 / 4 + dspoV x C (1 / a) := by
  unfold ssUO dspoV dspoc
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

/-- **The outer test at `ū`** is `dspoG` at `r = 1/α`. -/
theorem dspo_G_eq {x C a n : ℝ} (hx : 1 < x) (ha : 1 < a) (hC : 0 < C) (hCx : C ≤ x) :
    dspFn x (x + C * (a - 1)) a (ssUO x (x + C * (a - 1))) (1 / 7) n
        (319847 / 180000 - 56 * a / (19 * a + 5 * (x + C * (a - 1)))) = dspoG x C n (1 / a) := by
  rw [dspo_decomp (by linarith) (by linarith) hC.le hCx, dspo_UO hx ha hC]
  unfold dspoG
  ring

/-! ### Calculus helpers -/

theorem dsp_hd_quartic (c0 c1 c2 c3 c4 t : ℝ) :
    HasDerivAt (fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 + c4 * s ^ 4)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3) t := by
  have := (((((hasDerivAt_id t).const_mul c1).const_add c0).add ((hasDerivAt_pow 2 t).const_mul c2)).add
    ((hasDerivAt_pow 3 t).const_mul c3)).add ((hasDerivAt_pow 4 t).const_mul c4)
  refine this.congr_deriv ?_
  push_cast
  ring

theorem dsp_hd_cubic (c1 c2 c3 c4 t : ℝ) :
    HasDerivAt (fun s => c1 + 2 * c2 * s + 3 * c3 * s ^ 2 + 4 * c4 * s ^ 3)
      (2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2) t := by
  have := ((((hasDerivAt_id t).const_mul (2 * c2)).const_add c1).add
    ((hasDerivAt_pow 2 t).const_mul (3 * c3))).add ((hasDerivAt_pow 3 t).const_mul (4 * c4))
  refine this.congr_deriv ?_
  push_cast
  ring

/-- **Convexity keeps the sign of the endpoints**: if `g'' ≥ 0` on `[r₁, r₂]` and `g < 0` at both
ends, then `g < 0` on `[r₁, r₂]`. -/
theorem dsp_neg_of_convex {g g' g'' : ℝ → ℝ} {r₁ r₂ s : ℝ}
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

theorem dspo_hd_A : HasDerivAt (fun s => dspoA x C n s) (dspoA1 x C n t) t := by
  unfold dspoA dspoA1; exact dsp_hd_quartic _ _ _ _ _ t

theorem dspo_hd_A1 : HasDerivAt (fun s => dspoA1 x C n s) (dspoA2 x C n t) t := by
  unfold dspoA1 dspoA2; exact dsp_hd_cubic _ _ _ _ t

theorem dspo_hd_P : HasDerivAt (fun s => dspoP x C n s) (dspoP1 x C n t) t := by
  unfold dspoP dspoP1; exact dsp_hd_quartic _ _ _ _ _ t

theorem dspo_hd_P1 : HasDerivAt (fun s => dspoP1 x C n s) (dspoP2 x C n t) t := by
  unfold dspoP1 dspoP2; exact dsp_hd_cubic _ _ _ _ t

theorem dspo_hd_V (hH : C + (x - C - 1) * t ≠ 0) :
    HasDerivAt (fun s => dspoV x C s) (dspoV1 x C t) t := by
  have := (((hasDerivAt_id t).const_mul (dspoc x * (x - 1))).fun_div
    (((hasDerivAt_id t).const_mul (x - C - 1)).const_add C) hH).const_add (dspoc x)
  unfold dspoV dspoV1
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem dspo_hd_V1 (hH : C + (x - C - 1) * t ≠ 0) :
    HasDerivAt (fun s => dspoV1 x C s) (dspoV2 x C t) t := by
  have := (hasDerivAt_const t (dspoc x * (x - 1) * C)).fun_div
    ((((hasDerivAt_id t).const_mul (x - C - 1)).const_add C).fun_pow 2) (pow_ne_zero 2 hH)
  unfold dspoV1 dspoV2
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem dspo_hd_Phi (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => dspoPhi x C s) ((x - C) * dspof (1 + C + (x - C) * t)) t := by
  have hZd : HasDerivAt (fun s => 1 + C + (x - C) * s) (x - C) t := by
    simpa using ((hasDerivAt_id t).const_mul (x - C)).const_add (1 + C)
  have hK : (5 * (1 + C + (x - C) * t) + 14) ≠ 0 := by positivity
  have := ((hasDerivAt_const t (1 : ℝ)).fun_div hZd hZ.ne').sub
    ((hasDerivAt_const t (56 : ℝ)).fun_div ((hZd.const_mul 5).add_const 14) hK)
  unfold dspoPhi dspof
  refine this.congr_deriv ?_
  field_simp
  ring

theorem dspo_hd_Phi1 (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => (x - C) * dspof (1 + C + (x - C) * s))
      ((x - C) ^ 2 * dspof1 (1 + C + (x - C) * t)) t := by
  have hZd : HasDerivAt (fun s => 1 + C + (x - C) * s) (x - C) t := by
    simpa using ((hasDerivAt_id t).const_mul (x - C)).const_add (1 + C)
  have hK : (5 * (1 + C + (x - C) * t) + 14) ≠ 0 := by positivity
  have := (((hasDerivAt_const t (-1 : ℝ)).fun_div (hZd.fun_pow 2) (pow_ne_zero 2 hZ.ne')).add
    ((hasDerivAt_const t (280 : ℝ)).fun_div (((hZd.const_mul 5).add_const 14).fun_pow 2)
      (pow_ne_zero 2 hK))).const_mul (x - C)
  unfold dspof dspof1
  refine this.congr_deriv ?_
  push_cast
  field_simp
  ring

theorem dspo_hd_G (hH : C + (x - C - 1) * t ≠ 0) (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => dspoG x C n s) (dspoG1 x C n t) t := by
  have := ((dspo_hd_P (x := x) (C := C) (n := n) (t := t)).add
    ((dspo_hd_V hH).mul (dspo_hd_A (x := x) (C := C) (n := n) (t := t)))).add (dspo_hd_Phi hZ)
  unfold dspoG dspoG1
  exact this.congr_deriv (by ring)

theorem dspo_hd_G1 (hH : C + (x - C - 1) * t ≠ 0) (hZ : 0 < 1 + C + (x - C) * t) :
    HasDerivAt (fun s => dspoG1 x C n s) (dspoG2 x C n t) t := by
  have := (((dspo_hd_P1 (x := x) (C := C) (n := n) (t := t)).add
    ((dspo_hd_V1 hH).mul (dspo_hd_A (x := x) (C := C) (n := n) (t := t)))).add
    ((dspo_hd_V hH).mul (dspo_hd_A1 (x := x) (C := C) (n := n) (t := t)))).add (dspo_hd_Phi1 hZ)
  unfold dspoG1 dspoG2
  exact this.congr_deriv (by ring)

end Deriv

/-- Expand the derivative of an explicit rational expression by the chain rule (`deriv_fun_*`),
discharging differentiability by `fun_prop` and nonvanishing denominators by hypotheses or
`positivity`. -/
macro "dsp_deriv" : tactic =>
  `(tactic| simp (disch := first
      | fun_prop (disch := first | assumption | positivity)
      | assumption
      | positivity) only [deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_fun_div, deriv_fun_pow,
      deriv_div_const, deriv_id'', deriv_const, deriv_add_const, deriv_sub_const, deriv_const_sub,
      deriv_const_add, deriv_const_mul_id])

end SmoothedOctagon

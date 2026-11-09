module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.Tools

/-!
# Smaller-short window, lower ratio: the outer tests in the reciprocal shape

At a fixed slope `C` (`β = x + C(α - 1)`) put `r = 1/α`,
`d = 1 + C`, `e = x - C`, `Z = d + er = B/α`, `S = 1 + x`, `E₀ = S(u - 1) + 1/S`,
`J₂ = E₀ + 2S - 1`, `d₀ = 1 + 2C`, `d₁ = 2((1 - C)x - C)`, `d₂ = 1 + 2x - 2x² + 2Cx`,
`D_r = d₀ + d₁r + d₂r²`. Then
`49w = W(r) = 36 + (12 - 6S)r² + (S² - S + 1)r⁴ + uD_r² - D_r(6E₀ + J₂r²)`,
`7E_L = 2uD_r - 6E₀ - J₂r²`, `576Γ_* = 4u[36 + (12 - 6S)r² + (S² - S + 1)r⁴] - (6E₀ + J₂r²)²`.
The quartic `W` is kept with opaque coefficients `W₀, …, W₄` and divided by `Z`, so
both tests have the form `g(r) = b₀ + b₁r + b₂r² + b₃r³ + b₄r⁴ + Q/Z - cℓ(2Z/7)` (`lrG`,
`lro_F1_rG`, `lro_F0_rG`), with `Q = (119/4 - W(-d/e))/96` for `F₁` and `Q = -c` for `F₀`.
Its curvature is `g'' = 2b₂ + 6b₃r + 12b₄r² + 2Qe²/Z³ - c(2e/7)²ℓ''(2Z/7)`, and
`ℓ'' ≥ -1/y²` bounds the last term by `ce²/Z²` (`lrG_min`).

## Main API

* `lrd0`, `lrd1`, `lrd2`, `lrJ2`, `lrW0`, …, `lrW4`, `lrg0`, `lrg2`, `lrg4`,
  `lrq0`, …, `lrq3`, `lrb0`, …, `lrb4`, `lrQ1`, `lrp0`, …, `lrp4`;
* `lrG`, `lrG1`, `lrG2`, `lrG_hasDerivAt`, `lrG1_hasDerivAt`, `lrG2_le`, `lrG_min`;
* `lro_F1_rG`, `lro_F0_rG`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### The coefficient circuit -/

/-- `d₀ = 1 + 2C`. -/
noncomputable def lrd0 (C : ℝ) : ℝ := 1 + 2 * C
/-- `d₁ = 2((1 - C)x - C)`. -/
noncomputable def lrd1 (x C : ℝ) : ℝ := 2 * ((1 - C) * x - C)
/-- `d₂ = 1 + 2x - 2x² + 2Cx`. -/
noncomputable def lrd2 (x C : ℝ) : ℝ := 1 + 2 * x - 2 * x ^ 2 + 2 * C * x
/-- `J₂ = E₀ + 2S - 1 = Su + A₀`. -/
noncomputable def lrJ2 (x u : ℝ) : ℝ := ssE0 x u + 2 * (1 + x) - 1

/-- `W₀ = 36 + ud₀² - 6d₀E₀`. -/
noncomputable def lrW0 (x C u : ℝ) : ℝ := 36 + u * lrd0 C ^ 2 - 6 * lrd0 C * ssE0 x u
/-- `W₁ = 2ud₀d₁ - 6d₁E₀`. -/
noncomputable def lrW1 (x C u : ℝ) : ℝ :=
  2 * u * lrd0 C * lrd1 x C - 6 * lrd1 x C * ssE0 x u
/-- `W₂ = 12 - 6S + u(d₁² + 2d₀d₂) - 6d₂E₀ - d₀J₂`. -/
noncomputable def lrW2 (x C u : ℝ) : ℝ :=
  12 - 6 * (1 + x) + u * (lrd1 x C ^ 2 + 2 * lrd0 C * lrd2 x C) - 6 * lrd2 x C * ssE0 x u -
    lrd0 C * lrJ2 x u
/-- `W₃ = d₁(2ud₂ - J₂)`. -/
noncomputable def lrW3 (x C u : ℝ) : ℝ := lrd1 x C * (2 * u * lrd2 x C - lrJ2 x u)
/-- `W₄ = (S² - S + 1) + ud₂² - d₂J₂ = (S - d₂)(A₀ - ud₂)`. -/
noncomputable def lrW4 (x C u : ℝ) : ℝ :=
  ((1 + x) ^ 2 - (1 + x) + 1) + u * lrd2 x C ^ 2 - lrd2 x C * lrJ2 x u

/-- `γ₀ = u/4 - E₀²/16`. -/
noncomputable def lrg0 (x u : ℝ) : ℝ := u / 4 - ssE0 x u ^ 2 / 16
/-- `γ₂ = u(2 - S)/24 - E₀J₂/48`. -/
noncomputable def lrg2 (x u : ℝ) : ℝ := u * (2 - (1 + x)) / 24 - ssE0 x u * lrJ2 x u / 48
/-- `γ₄ = (4u(S² - S + 1) - J₂²)/576 = -(Su - A₀)²/576`. -/
noncomputable def lrg4 (x u : ℝ) : ℝ := (4 * u * ((1 + x) ^ 2 - (1 + x) + 1) - lrJ2 x u ^ 2) / 576

/-- Division of `W` by `Z = d + er`: `q₃ = W₄/e`. -/
noncomputable def lrq3 (x C u : ℝ) : ℝ := lrW4 x C u / (x - C)
/-- `q₂ = (W₃ - dq₃)/e`. -/
noncomputable def lrq2 (x C u : ℝ) : ℝ := (lrW3 x C u - (1 + C) * lrq3 x C u) / (x - C)
/-- `q₁ = (W₂ - dq₂)/e`. -/
noncomputable def lrq1 (x C u : ℝ) : ℝ := (lrW2 x C u - (1 + C) * lrq2 x C u) / (x - C)
/-- `q₀ = (W₁ - dq₁)/e`. -/
noncomputable def lrq0 (x C u : ℝ) : ℝ := (lrW1 x C u - (1 + C) * lrq1 x C u) / (x - C)

/-- `b₄ = γ₄`. -/
noncomputable def lrb4 (x u : ℝ) : ℝ := lrg4 x u
/-- `b₃ = -q₃/96 = -W₄/(96e)`. -/
noncomputable def lrb3 (x C u : ℝ) : ℝ := -lrq3 x C u / 96
/-- `b₂ = γ₂ - q₂/96 + (2ud₂ - J₂)/96`. -/
noncomputable def lrb2 (x C u : ℝ) : ℝ :=
  lrg2 x u - lrq2 x C u / 96 + (2 * u * lrd2 x C - lrJ2 x u) / 96
/-- `b₁`. -/
noncomputable def lrb1 (x C u : ℝ) : ℝ :=
  -lrq1 x C u / 96 - 7 / 96 * (u - 1) * (x - C) + 2 * u * lrd1 x C / 96
/-- `b₀`. -/
noncomputable def lrb0 (x C u : ℝ) : ℝ :=
  lrg0 x u - lrq0 x C u / 96 - 7 / 96 * (u - 1) * (1 + C) +
    (2 * u * lrd0 C - 6 * ssE0 x u) / 96 - 1 / 16 - 9193 / 50000
/-- The residue `Q = (119/4 - W(-d/e))/96`. -/
noncomputable def lrQ1 (x C u : ℝ) : ℝ := -(lrW0 x C u - 119 / 4 - (1 + C) * lrq0 x C u) / 96

/-- `p₄ = γ₄ - W₄/336` (the `F₀` coefficients). -/
noncomputable def lrp4 (x C u : ℝ) : ℝ := lrg4 x u - lrW4 x C u / 336
/-- `p₃ = -W₃/336`. -/
noncomputable def lrp3 (x C u : ℝ) : ℝ := -lrW3 x C u / 336
/-- `p₂ = γ₂ - W₂/336 + (2ud₂ - J₂)/96`. -/
noncomputable def lrp2 (x C u : ℝ) : ℝ :=
  lrg2 x u - lrW2 x C u / 336 + (2 * u * lrd2 x C - lrJ2 x u) / 96
/-- `p₁`. -/
noncomputable def lrp1 (x C u : ℝ) : ℝ :=
  -lrW1 x C u / 336 - 7 / 96 * (u - 1) * (x - C) + 2 * u * lrd1 x C / 96
/-- `p₀`. -/
noncomputable def lrp0 (x C u : ℝ) : ℝ :=
  lrg0 x u - lrW0 x C u / 336 + 3 / 64 - 7 / 96 * (u - 1) * (1 + C) +
    (2 * u * lrd0 C - 6 * ssE0 x u) / 96 - 9193 / 50000

/-! ### The generic reciprocal-shape function -/

/-- `g(r) = b₀ + b₁r + b₂r² + b₃r³ + b₄r⁴ + Q/(d + er) - cℓ(2(d + er)/7)`. -/
noncomputable def lrG (b0 b1 b2 b3 b4 Q d e r : ℝ) : ℝ :=
  b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3 + b4 * r ^ 4 + Q / (d + e * r) -
    7 / 96 * lrell (2 * (d + e * r) / 7)

/-- `g'(r)`. -/
noncomputable def lrG1 (b1 b2 b3 b4 Q d e r : ℝ) : ℝ :=
  b1 + 2 * b2 * r + 3 * b3 * r ^ 2 + 4 * b4 * r ^ 3 - Q * e / (d + e * r) ^ 2 -
    7 / 96 * lrell1 (2 * (d + e * r) / 7) * (2 * e / 7)

/-- `g''(r)`. -/
noncomputable def lrG2 (b2 b3 b4 Q d e r : ℝ) : ℝ :=
  2 * b2 + 6 * b3 * r + 12 * b4 * r ^ 2 + 2 * Q * e ^ 2 / (d + e * r) ^ 3 -
    7 / 96 * lrell2 (2 * (d + e * r) / 7) * (2 * e / 7) ^ 2

theorem lrG_hasDerivAt {b0 b1 b2 b3 b4 Q d e r : ℝ} (hZ : 0 < d + e * r) :
    HasDerivAt (lrG b0 b1 b2 b3 b4 Q d e) (lrG1 b1 b2 b3 b4 Q d e r) r := by
  have hZd : HasDerivAt (fun s => d + e * s) e r := by
    simpa using ((hasDerivAt_id' r).const_mul e).const_add d
  have hyd : HasDerivAt (fun s => 2 * (d + e * s) / 7) (2 * e / 7) r := by
    simpa using (hZd.const_mul 2).div_const 7
  have hy : -1 < 2 * (d + e * r) / 7 := by
    have : 0 < 2 * (d + e * r) / 7 := by positivity
    linarith
  have hl := (lr_ell_hasDerivAt' hy).comp r hyd
  have hid := hasDerivAt_id' r
  have hp := (((((hid.const_mul b1).const_add b0).add ((hid.fun_pow 2).const_mul b2)).add
    ((hid.fun_pow 3).const_mul b3)).add ((hid.fun_pow 4).const_mul b4)).add
      ((hasDerivAt_const r Q).fun_div hZd hZ.ne')
  have h := hp.sub (hl.const_mul (7 / 96))
  have hf : lrG b0 b1 b2 b3 b4 Q d e = fun s => b0 + b1 * s + b2 * s ^ 2 + b3 * s ^ 3 +
      b4 * s ^ 4 + Q / (d + e * s) - 7 / 96 * lrell (2 * (d + e * s) / 7) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  unfold lrG1
  norm_num
  field_simp
  ring

theorem lrG1_hasDerivAt {b1 b2 b3 b4 Q d e r : ℝ} (hZ : 0 < d + e * r) :
    HasDerivAt (lrG1 b1 b2 b3 b4 Q d e) (lrG2 b2 b3 b4 Q d e r) r := by
  have hZd : HasDerivAt (fun s => d + e * s) e r := by
    simpa using ((hasDerivAt_id' r).const_mul e).const_add d
  have hyd : HasDerivAt (fun s => 2 * (d + e * s) / 7) (2 * e / 7) r := by
    simpa using (hZd.const_mul 2).div_const 7
  have hy : -1 < 2 * (d + e * r) / 7 := by
    have : 0 < 2 * (d + e * r) / 7 := by positivity
    linarith
  have hl := (lr_ell1_hasDerivAt hy).comp r hyd
  have hid := hasDerivAt_id' r
  have hp := (((((hid.const_mul (2 * b2)).const_add b1).add ((hid.fun_pow 2).const_mul
    (3 * b3))).add ((hid.fun_pow 3).const_mul (4 * b4))).sub
      ((hasDerivAt_const r (Q * e)).fun_div (hZd.fun_pow 2) (pow_ne_zero 2 hZ.ne')))
  have h := hp.sub ((hl.mul_const (2 * e / 7)).const_mul (7 / 96))
  have hf : lrG1 b1 b2 b3 b4 Q d e = fun s => b1 + 2 * b2 * s + 3 * b3 * s ^ 2 +
      4 * b4 * s ^ 3 - Q * e / (d + e * s) ^ 2 -
        7 / 96 * lrell1 (2 * (d + e * s) / 7) * (2 * e / 7) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]; ring
  unfold lrG2
  norm_num
  field_simp
  ring

/-- **The curvature bound** `g'' ≤ 2b₂ + 6b₃r + 12b₄r² + 2Qe²/Z³ + ce²/Z²` for `0 < 2Z/7 ≤ 1`. -/
theorem lrG2_le {b2 b3 b4 Q d e r : ℝ} (hZ : 0 < d + e * r) (hZ7 : 2 * (d + e * r) ≤ 7) :
    lrG2 b2 b3 b4 Q d e r ≤ 2 * b2 + 6 * b3 * r + 12 * b4 * r ^ 2 +
      2 * Q * e ^ 2 / (d + e * r) ^ 3 + 7 / 96 * e ^ 2 / (d + e * r) ^ 2 := by
  have hy : 0 < 2 * (d + e * r) / 7 := by positivity
  have hl := lr_ell2_ge hy (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hl (sq_nonneg (2 * e / 7))
  have h2 : -(1 / (2 * (d + e * r) / 7) ^ 2) * (2 * e / 7) ^ 2 = -(e ^ 2 / (d + e * r) ^ 2) := by
    field_simp
  rw [h2] at h1
  unfold lrG2
  have : 7 / 96 * e ^ 2 / (d + e * r) ^ 2 = 7 / 96 * (e ^ 2 / (d + e * r) ^ 2) := by ring
  rw [this]
  nlinarith

/-- **Reciprocal-shape concavity**: if the curvature bound is nonpositive on `[r₀, r₁]` (with
`0 < Z`, `2Z ≤ 7` there), then `g ≥ min (g r₀) (g r₁)` on `[r₀, r₁]`. -/
theorem lrG_min {b0 b1 b2 b3 b4 Q d e r0 r r1 : ℝ} (h0 : r0 ≤ r) (h1 : r ≤ r1)
    (hZ : ∀ s ∈ Icc r0 r1, 0 < d + e * s ∧ 2 * (d + e * s) ≤ 7)
    (hc : ∀ s ∈ Icc r0 r1, 2 * b2 + 6 * b3 * s + 12 * b4 * s ^ 2 +
      2 * Q * e ^ 2 / (d + e * s) ^ 3 + 7 / 96 * e ^ 2 / (d + e * s) ^ 2 ≤ 0) :
    min (lrG b0 b1 b2 b3 b4 Q d e r0) (lrG b0 b1 b2 b3 b4 Q d e r1) ≤
      lrG b0 b1 b2 b3 b4 Q d e r :=
  lr_conc_min h0 h1 (fun s hs => lrG_hasDerivAt (hZ s hs).1)
    (fun s hs => lrG1_hasDerivAt (hZ s hs).1)
    (fun s hs => (lrG2_le (hZ s hs).1 (hZ s hs).2).trans (hc s hs))

/-! ### The two outer tests in the reciprocal shape -/

/-- The polynomial-in-`r` pieces at `α = 1/r`, `β = x + C(α - 1)`. -/
private theorem lro_pieces {x a b C u : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hb : b = x + C * (a - 1)) :
    lroG x a u = (4 * u * (36 + (12 - 6 * (1 + x)) * (1 / a) ^ 2 +
        ((1 + x) ^ 2 - (1 + x) + 1) * (1 / a) ^ 4) -
        (6 * ssE0 x u + lrJ2 x u * (1 / a) ^ 2) ^ 2) / 576 ∧
      lrow x a b u = (36 + (12 - 6 * (1 + x)) * (1 / a) ^ 2 +
        ((1 + x) ^ 2 - (1 + x) + 1) * (1 / a) ^ 4 +
        u * (lrd0 C + lrd1 x C * (1 / a) + lrd2 x C * (1 / a) ^ 2) ^ 2 -
        (lrd0 C + lrd1 x C * (1 / a) + lrd2 x C * (1 / a) ^ 2) *
          (6 * ssE0 x u + lrJ2 x u * (1 / a) ^ 2)) / 49 ∧
      lroEL x a b u = (2 * u * (lrd0 C + lrd1 x C * (1 / a) + lrd2 x C * (1 / a) ^ 2) -
        (6 * ssE0 x u + lrJ2 x u * (1 / a) ^ 2)) / 7 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hD : ssDg x b a = a ^ 2 * (lrd0 C + lrd1 x C * (1 / a) + lrd2 x C * (1 / a) ^ 2) := by
    rw [hb]; unfold ssDg lrd0 lrd1 lrd2; field_simp; ring
  have hJ : lroJ x a u = a ^ 2 * (6 * ssE0 x u + lrJ2 x u * (1 / a) ^ 2) := by
    unfold lroJ lrJ2 lroK; field_simp; ring
  have hM : lroM x a = a ^ 4 * (36 + (12 - 6 * (1 + x)) * (1 / a) ^ 2 +
      ((1 + x) ^ 2 - (1 + x) + 1) * (1 / a) ^ 4) := by
    unfold lroM lroK; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [lro_G hx ha0, hM, hJ]; field_simp
  · rw [lro_w hx ha0, hM, hJ, hD]; field_simp
  · rw [lro_EL hx ha0, hJ, hD]; field_simp

/-- **Division of the quartic `W` by `Z = d + er`**. -/
theorem lr_div4 {x C u r : ℝ} (he : x - C ≠ 0) (hZ : 1 + C + (x - C) * r ≠ 0) :
    1 / (1 + C + (x - C) * r) * (7 * ((lrW0 x C u + lrW1 x C u * r + lrW2 x C u * r ^ 2 +
      lrW3 x C u * r ^ 3 + lrW4 x C u * r ^ 4) / 49) - 17 / 4) =
      (lrq3 x C u * r ^ 3 + lrq2 x C u * r ^ 2 + lrq1 x C u * r + lrq0 x C u) / 7 +
        (lrW0 x C u - 119 / 4 - (1 + C) * lrq0 x C u) / (1 + C + (x - C) * r) / 7 := by
  unfold lrq0 lrq1 lrq2 lrq3
  generalize lrW0 x C u = W0
  generalize lrW1 x C u = W1
  generalize lrW2 x C u = W2
  generalize lrW3 x C u = W3
  generalize lrW4 x C u = W4
  generalize x - C = e at he hZ ⊢
  generalize 1 + C = d at hZ ⊢
  field_simp
  ring

/-- **The reciprocal-shape form of `F₁`**: on `β = x + C(α - 1)`, `F₁ = g(1/α)` with
`Q = (119/4 - W(-d/e))/96`. -/
theorem lro_F1_rG {x a b C u : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : b = x + C * (a - 1))
    (hCx : C < x) (hZ : 0 < 1 + C + (x - C) * (1 / a)) :
    lroF1 x a b u = lrG (lrb0 x C u) (lrb1 x C u) (lrb2 x C u) (lrb3 x C u) (lrb4 x u)
      (lrQ1 x C u) (1 + C) (x - C) (1 / a) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hab : a + b = a * (1 + C + (x - C) * (1 / a)) := by rw [hb]; field_simp; ring
  have hab0 : a + b ≠ 0 := by rw [hab]; positivity
  obtain ⟨hG, hw, hE⟩ := lro_pieces (u := u) hx ha hb
  rw [lro_F1_R1 ha0 hab0, hG, hw, hE]
  have hy : lroy a b = 2 * (1 + C + (x - C) * (1 / a)) / 7 := by
    unfold lroy; rw [hab]; field_simp
  have h1 : a / (a + b) = 1 / (1 + C + (x - C) * (1 / a)) := by rw [hab]; field_simp
  have h2 : (a + b) / a = 1 + C + (x - C) * (1 / a) := by rw [hab]; field_simp
  rw [hy, mul_div_assoc, h2, h1]
  have he : x - C ≠ 0 := by linarith
  have hW : ∀ r : ℝ, 36 + (12 - 6 * (1 + x)) * r ^ 2 + ((1 + x) ^ 2 - (1 + x) + 1) * r ^ 4 +
      u * (lrd0 C + lrd1 x C * r + lrd2 x C * r ^ 2) ^ 2 -
      (lrd0 C + lrd1 x C * r + lrd2 x C * r ^ 2) * (6 * ssE0 x u + lrJ2 x u * r ^ 2) =
      lrW0 x C u + lrW1 x C u * r + lrW2 x C u * r ^ 2 + lrW3 x C u * r ^ 3 +
        lrW4 x C u * r ^ 4 := by
    intro r; unfold lrW0 lrW1 lrW2 lrW3 lrW4; ring
  rw [hW]
  have hdiv := lr_div4 (x := x) (C := C) (u := u) (r := 1 / a) he hZ.ne'
  unfold lrG lrb0 lrb1 lrb2 lrb3 lrb4 lrQ1 lrg0 lrg2 lrg4
  linear_combination (-(7 / 96)) * hdiv

/-- **The reciprocal-shape form of `F₀`**: on `β = x + C(α - 1)`, `F₀ = g(1/α)` with
`Q = -c`. -/
theorem lro_F0_rG {x a b C u : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : b = x + C * (a - 1))
    (hZ : 0 < 1 + C + (x - C) * (1 / a)) :
    lroF0 x a b u = lrG (lrp0 x C u) (lrp1 x C u) (lrp2 x C u) (lrp3 x C u) (lrp4 x C u)
      (-(7 / 96)) (1 + C) (x - C) (1 / a) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hab : a + b = a * (1 + C + (x - C) * (1 / a)) := by rw [hb]; field_simp; ring
  have hab0 : a + b ≠ 0 := by rw [hab]; positivity
  obtain ⟨hG, hw, hE⟩ := lro_pieces (u := u) hx ha hb
  have hR : lroF0 x a b u = lroG x a u - 7 / 96 * (2 * lrow x a b u - 1 / 2 +
      (u - 1) * ((a + b) / a) + a / (a + b) - 1 / 7 - lroEL x a b u + lrell (lroy a b)) -
        9193 / 50000 := by
    unfold lroF0 lroR2; ring
  rw [hR, hG, hw, hE]
  have hy : lroy a b = 2 * (1 + C + (x - C) * (1 / a)) / 7 := by
    unfold lroy; rw [hab]; field_simp
  have h1 : a / (a + b) = 1 / (1 + C + (x - C) * (1 / a)) := by rw [hab]; field_simp
  have h2 : (a + b) / a = 1 + C + (x - C) * (1 / a) := by rw [hab]; field_simp
  rw [hy, h2, h1]
  unfold lrG lrp0 lrp1 lrp2 lrp3 lrp4 lrg0 lrg2 lrg4 lrW0 lrW1 lrW2 lrW3 lrW4
  generalize 1 / a = r at hZ ⊢
  generalize lrell (2 * (1 + C + (x - C) * r) / 7) = L
  generalize ssE0 x u = E0
  generalize lrJ2 x u = J2
  generalize lrd0 C = d0
  generalize lrd1 x C = d1
  generalize lrd2 x C = d2
  field_simp
  ring

end SmoothedOctagon

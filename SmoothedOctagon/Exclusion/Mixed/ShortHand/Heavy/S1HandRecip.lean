module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandBase

/-!
# Gate S1 by hand: the outer tests in the reciprocal shape

`SHORT_OUTER_LARGE_SHAPE_REDUCTION` §3, `SHORT_OUTER_S_RECIPROCAL` §1,
`SHORT_OUTER_RECIPROCAL_LOW_SHAPE` §2. At a fixed slope `C` (`β = x + C(α - 1)`) put `r = 1/α`,
`d = 1 + C`, `e = x - C`, `Z = d + er = B/α`, `S = 1 + x`, `E₀ = S(u - 1) + 1/S`,
`J₂ = E₀ + 2S - 1`, `d₀ = 1 + 2C`, `d₁ = 2((1 - C)x - C)`, `d₂ = 1 + 2x - 2x² + 2Cx`,
`D_r = d₀ + d₁r + d₂r²`. Then (`(A11)`)
`49w = W(r) = 36 + (12 - 6S)r² + (S² - S + 1)r⁴ + uD_r² - D_r(6E₀ + J₂r²)`,
`7E_L = 2uD_r - 6E₀ - J₂r²`, `576Γ_* = 4u[36 + (12 - 6S)r² + (S² - S + 1)r⁴] - (6E₀ + J₂r²)²`.
The quartic `W` is kept with opaque coefficients `W₀, …, W₄` and divided by `Z` (`(7)`, `(A13)`), so
both tests have the form `g(r) = b₀ + b₁r + b₂r² + b₃r³ + b₄r⁴ + Q/Z - cℓ(2Z/7)` (`hl1G`,
`hl1o_F1_rG`, `hl1o_F0_rG`), with `Q = (119/4 - W(-d/e))/96` for `F₁` and `Q = -c` for `F₀`.
Its curvature is `g'' = 2b₂ + 6b₃r + 12b₄r² + 2Qe²/Z³ - c(2e/7)²ℓ''(2Z/7)`, and
`ℓ'' ≥ -1/y²` bounds the last term by `ce²/Z²` (`hl1G_min`).

## Main API

* `hl1d0`, `hl1d1`, `hl1d2`, `hl1J2`, `hl1W0`, …, `hl1W4`, `hl1g0`, `hl1g2`, `hl1g4`,
  `hl1q0`, …, `hl1q3`, `hl1b0`, …, `hl1b4`, `hl1Q1`, `hl1p0`, …, `hl1p4`;
* `hl1G`, `hl1G1`, `hl1G2`, `hl1G_hasDerivAt`, `hl1G1_hasDerivAt`, `hl1G2_le`, `hl1G_min`;
* `hl1o_F1_rG`, `hl1o_F0_rG`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### The coefficient circuit -/

/-- `d₀ = 1 + 2C`. -/
noncomputable def hl1d0 (C : ℝ) : ℝ := 1 + 2 * C
/-- `d₁ = 2((1 - C)x - C)`. -/
noncomputable def hl1d1 (x C : ℝ) : ℝ := 2 * ((1 - C) * x - C)
/-- `d₂ = 1 + 2x - 2x² + 2Cx`. -/
noncomputable def hl1d2 (x C : ℝ) : ℝ := 1 + 2 * x - 2 * x ^ 2 + 2 * C * x
/-- `J₂ = E₀ + 2S - 1 = Su + A₀`. -/
noncomputable def hl1J2 (x u : ℝ) : ℝ := hsE0 x u + 2 * (1 + x) - 1

/-- `W₀ = 36 + ud₀² - 6d₀E₀`. -/
noncomputable def hl1W0 (x C u : ℝ) : ℝ := 36 + u * hl1d0 C ^ 2 - 6 * hl1d0 C * hsE0 x u
/-- `W₁ = 2ud₀d₁ - 6d₁E₀`. -/
noncomputable def hl1W1 (x C u : ℝ) : ℝ :=
  2 * u * hl1d0 C * hl1d1 x C - 6 * hl1d1 x C * hsE0 x u
/-- `W₂ = 12 - 6S + u(d₁² + 2d₀d₂) - 6d₂E₀ - d₀J₂`. -/
noncomputable def hl1W2 (x C u : ℝ) : ℝ :=
  12 - 6 * (1 + x) + u * (hl1d1 x C ^ 2 + 2 * hl1d0 C * hl1d2 x C) - 6 * hl1d2 x C * hsE0 x u -
    hl1d0 C * hl1J2 x u
/-- `W₃ = d₁(2ud₂ - J₂)`. -/
noncomputable def hl1W3 (x C u : ℝ) : ℝ := hl1d1 x C * (2 * u * hl1d2 x C - hl1J2 x u)
/-- `W₄ = (S² - S + 1) + ud₂² - d₂J₂ = (S - d₂)(A₀ - ud₂)`. -/
noncomputable def hl1W4 (x C u : ℝ) : ℝ :=
  ((1 + x) ^ 2 - (1 + x) + 1) + u * hl1d2 x C ^ 2 - hl1d2 x C * hl1J2 x u

/-- `γ₀ = u/4 - E₀²/16`. -/
noncomputable def hl1g0 (x u : ℝ) : ℝ := u / 4 - hsE0 x u ^ 2 / 16
/-- `γ₂ = u(2 - S)/24 - E₀J₂/48`. -/
noncomputable def hl1g2 (x u : ℝ) : ℝ := u * (2 - (1 + x)) / 24 - hsE0 x u * hl1J2 x u / 48
/-- `γ₄ = (4u(S² - S + 1) - J₂²)/576 = -(Su - A₀)²/576`. -/
noncomputable def hl1g4 (x u : ℝ) : ℝ := (4 * u * ((1 + x) ^ 2 - (1 + x) + 1) - hl1J2 x u ^ 2) / 576

/-- Division of `W` by `Z = d + er`: `q₃ = W₄/e`. -/
noncomputable def hl1q3 (x C u : ℝ) : ℝ := hl1W4 x C u / (x - C)
/-- `q₂ = (W₃ - dq₃)/e`. -/
noncomputable def hl1q2 (x C u : ℝ) : ℝ := (hl1W3 x C u - (1 + C) * hl1q3 x C u) / (x - C)
/-- `q₁ = (W₂ - dq₂)/e`. -/
noncomputable def hl1q1 (x C u : ℝ) : ℝ := (hl1W2 x C u - (1 + C) * hl1q2 x C u) / (x - C)
/-- `q₀ = (W₁ - dq₁)/e`. -/
noncomputable def hl1q0 (x C u : ℝ) : ℝ := (hl1W1 x C u - (1 + C) * hl1q1 x C u) / (x - C)

/-- `b₄ = γ₄`. -/
noncomputable def hl1b4 (x u : ℝ) : ℝ := hl1g4 x u
/-- `b₃ = -q₃/96 = -W₄/(96e)`. -/
noncomputable def hl1b3 (x C u : ℝ) : ℝ := -hl1q3 x C u / 96
/-- `b₂ = γ₂ - q₂/96 + (2ud₂ - J₂)/96`. -/
noncomputable def hl1b2 (x C u : ℝ) : ℝ :=
  hl1g2 x u - hl1q2 x C u / 96 + (2 * u * hl1d2 x C - hl1J2 x u) / 96
/-- `b₁`. -/
noncomputable def hl1b1 (x C u : ℝ) : ℝ :=
  -hl1q1 x C u / 96 - 7 / 96 * (u - 1) * (x - C) + 2 * u * hl1d1 x C / 96
/-- `b₀`. -/
noncomputable def hl1b0 (x C u : ℝ) : ℝ :=
  hl1g0 x u - hl1q0 x C u / 96 - 7 / 96 * (u - 1) * (1 + C) +
    (2 * u * hl1d0 C - 6 * hsE0 x u) / 96 - 1 / 16 - 9193 / 50000
/-- The residue `Q = (119/4 - W(-d/e))/96`. -/
noncomputable def hl1Q1 (x C u : ℝ) : ℝ := -(hl1W0 x C u - 119 / 4 - (1 + C) * hl1q0 x C u) / 96

/-- `p₄ = γ₄ - W₄/336` (the `F₀` coefficients, `(A13)`). -/
noncomputable def hl1p4 (x C u : ℝ) : ℝ := hl1g4 x u - hl1W4 x C u / 336
/-- `p₃ = -W₃/336`. -/
noncomputable def hl1p3 (x C u : ℝ) : ℝ := -hl1W3 x C u / 336
/-- `p₂ = γ₂ - W₂/336 + (2ud₂ - J₂)/96`. -/
noncomputable def hl1p2 (x C u : ℝ) : ℝ :=
  hl1g2 x u - hl1W2 x C u / 336 + (2 * u * hl1d2 x C - hl1J2 x u) / 96
/-- `p₁`. -/
noncomputable def hl1p1 (x C u : ℝ) : ℝ :=
  -hl1W1 x C u / 336 - 7 / 96 * (u - 1) * (x - C) + 2 * u * hl1d1 x C / 96
/-- `p₀`. -/
noncomputable def hl1p0 (x C u : ℝ) : ℝ :=
  hl1g0 x u - hl1W0 x C u / 336 + 3 / 64 - 7 / 96 * (u - 1) * (1 + C) +
    (2 * u * hl1d0 C - 6 * hsE0 x u) / 96 - 9193 / 50000

/-! ### The generic reciprocal-shape function -/

/-- `g(r) = b₀ + b₁r + b₂r² + b₃r³ + b₄r⁴ + Q/(d + er) - cℓ(2(d + er)/7)`. -/
noncomputable def hl1G (b0 b1 b2 b3 b4 Q d e r : ℝ) : ℝ :=
  b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3 + b4 * r ^ 4 + Q / (d + e * r) -
    7 / 96 * hh1ell (2 * (d + e * r) / 7)

/-- `g'(r)`. -/
noncomputable def hl1G1 (b1 b2 b3 b4 Q d e r : ℝ) : ℝ :=
  b1 + 2 * b2 * r + 3 * b3 * r ^ 2 + 4 * b4 * r ^ 3 - Q * e / (d + e * r) ^ 2 -
    7 / 96 * hl1ell1 (2 * (d + e * r) / 7) * (2 * e / 7)

/-- `g''(r)`. -/
noncomputable def hl1G2 (b2 b3 b4 Q d e r : ℝ) : ℝ :=
  2 * b2 + 6 * b3 * r + 12 * b4 * r ^ 2 + 2 * Q * e ^ 2 / (d + e * r) ^ 3 -
    7 / 96 * hl1ell2 (2 * (d + e * r) / 7) * (2 * e / 7) ^ 2

theorem hl1G_hasDerivAt {b0 b1 b2 b3 b4 Q d e r : ℝ} (hZ : 0 < d + e * r) :
    HasDerivAt (hl1G b0 b1 b2 b3 b4 Q d e) (hl1G1 b1 b2 b3 b4 Q d e r) r := by
  have hZd : HasDerivAt (fun s => d + e * s) e r := by
    simpa using ((hasDerivAt_id' r).const_mul e).const_add d
  have hyd : HasDerivAt (fun s => 2 * (d + e * s) / 7) (2 * e / 7) r := by
    simpa using (hZd.const_mul 2).div_const 7
  have hy : -1 < 2 * (d + e * r) / 7 := by
    have : 0 < 2 * (d + e * r) / 7 := by positivity
    linarith
  have hl := (hl1_ell_hasDerivAt hy).comp r hyd
  have hid := hasDerivAt_id' r
  have hp := (((((hid.const_mul b1).const_add b0).add ((hid.fun_pow 2).const_mul b2)).add
    ((hid.fun_pow 3).const_mul b3)).add ((hid.fun_pow 4).const_mul b4)).add
      ((hasDerivAt_const r Q).fun_div hZd hZ.ne')
  have h := hp.sub (hl.const_mul (7 / 96))
  have hf : hl1G b0 b1 b2 b3 b4 Q d e = fun s => b0 + b1 * s + b2 * s ^ 2 + b3 * s ^ 3 +
      b4 * s ^ 4 + Q / (d + e * s) - 7 / 96 * hh1ell (2 * (d + e * s) / 7) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  unfold hl1G1
  norm_num
  field_simp
  ring

theorem hl1G1_hasDerivAt {b1 b2 b3 b4 Q d e r : ℝ} (hZ : 0 < d + e * r) :
    HasDerivAt (hl1G1 b1 b2 b3 b4 Q d e) (hl1G2 b2 b3 b4 Q d e r) r := by
  have hZd : HasDerivAt (fun s => d + e * s) e r := by
    simpa using ((hasDerivAt_id' r).const_mul e).const_add d
  have hyd : HasDerivAt (fun s => 2 * (d + e * s) / 7) (2 * e / 7) r := by
    simpa using (hZd.const_mul 2).div_const 7
  have hy : -1 < 2 * (d + e * r) / 7 := by
    have : 0 < 2 * (d + e * r) / 7 := by positivity
    linarith
  have hl := (hl1_ell1_hasDerivAt hy).comp r hyd
  have hid := hasDerivAt_id' r
  have hp := (((((hid.const_mul (2 * b2)).const_add b1).add ((hid.fun_pow 2).const_mul
    (3 * b3))).add ((hid.fun_pow 3).const_mul (4 * b4))).sub
      ((hasDerivAt_const r (Q * e)).fun_div (hZd.fun_pow 2) (pow_ne_zero 2 hZ.ne')))
  have h := hp.sub ((hl.mul_const (2 * e / 7)).const_mul (7 / 96))
  have hf : hl1G1 b1 b2 b3 b4 Q d e = fun s => b1 + 2 * b2 * s + 3 * b3 * s ^ 2 +
      4 * b4 * s ^ 3 - Q * e / (d + e * s) ^ 2 -
        7 / 96 * hl1ell1 (2 * (d + e * s) / 7) * (2 * e / 7) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]; ring
  unfold hl1G2
  norm_num
  field_simp
  ring

/-- **The curvature bound** `g'' ≤ 2b₂ + 6b₃r + 12b₄r² + 2Qe²/Z³ + ce²/Z²` for `0 < 2Z/7 ≤ 1`. -/
theorem hl1G2_le {b2 b3 b4 Q d e r : ℝ} (hZ : 0 < d + e * r) (hZ7 : 2 * (d + e * r) ≤ 7) :
    hl1G2 b2 b3 b4 Q d e r ≤ 2 * b2 + 6 * b3 * r + 12 * b4 * r ^ 2 +
      2 * Q * e ^ 2 / (d + e * r) ^ 3 + 7 / 96 * e ^ 2 / (d + e * r) ^ 2 := by
  have hy : 0 < 2 * (d + e * r) / 7 := by positivity
  have hl := hl1_ell2_ge hy (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hl (sq_nonneg (2 * e / 7))
  have h2 : -(1 / (2 * (d + e * r) / 7) ^ 2) * (2 * e / 7) ^ 2 = -(e ^ 2 / (d + e * r) ^ 2) := by
    field_simp
  rw [h2] at h1
  unfold hl1G2
  have : 7 / 96 * e ^ 2 / (d + e * r) ^ 2 = 7 / 96 * (e ^ 2 / (d + e * r) ^ 2) := by ring
  rw [this]
  nlinarith

/-- **Reciprocal-shape concavity**: if the curvature bound is nonpositive on `[r₀, r₁]` (with
`0 < Z`, `2Z ≤ 7` there), then `g ≥ min (g r₀) (g r₁)` on `[r₀, r₁]`. -/
theorem hl1G_min {b0 b1 b2 b3 b4 Q d e r0 r r1 : ℝ} (h0 : r0 ≤ r) (h1 : r ≤ r1)
    (hZ : ∀ s ∈ Icc r0 r1, 0 < d + e * s ∧ 2 * (d + e * s) ≤ 7)
    (hc : ∀ s ∈ Icc r0 r1, 2 * b2 + 6 * b3 * s + 12 * b4 * s ^ 2 +
      2 * Q * e ^ 2 / (d + e * s) ^ 3 + 7 / 96 * e ^ 2 / (d + e * s) ^ 2 ≤ 0) :
    min (hl1G b0 b1 b2 b3 b4 Q d e r0) (hl1G b0 b1 b2 b3 b4 Q d e r1) ≤
      hl1G b0 b1 b2 b3 b4 Q d e r :=
  hl1_conc_min h0 h1 (fun s hs => hl1G_hasDerivAt (hZ s hs).1)
    (fun s hs => hl1G1_hasDerivAt (hZ s hs).1)
    (fun s hs => (hl1G2_le (hZ s hs).1 (hZ s hs).2).trans (hc s hs))

/-! ### The two outer tests in the reciprocal shape -/

/-- The polynomial-in-`r` pieces at `α = 1/r`, `β = x + C(α - 1)`. -/
private theorem hl1o_pieces {x a b C u : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hb : b = x + C * (a - 1)) :
    hh1oG x a u = (4 * u * (36 + (12 - 6 * (1 + x)) * (1 / a) ^ 2 +
        ((1 + x) ^ 2 - (1 + x) + 1) * (1 / a) ^ 4) -
        (6 * hsE0 x u + hl1J2 x u * (1 / a) ^ 2) ^ 2) / 576 ∧
      hh1ow x a b u = (36 + (12 - 6 * (1 + x)) * (1 / a) ^ 2 +
        ((1 + x) ^ 2 - (1 + x) + 1) * (1 / a) ^ 4 +
        u * (hl1d0 C + hl1d1 x C * (1 / a) + hl1d2 x C * (1 / a) ^ 2) ^ 2 -
        (hl1d0 C + hl1d1 x C * (1 / a) + hl1d2 x C * (1 / a) ^ 2) *
          (6 * hsE0 x u + hl1J2 x u * (1 / a) ^ 2)) / 49 ∧
      hh1oEL x a b u = (2 * u * (hl1d0 C + hl1d1 x C * (1 / a) + hl1d2 x C * (1 / a) ^ 2) -
        (6 * hsE0 x u + hl1J2 x u * (1 / a) ^ 2)) / 7 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hD : hsDg x b a = a ^ 2 * (hl1d0 C + hl1d1 x C * (1 / a) + hl1d2 x C * (1 / a) ^ 2) := by
    rw [hb]; unfold hsDg hl1d0 hl1d1 hl1d2; field_simp; ring
  have hJ : hl1oJ x a u = a ^ 2 * (6 * hsE0 x u + hl1J2 x u * (1 / a) ^ 2) := by
    unfold hl1oJ hl1J2 hh1oK; field_simp; ring
  have hM : hl1oM x a = a ^ 4 * (36 + (12 - 6 * (1 + x)) * (1 / a) ^ 2 +
      ((1 + x) ^ 2 - (1 + x) + 1) * (1 / a) ^ 4) := by
    unfold hl1oM hh1oK; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hl1o_G hx ha0, hM, hJ]; field_simp
  · rw [hl1o_w hx ha0, hM, hJ, hD]; field_simp
  · rw [hl1o_EL hx ha0, hJ, hD]; field_simp

/-- **Division of the quartic `W` by `Z = d + er`** (`SHORT_OUTER_S_RECIPROCAL` (7)). -/
theorem hl1_div4 {x C u r : ℝ} (he : x - C ≠ 0) (hZ : 1 + C + (x - C) * r ≠ 0) :
    1 / (1 + C + (x - C) * r) * (7 * ((hl1W0 x C u + hl1W1 x C u * r + hl1W2 x C u * r ^ 2 +
      hl1W3 x C u * r ^ 3 + hl1W4 x C u * r ^ 4) / 49) - 17 / 4) =
      (hl1q3 x C u * r ^ 3 + hl1q2 x C u * r ^ 2 + hl1q1 x C u * r + hl1q0 x C u) / 7 +
        (hl1W0 x C u - 119 / 4 - (1 + C) * hl1q0 x C u) / (1 + C + (x - C) * r) / 7 := by
  unfold hl1q0 hl1q1 hl1q2 hl1q3
  generalize hl1W0 x C u = W0
  generalize hl1W1 x C u = W1
  generalize hl1W2 x C u = W2
  generalize hl1W3 x C u = W3
  generalize hl1W4 x C u = W4
  generalize x - C = e at he hZ ⊢
  generalize 1 + C = d at hZ ⊢
  field_simp
  ring

/-- **The reciprocal-shape form of `F₁`** (`SHORT_OUTER_S_RECIPROCAL` (6)-(8)). -/
theorem hl1o_F1_rG {x a b C u : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : b = x + C * (a - 1))
    (hCx : C < x) (hZ : 0 < 1 + C + (x - C) * (1 / a)) :
    hh1oF1 x a b u = hl1G (hl1b0 x C u) (hl1b1 x C u) (hl1b2 x C u) (hl1b3 x C u) (hl1b4 x u)
      (hl1Q1 x C u) (1 + C) (x - C) (1 / a) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hab : a + b = a * (1 + C + (x - C) * (1 / a)) := by rw [hb]; field_simp; ring
  have hab0 : a + b ≠ 0 := by rw [hab]; positivity
  obtain ⟨hG, hw, hE⟩ := hl1o_pieces (u := u) hx ha hb
  rw [hl1o_F1_R1 ha0 hab0, hG, hw, hE]
  have hy : hh1oy a b = 2 * (1 + C + (x - C) * (1 / a)) / 7 := by
    unfold hh1oy; rw [hab]; field_simp
  have h1 : a / (a + b) = 1 / (1 + C + (x - C) * (1 / a)) := by rw [hab]; field_simp
  have h2 : (a + b) / a = 1 + C + (x - C) * (1 / a) := by rw [hab]; field_simp
  rw [hy, mul_div_assoc, h2, h1]
  have he : x - C ≠ 0 := by linarith
  have hW : ∀ r : ℝ, 36 + (12 - 6 * (1 + x)) * r ^ 2 + ((1 + x) ^ 2 - (1 + x) + 1) * r ^ 4 +
      u * (hl1d0 C + hl1d1 x C * r + hl1d2 x C * r ^ 2) ^ 2 -
      (hl1d0 C + hl1d1 x C * r + hl1d2 x C * r ^ 2) * (6 * hsE0 x u + hl1J2 x u * r ^ 2) =
      hl1W0 x C u + hl1W1 x C u * r + hl1W2 x C u * r ^ 2 + hl1W3 x C u * r ^ 3 +
        hl1W4 x C u * r ^ 4 := by
    intro r; unfold hl1W0 hl1W1 hl1W2 hl1W3 hl1W4; ring
  rw [hW]
  have hdiv := hl1_div4 (x := x) (C := C) (u := u) (r := 1 / a) he hZ.ne'
  unfold hl1G hl1b0 hl1b1 hl1b2 hl1b3 hl1b4 hl1Q1 hl1g0 hl1g2 hl1g4
  linear_combination (-(7 / 96)) * hdiv

/-- **The reciprocal-shape form of `F₀`** (`SHORT_OUTER_LARGE_SHAPE_REDUCTION` (A14)): `Q = -c`. -/
theorem hl1o_F0_rG {x a b C u : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : b = x + C * (a - 1))
    (hZ : 0 < 1 + C + (x - C) * (1 / a)) :
    hh1oF0 x a b u = hl1G (hl1p0 x C u) (hl1p1 x C u) (hl1p2 x C u) (hl1p3 x C u) (hl1p4 x C u)
      (-(7 / 96)) (1 + C) (x - C) (1 / a) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hab : a + b = a * (1 + C + (x - C) * (1 / a)) := by rw [hb]; field_simp; ring
  have hab0 : a + b ≠ 0 := by rw [hab]; positivity
  obtain ⟨hG, hw, hE⟩ := hl1o_pieces (u := u) hx ha hb
  have hR : hh1oF0 x a b u = hh1oG x a u - 7 / 96 * (2 * hh1ow x a b u - 1 / 2 +
      (u - 1) * ((a + b) / a) + a / (a + b) - 1 / 7 - hh1oEL x a b u + hh1ell (hh1oy a b)) -
        9193 / 50000 := by
    unfold hh1oF0 hh1oR2; ring
  rw [hR, hG, hw, hE]
  have hy : hh1oy a b = 2 * (1 + C + (x - C) * (1 / a)) / 7 := by
    unfold hh1oy; rw [hab]; field_simp
  have h1 : a / (a + b) = 1 / (1 + C + (x - C) * (1 / a)) := by rw [hab]; field_simp
  have h2 : (a + b) / a = 1 + C + (x - C) * (1 / a) := by rw [hab]; field_simp
  rw [hy, h2, h1]
  unfold hl1G hl1p0 hl1p1 hl1p2 hl1p3 hl1p4 hl1g0 hl1g2 hl1g4 hl1W0 hl1W1 hl1W2 hl1W3 hl1W4
  generalize 1 / a = r at hZ ⊢
  generalize hh1ell (2 * (1 + C + (x - C) * r) / 7) = L
  generalize hsE0 x u = E0
  generalize hl1J2 x u = J2
  generalize hl1d0 C = d0
  generalize hl1d1 x C = d1
  generalize hl1d2 x C = d2
  field_simp
  ring

end SmoothedOctagon

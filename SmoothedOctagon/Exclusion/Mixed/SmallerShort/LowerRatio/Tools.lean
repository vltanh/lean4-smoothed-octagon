module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.PathDerivative
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.MonotonicityBounds

/-!
# Smaller-short window, lower ratio: shared one-variable tools and the factored outer source

Shared tools for the proofs of the two lower-ratio faces.

* One-variable calculus: a function with nonpositive second derivative on `[p, q]` is at least
  `min (f p) (f q)` (`lr_conc_min`); a function whose derivative is concave and positive at the
  left end is at least the smaller endpoint value (`lr_dconc_min`); a concave quadratic in the norm
  (`lr_conc3`, with `lro_F0_u3`, `lro_F1_u3`).
* The cubic logarithm majorant `ℓ(y) = 2s + (2/3)s³`, `s = (y - 1)/(y + 1)` (`lrell`): its
  derivatives `ℓ' = 8(y² + 1)/(y + 1)⁴`, `ℓ'' = -16(y² - y + 2)/(y + 1)⁵`,
  `ℓ''' = 16(3y² - 6y + 11)/(y + 1)⁶` and the comparisons `ℓ' ≤ 1/y`, `ℓ'' ≥ -1/y²` for
  `0 < y ≤ 1`.
* The factored outer source: `J = K E₀ + 2S - 1`, `M = K² - SK + S²`,
  `w = (M + uD² - DJ)/(49α⁴)`, `E_L = (2uD - J)/(7α²)`, `Γ_* = (4uM - J²)/(576α⁴)`, and the
  residual form `R₁ = (α/B)(7w - 17/4) + (u - 1)B/α - E_L + ℓ(y) + 6/7`.

## Main API

* `lr_conc_min`, `lr_dconc_min`, `lr_conc3`, `lro_F0_u3`, `lro_F1_u3`;
* `lrell1`, `lrell2`, `lrell3`, `lr_ell_hasDerivAt'`, `lr_ell1_hasDerivAt`,
  `lr_ell2_hasDerivAt`, `lr_ell1_le`, `lr_ell2_ge`;
* `lroJ`, `lroM`, `lro_w`, `lro_EL`, `lro_G`, `lro_F1_R1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### One-variable concavity -/

/-- **Concavity on an interval**: `f'' ≤ 0` on `[p, q]` gives `f ≥ min (f p) (f q)` there. -/
theorem lr_conc_min {f f' f'' : ℝ → ℝ} {p q t : ℝ} (hpt : p ≤ t) (htq : t ≤ q)
    (h1 : ∀ s ∈ Icc p q, HasDerivAt f (f' s) s) (h2 : ∀ s ∈ Icc p q, HasDerivAt f' (f'' s) s)
    (h3 : ∀ s ∈ Icc p q, f'' s ≤ 0) : min (f p) (f q) ≤ f t := by
  have hanti : ∀ s w, p ≤ s → s ≤ w → w ≤ q → f' w ≤ f' s := by
    intro s w hs hsw hw
    have key := ss_le_of_deriv (f := fun z => -f' z) (f' := fun z => -f'' z) hsw
      (fun z hz => (h2 z ⟨by linarith [hz.1], by linarith [hz.2]⟩).neg)
      (fun z hz => by
        have := h3 z ⟨by linarith [hz.1], by linarith [hz.2]⟩
        linarith)
    linarith
  rcases le_total 0 (f' t) with hp | hn
  · have key := ss_le_of_deriv (f := f) (f' := f') hpt
      (fun z hz => h1 z ⟨hz.1, by linarith [hz.2]⟩)
      (fun z hz => le_trans hp (hanti z t (by linarith [hz.1]) (by linarith [hz.2]) htq))
    exact (min_le_left _ _).trans key
  · have key := ss_le_of_deriv (f := fun z => -f z) (f' := fun z => -f' z) htq
      (fun z hz => (h1 z ⟨by linarith [hz.1], hz.2⟩).neg)
      (fun z hz => by
        have := hanti t z hpt (by linarith [hz.1]) (by linarith [hz.2])
        linarith)
    exact (min_le_right _ _).trans (by linarith)

/-- **A concave derivative positive at the left end**: if `f'` has nonpositive derivative `f'''`
on `[p, q]` (through `f''`) and `f'(p) > 0`, then `f ≥ min (f p) (f q)` on `[p, q]`. -/
theorem lr_dconc_min {f f' f'' f''' : ℝ → ℝ} {p q t : ℝ} (hpt : p ≤ t) (htq : t ≤ q)
    (h1 : ∀ s ∈ Icc p q, HasDerivAt f (f' s) s) (h2 : ∀ s ∈ Icc p q, HasDerivAt f' (f'' s) s)
    (h3 : ∀ s ∈ Icc p q, HasDerivAt f'' (f''' s) s) (h4 : ∀ s ∈ Icc p q, f''' s ≤ 0)
    (h0 : 0 < f' p) : min (f p) (f q) ≤ f t := by
  rcases le_total 0 (f' t) with hp | hn
  · -- `f' ≥ 0` on `[p, t]` by concavity of `f'`
    have key := ss_le_of_deriv (f := f) (f' := f') hpt
      (fun z hz => h1 z ⟨hz.1, by linarith [hz.2]⟩)
      (fun z hz => by
        have hm := lr_conc_min (f := f') (f' := f'') (f'' := f''') (p := p) (q := t) (t := z)
          hz.1.le hz.2.le (fun s hs => h2 s ⟨hs.1, by linarith [hs.2]⟩)
          (fun s hs => h3 s ⟨hs.1, by linarith [hs.2]⟩)
          (fun s hs => h4 s ⟨hs.1, by linarith [hs.2]⟩)
        exact le_trans (le_min h0.le hp) hm)
    exact (min_le_left _ _).trans key
  · -- `f' ≤ 0` on `[t, q]`: otherwise concavity on `[p, z]` would force `f'(t) ≥ 0`
    have key := ss_le_of_deriv (f := fun z => -f z) (f' := fun z => -f' z) htq
      (fun z hz => (h1 z ⟨by linarith [hz.1], hz.2⟩).neg)
      (fun z hz => by
        have hm := lr_conc_min (f := f') (f' := f'') (f'' := f''') (p := p) (q := z) (t := t)
          hpt hz.1.le (fun s hs => h2 s ⟨hs.1, by linarith [hs.2, hz.2]⟩)
          (fun s hs => h3 s ⟨hs.1, by linarith [hs.2, hz.2]⟩)
          (fun s hs => h4 s ⟨hs.1, by linarith [hs.2, hz.2]⟩)
        rcases le_total (f' p) (f' z) with h | h
        · rw [min_eq_left h] at hm; linarith
        · rw [min_eq_right h] at hm; linarith)
    exact (min_le_right _ _).trans (by linarith)

/-- A concave quadratic is at least the smaller of its endpoint values. -/
theorem lr_conc3 {f : ℝ → ℝ} {u1 u u2 κ : ℝ} (h1 : u1 ≤ u) (h2 : u ≤ u2) (hκ : 0 ≤ κ)
    (hid : ∀ s, (u2 - u1) * f s - (u2 - s) * f u1 - (s - u1) * f u2 =
      κ * (s - u1) * (u2 - s) * (u2 - u1)) : min (f u1) (f u2) ≤ f u := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h]; exact min_le_left _ _
  have h12 : 0 < u2 - u1 := by linarith
  have hm1 := min_le_left (f u1) (f u2)
  have hm2 := min_le_right (f u1) (f u2)
  have p1 := mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hm1)
  have p2 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hm2)
  have p3 := mul_nonneg (mul_nonneg (mul_nonneg hκ (sub_nonneg.2 h1)) (sub_nonneg.2 h2)) h12.le
  have e : (u2 - u1) * (f u - min (f u1) (f u2)) = (u2 - u) * (f u1 - min (f u1) (f u2)) +
      (u - u1) * (f u2 - min (f u1) (f u2)) + κ * (u - u1) * (u2 - u) * (u2 - u1) := by
    linear_combination hid u
  have key : 0 ≤ (u2 - u1) * (f u - min (f u1) (f u2)) := by rw [e]; linarith
  by_contra hc
  have := mul_neg_of_pos_of_neg h12 (sub_neg.2 (not_le.mp hc))
  linarith

/-- The outer `F₀` is a concave quadratic in the norm. -/
theorem lro_F0_u3 (x a b u1 u2 : ℝ) : ∀ s, (u2 - u1) * lroF0 x a b s -
    (u2 - s) * lroF0 x a b u1 - (s - u1) * lroF0 x a b u2 =
      (1 + x) ^ 2 * lroK a ^ 2 / (576 * a ^ 4) * (s - u1) * (u2 - s) * (u2 - u1) := by
  intro s
  simp only [lroF0, lroR2, lrow, lroEL, lroG, lroE]
  ring

/-- The outer `F₁` is a concave quadratic in the norm. -/
theorem lro_F1_u3 (x a b u1 u2 : ℝ) : ∀ s, (u2 - u1) * lroF1 x a b s -
    (u2 - s) * lroF1 x a b u1 - (s - u1) * lroF1 x a b u2 =
      (1 + x) ^ 2 * lroK a ^ 2 / (576 * a ^ 4) * (s - u1) * (u2 - s) * (u2 - u1) := by
  intro s
  simp only [lroF1, lroF0, lroR2, lrow, lroEL, lroG, lroE]
  ring

/-- Norm concavity of the outer `F₀`: `F₀(u) ≥ min (F₀(u₁), F₀(u₂))` for `u ∈ [u₁, u₂]`. -/
theorem lro_F0_umin {x a b u1 u u2 : ℝ} (h1 : u1 ≤ u) (h2 : u ≤ u2) (ha : a ≠ 0) :
    min (lroF0 x a b u1) (lroF0 x a b u2) ≤ lroF0 x a b u :=
  lr_conc3 (f := fun s => lroF0 x a b s) h1 h2 (by positivity) (lro_F0_u3 x a b u1 u2)

/-- Norm concavity of the outer `F₁`: `F₁(u) ≥ min (F₁(u₁), F₁(u₂))` for `u ∈ [u₁, u₂]`. -/
theorem lro_F1_umin {x a b u1 u u2 : ℝ} (h1 : u1 ≤ u) (h2 : u ≤ u2) (ha : a ≠ 0) :
    min (lroF1 x a b u1) (lroF1 x a b u2) ≤ lroF1 x a b u :=
  lr_conc3 (f := fun s => lroF1 x a b s) h1 h2 (by positivity) (lro_F1_u3 x a b u1 u2)

/-! ### The cubic logarithm majorant -/

/-- `ℓ'(y) = 8(y² + 1)/(y + 1)⁴`. -/
noncomputable def lrell1 (y : ℝ) : ℝ := 8 * (y ^ 2 + 1) / (y + 1) ^ 4

/-- `ℓ''(y) = -16(y² - y + 2)/(y + 1)⁵`. -/
noncomputable def lrell2 (y : ℝ) : ℝ := -16 * (y ^ 2 - y + 2) / (y + 1) ^ 5

/-- `ℓ'''(y) = 16(3y² - 6y + 11)/(y + 1)⁶`. -/
noncomputable def lrell3 (y : ℝ) : ℝ := 16 * (3 * y ^ 2 - 6 * y + 11) / (y + 1) ^ 6

theorem lr_ell_hasDerivAt' {y : ℝ} (hy : -1 < y) : HasDerivAt lrell (lrell1 y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have hz : HasDerivAt (fun s => (s - 1) / (s + 1))
      (((1 : ℝ) * (y + 1) - (y - 1) * 1) / (y + 1) ^ 2) y :=
    ((hasDerivAt_id' y).sub_const 1).fun_div ((hasDerivAt_id' y).add_const 1) h1
  have h := (hz.const_mul 2).add ((hz.fun_pow 3).const_mul (2 / 3))
  have hf : lrell = fun s => 2 * ((s - 1) / (s + 1)) + 2 / 3 * ((s - 1) / (s + 1)) ^ 3 := rfl
  rw [hf]
  convert h using 1
  unfold lrell1
  norm_num
  field_simp
  ring

theorem lr_ell1_hasDerivAt {y : ℝ} (hy : -1 < y) : HasDerivAt lrell1 (lrell2 y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have h := ((((hasDerivAt_id' y).fun_pow 2).add_const 1).const_mul 8).fun_div
    (((hasDerivAt_id' y).add_const 1).fun_pow 4) (pow_ne_zero 4 h1)
  have hf : lrell1 = fun s => 8 * (s ^ 2 + 1) / (s + 1) ^ 4 := rfl
  rw [hf]
  convert h using 1
  unfold lrell2
  norm_num
  field_simp
  ring

theorem lr_ell2_hasDerivAt {y : ℝ} (hy : -1 < y) : HasDerivAt lrell2 (lrell3 y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have h := (((((hasDerivAt_id' y).fun_pow 2).sub (hasDerivAt_id' y)).add_const 2).const_mul
    (-16)).fun_div (((hasDerivAt_id' y).add_const 1).fun_pow 5) (pow_ne_zero 5 h1)
  have hf : lrell2 = fun s => -16 * (s ^ 2 - s + 2) / (s + 1) ^ 5 := rfl
  rw [hf]
  convert h using 1
  unfold lrell3
  simp only [Pi.sub_apply]
  norm_num
  field_simp
  ring

/-- `ℓ'(y) ≤ 1/y` for `y > 0`: `1/y - ℓ'(y) = (y - 1)⁴/(y(y + 1)⁴)`. -/
theorem lr_ell1_le {y : ℝ} (hy : 0 < y) : lrell1 y ≤ 1 / y := by
  have key : 1 / y - lrell1 y = (y - 1) ^ 4 / (y * (y + 1) ^ 4) := by
    unfold lrell1
    have h2 : y + 1 ≠ 0 := by linarith
    field_simp
    ring
  have : 0 ≤ (y - 1) ^ 4 / (y * (y + 1) ^ 4) := by positivity
  linarith

/-- `ℓ'(y) ≥ 0`. -/
theorem lr_ell1_nonneg (y : ℝ) : 0 ≤ lrell1 y := by unfold lrell1; positivity

/-- `ℓ''(y) ≥ -1/y²` for `0 < y ≤ 1`: `ℓ'' + 1/y² = (1 - y)³(1 + 8y - y²)/(y²(y + 1)⁵)`. -/
theorem lr_ell2_ge {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : -(1 / y ^ 2) ≤ lrell2 y := by
  have h1 : 0 < y + 1 := by linarith
  have key : lrell2 y + 1 / y ^ 2 = (1 - y) ^ 3 * (1 + 8 * y - y ^ 2) / (y ^ 2 * (y + 1) ^ 5) := by
    unfold lrell2
    have h2 : y + 1 ≠ 0 := h1.ne'
    field_simp
    ring
  have : 0 ≤ (1 - y) ^ 3 * (1 + 8 * y - y ^ 2) / (y ^ 2 * (y + 1) ^ 5) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (pow_nonneg (by linarith) 3) (by nlinarith)
  linarith

/-- `ℓ''(y) ≤ 0` for `y > -1`. -/
theorem lr_ell2_nonpos {y : ℝ} (hy : -1 < y) : lrell2 y ≤ 0 := by
  unfold lrell2
  have h1 : 0 < y + 1 := by linarith
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith [sq_nonneg (y - 1 / 2)]

/-! ### The factored outer source -/

/-- `J = K E₀ + 2S - 1`. -/
noncomputable def lroJ (x a u : ℝ) : ℝ := lroK a * ssE0 x u + 2 * (1 + x) - 1

/-- `M = K² - SK + S²`. -/
noncomputable def lroM (x a : ℝ) : ℝ := lroK a ^ 2 - (1 + x) * lroK a + (1 + x) ^ 2

theorem lro_w {x a b u : ℝ} (hx : 0 < x) (ha : a ≠ 0) :
    lrow x a b u = (lroM x a + u * ssDg x b a ^ 2 - ssDg x b a * lroJ x a u) / (49 * a ^ 4) := by
  have hK : lroK a ≠ 0 := by unfold lroK; positivity
  simp only [lrow, lroL, lrod, lrov, lroE, lroM, lroJ, ssE0]
  field_simp
  ring

theorem lro_EL {x a b u : ℝ} (hx : 0 < x) (ha : a ≠ 0) :
    lroEL x a b u = (2 * u * ssDg x b a - lroJ x a u) / (7 * a ^ 2) := by
  have hK : lroK a ≠ 0 := by unfold lroK; positivity
  simp only [lroEL, lroL, lrod, lroE, lroJ, ssE0]
  field_simp
  ring

theorem lro_G {x a u : ℝ} (hx : 0 < x) (ha : a ≠ 0) :
    lroG x a u = (4 * u * lroM x a - lroJ x a u ^ 2) / (576 * a ^ 4) := by
  have hK : lroK a ≠ 0 := by unfold lroK; positivity
  simp only [lroG, lrov, lroE, lroM, lroJ, ssE0]
  field_simp
  ring

/-- **The residual form of `F₁`**:
`F₁ = Γ_* - c[(α/B)(7w - 17/4) + (u - 1)B/α - E_L + ℓ(y) + 6/7] - g`. -/
theorem lro_F1_R1 {x a b u : ℝ} (ha : a ≠ 0) (hab : a + b ≠ 0) :
    lroF1 x a b u = lroG x a u - 7 / 96 * (a / (a + b) * (7 * lrow x a b u - 17 / 4) +
      (u - 1) * (a + b) / a - lroEL x a b u + lrell (lroy a b) + 6 / 7) - 9193 / 50000 := by
  simp only [lroF1, lroF0, lroR2, lroT]
  field_simp
  ring

end SmoothedOctagon

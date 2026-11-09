module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandBase

/-!
# Gate S1 by hand: the outer `F₁` as a function of `B = α + β`

With `η = x - α`,
`D₀ = (α + 1)(2x + 1 - α)` the transport numerator is `D = D₀ - 2ηB`, so `w = w₀ + w₁B + w₂B²` is
quadratic in `B` and
`F₁ = Γ_* - c[A₀ + A₁B + α(7w₀ - 17/4)/B + ℓ(2B/(7α))] - g` (`hl1o_F1_B`), with the
division coefficient `w₀ = (M + uD₀² - D₀J)/(49α⁴)` (the formal value at `β = -α`).
The bracket `φ(B) = A₀ + A₁B + γ/B + ℓ(kB)` is convex when `2γ ≥ B` and `0 < kB ≤ 1`, by
`ℓ'' ≥ -1/y²`. Hence `β ↦ F₁` is concave (`hl1o_F1_bmin`) and its
increments are controlled by the right-end derivative (`hl1_phi_incr`).

## Main API

* `hl1oD0`, `hl1ow0`, `hl1oA0`, `hl1oA1`, `hl1o_F1_B`;
* `hl1phi`, `hl1phi1`, `hl1phi2`, `hl1_phi_hasDerivAt`, `hl1_phi1_hasDerivAt`, `hl1_phi2_nonneg`;
* `hl1_phi_incr`, `hl1o_F1_bmin`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `D₀ = (α + 1)(2x + 1 - α)`, the value of `D` at `β = -α`. -/
noncomputable def hl1oD0 (x a : ℝ) : ℝ := (a + 1) * (2 * x + 1 - a)

/-- The division coefficient `w₀ = (M + uD₀² - D₀J)/(49α⁴)`. -/
noncomputable def hl1ow0 (x a u : ℝ) : ℝ :=
  (hl1oM x a + u * hl1oD0 x a ^ 2 - hl1oD0 x a * hl1oJ x a u) / (49 * a ^ 4)

/-- `A₀ = 7αw₁ + 6/7 - (2uD₀ - J)/(7α²)`, `w₁ = 2η(J - 2uD₀)/(49α⁴)`. -/
noncomputable def hl1oA0 (x a u : ℝ) : ℝ :=
  7 * a * (2 * (x - a) * (hl1oJ x a u - 2 * u * hl1oD0 x a) / (49 * a ^ 4)) + 6 / 7 -
    (2 * u * hl1oD0 x a - hl1oJ x a u) / (7 * a ^ 2)

/-- `A₁ = 7αw₂ + (u - 1)/α + 4uη/(7α²) = 4ux(x - α)/(7α³) + (u - 1)/α`. -/
noncomputable def hl1oA1 (x a u : ℝ) : ℝ := 4 * u * x * (x - a) / (7 * a ^ 3) + (u - 1) / a

/-- **The `B`-form of `F₁`**: `F₁ = Γ_* - c[A₀ + A₁B + α(7w₀ - 17/4)/B + ℓ(2B/(7α))] - g`,
`B = α + β`. -/
theorem hl1o_F1_B {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : 0 < a + b) :
    hh1oF1 x a b u = hh1oG x a u - 7 / 96 * (hl1oA0 x a u + hl1oA1 x a u * (a + b) +
      a * (7 * hl1ow0 x a u - 17 / 4) / (a + b) + hh1ell (2 / (7 * a) * (a + b))) - 9193 / 50000 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hab0 : a + b ≠ 0 := hab.ne'
  rw [hl1o_F1_R1 ha0 hab0, hl1o_w hx ha0, hl1o_EL hx ha0]
  have hy : hh1oy a b = 2 / (7 * a) * (a + b) := by unfold hh1oy; field_simp
  rw [hy]
  have hD : hsDg x b a = hl1oD0 x a - 2 * (x - a) * (a + b) := by
    unfold hsDg hl1oD0; ring
  rw [hD]
  unfold hl1ow0 hl1oA0 hl1oA1
  generalize hl1oM x a = M
  generalize hl1oJ x a u = J
  generalize hl1oD0 x a = D0
  generalize hh1ell (2 / (7 * a) * (a + b)) = L
  field_simp
  ring

/-! ### The convex bracket `φ(B) = p + qB + γ/B + ℓ(kB)` -/

/-- `φ(B) = p + qB + γ/B + ℓ(kB)`. -/
noncomputable def hl1phi (p q γ k B : ℝ) : ℝ := p + q * B + γ / B + hh1ell (k * B)

/-- `φ'(B) = q - γ/B² + kℓ'(kB)`. -/
noncomputable def hl1phi1 (q γ k B : ℝ) : ℝ := q - γ / B ^ 2 + k * hl1ell1 (k * B)

/-- `φ''(B) = 2γ/B³ + k²ℓ''(kB)`. -/
noncomputable def hl1phi2 (γ k B : ℝ) : ℝ := 2 * γ / B ^ 3 + k ^ 2 * hl1ell2 (k * B)

theorem hl1_phi_hasDerivAt {p q γ k B : ℝ} (hB : 0 < B) (hk : 0 < k) :
    HasDerivAt (hl1phi p q γ k) (hl1phi1 q γ k B) B := by
  have hkB : -1 < k * B := by nlinarith [mul_pos hk hB]
  have hl := (hl1_ell_hasDerivAt hkB).comp B ((hasDerivAt_id' B).const_mul k)
  have h := (((hasDerivAt_id' B).const_mul q).const_add p).add
    ((hasDerivAt_const B γ).fun_div (hasDerivAt_id' B) hB.ne')
  have h2 := h.add hl
  have hf : hl1phi p q γ k = fun s => p + q * s + γ / s + hh1ell (k * s) := rfl
  rw [hf]
  convert h2 using 1
  · funext s; simp only [Pi.add_apply, Function.comp_apply]
  unfold hl1phi1
  try simp only [Function.comp_apply]
  field_simp
  ring

theorem hl1_phi1_hasDerivAt {q γ k B : ℝ} (hB : 0 < B) (hk : 0 < k) :
    HasDerivAt (hl1phi1 q γ k) (hl1phi2 γ k B) B := by
  have hkB : -1 < k * B := by nlinarith [mul_pos hk hB]
  have hl := (hl1_ell1_hasDerivAt hkB).comp B ((hasDerivAt_id' B).const_mul k)
  have h := ((hasDerivAt_const B q).sub ((hasDerivAt_const B γ).fun_div
    ((hasDerivAt_id' B).fun_pow 2) (pow_ne_zero 2 hB.ne'))).add (hl.const_mul k)
  have hf : hl1phi1 q γ k = fun s => q - γ / s ^ 2 + k * hl1ell1 (k * s) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  unfold hl1phi2
  try simp only [Function.comp_apply]
  norm_num
  field_simp

/-- `φ'' ≥ (2γ - B)/B³ ≥ 0` when `2γ ≥ B`, `0 < kB ≤ 1`. -/
theorem hl1_phi2_nonneg {γ k B : ℝ} (hB : 0 < B) (hk : 0 < k) (hkB : k * B ≤ 1)
    (hγ : B ≤ 2 * γ) : 0 ≤ hl1phi2 γ k B := by
  have hl := hl1_ell2_ge (mul_pos hk hB) hkB
  have h1 : k ^ 2 * (-(1 / (k * B) ^ 2)) = -(1 / B ^ 2) := by field_simp
  have h2 := mul_le_mul_of_nonneg_left hl (sq_nonneg k)
  rw [h1] at h2
  unfold hl1phi2
  have h3 : 1 / B ^ 2 ≤ 2 * γ / B ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hB 2]
  linarith

/-- **Increment bound for a convex bracket**: on `[B₁, B₂]` with `2γ ≥ B₂`, `kB₂ ≤ 1`,
`φ(t) - φ(s) ≤ φ'(B₂)(t - s)` for `B₁ ≤ s ≤ t ≤ B₂`. -/
theorem hl1_phi_incr {p q γ k B1 B2 s t : ℝ} (hB1 : 0 < B1) (hk : 0 < k) (hkB : k * B2 ≤ 1)
    (hγ : B2 ≤ 2 * γ) (hs : B1 ≤ s) (hst : s ≤ t) (ht : t ≤ B2) :
    hl1phi p q γ k t - hl1phi p q γ k s ≤ hl1phi1 q γ k B2 * (t - s) := by
  have hmono : ∀ z ∈ Icc s B2, hl1phi1 q γ k z ≤ hl1phi1 q γ k B2 := by
    intro z hz
    exact ss_le_of_deriv (f := hl1phi1 q γ k) (f' := hl1phi2 γ k) hz.2
      (fun w hw => hl1_phi1_hasDerivAt (by linarith [hw.1, hz.1]) hk)
      (fun w hw => hl1_phi2_nonneg (by linarith [hw.1, hz.1]) hk
        (by nlinarith [hw.2]) (by linarith [hw.2]))
  have key := ss_le_of_deriv (f := fun z => hl1phi1 q γ k B2 * z - hl1phi p q γ k z)
    (f' := fun z => hl1phi1 q γ k B2 - hl1phi1 q γ k z) hst
    (fun z hz => ((hasDerivAt_id' z).const_mul _).sub (hl1_phi_hasDerivAt
      (by linarith [hz.1]) hk) |>.congr_deriv (by ring))
    (fun z hz => by
      have := hmono z ⟨hz.1.le, by linarith [hz.2]⟩
      linarith)
  linarith

/-- **Concavity of `β ↦ F₁`**: if
`2α(7w₀ - 17/4) ≥ α + β₂` and `2(α + β₂) ≤ 7α`, then `F₁(β) ≥ min (F₁(β₁), F₁(β₂))` on
`[β₁, β₂]`, `α + β₁ > 0`. -/
theorem hl1o_F1_bmin {x a b1 b b2 u : ℝ} (hx : 0 < x) (ha : 0 < a) (hb1 : 0 < a + b1)
    (h1 : b1 ≤ b) (h2 : b ≤ b2) (hk : 2 * (a + b2) ≤ 7 * a)
    (hγ : a + b2 ≤ 2 * (a * (7 * hl1ow0 x a u - 17 / 4))) :
    min (hh1oF1 x a b1 u) (hh1oF1 x a b2 u) ≤ hh1oF1 x a b u := by
  have hk0 : 0 < 2 / (7 * a) := by positivity
  set φ := hl1phi (hl1oA0 x a u) (hl1oA1 x a u) (a * (7 * hl1ow0 x a u - 17 / 4)) (2 / (7 * a))
    with hφ
  have hF : ∀ c, 0 < a + c → hh1oF1 x a c u = hh1oG x a u - 7 / 96 * φ (a + c) - 9193 / 50000 := by
    intro c hc
    rw [hl1o_F1_B hx ha hc, hφ]
    simp only [hl1phi]
  have hkB : 2 / (7 * a) * (a + b2) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
  -- `-φ` is concave on `[a + b₁, a + b₂]`
  have hm := hl1_conc_min (f := fun B => -φ B)
    (f' := fun B => -hl1phi1 (hl1oA1 x a u) (a * (7 * hl1ow0 x a u - 17 / 4)) (2 / (7 * a)) B)
    (f'' := fun B => -hl1phi2 (a * (7 * hl1ow0 x a u - 17 / 4)) (2 / (7 * a)) B)
    (p := a + b1) (q := a + b2) (t := a + b) (by linarith) (by linarith)
    (fun s hs => (hl1_phi_hasDerivAt (by linarith [hs.1]) hk0).neg)
    (fun s hs => (hl1_phi1_hasDerivAt (by linarith [hs.1]) hk0).neg)
    (fun s hs => by
      have := hl1_phi2_nonneg (γ := a * (7 * hl1ow0 x a u - 17 / 4)) (by linarith [hs.1]) hk0
        (le_trans (mul_le_mul_of_nonneg_left hs.2 hk0.le) hkB) (by linarith [hs.2])
      linarith)
  rw [hF b1 hb1, hF b (by linarith), hF b2 (by linarith)]
  rcases le_total (φ (a + b1)) (φ (a + b2)) with h | h
  · rw [min_eq_right (by linarith)]
    rw [min_eq_right (by linarith)] at hm
    linarith
  · rw [min_eq_left (by linarith)]
    rw [min_eq_left (by linarith)] at hm
    linarith

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2c

/-!
# Gate S4, hand proof W2: `Ψ` increases in the shape parameter `e` on the curve

The sign proved is `Ψ_e/(xd) > 0`. On the actual shape curve `a = 1 + ed`, `b = x(1 + d)`,
`u = ū(x, b)`, only `a` depends on `e`, so it suffices that `a ↦ Ψ(x, a, b, u)` is nondecreasing on
`[1, 22/19]`. By `S4HandW2a`-`S4HandW2c`, with `c = a - 1`, `h = x - 2`, `z = b - x ≥ 0`,

`28a²B²K²Ψ_a = (P_* + T₁z + T₂z² + T₃z³) + (4u - 3)(U₀ + U₁z + U₂z² + U₃z³) > 0`

for `u ≥ 3/4` (`U_i > 0` and `P_* > 19` are proved in `S4HandW2c`). The incoming norm
`ū(x, x(1 + d))` lies in `[3/4, 19/25]` (`hl46_w2_ubar_mem`); only `ū ≥ 3/4` is used.

The dependence on `b` is controlled by the positivity of the `z`-coefficients `T₁, T₂, T₃` of
the same numerator (`S4HandW2b`).

## Main API

* `hl46_w2_ubar_mem`: `3/4 ≤ ū(x, x(1 + d)) ≤ 19/25`.
* `hl46_W2`: `Ψ` is nondecreasing in `e` on the curve.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- On `b = x(1 + d)` the incoming upper norm `ū(x, b)` lies in `[3/4, 19/25]`:
`2(x - 1)²/((x + 1)(35x + 13)) ≤ 1/103` and `(b - x)³/(48x²) ≤ (b - 1)/100000`. -/
theorem hl46_w2_ubar_mem {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) :
    3 / 4 ≤ hsUbar x (x * (1 + d)) ∧ hsUbar x (x * (1 + d)) ≤ 19 / 25 := by
  have hb1 : 1 ≤ x * (1 + d) - 1 := by nlinarith
  have e : x * (1 + d) - x = x * d := by ring
  have hx1 : 0 ≤ x - 1 := by linarith
  have hJ : 0 ≤ 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) := by
    apply div_nonneg _ (by positivity)
    positivity
  have hJ' : 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) ≤ (x * (1 + d) - 1) / 103 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : 0 ≤ (x - 2) * (13 / 6 - x) := mul_nonneg (by linarith) (by linarith)
    have h3 : 206 * (x - 1) ^ 2 ≤ (x + 1) * (35 * x + 13) := by nlinarith
    have h4 : x - 1 ≤ x * (1 + d) - 1 := by nlinarith
    have h5 : 0 ≤ (x + 1) * (35 * x + 13) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hx1, mul_le_mul_of_nonneg_right h4 h5]
  have hT : 0 ≤ (x * (1 + d) - x) ^ 3 / (48 * x ^ 2) := by
    rw [e]
    have : 0 ≤ x * d := by nlinarith
    positivity
  have hT' : (x * (1 + d) - x) ^ 3 / (48 * x ^ 2) ≤ (x * (1 + d) - 1) / 100000 := by
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : d ^ 3 ≤ (1 / 19) ^ 3 := pow_le_pow_left₀ hd hd' 3
    have h2 : (x * d) ^ 3 = x ^ 2 * (x * d ^ 3) := by ring
    rw [h2]
    have h3 : x * d ^ 3 ≤ 13 / 6 * (1 / 19) ^ 3 := by nlinarith [pow_nonneg hd 3]
    have h4 : 0 ≤ x ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4, mul_le_mul_of_nonneg_left hb1 h4]
  unfold hsUbar
  constructor
  · have := div_nonneg (add_nonneg hJ hT) (by linarith : (0 : ℝ) ≤ x * (1 + d) - 1)
    linarith
  · have : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (x * (1 + d) - x) ^ 3 / (48 * x ^ 2)) /
        (x * (1 + d) - 1) ≤ 1 / 103 + 1 / 100000 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith

/-- **W2**: `Ψ` increases in `e` on the curve. -/
theorem hl46_W2 {x d e₁ e₂ : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19)
    (h1 : 13 / 5 ≤ e₁) (h12 : e₁ ≤ e₂) (h2 : e₂ ≤ 3) : hl46PsiC x d e₁ ≤ hl46PsiC x d e₂ := by
  have hu := (hl46_w2_ubar_mem hx hx' hd hd').1
  unfold hl46PsiC
  generalize hsUbar x (x * (1 + d)) = u at hu ⊢
  have hx0 : 0 < x := by linarith
  have hb : x ≤ x * (1 + d) := by nlinarith
  generalize x * (1 + d) = b at hb ⊢
  have hpos : ∀ y ∈ Icc (1 : ℝ) (22 / 19),
      0 ≤ -hl46W2V x b y u / (7 * y ^ 2 * (y + b) ^ 2 * (x * (x + 2) + y ^ 2) ^ 2) := by
    intro y hy
    have e := hl46_w2_V_eq (y - 1) (x - 2) (b - x) u
    rw [show 2 + (x - 2) + (b - x) = b by ring, show 2 + (x - 2) = x by ring,
      show 1 + (y - 1) = y by ring] at e
    have hT := hl46_w2_Tz_pos (c := y - 1) (h := x - 2) (z := b - x) (by linarith [hy.1])
      (by linarith [hy.2]) (by linarith) (by linarith) (by linarith)
    have hU := hl46_w2_Uz_nonneg (c := y - 1) (h := x - 2) (z := b - x) (by linarith [hy.1])
      (by linarith [hy.2]) (by linarith) (by linarith) (by linarith)
    have hm : 0 ≤ (4 * u - 3) * hl46W2Uz (y - 1) (x - 2) (b - x) := mul_nonneg (by linarith) hU
    have hV : hl46W2V x b y u ≤ 0 := by
      rw [e]
      linarith
    exact div_nonneg (by linarith) (by positivity)
  have ha1 : 1 ≤ 1 + e₁ * d := by nlinarith
  have ha12 : 1 + e₁ * d ≤ 1 + e₂ * d := by nlinarith
  have ha2 : 1 + e₂ * d ≤ 22 / 19 := by nlinarith
  exact hl46_mono_of (f := fun y => hh46S4PsiC x b y u)
    (f₁ := fun y => -hl46W2V x b y u / (7 * y ^ 2 * (y + b) ^ 2 * (x * (x + 2) + y ^ 2) ^ 2))
    (fun y hy => hl46_w2_deriv hx0 (by linarith [hy.1]) (by linarith)) hpos ha1 ha12 ha2

end SmoothedOctagon

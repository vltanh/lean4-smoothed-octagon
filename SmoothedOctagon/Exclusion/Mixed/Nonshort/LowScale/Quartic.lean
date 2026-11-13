module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Absorbing the negative quadratic term of a quartic

The function `y²(1-4y)` attains its maximum `1/108` at `y=1/6`.
The identity `(1-6y)²(1+12y)=1-108y²+432y³` proves this directly.
If the cubic tail absorbs the negative quadratic coefficient, only
half the positive constant term is needed.
-/

@[expose] public section

namespace SmoothedOctagon

/-- A negative quadratic coefficient is absorbed by the cubic tail and the constant term. -/
theorem nsr_quartic_cubic_tail {a b c d e y : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hc : 0 ≤ c + 54 * a) (hcd : 0 ≤ d + 4 * c) (hy : 0 ≤ y) :
    0 < a + b * y + c * y ^ 2 + d * y ^ 3 + e * y ^ 4 := by
  by_cases hc0 : 0 ≤ c
  · positivity
  have hc0 : 0 ≤ -c := by linarith only [hc0]
  have hsq : 0 ≤ (1 - 6 * y) ^ 2 * (1 + 12 * y) := by positivity
  have hbound := mul_nonneg hc0 hsq
  have hlin := mul_nonneg hb hy
  have htail := mul_nonneg hcd (pow_nonneg hy 3)
  have hlast := mul_nonneg he (pow_nonneg hy 4)
  linear_combination (1 / 108 : ℝ) * hbound + hlin + htail + hlast
    + (1 / 108 : ℝ) * hc + (1 / 2 : ℝ) * ha

end SmoothedOctagon

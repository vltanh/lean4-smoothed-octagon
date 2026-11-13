module

public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv

/-!
# Case M2, forward successor: small tools for the low-`t` large-gap signs

Elementary one-variable tools for the proofs of the low-`t` signs:

* `nlt_pw`: `z^(k+1) ≤ w z^k` on `0 ≤ z ≤ w`, the step of every termwise monomial bound on an
  interval (a negative monomial is absorbed into the next lower power);
* `nlt_lo`, `nlt_hi`: monomial comparisons `aʳ xˢ ≤ tʳ xˢ ≤ bʳ xˢ` on `a ≤ t ≤ b`;
* `nlt_taylor3`: the cubic Taylor lower bound from a lower bound of the third derivative.

## Main API

* `nlt_pw`, `nlt_lo`, `nlt_hi`, `nlt_taylor3`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `z^(k+1) ≤ w z^k` for `0 ≤ z ≤ w`. -/
theorem nlt_pw {z w : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ w) (k : ℕ) : z ^ (k + 1) ≤ w * z ^ k := by
  rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_right h1 (pow_nonneg h0 k)

/-- Monomial comparison from below: `c xˢ ≤ tʳ xˢ` for `0 ≤ a ≤ t`, `aʳ = c`, `0 ≤ x`. -/
theorem nlt_lo (r s : ℕ) {t x a c : ℝ} (hc : a ^ r = c) (ha : 0 ≤ a) (h : a ≤ t) (hx : 0 ≤ x) :
    c * x ^ s ≤ t ^ r * x ^ s := by
  rw [← hc]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha h r) (pow_nonneg hx s)

/-- Monomial comparison from above: `tʳ xˢ ≤ c xˢ` for `0 ≤ t ≤ b`, `bʳ = c`, `0 ≤ x`. -/
theorem nlt_hi (r s : ℕ) {t x b c : ℝ} (hc : b ^ r = c) (ht : 0 ≤ t) (h : t ≤ b) (hx : 0 ≤ x) :
    t ^ r * x ^ s ≤ c * x ^ s := by
  rw [← hc]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht h r) (pow_nonneg hx s)

/-- **The cubic Taylor lower bound**: if `f''' ≥ c` on `[a, b]`, then for `s ∈ [a, b]`,
`f(s) ≥ f(a) + (s - a)f'(a) + (s - a)²f''(a)/2 + c(s - a)³/6`. -/
theorem nlt_taylor3 {f f1 f2 f3 : ℝ → ℝ} {a b c : ℝ} (hd0 : ∀ s, HasDerivAt f (f1 s) s)
    (hd1 : ∀ s, HasDerivAt f1 (f2 s) s) (hd2 : ∀ s, HasDerivAt f2 (f3 s) s)
    (h3 : ∀ s, a ≤ s → s ≤ b → c ≤ f3 s) {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    f a + (s - a) * f1 a + (s - a) ^ 2 / 2 * f2 a + c * (s - a) ^ 3 / 6 ≤ f s := by
  have g2 : ∀ w, a ≤ w → w ≤ b → f2 a + c * (w - a) ≤ f2 w := by
    intro w h1 h2
    have hd : ∀ v, HasDerivAt (fun v => f2 v - c * (v - a)) (f3 v - c) v := fun v =>
      ((hd2 v).sub (((hasDerivAt_id v).sub_const a).const_mul c)).congr_deriv (by simp)
    have := poly_mono hd (fun v h1 h2 => by linarith [h3 v h1 h2]) le_rfl h1 h2
    simp only [sub_self, mul_zero, sub_zero] at this
    linarith
  have g1 : ∀ w, a ≤ w → w ≤ b → f1 a + (w - a) * f2 a + c * (w - a) ^ 2 / 2 ≤ f1 w := by
    intro w h1 h2
    have hd : ∀ v, HasDerivAt (fun v => f1 v - ((v - a) * f2 a + c * (v - a) ^ 2 / 2))
        (f2 v - (f2 a + c * (v - a))) v := fun v => by
      have e1 := ((hasDerivAt_id v).sub_const a).mul_const (f2 a)
      have e2 := ((((hasDerivAt_id v).sub_const a).pow 2).const_mul c).div_const 2
      exact ((hd1 v).sub (e1.add e2)).congr_deriv (by simp; ring)
    have := poly_mono hd (fun v h1 h2 => by linarith [g2 v h1 h2]) le_rfl h1 h2
    simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, add_zero, sub_zero] at this
    linarith
  have hd : ∀ v, HasDerivAt
      (fun v => f v - ((v - a) * f1 a + (v - a) ^ 2 / 2 * f2 a + c * (v - a) ^ 3 / 6))
      (f1 v - (f1 a + (v - a) * f2 a + c * (v - a) ^ 2 / 2)) v := fun v => by
    have e1 := ((hasDerivAt_id v).sub_const a).mul_const (f1 a)
    have e2 := ((((hasDerivAt_id v).sub_const a).pow 2).div_const 2).mul_const (f2 a)
    have e3 := ((((hasDerivAt_id v).sub_const a).pow 3).const_mul c).div_const 6
    exact ((hd0 v).sub ((e1.add e2).add e3)).congr_deriv (by simp; ring)
  have := poly_mono hd (fun v h1 h2 => by linarith [g1 v h1 h2]) le_rfl has hsb
  simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, mul_zero, add_zero, sub_zero] at this
  linarith

end SmoothedOctagon

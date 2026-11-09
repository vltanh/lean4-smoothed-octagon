module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Case M1 angle gap: logarithm bounds and the corner reduction of one factor

## Main API

* `ag_log_le_tangent`: `log z ≤ l + z/z₀ - 1` whenever `log z₀ ≤ l` (tangent line of `log`).
* `ag_log_le_atanh`: `log z ≤ -2τ - 2τ³/3` for `0 < z ≤ 1`, `τ = (1 - z)/(1 + z)`.
* `ag_half_sub_inv_le_log`: `(x - x⁻¹)/2 ≤ log x` on `(0, 1]`.
* `ag_sigma_superadd`: `σ(x) = -x - log(1 - x)` satisfies `σ(a) + σ(b) ≤ σ(c)` for
  `0 ≤ a, b, c`, `c < 1`, `a² + b² ≤ c²`.
* `ag_phi_le`: for `0 < r < 1/2` and `3/4 ≤ u ≤ U(r) = 1 - r + r²`, with `s = √(4u - 3)`:
  `0 ≤ s < 1`, `s² = 4u - 3`, `2r ≤ 1 - s` and
  `r - log r - (1 - u)/r ≤ σ(s) + log 2` (the reverse-switch term is largest on the boundary
  `u = U(r)`).
-/

@[expose] public section

namespace SmoothedOctagon

open Real Finset

/-- Tangent line of the logarithm at `z₀`, with an upper bound `l` for `log z₀`. -/
theorem ag_log_le_tangent {z z₀ l : ℝ} (hz : 0 < z) (hz₀ : 0 < z₀) (hl : Real.log z₀ ≤ l) :
    Real.log z ≤ l + z / z₀ - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos hz hz₀)
  rw [Real.log_div hz.ne' hz₀.ne'] at h1
  linarith

/-- The first two terms of the `artanh` series: `log z ≤ -2τ - 2τ³/3` on `(0, 1]`. -/
theorem ag_log_le_atanh {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    Real.log z ≤ -2 * ((1 - z) / (1 + z)) - 2 * ((1 - z) / (1 + z)) ^ 3 / 3 := by
  set τ := (1 - z) / (1 + z) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) (by linarith)
  have hτ1 : τ < 1 := by rw [hτ, div_lt_one (by linarith)]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := τ) (by rw [abs_of_nonneg hτ0]; exact hτ1)
  have hle := sum_le_hasSum (range 2) (fun k _ ↦ by positivity) hs
  simp only [sum_range_succ, sum_range_zero] at hle
  norm_num at hle
  have h1 : 1 + τ = (1 - τ) / z := by
    rw [hτ]; field_simp; ring
  have h2 : Real.log (1 + τ) = Real.log (1 - τ) - Real.log z := by
    rw [h1, Real.log_div (by linarith) hz.ne']
  linarith

/-- `(x - x⁻¹)/2 ≤ log x` on `(0, 1]`: with `y = -log x ≥ 0` this is `y ≤ sinh y`. -/
theorem ag_half_sub_inv_le_log {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (x - x⁻¹) / 2 ≤ Real.log x := by
  have hy : 0 ≤ -Real.log x := neg_nonneg.2 (Real.log_nonpos hx0.le hx1)
  have h := Real.self_le_sinh_iff.2 hy
  rw [Real.sinh_eq, neg_neg, Real.exp_log hx0, Real.exp_neg, Real.exp_log hx0] at h
  linarith

/-- `σ(x) = -x - log(1 - x) = ∑ x^(n+2)/(n+2)`. -/
private lemma ag_sigma_hasSum {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun n : ℕ ↦ x ^ (n + 2) / ((n : ℝ) + 2)) (-x - Real.log (1 - x)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have h2 := (hasSum_nat_add_iff' 1).2 h
  simp only [sum_range_one] at h2
  convert h2 using 1
  · funext n; push_cast; ring_nf
  · simp only [Nat.cast_zero, zero_add, pow_one, div_one]; ring

/-- Superadditivity of `σ(x) = -x - log(1 - x)` in `x²`. -/
theorem ag_sigma_superadd {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hc1 : c < 1)
    (h : a ^ 2 + b ^ 2 ≤ c ^ 2) :
    (-a - Real.log (1 - a)) + (-b - Real.log (1 - b)) ≤ -c - Real.log (1 - c) := by
  have hac : a ≤ c := by nlinarith
  have hbc : b ≤ c := by nlinarith
  have hsa := ag_sigma_hasSum ha (lt_of_le_of_lt hac hc1)
  have hsb := ag_sigma_hasSum hb (lt_of_le_of_lt hbc hc1)
  have hsc := ag_sigma_hasSum hc hc1
  refine hasSum_le (fun n ↦ ?_) (hsa.add hsb) hsc
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hpa : a ^ (n + 2) ≤ a ^ 2 * c ^ n := by
    rw [pow_add, mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hac n) (by positivity)
  have hpb : b ^ (n + 2) ≤ b ^ 2 * c ^ n := by
    rw [pow_add, mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbc n) (by positivity)
  have hpc : (a ^ 2 + b ^ 2) * c ^ n ≤ c ^ (n + 2) := by
    rw [pow_add, mul_comm (c ^ n)]; exact mul_le_mul_of_nonneg_right h (by positivity)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by nlinarith) hn.le

/-- **One reverse-switch factor at its boundary**: for `0 < r < 1/2` and
`3/4 ≤ u ≤ U(r)`, with `s = √(4u - 3)` (so `u = U((1 - s)/2)`), the term
`r - log r - (1 - u)/r` is at most its value `σ(s) + log 2` at `r = (1 - s)/2`. -/
theorem ag_phi_le {r u : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 1 - r + r ^ 2) :
    0 ≤ √(4 * u - 3) ∧ √(4 * u - 3) < 1 ∧ √(4 * u - 3) ^ 2 = 4 * u - 3 ∧
      2 * r ≤ 1 - √(4 * u - 3) ∧
      r - Real.log r - (1 - u) / r ≤
        -√(4 * u - 3) - Real.log (1 - √(4 * u - 3)) + Real.log 2 := by
  set s := √(4 * u - 3) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 4 * u - 3 := Real.sq_sqrt (by linarith)
  have hu1 : u < 1 := by nlinarith
  have hs1 : s < 1 := by nlinarith
  have hrs : 2 * r ≤ 1 - s := by nlinarith
  refine ⟨hs0, hs1, hs2, hrs, ?_⟩
  set r' := (1 - s) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hrr' : r ≤ r' := by rw [hr']; linarith
  have hy := ag_half_sub_inv_le_log (div_pos hr0 hr'0) ((div_le_one hr'0).2 hrr')
  rw [Real.log_div hr0.ne' hr'0.ne'] at hy
  have hlog2 : Real.log (1 - s) = Real.log r' + Real.log 2 := by
    rw [show 1 - s = r' * 2 by rw [hr']; ring, Real.log_mul hr'0.ne' two_ne_zero]
  have hu_eq : u = 1 - r' + r' ^ 2 := by rw [hr']; linear_combination (-1 / 4 : ℝ) * hs2
  have key : r - (r / r' - (r / r')⁻¹) / 2 - (1 - u) / r ≤ 2 * r' - 1 := by
    have e : 2 * r' - 1 - (r - (r / r' - (r / r')⁻¹) / 2 - (1 - u) / r) =
        (r' - r) ^ 2 * (1 - 2 * r') / (2 * r * r') := by
      rw [hu_eq]; field_simp; ring
    have : 0 ≤ (r' - r) ^ 2 * (1 - 2 * r') / (2 * r * r') :=
      div_nonneg (mul_nonneg (sq_nonneg _) (by rw [hr']; linarith)) (by positivity)
    linarith
  have h2r : 2 * r' - 1 = -s := by rw [hr']; ring
  linarith

end SmoothedOctagon

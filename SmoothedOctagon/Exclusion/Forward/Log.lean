module

public import SmoothedOctagon.Exclusion.Forward.Edge
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Case F: logarithm bounds and the function `f`

## Main API

* `ff_log_atanh`: `log v = log((1 + τ)/(1 - τ))` with `τ = (v - 1)/(v + 1)`.
* `ff_log_ge_sum`, `ff_log_le_sum`: the truncated series
  `∑_{k<n} 2τ^{2k+1}/(2k+1) ≤ log((1+τ)/(1-τ)) ≤ ∑_{k<n} 2τ^{2k+1}/(2k+1) + 2τ^{2n+1}/((2n+1)(1-τ²))`
  for `0 ≤ τ < 1`.
* `ff_log_ge_two`: `log v ≥ 2(v - 1)/(v + 1)` for `v ≥ 1`; `ff_log_ge_three`:
  `log v ≥ 2τ + 2τ³/3`; `ff_log_le_three`: `log v ≤ 2τ + 2τ³/(3(1 - τ²))`.
* `ff_log_five_fourths_lt`: `log(5/4) < 9/40`.
* `ff_f_nonneg` (`f(r) ≥ 0` for `r ≥ 1`), `ff_f_le_cube` (`f(1 + t) ≤ t³/6`).
-/

@[expose] public section

namespace SmoothedOctagon

open Real Finset

/-- The atanh series for `0 ≤ τ < 1`. -/
theorem ff_hasSum_log {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) :
    HasSum (fun k : ℕ ↦ 2 * (1 / (2 * k + 1)) * τ ^ (2 * k + 1)) (Real.log ((1 + τ) / (1 - τ))) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := τ) (by rw [abs_of_nonneg h0]; exact h1)
  rwa [← Real.log_div (by linarith) (by linarith)] at h

theorem ff_log_ge_sum {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (n : ℕ) :
    ∑ k ∈ range n, 2 * (1 / (2 * (k : ℝ) + 1)) * τ ^ (2 * k + 1) ≤ Real.log ((1 + τ) / (1 - τ)) :=
  sum_le_hasSum (range n) (fun k _ ↦ by positivity) (ff_hasSum_log h0 h1)

theorem ff_log_le_sum {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (n : ℕ) :
    Real.log ((1 + τ) / (1 - τ)) ≤ ∑ k ∈ range n, 2 * (1 / (2 * (k : ℝ) + 1)) * τ ^ (2 * k + 1) +
      2 * τ ^ (2 * n + 1) / ((2 * n + 1) * (1 - τ ^ 2)) := by
  have hs := ff_hasSum_log h0 h1
  have ht := (hasSum_nat_add_iff' n).2 hs
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ ↦ 2 * τ ^ (2 * n + 1) / (2 * n + 1) * (τ ^ 2) ^ k)
      (2 * τ ^ (2 * n + 1) / (2 * n + 1) * (1 - τ ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hτ2).mul_left _
  have hle := hasSum_le (fun k ↦ ?_) ht hg
  · have e : 2 * τ ^ (2 * n + 1) / (2 * n + 1) * (1 - τ ^ 2)⁻¹ =
        2 * τ ^ (2 * n + 1) / ((2 * n + 1) * (1 - τ ^ 2)) := by
      field_simp
    rw [e] at hle
    linarith
  · have e : τ ^ (2 * (k + n) + 1) = τ ^ (2 * n + 1) * (τ ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [e]
    have hk : (2 * (n : ℝ) + 1) ≤ 2 * ((k + n : ℕ) : ℝ) + 1 := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
    have hp : 0 ≤ τ ^ (2 * n + 1) * (τ ^ 2) ^ k := by positivity
    have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
    have : 2 * (τ ^ (2 * n + 1) * (τ ^ 2) ^ k) / (2 * ((k + n : ℕ) : ℝ) + 1) ≤
        2 * (τ ^ (2 * n + 1) * (τ ^ 2) ^ k) / (2 * n + 1) :=
      div_le_div_of_nonneg_left (by positivity) hpos hk
    calc _ = 2 * (τ ^ (2 * n + 1) * (τ ^ 2) ^ k) / (2 * ((k + n : ℕ) : ℝ) + 1) := by ring
      _ ≤ _ := this
      _ = _ := by ring

/-- `log v = log((1 + τ)/(1 - τ))`, `τ = (v - 1)/(v + 1)`. -/
theorem ff_log_atanh {v : ℝ} (hv : 0 < v) :
    Real.log v = Real.log ((1 + (v - 1) / (v + 1)) / (1 - (v - 1) / (v + 1))) := by
  congr 1; field_simp; ring

theorem ff_tau_bounds {v : ℝ} (hv : 1 ≤ v) : 0 ≤ (v - 1) / (v + 1) ∧ (v - 1) / (v + 1) < 1 := by
  constructor
  · apply div_nonneg <;> linarith
  · rw [div_lt_one (by linarith)]; linarith

/-- `log v ≥ 2(v - 1)/(v + 1)` for `v ≥ 1`. -/
theorem ff_log_ge_two {v : ℝ} (hv : 1 ≤ v) : 2 * ((v - 1) / (v + 1)) ≤ Real.log v := by
  obtain ⟨h0, h1⟩ := ff_tau_bounds hv
  have := ff_log_ge_sum h0 h1 1
  rw [ff_log_atanh (by linarith : (0 : ℝ) < v)]
  simpa using this

/-- `log v ≥ 2τ + 2τ³/3` for `v ≥ 1`. -/
theorem ff_log_ge_three {v : ℝ} (hv : 1 ≤ v) :
    2 * ((v - 1) / (v + 1)) + 2 * ((v - 1) / (v + 1)) ^ 3 / 3 ≤ Real.log v := by
  obtain ⟨h0, h1⟩ := ff_tau_bounds hv
  have := ff_log_ge_sum h0 h1 2
  rw [ff_log_atanh (by linarith : (0 : ℝ) < v)]
  simp only [sum_range_succ, sum_range_zero] at this
  norm_num at this
  linarith

/-- `log v ≤ 2τ + 2τ³/(3(1 - τ²))` for `v ≥ 1`. -/
theorem ff_log_le_three {v : ℝ} (hv : 1 ≤ v) :
    Real.log v ≤ 2 * ((v - 1) / (v + 1)) +
      2 * ((v - 1) / (v + 1)) ^ 3 / (3 * (1 - ((v - 1) / (v + 1)) ^ 2)) := by
  obtain ⟨h0, h1⟩ := ff_tau_bounds hv
  have := ff_log_le_sum h0 h1 1
  rw [ff_log_atanh (by linarith : (0 : ℝ) < v)]
  simp only [sum_range_succ, sum_range_zero] at this
  norm_num at this
  linarith

/-- `log(5/4) < 9/40`. -/
theorem ff_log_five_fourths_lt : Real.log (5 / 4) < 9 / 40 := by
  have := ff_log_le_three (v := 5 / 4) (by norm_num)
  norm_num at this
  linarith

/-- `f(r) = (r - r⁻¹)/2 - log r ≥ 0` for `r ≥ 1`. -/
theorem ff_f_nonneg {r : ℝ} (hr : 1 ≤ r) : 0 ≤ ff_f r := by
  have hy : 0 ≤ Real.log r := Real.log_nonneg hr
  have h := Real.self_le_sinh_iff.2 hy
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (by linarith)] at h
  unfold ff_f; linarith

/-- `f(1 + t) ≤ t³/6` for `t ≥ 0` (GLOBAL_FORWARD_CENTERED_SYSTEM (7)). -/
theorem ff_f_le_cube {t : ℝ} (ht : 0 ≤ t) : ff_f (1 + t) ≤ t ^ 3 / 6 := by
  have key := ff_le_of_deriv (f := fun s ↦ s ^ 3 / 6 - ff_f (1 + s))
    (f' := fun s ↦ s ^ 2 / 2 - s ^ 2 / (2 * (1 + s) ^ 2)) ht (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have : ff_f (1 + 0) = 0 := by simp [ff_f]
    rw [this] at key
    linarith
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    have h1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s)) (1 / (1 + s)) s := by
      simpa using ((hasDerivAt_id s).const_add 1).log hs0.ne'
    have hc : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 s := by simpa using (hasDerivAt_id s).const_add 1
    have h2 := hc.inv hs0.ne'
    have h := (((hasDerivAt_pow 3 s).div_const 6).sub
      (((hc.sub h2).div_const 2).sub h1))
    convert h using 1
    · ext y; simp [ff_f]
    · field_simp; ring
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    have : s ^ 2 / (2 * (1 + s) ^ 2) ≤ s ^ 2 / 2 := by
      apply div_le_div_of_nonneg_left (sq_nonneg s) (by norm_num)
      nlinarith [hs.1]
    linarith

end SmoothedOctagon

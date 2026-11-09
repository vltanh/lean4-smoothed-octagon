module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.ScaleStrip
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.OrderFace
public import SmoothedOctagon.Exclusion.Mixed.OrderBounds

/-!
# Case M2, reverse successor: the scalar reverse exclusion

Every point of the necessary domain `0 < t < 2/5`, `x > 0`, `k ≥ max{1, 2t + x, 29t²/4}`,
`k < 2t + 2x + x²`, `x < 7/3 - (10/3)t`, `1 < q < W/p`, `v = Sec(t, 1 - t, t + x) ≤ U(t)`,
`v ≥ F_{p/W}(q)` has `N_k > 0`. The three exhaustive cases lower `k` (shape monotonicity,
`nsrN_mono_k`) to the unit face (`nsr_unit_shape`), the order face (`nsr_order_face`, with
`q ≤ W/(2t + x)` from `nsr_q_le_order`) or the scale strip (`nsr_strip`).

## Main API

* `nsr_reverse_core`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The scalar reverse exclusion**: every point of the necessary domain has `N_k > 0`. -/
theorem nsr_reverse_core {t x k q v : ℝ} (ht : 0 < t) (ht2 : t < 2 / 5) (hx : 0 < x) (hk1 : 1 ≤ k)
    (hko : 2 * t + x ≤ k) (hks : 29 / 4 * t ^ 2 ≤ k) (hgap : k < 2 * t + 2 * x + x ^ 2)
    (hdur : x < 7 / 3 - 10 / 3 * t) (hq : 1 < q) (hqW : q < (1 + x) / (t + x))
    (hv : v = nsrSecN t x) (hvU : v ≤ 1 - t + t ^ 2) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x k q v (Real.log q) := by
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos (by linarith) hq.ne'
  have mono : ∀ k', k' ≤ k → nsrN t x k' q v (Real.log q) ≤ nsrN t x k q v (Real.log q) :=
    fun k' hk' => nsrN_mono_k ht (by linarith) hx hq.le hvU hL hk'
  by_cases h1 : t ≤ 13 / 35 ∧ x ≤ 1 - 2 * t
  · exact lt_of_lt_of_le (nsr_unit_shape ht h1.1 hx h1.2 (by linarith) hq hv hF) (mono 1 hk1)
  by_cases h2 : 1 ≤ 2 * t + x ∧ 1 / 4 < x
  · have hqk := nsr_q_le_order ht (by linarith) hx h2.1 hq hqW hv hF
    exact lt_of_lt_of_le (nsr_order_face ht ht2 h2.2 h2.1 hdur hv hq hqk) (mono _ hko)
  -- the scale strip: `t > 13/35`, `x ≤ 9/35`
  have ht0 : 13 / 35 < t := by
    by_contra h
    push Not at h
    have hx' : 1 - 2 * t < x := by
      by_contra h'
      push Not at h'
      exact h1 ⟨h, h'⟩
    exact h2 ⟨by linarith, by linarith⟩
  have hx9 : x ≤ 9 / 35 := by
    by_contra h
    push Not at h
    exact h2 ⟨by linarith, by linarith⟩
  exact lt_of_lt_of_le (nsr_strip ht0.le ht2.le hx hx9 (by linarith) hq hv hF) (mono _ hks)

end SmoothedOctagon

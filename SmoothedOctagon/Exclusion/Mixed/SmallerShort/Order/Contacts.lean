module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Simpson bounds for the endpoint gaps

The strict Simpson bound for the reciprocal integral gives a lower bound for
the right endpoint gap. Clearing its positive denominator gives the ratio
comparison used by the integral proof of the lower bridge orders.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- Strict Padé: `log z < (z - 1)(z² + 10z + 1)/(6z(z + 1))` for `z > 1`. -/
theorem ord_log_lt_pade3 {z : ℝ} (hz : 1 < z) :
    Real.log z < (z - 1) * (z ^ 2 + 10 * z + 1) / (6 * z * (z + 1)) := by
  have h := ss_lt_of_deriv
    (f := fun t => (t - 1) * (t ^ 2 + 10 * t + 1) / (6 * t * (t + 1)) - Real.log t)
    (f' := fun t => (t - 1) ^ 4 / (6 * t ^ 2 * (t + 1) ^ 2)) hz (fun t ht => ?_)
    (fun t ht => by
      have : 0 < t - 1 := by linarith [ht.1]
      have : 0 < t := by linarith [ht.1]
      positivity)
  · simp only [sub_self, zero_mul, zero_div, Real.log_one] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have h1 : HasDerivAt (fun t : ℝ => (t - 1) * (t ^ 2 + 10 * t + 1))
      (3 * t ^ 2 + 18 * t - 9) t := by
    have := ((hasDerivAt_id' t).sub_const 1).mul
      ((((hasDerivAt_id' t).mul (hasDerivAt_id' t)).add
        ((hasDerivAt_id' t).const_mul 10)).add_const 1)
    convert this using 1
    · funext s; simp only [Pi.mul_apply, Pi.add_apply]; ring
    · simp only [Pi.mul_apply, Pi.add_apply]; ring
  have h2 : HasDerivAt (fun t : ℝ => 6 * t * (t + 1)) (12 * t + 6) t := by
    have := ((hasDerivAt_id' t).const_mul 6).mul ((hasDerivAt_id' t).add_const 1)
    convert this using 1
    · ring
  have := (h1.div h2 (by positivity)).sub (Real.hasDerivAt_log ht.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-- **The Padé gap**: for
`0 < p < q ≤ 1`, `η = avg(p, q) - g(q) > η₀ = (q - p)(6 + p - 5pq - q² - q)/(6(1 + p)(1 + q)²(p + q +
2))` (strict `log z < (z - 1)(z² + 10z + 1)/(6z(z + 1))` at `z = (1 + q)/(1 + p)`). -/
theorem ss_pade_gap {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (q - p) * (6 + p - 5 * p * q - q ^ 2 - q) / (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2)) <
      m2Sec p 1 q - ss_gB 1 q := by
  have hq1 : q ≤ 1 := hq
  have hq0 : 0 < q := by linarith
  have hz : 1 < (q + 1) / (p + 1) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hlog := ord_log_lt_pade3 hz
  rw [m2Sec_of_ne hpq.ne]
  have hqp : 0 < q - p := by linarith
  have k : 1 / (q - p) * Real.log ((q + 1) / (p + 1)) <
      1 / (q - p) * (((q + 1) / (p + 1) - 1) *
        (((q + 1) / (p + 1)) ^ 2 + 10 * ((q + 1) / (p + 1)) + 1) /
          (6 * ((q + 1) / (p + 1)) * ((q + 1) / (p + 1) + 1))) :=
    mul_lt_mul_of_pos_left hlog (by positivity)
  have e : 1 / (q - p) * (((q + 1) / (p + 1) - 1) *
      (((q + 1) / (p + 1)) ^ 2 + 10 * ((q + 1) / (p + 1)) + 1) /
        (6 * ((q + 1) / (p + 1)) * ((q + 1) / (p + 1) + 1))) =
      (p ^ 2 + 10 * p * q + 12 * p + q ^ 2 + 12 * q + 12) /
        (6 * (p + 1) * (q + 1) * (p + q + 2)) := by
    have : p + 1 ≠ 0 := by positivity
    have : q + 1 ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at k
  have e2 : 1 + 1 ^ 2 / ((p + 1) * (q + 1)) -
      (p ^ 2 + 10 * p * q + 12 * p + q ^ 2 + 12 * q + 12) /
        (6 * (p + 1) * (q + 1) * (p + q + 2)) - ss_gB 1 q =
      (q - p) * (6 + p - 5 * p * q - q ^ 2 - q) / (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2)) := by
    unfold ss_gB
    have : p + 1 ≠ 0 := by positivity
    have : q + 1 ≠ 0 := by positivity
    have : 1 + q ≠ 0 := by positivity
    have : 1 + p ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [← e2]
  linarith

/-- **The gap ratio from below**: for `0 < p < q ≤ 1`, with
`N = (1 + p)(6 + p - 5pq - q² - q)`, `W = 6(p + q + 2)(1 - pq)`, `η = avg - g(q)`, `ξ = g(p) - avg`:
`η/ξ > N/(W - N)`, in cleared form `N ξ < (W - N) η`. -/
theorem ss_gap_ratio_low {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q) * (ss_gB 1 p - m2Sec p 1 q) <
      (6 * (p + q + 2) * (1 - p * q) - (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q)) *
        (m2Sec p 1 q - ss_gB 1 q) := by
  have hq0 : 0 < q := by linarith
  have hgap := ss_pade_gap hp hpq hq
  have hpq1 : p * q < 1 := by have := mul_le_of_le_one_right hp.le hq; linarith
  have hW : 0 < 6 * (p + q + 2) * (1 - p * q) := by
    have : 0 < 1 - p * q := by linarith
    positivity
  have e : (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q) * (ss_gB 1 p - ss_gB 1 q) =
      6 * (p + q + 2) * (1 - p * q) *
        ((q - p) * (6 + p - 5 * p * q - q ^ 2 - q) /
          (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2))) := by
    unfold ss_gB
    have : 1 + q ≠ 0 := by positivity
    have : 1 + p ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
    ring
  have := mul_lt_mul_of_pos_left hgap hW
  linarith

end SmoothedOctagon

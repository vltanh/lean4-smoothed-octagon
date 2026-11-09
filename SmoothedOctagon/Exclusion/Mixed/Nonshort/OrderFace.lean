module

public import SmoothedOctagon.Exclusion.Mixed.WindowData
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.OrderFace.Signs
public import Mathlib.Analysis.Convex.Deriv

/-!
# Case M2, reverse successor: the reverse order face `k = 2t + x`

For `0 < t < 2/5`, `x > 1/4`, `k = 2t + x ≥ 1`, `x < 7/3 - (10/3)t`, the exact incoming secant `v`
and `1 < q ≤ W/k`, `N(k) > 0`. On this face `B = Wk` and `R(q) = α + βq + γ/q - p log q` is
concave on `[1, W/k]` (`nsr_concave_min`), so it suffices to check the two endpoints: `R(1) > 0`
from the reciprocal-mean ceiling and a completed square (`nsr_order_one_pos`), and
`R(W/k) > 0` from the rational relaxations `v < v̄`, `log q < L₊(q)` and the certificate
`nsrOP_pos_a`, `nsrOP_pos_b`.
The bound `q ≤ W/k` (from the incoming floor and the swapped secant order) is a hypothesis here.

## Main API

* `nsr_concave_min`: the minimum principle for `α + βq + γ/q - p log q` where it is concave.
* `nsr_order_face`: **the order-face lemma**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Minimum principle**: `f(q) = α + βq + γ/q - p log q` is concave on `[q₀, q₁]` when
`p q₁ + 2γ ≤ 0`, hence at least the smaller endpoint value. -/
theorem nsr_concave_min {α β γ p q0 q1 q : ℝ} (hq0 : 0 < q0) (hp : 0 ≤ p)
    (hγ : p * q1 + 2 * γ ≤ 0) (hq : q ∈ Set.Icc q0 q1) :
    min (α + β * q0 + γ / q0 - p * Real.log q0) (α + β * q1 + γ / q1 - p * Real.log q1) ≤
      α + β * q + γ / q - p * Real.log q := by
  have hconc : ConcaveOn ℝ (Set.Icc q0 q1) (fun z => α + β * z + γ / z - p * Real.log z) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc q0 q1)
      (f' := fun z => β - γ / z ^ 2 - p / z) (f'' := fun z => 2 * γ / z ^ 3 + p / z ^ 2)
    · intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hq0 hz.1
      have : HasDerivAt (fun z => α + β * z + γ / z - p * Real.log z)
          (β - γ / z ^ 2 - p / z) z := by
        have h1 := ((hasDerivAt_id z).const_mul β).const_add α
        have h2 := (hasDerivAt_inv hz0.ne').const_mul γ
        have h3 := (Real.hasDerivAt_log hz0.ne').const_mul p
        convert (h1.add h2).sub h3 using 1
        · ext w; simp [div_eq_mul_inv]
        · simp [div_eq_mul_inv]; ring
      exact this.continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hq0 hz.1
      have h1 := ((hasDerivAt_id z).const_mul β).const_add α
      have h2 := (hasDerivAt_inv hz0.ne').const_mul γ
      have h3 := (Real.hasDerivAt_log hz0.ne').const_mul p
      have := (h1.add h2).sub h3
      refine (this.congr_deriv ?_).hasDerivWithinAt.congr_of_mem (fun w _ => ?_) ?_
      · simp [div_eq_mul_inv]; ring
      · simp [div_eq_mul_inv]
      · rw [interior_Icc]; exact hz
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hq0 hz.1
      have h2 : HasDerivAt (fun z : ℝ => γ / z ^ 2) (-(2 * γ) / z ^ 3) z := by
        have := (hasDerivAt_pow 2 z).inv (by positivity) |>.const_mul γ
        convert this using 1
        · ext w; simp [div_eq_mul_inv]
        · field_simp; ring
      have h3 : HasDerivAt (fun z : ℝ => p / z) (-p / z ^ 2) z := by
        have := (hasDerivAt_inv hz0.ne').const_mul p
        convert this using 1
        · ext w; simp [div_eq_mul_inv]
        · field_simp
      have := ((hasDerivAt_const z β).sub h2).sub h3
      refine (this.congr_deriv ?_).hasDerivWithinAt
      field_simp; ring
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hq0 hz.1
      have hpz : p * z ≤ p * q1 := mul_le_mul_of_nonneg_left hz.2.le hp
      have : 2 * γ / z ^ 3 + p / z ^ 2 = (p * z + 2 * γ) / z ^ 3 := by field_simp; ring
      rw [this]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  exact hconc.min_le_of_mem_Icc (Set.left_mem_Icc.2 (hq.1.trans hq.2))
    (Set.right_mem_Icc.2 (hq.1.trans hq.2)) hq

/-- At the factor `q = 1`, the reciprocal-mean ceiling leaves a square and a positive
term. No duration bound or coefficient estimate is needed. -/
theorem nsr_order_one_pos {t x v : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x)
    (hv : v ≤ nsrVJensen t x) : 0 < nsrN t x (2 * t + x) 1 v 0 := by
  have hc : 0 < 1 - t := by linarith
  have hW : 0 < 1 + x := by positivity
  have hD : 0 < x ^ 2 + 6 * x + 6 := by positivity
  have hceiling : 0 < nsrN t x (2 * t + x) 1 (nsrVJensen t x) 0 := by
    have e : nsrN t x (2 * t + x) 1 (nsrVJensen t x) 0 =
        (1 - t) * x ^ 3 / ((1 + x) * (x ^ 2 + 6 * x + 6) ^ 2) *
          (((x ^ 2 + 6 * x + 6) * t - 3 * x - 4) ^ 2 + 2 * (1 + x) ^ 3) := by
      unfold nsrN nsrVJensen
      field_simp
      ring
    rw [e]
    positivity
  rw [nsrN_sub_v t x (2 * t + x) 1 v (nsrVJensen t x) 0]
  have hNv := nsrNv_nonpos ht.le hx.le (by norm_num : (1 : ℝ) ≤ 1)
    (by linarith : 2 * t ≤ 2 * t + x)
  have := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hv) hNv
  linarith

/-- The concave form of the residual on the face `k = 2t + x` (`B = Wk`, `Z = qk`). -/
theorem nsr_order_R_form {t x q v L : ℝ} (ht : 0 < t) (hx : 0 < x) (_hk : 0 < 2 * t + x)
    (hq : q ≠ 0) :
    nsrR t x (2 * t + x) q v L =
      ((1 - t) - (t + x) ^ 2 / (1 + x) + (t + x) ^ 3 / ((1 + x) * (2 * t + x)) - (1 + x) * v
        + (t + x) * ((2 * t + x) / t * (v - 1 + t ^ 2) + t * (2 - t) + 2 * v * (x * (x + 2)))
          / ((1 + x) * (2 * t + x)))
      + ((2 * t + x) * (1 - ((2 * t + x) ^ 2 - (2 * t + x) * t + t ^ 2
          + ((2 * t + x) / t * (v - 1 + t ^ 2) + t * (2 - t)) * (x * (x + 2))
          + v * (x * (x + 2)) ^ 2) / ((1 + x) * (2 * t + x)) ^ 2)) * q
      + (-(t + x) ^ 2 / (2 * t + x)) / q - (t + x) * L := by
  have hW : 0 < 1 + x := by linarith
  have hB : 2 * t + x + 2 * t * x + x ^ 2 = (1 + x) * (2 * t + x) := by ring
  unfold nsrR
  rw [hB]
  field_simp
  ring

/-- **The order-face lemma**: on the face `k = 2t + x`, `N > 0` for `1 < q ≤ W/k`. -/
theorem nsr_order_face {t x q v : ℝ} (ht : 0 < t) (ht2 : t < 2 / 5) (hx : 1 / 4 < x)
    (hk : 1 ≤ 2 * t + x) (hdur : x < 7 / 3 - 10 / 3 * t) (hv : v = nsrSecN t x) (hq : 1 < q)
    (hqk : q ≤ (1 + x) / (2 * t + x)) : 0 < nsrN t x (2 * t + x) q v (Real.log q) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < 2 * t + x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hq0 : 0 < q := by linarith
  have hvb : v < nsrVbar t x := hv ▸ nsr_secN_lt_vbar hx0 (by linarith)
  set k := 2 * t + x with hkdef
  -- the concave form
  set α := (1 - t) - (t + x) ^ 2 / (1 + x) + (t + x) ^ 3 / ((1 + x) * k) - (1 + x) * v
        + (t + x) * (k / t * (v - 1 + t ^ 2) + t * (2 - t) + 2 * v * (x * (x + 2))) / ((1 + x) * k)
    with hα
  set β := k * (1 - (k ^ 2 - k * t + t ^ 2 + (k / t * (v - 1 + t ^ 2) + t * (2 - t)) * (x * (x + 2))
          + v * (x * (x + 2)) ^ 2) / ((1 + x) * k) ^ 2) with hβ
  set γ := -(t + x) ^ 2 / k with hγ
  have hRf : ∀ z, z ≠ 0 → nsrR t x k z v (Real.log z) = α + β * z + γ / z - (t + x) * Real.log z :=
    fun z hz => nsr_order_R_form ht hx0 hk0 hz
  have hBk : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hNR : ∀ z, 0 < z → nsrN t x k z v (Real.log z) =
      t * (k + 2 * t * x + x ^ 2) * z * (1 + x) * (α + β * z + γ / z - (t + x) * Real.log z) :=
    fun z hz => by rw [nsrN_eq_R ht hx0 hk0 hz, hRf z hz.ne']
  -- the endpoint q = 1
  have hR1 : 0 < α + β * 1 + γ / 1 - (t + x) * Real.log 1 := by
    have hN1 : 0 < nsrN t x k 1 v 0 := by
      apply nsr_order_one_pos ht (by linarith) hx0
      rw [hv]
      exact (nsr_secN_lt_jensen hx0 (by linarith)).le
    have := hNR 1 one_pos
    rw [Real.log_one] at this
    rw [this] at hN1
    have hc : 0 < t * (k + 2 * t * x + x ^ 2) * 1 * (1 + x) := by positivity
    rw [Real.log_one]
    exact pos_of_mul_pos_right hN1 hc.le
  -- the endpoint q = W/k
  have hq1 : 1 < (1 + x) / k := by rw [lt_div_iff₀ hk0]; linarith
  have hR2 : 0 < α + β * ((1 + x) / k) + γ / ((1 + x) / k) - (t + x) * Real.log ((1 + x) / k) := by
    have hq10 : 0 < (1 + x) / k := by positivity
    have hcert : 0 < nsrOP (1 - 2 * t) (2 * t + x - 1) := by
      rcases le_total (1 - 2 * t) (1 / 4) with h1 | h1
      · exact nsrOP_pos_a _ _ (by linarith) h1 (by linarith) (by linarith) (by linarith)
      · exact nsrOP_pos_b _ _ h1 (by linarith) (by linarith) (by linarith) (by linarith)
    have eP : 24 * k ^ 3 * (1 + x + k) * (x + 2) ^ 3 *
        nsrN t x k ((1 + x) / k) (nsrVbar t x) (nsrLp ((1 + x) / k)) =
        (k + 2 * t * x + x ^ 2) * nsrOP (1 - 2 * t) (2 * t + x - 1) := by
      rw [hkdef]; unfold nsrN nsrVbar nsrLp nsrOP; field_simp; ring
    have hNb : 0 < nsrN t x k ((1 + x) / k) (nsrVbar t x) (nsrLp ((1 + x) / k)) := by
      have h1 : 0 < (k + 2 * t * x + x ^ 2) * nsrOP (1 - 2 * t) (2 * t + x - 1) := mul_pos hBk hcert
      rw [← eP] at h1
      exact pos_of_mul_pos_right h1 (by positivity)
    have hN := nsr_N_pos_of_relax (t := t) (x := x) (k := k) (q := (1 + x) / k) (v := v)
      (L := Real.log ((1 + x) / k)) (vb := nsrVbar t x) (Lb := nsrLp ((1 + x) / k)) (Fl := v) (m := 0)
      hvb.le (nsr_log_lt_Lp hq1).le (nsrNv_nonpos ht.le hx0.le hq1.le (by linarith))
      (nsrNL_nonpos ht.le hx0.le hq10.le hk0.le) le_rfl le_rfl (by simpa using hNb)
    rw [hNR _ hq10] at hN
    have hc : 0 < t * (k + 2 * t * x + x ^ 2) * ((1 + x) / k) * (1 + x) := by positivity
    exact pos_of_mul_pos_right hN hc.le
  -- concavity
  have hmin := nsr_concave_min (α := α) (β := β) (γ := γ) (p := t + x) (q0 := 1)
    (q1 := (1 + x) / k) (q := q) one_pos (by linarith) (by
      rw [hγ]
      have : (t + x) * ((1 + x) / k) + 2 * (-(t + x) ^ 2 / k) = (t + x) * (1 + x - 2 * (t + x)) / k := by
        field_simp; ring
      rw [this]
      apply div_nonpos_of_nonpos_of_nonneg _ hk0.le
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) ⟨hq.le, hqk⟩
  have hRq : 0 < α + β * q + γ / q - (t + x) * Real.log q :=
    lt_of_lt_of_le (lt_min hR1 hR2) hmin
  rw [hNR q hq0]
  positivity

end SmoothedOctagon

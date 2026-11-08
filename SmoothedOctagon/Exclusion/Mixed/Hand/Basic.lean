module

public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Case M2 by hand: the normalized incident-upper residual

The normalized residual of `MIXED_NONSHORT_SHAPE_MONOTONICITY` and
`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION` (1): in the coordinates `t = a/T`, `x = (d - a)/T`,
`k = K/T²`, `q = WZ/Q` (`T = a + c`), with `W = 1 + x`, `X = x + 2`, `p = t + x`, `Y = x X`,
`B = k + 2tx + x²`, the residual `R = R_d(U*; b*)/T` and its positive multiple `N = tBqW R`.
`N` is a polynomial in `t, x, k, q, v` and `L = log q` (`nhN`, checked against the notes' formula
by exact symbolic expansion), affine in `k`, `v` and `L`.

## Main API

* `nhN t x k q v L`; its `v`-, `L`- and `k`-coefficients `nhNv`, `nhNL`, `nhA`, and the affine
  identities `nhN_sub_v`, `nhN_sub_L`, `nhN_sub_k`.
* `nhA_pos`, `nhN_mono_k`: **shape monotonicity** (`MIXED_NONSHORT_SHAPE_MONOTONICITY`): `N` is
  strictly increasing in `k` when `v ≤ U(t)` and `L < q - 1`.
* `nhNv_nonpos`, `nhNL_nonpos`: the signs of the `v`- and `log q`-coefficients.
* The rational relaxations: `nhVbar` (`v̄`), `nhLp` (`L₊`), `nhFl` (`F_ℓ`), `nhSecN` (the exact
  normalized secant); `nh_log_one_add_gt`, `nh_log_lt_Lp`, `nh_secN_lt_vbar`, `nh_m2F_gt_Fl`.
* `nh_N_pos_of_relax`: the comparison `N ≥ N̄ ≥ N̄ - m (v̄ - F_ℓ)` used by every hand sign
  (`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` §2).
* `nh_strictMonoOn_Ici`: strict monotonicity from a positive derivative on `[a, ∞)`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The normalized residual** `N = tBqW R` (`MIXED_NONSHORT_SHAPE_MONOTONICITY`), as a polynomial
in `t, x, k, q, v` and `L = log q`. -/
noncomputable def nhN (t x k q v L : ℝ) : ℝ :=
  -t * (t + x) ^ 2 * (1 + x) ^ 2
    - t * (2 * t ^ 3 * x + 5 * t ^ 2 * x ^ 2 - 2 * t ^ 2 * x - 2 * t ^ 2 + 2 * t * x ^ 3
      - 6 * t * x ^ 2 - 4 * t * x - 2 * x ^ 3 - x ^ 2) * q
    + t * (5 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x - t ^ 2 + 4 * t * x ^ 3 - 2 * t * x ^ 2 - 4 * t * x
      + x ^ 4) * q ^ 2
    - t * x * (t + x) * (2 * t + x) * (1 + x) * L * q
    + t * x * (1 + x) * (2 * t + x ^ 2 + 3 * x) * v * q
    - t * x ^ 2 * (x + 2) ^ 2 * v * q ^ 2
    + k * ((t ^ 3 * x + t ^ 2 * x ^ 2 - 2 * t ^ 2 * x - t ^ 2 - t * x ^ 2 - x ^ 2 - x) * q
      + (-t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + t ^ 2 + 2 * t * x ^ 2 + x ^ 2 + 2 * x) * q ^ 2
      - t * (t + x) * (1 + x) * L * q
      + x * (1 - t) * (1 + x) * v * q
      - x * (x + 2) * v * q ^ 2)

/-- The coefficient of `v` in `N`: `N_v = -xqI`,
`I = k + tx + tW(k - 2t) + (q - 1)(kX + txX²)`. -/
noncomputable def nhNv (t x k q : ℝ) : ℝ :=
  -(x * q * (k + t * x + t * (1 + x) * (k - 2 * t)
    + (q - 1) * (k * (x + 2) + t * x * (x + 2) ^ 2)))

/-- The coefficient of `L = log q` in `N`: `-tpqWB`. -/
noncomputable def nhNL (t x k q : ℝ) : ℝ :=
  -(q * t * (t + x) * (1 + x) * (k + 2 * t * x + x ^ 2))

/-- The coefficient of `k` in `N` (`MIXED_NONSHORT_SHAPE_MONOTONICITY`, `A`). -/
noncomputable def nhA (t x q v L : ℝ) : ℝ :=
  (t ^ 3 * x + t ^ 2 * x ^ 2 - 2 * t ^ 2 * x - t ^ 2 - t * x ^ 2 - x ^ 2 - x) * q
    + (-t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + t ^ 2 + 2 * t * x ^ 2 + x ^ 2 + 2 * x) * q ^ 2
    - t * (t + x) * (1 + x) * L * q
    + x * (1 - t) * (1 + x) * v * q
    - x * (x + 2) * v * q ^ 2

theorem nhN_sub_v (t x k q v v' L : ℝ) :
    nhN t x k q v L = nhN t x k q v' L + (v - v') * nhNv t x k q := by
  unfold nhN nhNv; ring

theorem nhN_sub_L (t x k q v L L' : ℝ) :
    nhN t x k q v L = nhN t x k q v L' + (L - L') * nhNL t x k q := by
  unfold nhN nhNL; ring

theorem nhN_sub_k (t x k k' q v L : ℝ) :
    nhN t x k q v L = nhN t x k' q v L + (k - k') * nhA t x q v L := by
  unfold nhN nhA; ring

/-- The `v`-coefficient is negative when `k ≥ 2t` (`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` §2). -/
theorem nhNv_nonpos {t x k q : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (hq : 1 ≤ q) (hk : 2 * t ≤ k) :
    nhNv t x k q ≤ 0 := by
  unfold nhNv
  have hk0 : 0 ≤ k := by linarith
  have h1 : 0 ≤ t * (1 + x) * (k - 2 * t) := by
    apply mul_nonneg (by positivity); linarith
  have h2 : 0 ≤ (q - 1) * (k * (x + 2) + t * x * (x + 2) ^ 2) := by
    apply mul_nonneg (by linarith); positivity
  have : 0 ≤ x * q * (k + t * x + t * (1 + x) * (k - 2 * t)
      + (q - 1) * (k * (x + 2) + t * x * (x + 2) ^ 2)) := by
    apply mul_nonneg (by positivity)
    have : 0 ≤ t * x := by positivity
    linarith
  linarith

/-- The `log q`-coefficient is negative. -/
theorem nhNL_nonpos {t x k q : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (hq : 0 ≤ q) (hk : 0 ≤ k) :
    nhNL t x k q ≤ 0 := by
  unfold nhNL
  have : 0 ≤ q * t * (t + x) * (1 + x) * (k + 2 * t * x + x ^ 2) := by positivity
  linarith

/-- **Shape monotonicity** (`MIXED_NONSHORT_SHAPE_MONOTONICITY`): with `v ≤ U(t)` and
`log q < q - 1`, `A > qtx(1 - t)[(q - 1)(2x + 1) + tx] > 0`. -/
theorem nhA_pos {t x q v L : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hq : 1 ≤ q)
    (hv : v ≤ 1 - t + t ^ 2) (hL : L < q - 1) : 0 < nhA t x q v L := by
  have e : nhA t x q v L = q * t * x * (1 - t) * ((q - 1) * (2 * x + 1) + t * x)
      + (1 - t + t ^ 2 - v) * (q * x * ((q - 1) * (x + 2) + 1 + t * (1 + x)))
      + (q - 1 - L) * (q * t * (t + x) * (1 + x)) := by
    unfold nhA; ring
  rw [e]
  have hq0 : 0 < q := by linarith
  have h1 : 0 ≤ q * t * x * (1 - t) * ((q - 1) * (2 * x + 1) + t * x) := by
    apply mul_nonneg
    · have : 0 < 1 - t := by linarith
      positivity
    · have : 0 ≤ (q - 1) * (2 * x + 1) := mul_nonneg (by linarith) (by linarith)
      have : 0 ≤ t * x := by positivity
      linarith
  have h2 : 0 ≤ (1 - t + t ^ 2 - v) * (q * x * ((q - 1) * (x + 2) + 1 + t * (1 + x))) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (q - 1) * (x + 2) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ t * (1 + x) := by positivity
    have : 0 ≤ (q - 1) * (x + 2) + 1 + t * (1 + x) := by linarith
    positivity
  have h3 : 0 < (q - 1 - L) * (q * t * (t + x) * (1 + x)) := by
    apply mul_pos (by linarith); positivity
  linarith

/-- `N` is nondecreasing in the shape `k` (strictly increasing; weak form). -/
theorem nhN_mono_k {t x k k' q v L : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hq : 1 ≤ q)
    (hv : v ≤ 1 - t + t ^ 2) (hL : L < q - 1) (hk : k ≤ k') :
    nhN t x k q v L ≤ nhN t x k' q v L := by
  rw [nhN_sub_k t x k' k q v L]
  have := nhA_pos ht ht1 hx hq hv hL
  nlinarith

/-- A function with a derivative on `[a, ∞)`, positive on `(a, ∞)`, is strictly increasing
on `[a, ∞)`. -/
theorem nh_strictMonoOn_Ici {f f' : ℝ → ℝ} {a : ℝ} (hd : ∀ z, a ≤ z → HasDerivAt f (f' z) z)
    (hpos : ∀ z, a < z → 0 < f' z) : StrictMonoOn f (Set.Ici a) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici a)
  · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ici] at hz
    rw [(hd z (le_of_lt hz)).deriv]
    exact hpos z hz

/-- The two-term atanh lower bound `log(1 + x) > 2x/X + 2x³/(3X³)`, `X = x + 2`
(`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` (4)). -/
theorem nh_log_one_add_gt {x : ℝ} (hx : 0 < x) :
    2 * x / (x + 2) + 2 * x ^ 3 / (3 * (x + 2) ^ 3) < Real.log (1 + x) := by
  have hmono := nh_strictMonoOn_Ici (a := 0)
    (f := fun z => Real.log (1 + z) - (2 * z / (z + 2) + 2 * z ^ 3 / (3 * (z + 2) ^ 3)))
    (f' := fun z => z ^ 4 / ((z + 1) * (z + 2) ^ 4)) (fun z hz => ?_) (fun z hz => by positivity)
  · have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
    simp only [add_zero, Real.log_one] at this
    norm_num at this
    linarith
  · have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h2 : HasDerivAt (fun z : ℝ => z + 2) 1 z := by
      simpa using (hasDerivAt_id z).add_const 2
    have hz1 : (1 + z) ≠ 0 := by linarith
    have hz2 : z + 2 ≠ 0 := by linarith
    have h3 : HasDerivAt (fun z : ℝ => 2 * z) 2 z := by
      simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
    have h4 : HasDerivAt (fun z : ℝ => 2 * z ^ 3) (2 * (3 * z ^ 2)) z := by
      simpa using (hasDerivAt_pow 3 z).const_mul (2 : ℝ)
    have h5 : HasDerivAt (fun z : ℝ => 3 * (z + 2) ^ 3) (3 * (3 * (z + 2) ^ 2 * 1)) z := by
      have := (h2.pow 3).const_mul (3 : ℝ)
      simpa using this
    have := (h1.log hz1).sub ((h3.div h2 hz2).add (h4.div h5 (by positivity)))
    refine this.congr_deriv ?_
    field_simp
    ring

/-- The rational upper bound `L₊(q) = (q - 1)(q² + 10q + 1)/(6q(q + 1))` for `log q`. -/
noncomputable def nhLp (q : ℝ) : ℝ := (q - 1) * (q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))

/-- `log q < L₊(q)` for `q > 1` (`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` (4)). -/
theorem nh_log_lt_Lp {q : ℝ} (hq : 1 < q) : Real.log q < nhLp q := by
  have hmono := nh_strictMonoOn_Ici (a := 1) (f := fun z => nhLp z - Real.log z)
    (f' := fun z => (z - 1) ^ 4 / (6 * z ^ 2 * (z + 1) ^ 2)) (fun z hz => ?_) (fun z hz => by
      have : 0 < z - 1 := by linarith
      have : 0 < z := by linarith
      positivity)
  · have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq.le) hq
    simp only [nhLp, Real.log_one] at this
    norm_num at this
    unfold nhLp
    linarith
  · have hz : 0 < z := by linarith
    have h1 : HasDerivAt (fun z : ℝ => (z - 1) * (z ^ 2 + 10 * z + 1))
        (1 * (z ^ 2 + 10 * z + 1) + (z - 1) * (2 * z + 10)) z := by
      have ha : HasDerivAt (fun z : ℝ => z - 1) 1 z := by simpa using (hasDerivAt_id z).sub_const 1
      have hb : HasDerivAt (fun z : ℝ => z ^ 2 + 10 * z + 1) (2 * z + 10) z := by
        have := ((hasDerivAt_pow 2 z).add ((hasDerivAt_id z).const_mul (10 : ℝ))).add_const 1
        simpa [mul_comm] using this
      exact ha.mul hb
    have h2 : HasDerivAt (fun z : ℝ => 6 * z * (z + 1)) (6 * (z + 1) + 6 * z * 1) z := by
      have ha : HasDerivAt (fun z : ℝ => 6 * z) 6 z := by
        simpa using (hasDerivAt_id z).const_mul (6 : ℝ)
      have hb : HasDerivAt (fun z : ℝ => z + 1) 1 z := by simpa using (hasDerivAt_id z).add_const 1
      exact ha.mul hb
    have := (h1.div h2 (by positivity)).sub (Real.hasDerivAt_log hz.ne')
    refine this.congr_deriv ?_
    field_simp
    ring

/-- The exact normalized incoming secant `v = Sec(t, 1 - t, t + x)`
`= 1 + (1 - t)²/W - (1 - t) log W/x`. -/
noncomputable def nhSecN (t x : ℝ) : ℝ :=
  1 + (1 - t) ^ 2 / (1 + x) - (1 - t) * Real.log (1 + x) / x

/-- The rational secant upper bound `v̄ = 1 + (1 - t)²/W - (2(1 - t)/X)(1 + x²/(3X²))`. -/
noncomputable def nhVbar (t x : ℝ) : ℝ :=
  1 + (1 - t) ^ 2 / (1 + x) - 2 * (1 - t) / (x + 2) * (1 + x ^ 2 / (3 * (x + 2) ^ 2))

/-- `v < v̄` (from `nh_log_one_add_gt`). -/
theorem nh_secN_lt_vbar {t x : ℝ} (hx : 0 < x) (ht : t < 1) : nhSecN t x < nhVbar t x := by
  have h := nh_log_one_add_gt hx
  unfold nhSecN nhVbar
  have h1 : 0 < 1 - t := by linarith
  have e : 2 * (1 - t) / (x + 2) * (1 + x ^ 2 / (3 * (x + 2) ^ 2)) =
      (1 - t) * (2 * x / (x + 2) + 2 * x ^ 3 / (3 * (x + 2) ^ 3)) / x := by
    field_simp
  rw [e]
  have : (1 - t) * (2 * x / (x + 2) + 2 * x ^ 3 / (3 * (x + 2) ^ 3)) / x <
      (1 - t) * Real.log (1 + x) / x := by
    apply div_lt_div_of_pos_right _ hx
    exact mul_lt_mul_of_pos_left h h1
  linarith

/-- The rational floor `F_ℓ = 1 + p²q/W² - (p/W)(q² + 10q + 1)/(6(q + 1))`. -/
noncomputable def nhFl (t x q : ℝ) : ℝ :=
  1 + (t + x) ^ 2 * q / (1 + x) ^ 2 - (t + x) / (1 + x) * ((q ^ 2 + 10 * q + 1) / (6 * (q + 1)))

/-- `F_{p/W}(q) > F_ℓ` for `q > 1`. -/
theorem nh_m2F_gt_Fl {t x q : ℝ} (hq : 1 < q) (hp : 0 < t + x) (hx : 0 < 1 + x) :
    nhFl t x q < m2F ((t + x) / (1 + x)) q := by
  rw [m2F_of_ne hq.ne']
  have hL := nh_log_lt_Lp hq
  unfold nhFl
  unfold nhLp at hL
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have he : 0 < (t + x) / (1 + x) := by positivity
  have e1 : (t + x) / (1 + x) * ((q ^ 2 + 10 * q + 1) / (6 * (q + 1))) =
      (t + x) / (1 + x) * q * ((q - 1) * (q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) / (q - 1) := by
    field_simp
  have e2 : ((t + x) / (1 + x)) ^ 2 * q = (t + x) ^ 2 * q / (1 + x) ^ 2 := by
    rw [div_pow]; ring
  rw [e1, ← e2]
  have : (t + x) / (1 + x) * q * Real.log q / (q - 1) <
      (t + x) / (1 + x) * q * ((q - 1) * (q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) / (q - 1) := by
    apply div_lt_div_of_pos_right _ hq1
    exact mul_lt_mul_of_pos_left hL (by positivity)
  linarith

/-- **The relaxation comparison** (`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` §2): if
`v ≤ v̄`, `L ≤ L̄`, the `v`- and `L`-coefficients are nonpositive, `F_ℓ ≤ v`, `m ≥ 0` and
`N(v̄, L̄) - m(v̄ - F_ℓ) > 0`, then `N(v, L) > 0`. -/
theorem nh_N_pos_of_relax {t x k q v L vb Lb Fl m : ℝ} (hv : v ≤ vb) (hL : L ≤ Lb)
    (hNv : nhNv t x k q ≤ 0) (hNL : nhNL t x k q ≤ 0) (hF : Fl ≤ v) (hm : 0 ≤ m)
    (hP : 0 < nhN t x k q vb Lb - m * (vb - Fl)) : 0 < nhN t x k q v L := by
  rw [nhN_sub_v t x k q v vb L, nhN_sub_L t x k q vb L Lb]
  have h1 : 0 ≤ (v - vb) * nhNv t x k q := mul_nonneg_of_nonpos_of_nonpos (by linarith) hNv
  have h2 : 0 ≤ (L - Lb) * nhNL t x k q := mul_nonneg_of_nonpos_of_nonpos (by linarith) hNL
  have h3 : 0 ≤ m * (vb - Fl) := mul_nonneg hm (by linarith)
  linarith

end SmoothedOctagon

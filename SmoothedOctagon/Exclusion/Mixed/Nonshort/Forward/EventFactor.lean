module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Casimir
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor.LeadingSigns
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor.DiscriminantSigns

/-!
# Case M2, forward successor: elimination of the event factor

With `η = p/W`, `α = B(w_U - 1)/(pW)`, `β = pW/B`, the
diagonal on the stationary line at `w_U`, divided by `B`, is `h(q) = log q + αq + β/q + d`; on
`1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`, `k ≥ 1`, `v ≤ min(1, V)`:
`h(q) - h(1) < F_η(q) - g` for `q > 1` (`nsf_qelim`).

The logarithm bound `L₊` leaves `y/(6(y + 1)(y + 2))·(C₀ + C₁y + C₂y²)` (`nsf_qelim_id`); the `Cᵢ`
increase with `k` and decrease with `v` (`α(k, v) - α(1, V) ≤ β(k) - β(1) ≤ 0`), and at `k = 1`,
`v = V` the quadratic is positive since `C₂ > 0` and `4C₀C₂ > C₁²` (certificates `nsfCQC_pos`,
`nsfCQD_pos`).

## Main API

* `nsfEta`, `nsfAq`, `nsfBq`, `nsfQC0`, `nsfQC1`, `nsfQC2`; `nsf_qelim_id`; `nsf_QC_link`, `nsf_QD_link`.
* `nsf_qelim_quad`: `C₀ + C₁y + C₂y² > 0` for `y ≥ 0`; `nsf_qelim`: **the factor elimination**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `η = p/W`. -/
noncomputable def nsfEta (t x : ℝ) : ℝ := (t + x) / (1 + x)

/-- `α = B(w_U - 1)/(pW)`. -/
noncomputable def nsfAq (t x k v : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) * (nsfwU t x k v - 1) / ((t + x) * (1 + x))

/-- `β = pW/B`. -/
noncomputable def nsfBq (t x k : ℝ) : ℝ := (t + x) * (1 + x) / (k + 2 * t * x + x ^ 2)

/-- `C₀ = 12η² - 6η - 12α + 12β - 12`. -/
noncomputable def nsfQC0 (η α β : ℝ) : ℝ := 12 * η ^ 2 - 6 * η - 12 * α + 12 * β - 12
/-- `C₁ = 18η² - 7η - 18α + 6β - 12`. -/
noncomputable def nsfQC1 (η α β : ℝ) : ℝ := 18 * η ^ 2 - 7 * η - 18 * α + 6 * β - 12
/-- `C₂ = 6η² - η - 6α - 1`. -/
noncomputable def nsfQC2 (η α _β : ℝ) : ℝ := 6 * η ^ 2 - η - 6 * α - 1

/-- The elimination identity with `L₊` in place of `log q`: with `q = 1 + y`, the difference
`η + (η² - α)y + βy/(1 + y) - (1 + η(1 + y)/y)L₊(1 + y)` is
`y/(6(y + 1)(y + 2))·(C₀ + C₁y + C₂y²)`. -/
theorem nsf_qelim_id (η α β y : ℝ) (hy : 0 < y) :
    η + (η ^ 2 - α) * y + β * y / (1 + y) - (1 + η * (1 + y) / y) * nsrLp (1 + y) =
      y / (6 * (y + 1) * (y + 2)) * (nsfQC0 η α β + nsfQC1 η α β * y + nsfQC2 η α β * y ^ 2) := by
  unfold nsrLp nsfQC0 nsfQC1 nsfQC2
  have : (1 + y) ≠ 0 := by linarith
  have : (y + 1) ≠ 0 := by linarith
  have : (y + 2) ≠ 0 := by linarith
  have : (1 + y + 1) ≠ 0 := by linarith
  field_simp
  ring

/-- The cleared leading coefficient `𝒟C₂(1, V)` is the certificate polynomial `nsfCQC`. -/
theorem nsf_QC_link (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    (t * (t + x) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) * (1 + 2 * t * x + x ^ 2)) * nsfQC2 (nsfEta t x) (nsfAq t x 1 (nsfVq t x)) (nsfBq t x 1) =
      (nsfCQCD0_0 (2 / 5 - t) + nsfCQCD0_1 (2 / 5 - t) * (2 * t + x - 1) + nsfCQCD0_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCQCD0_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCQCD0_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCQCD0_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCQCD0_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCQCD0_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ)) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity
  have hB : 1 + 2 * t * x + x ^ 2 ≠ 0 := by positivity
  have ht' : t ≠ 0 := by linarith
  unfold nsfCQCD0_0 nsfCQCD0_1 nsfCQCD0_2 nsfCQCD0_3 nsfCQCD0_4 nsfCQCD0_5 nsfCQCD0_6 nsfCQCD0_7
  unfold nsfQC2 nsfEta nsfAq nsfwU nsfVq
  field_simp
  ring

/-- The cleared discriminant `𝒟²(4C₀C₂ - C₁²)(1, V)` is the certificate polynomial `nsfCQD`. -/
theorem nsf_QD_link (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    (t * (t + x) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) * (1 + 2 * t * x + x ^ 2)) ^ 2 * (4 * nsfQC0 (nsfEta t x) (nsfAq t x 1 (nsfVq t x)) (nsfBq t x 1) * nsfQC2 (nsfEta t x) (nsfAq t x 1 (nsfVq t x)) (nsfBq t x 1) - nsfQC1 (nsfEta t x) (nsfAq t x 1 (nsfVq t x)) (nsfBq t x 1) ^ 2) =
      (nsfCQDD0_0 (2 / 5 - t) + nsfCQDD0_1 (2 / 5 - t) * (2 * t + x - 1) + nsfCQDD0_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCQDD0_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCQDD0_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCQDD0_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCQDD0_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCQDD0_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCQDD0_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCQDD0_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCQDD0_10 (2 / 5 - t) * (2 * t + x - 1) ^ (10 : ℕ) + nsfCQDD0_11 (2 / 5 - t) * (2 * t + x - 1) ^ (11 : ℕ) + nsfCQDD0_12 (2 / 5 - t) * (2 * t + x - 1) ^ (12 : ℕ) + nsfCQDD0_13 (2 / 5 - t) * (2 * t + x - 1) ^ (13 : ℕ) + nsfCQDD0_14 (2 / 5 - t) * (2 * t + x - 1) ^ (14 : ℕ)) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity
  have hB : 1 + 2 * t * x + x ^ 2 ≠ 0 := by positivity
  have ht' : t ≠ 0 := by linarith
  unfold nsfCQDD0_0 nsfCQDD0_1 nsfCQDD0_2 nsfCQDD0_3 nsfCQDD0_4 nsfCQDD0_5 nsfCQDD0_6 nsfCQDD0_7 nsfCQDD0_8 nsfCQDD0_9 nsfCQDD0_10 nsfCQDD0_11 nsfCQDD0_12 nsfCQDD0_13 nsfCQDD0_14
  unfold nsfQC0 nsfQC1 nsfQC2 nsfEta nsfAq nsfBq nsfwU nsfVq
  field_simp
  ring

/-- `α(k, v) - α(1, v) ≤ β(k) - β(1)` for `k ≥ 1`, `v ≤ 1`. -/
theorem nsf_Aq_sub_le {t x k v : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hk : 1 ≤ k) (hv : v ≤ 1) :
    nsfAq t x k v - nsfAq t x 1 v ≤ nsfBq t x k - nsfBq t x 1 := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hB1 : 0 < 1 + 2 * t * x + x ^ 2 := by positivity
  have hp : 0 < t + x := by linarith
  have hW : 0 < 1 + x := by linarith
  have e : nsfAq t x k v - nsfAq t x 1 v - (nsfBq t x k - nsfBq t x 1) =
      x * (k - 1) * (t - 1) * (2 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + 2 * t ^ 2 + t * x ^ 3 + 2 * t * x ^ 2
        + 3 * t * x + (1 - v) * (x ^ 3 + 2 * x ^ 2)) /
        (t * (t + x) * (1 + x) * (k + 2 * t * x + x ^ 2) * (1 + 2 * t * x + x ^ 2)) := by
    unfold nsfAq nsfBq nsfwU
    field_simp
    ring
  have hS : 0 ≤ 2 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + 2 * t ^ 2 + t * x ^ 3 + 2 * t * x ^ 2
      + 3 * t * x + (1 - v) * (x ^ 3 + 2 * x ^ 2) := by
    have : 0 ≤ (1 - v) * (x ^ 3 + 2 * x ^ 2) := mul_nonneg (by linarith) (by positivity)
    have : 0 ≤ 2 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + 2 * t ^ 2 + t * x ^ 3 + 2 * t * x ^ 2 + 3 * t * x := by
      positivity
    linarith
  have : x * (k - 1) * (t - 1) * (2 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + 2 * t ^ 2 + t * x ^ 3 + 2 * t * x ^ 2
        + 3 * t * x + (1 - v) * (x ^ 3 + 2 * x ^ 2)) /
        (t * (t + x) * (1 + x) * (k + 2 * t * x + x ^ 2) * (1 + 2 * t * x + x ^ 2)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have h1 : 0 ≤ x * (k - 1) := mul_nonneg hx.le (by linarith)
    have h2 : x * (k - 1) * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)
    exact mul_nonpos_of_nonpos_of_nonneg h2 hS
  linarith

/-- `β(k) ≤ β(1)` for `k ≥ 1`. -/
theorem nsf_Bq_le {t x k : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 1 ≤ k) : nsfBq t x k ≤ nsfBq t x 1 := by
  unfold nsfBq
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

/-- `α(1, v) ≤ α(1, V)` for `v ≤ V`. -/
theorem nsf_Aq_mono_v {t x v V : ℝ} (ht : 0 < t) (hx : 0 < x) (hv : v ≤ V) :
    nsfAq t x 1 v ≤ nsfAq t x 1 V := by
  have hB1 : 0 < 1 + 2 * t * x + x ^ 2 := by positivity
  have e : nsfAq t x 1 V - nsfAq t x 1 v = (V - v) * (x * (x + 2) * (1 / t + x * (x + 2))) /
      ((1 + 2 * t * x + x ^ 2) * (t + x) * (1 + x)) := by
    unfold nsfAq nsfwU
    field_simp
    ring
  have : 0 ≤ (V - v) * (x * (x + 2) * (1 / t + x * (x + 2))) /
      ((1 + 2 * t * x + x ^ 2) * (t + x) * (1 + x)) := by
    apply div_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
  linarith

/-- **The event-factor quadratic is positive**: `C₀ + C₁y + C₂y² > 0` for `y ≥ 0`. -/
theorem nsf_qelim_quad {t x k v y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hv1 : v ≤ 1) (hvV : v ≤ nsfVq t x) (hy : 0 ≤ y) :
    0 < nsfQC0 (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) + nsfQC1 (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) * y
      + nsfQC2 (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) * y ^ 2 := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  -- the coefficients decrease to `k = 1`, `v = V`
  have hd1 := nsf_Aq_sub_le ht (by linarith) hx hk hv1
  have hd2 := nsf_Bq_le ht hx hk
  have hd3 := nsf_Aq_mono_v (t := t) ht hx hvV
  set η := nsfEta t x
  set α := nsfAq t x k v
  set α1 := nsfAq t x 1 (nsfVq t x)
  set β := nsfBq t x k
  set β1 := nsfBq t x 1
  have c0 : nsfQC0 η α1 β1 ≤ nsfQC0 η α β := by unfold nsfQC0; linarith
  have c1 : nsfQC1 η α1 β1 ≤ nsfQC1 η α β := by unfold nsfQC1; linarith
  have c2 : nsfQC2 η α1 β1 ≤ nsfQC2 η α β := by unfold nsfQC2; linarith
  -- the certificates at `k = 1`, `v = V`
  have hD : 0 < t * (t + x) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) * (1 + 2 * t * x + x ^ 2) := by positivity
  have hC2 : 0 < nsfQC2 η α1 β1 := by
    have h := nsfCQC_pos (2 / 5 - t) (2 * t + x - 1) 0 (by linarith) (by linarith) hj0 hj1 le_rfl
      (by norm_num)
    rw [← nsf_QC_link t x ht hx] at h
    exact pos_of_mul_pos_right h hD.le
  have hΔ : 0 < 4 * nsfQC0 η α1 β1 * nsfQC2 η α1 β1 - nsfQC1 η α1 β1 ^ 2 := by
    have h := nsfCQD_pos (2 / 5 - t) (2 * t + x - 1) 0 (by linarith) (by linarith) hj0 hj1 le_rfl
      (by norm_num)
    rw [← nsf_QD_link t x ht hx] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hq1 : 0 < nsfQC0 η α1 β1 + nsfQC1 η α1 β1 * y + nsfQC2 η α1 β1 * y ^ 2 := by
    have : 4 * nsfQC2 η α1 β1 * (nsfQC0 η α1 β1 + nsfQC1 η α1 β1 * y + nsfQC2 η α1 β1 * y ^ 2) =
        (2 * nsfQC2 η α1 β1 * y + nsfQC1 η α1 β1) ^ 2 + (4 * nsfQC0 η α1 β1 * nsfQC2 η α1 β1 - nsfQC1 η α1 β1 ^ 2) := by
      ring
    have h4 : 0 < 4 * nsfQC2 η α1 β1 * (nsfQC0 η α1 β1 + nsfQC1 η α1 β1 * y + nsfQC2 η α1 β1 * y ^ 2) := by
      rw [this]; positivity
    exact pos_of_mul_pos_right h4 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right c1 hy, mul_le_mul_of_nonneg_right c2 (sq_nonneg y)]

/-- **The factor elimination**: for `q > 1`,
`h(q) - h(1) < F_η(q) - g`, `h(q) - h(1) = log q + α(q - 1) + β(1/q - 1)`, `g = 1 - η + η²`. -/
theorem nsf_qelim {t x k q v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hv1 : v ≤ 1) (hvV : v ≤ nsfVq t x) (hq : 1 < q) :
    Real.log q + nsfAq t x k v * (q - 1) + nsfBq t x k * (1 / q - 1) <
      m2F (nsfEta t x) q - (1 - nsfEta t x + nsfEta t x ^ 2) := by
  have hx : 0 < x := by linarith
  have hy : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hη : 0 < nsfEta t x := by unfold nsfEta; positivity
  have hQ := nsf_qelim_quad ht0 ht1 hj0 hj1 hk hv1 hvV hy.le
  have hid := nsf_qelim_id (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) (q - 1) hy
  rw [show 1 + (q - 1) = q by ring] at hid
  have hLp := nsr_log_lt_Lp hq
  have hcoef : 0 < 1 + nsfEta t x * q / (q - 1) := by positivity
  have hpos : 0 < (q - 1) / (6 * (q - 1 + 1) * (q - 1 + 2)) := by
    apply div_pos hy; nlinarith
  rw [m2F_of_ne hq.ne']
  have key : 1 + nsfEta t x ^ 2 * q - nsfEta t x * q * Real.log q / (q - 1) - (1 - nsfEta t x + nsfEta t x ^ 2)
      - (Real.log q + nsfAq t x k v * (q - 1) + nsfBq t x k * (1 / q - 1)) =
      nsfEta t x + (nsfEta t x ^ 2 - nsfAq t x k v) * (q - 1) + nsfBq t x k * (q - 1) / q
        - (1 + nsfEta t x * q / (q - 1)) * Real.log q := by
    field_simp; ring
  have m := mul_lt_mul_of_pos_left hLp hcoef
  nlinarith [mul_pos hpos hQ]

end SmoothedOctagon

from links import *
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/')
Dd = "(t * (t + x) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) * (1 + 2 * t * x + x ^ 2))"
pre = "  have hW : (1 + x) ≠ 0 := by linarith\n  have hp : t + x ≠ 0 := by linarith\n  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity\n  have hB : 1 + 2 * t * x + x ^ 2 ≠ 0 := by positivity\n  have ht' : t ≠ 0 := by linarith\n"
args = "nsfEta t x) (nsfAq t x 1 (nsfVq t x)) (nsfBq t x 1)"
C = lambda i: f"nsfQC{i} (nsfEta t x) (nsfAq t x 1 (nsfVq t x)) (nsfBq t x 1)"
lqc = link2('nsfCQC', 'nsf_QC_link', '(t x : ℝ)', '(ht : 0 < t) (hx : 0 < x)',
  f"{Dd} * {C(2)}", yform_sub('nsfCQC', "(2 / 5 - t)", "(2 * t + x - 1)", "0", var='z'),
  'nsfQC2 nsfEta nsfAq nsfwU nsfVq', 'The cleared leading coefficient `𝒟C₂(1, V)` is the certificate polynomial `nsfCQC`.', pre=pre)
lqd = link2('nsfCQD', 'nsf_QD_link', '(t x : ℝ)', '(ht : 0 < t) (hx : 0 < x)',
  f"{Dd} ^ 2 * (4 * {C(0)} * {C(2)} - {C(1)} ^ 2)", yform_sub('nsfCQD', "(2 / 5 - t)", "(2 * t + x - 1)", "0", var='z'),
  'nsfQC0 nsfQC1 nsfQC2 nsfEta nsfAq nsfBq nsfwU nsfVq', 'The cleared discriminant `𝒟²(4C₀C₂ - C₁²)(1, V)` is the certificate polynomial `nsfCQD`.', pre=pre)
s = '''module

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
* `nsf_qelim_quad`: `C₀ + C₁y + C₂y² > 0` for `y ≥ 0`; `nsf_qelim`: **the factor elimination (5)**.
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

/-- The elimination identity, with `L₊` in place of `log q`. -/
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

''' + lqc + "\n" + lqd + '''
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

/-- **The event-factor quadratic is positive**-(26)). -/
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

/-- **The factor elimination**): for `q > 1`,
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
'''
open(LEAN + 'EventFactor.lean', 'w').write(s)

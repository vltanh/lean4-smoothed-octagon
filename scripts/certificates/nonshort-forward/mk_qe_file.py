from links import *
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/FwdHand/')
Dd = "(t * (t + x) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) * (1 + 2 * t * x + x ^ 2))"
pre = "  have hW : (1 + x) ≠ 0 := by linarith\n  have hp : t + x ≠ 0 := by linarith\n  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity\n  have hB : 1 + 2 * t * x + x ^ 2 ≠ 0 := by positivity\n  have ht' : t ≠ 0 := by linarith\n"
args = "fhEta t x) (fhAq t x 1 (fhVq t x)) (fhBq t x 1)"
C = lambda i: f"fhQC{i} (fhEta t x) (fhAq t x 1 (fhVq t x)) (fhBq t x 1)"
lqc = link2('fhCQC', 'fh_QC_link', '(t x : ℝ)', '(ht : 0 < t) (hx : 0 < x)',
  f"{Dd} * {C(2)}", yform_sub('fhCQC', "(2 / 5 - t)", "(2 * t + x - 1)", "0", var='z'),
  'fhQC2 fhEta fhAq fhwU fhVq', 'The cleared leading coefficient `𝒟C₂(1, V)` is the certificate polynomial `fhCQC`.', pre=pre)
lqd = link2('fhCQD', 'fh_QD_link', '(t x : ℝ)', '(ht : 0 < t) (hx : 0 < x)',
  f"{Dd} ^ 2 * (4 * {C(0)} * {C(2)} - {C(1)} ^ 2)", yform_sub('fhCQD', "(2 / 5 - t)", "(2 * t + x - 1)", "0", var='z'),
  'fhQC0 fhQC1 fhQC2 fhEta fhAq fhBq fhwU fhVq', 'The cleared discriminant `𝒟²(4C₀C₂ - C₁²)(1, V)` is the certificate polynomial `fhCQD`.', pre=pre)
s = '''module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Casimir
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Secant
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertQC
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertQD

/-!
# Case M2, forward successor by hand: elimination of the event factor

`MIXED_NONSHORT_FORWARD_Q_ELIMINATION`. With `η = p/W`, `α = B(w_U - 1)/(pW)`, `β = pW/B`, the
diagonal on the stationary line at `w_U`, divided by `B`, is `h(q) = log q + αq + β/q + d`; on
`1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`, `k ≥ 1`, `v ≤ min(1, V)`:
`h(q) - h(1) < F_η(q) - g` for `q > 1` (`fh_qelim`).

The logarithm bound `L₊` leaves `y/(6(y + 1)(y + 2))·(C₀ + C₁y + C₂y²)` (`fh_qelim_id`); the `Cᵢ`
increase with `k` and decrease with `v` (`α(k, v) - α(1, V) ≤ β(k) - β(1) ≤ 0`), and at `k = 1`,
`v = V` the quadratic is positive since `C₂ > 0` and `4C₀C₂ > C₁²` (certificates `CertQC`,
`CertQD`, in place of the concavity argument of §§5-7).

## Main API

* `fhEta`, `fhAq`, `fhBq`, `fhQC0`, `fhQC1`, `fhQC2`; `fh_qelim_id`; `fh_QC_link`, `fh_QD_link`.
* `fh_qelim_quad`: `C₀ + C₁y + C₂y² > 0` for `y ≥ 0`; `fh_qelim`: **the factor elimination (5)**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `η = p/W`. -/
noncomputable def fhEta (t x : ℝ) : ℝ := (t + x) / (1 + x)

/-- `α = B(w_U - 1)/(pW)`. -/
noncomputable def fhAq (t x k v : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) * (fhwU t x k v - 1) / ((t + x) * (1 + x))

/-- `β = pW/B`. -/
noncomputable def fhBq (t x k : ℝ) : ℝ := (t + x) * (1 + x) / (k + 2 * t * x + x ^ 2)

/-- `C₀ = 12η² - 6η - 12α + 12β - 12`. -/
noncomputable def fhQC0 (η α β : ℝ) : ℝ := 12 * η ^ 2 - 6 * η - 12 * α + 12 * β - 12
/-- `C₁ = 18η² - 7η - 18α + 6β - 12`. -/
noncomputable def fhQC1 (η α β : ℝ) : ℝ := 18 * η ^ 2 - 7 * η - 18 * α + 6 * β - 12
/-- `C₂ = 6η² - η - 6α - 1`. -/
noncomputable def fhQC2 (η α β : ℝ) : ℝ := 6 * η ^ 2 - η - 6 * α - 1

/-- The identity (8) of `MIXED_NONSHORT_FORWARD_Q_ELIMINATION`, with `L₊` in place of `log q`. -/
theorem fh_qelim_id (η α β y : ℝ) (hy : 0 < y) :
    η + (η ^ 2 - α) * y + β * y / (1 + y) - (1 + η * (1 + y) / y) * nhLp (1 + y) =
      y / (6 * (y + 1) * (y + 2)) * (fhQC0 η α β + fhQC1 η α β * y + fhQC2 η α β * y ^ 2) := by
  unfold nhLp fhQC0 fhQC1 fhQC2
  have : (1 + y) ≠ 0 := by linarith
  have : (y + 1) ≠ 0 := by linarith
  have : (y + 2) ≠ 0 := by linarith
  have : (1 + y + 1) ≠ 0 := by linarith
  field_simp
  ring

''' + lqc + "\n" + lqd + '''
/-- `α(k, v) - α(1, v) ≤ β(k) - β(1)` for `k ≥ 1`, `v ≤ 1`. -/
theorem fh_Aq_sub_le {t x k v : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hk : 1 ≤ k) (hv : v ≤ 1) :
    fhAq t x k v - fhAq t x 1 v ≤ fhBq t x k - fhBq t x 1 := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hB1 : 0 < 1 + 2 * t * x + x ^ 2 := by positivity
  have hp : 0 < t + x := by linarith
  have hW : 0 < 1 + x := by linarith
  have e : fhAq t x k v - fhAq t x 1 v - (fhBq t x k - fhBq t x 1) =
      x * (k - 1) * (t - 1) * (2 * t ^ 2 * x ^ 2 + 2 * t ^ 2 * x + 2 * t ^ 2 + t * x ^ 3 + 2 * t * x ^ 2
        + 3 * t * x + (1 - v) * (x ^ 3 + 2 * x ^ 2)) /
        (t * (t + x) * (1 + x) * (k + 2 * t * x + x ^ 2) * (1 + 2 * t * x + x ^ 2)) := by
    unfold fhAq fhBq fhwU
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
theorem fh_Bq_le {t x k : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 1 ≤ k) : fhBq t x k ≤ fhBq t x 1 := by
  unfold fhBq
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

/-- `α(1, v) ≤ α(1, V)` for `v ≤ V`. -/
theorem fh_Aq_mono_v {t x v V : ℝ} (ht : 0 < t) (hx : 0 < x) (hv : v ≤ V) :
    fhAq t x 1 v ≤ fhAq t x 1 V := by
  have hB1 : 0 < 1 + 2 * t * x + x ^ 2 := by positivity
  have e : fhAq t x 1 V - fhAq t x 1 v = (V - v) * (x * (x + 2) * (1 / t + x * (x + 2))) /
      ((1 + 2 * t * x + x ^ 2) * (t + x) * (1 + x)) := by
    unfold fhAq fhwU
    field_simp
    ring
  have : 0 ≤ (V - v) * (x * (x + 2) * (1 / t + x * (x + 2))) /
      ((1 + 2 * t * x + x ^ 2) * (t + x) * (1 + x)) := by
    apply div_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
  linarith

/-- **The event-factor quadratic is positive** (`MIXED_NONSHORT_FORWARD_Q_ELIMINATION` (13)-(26)). -/
theorem fh_qelim_quad {t x k v y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hv1 : v ≤ 1) (hvV : v ≤ fhVq t x) (hy : 0 ≤ y) :
    0 < fhQC0 (fhEta t x) (fhAq t x k v) (fhBq t x k) + fhQC1 (fhEta t x) (fhAq t x k v) (fhBq t x k) * y
      + fhQC2 (fhEta t x) (fhAq t x k v) (fhBq t x k) * y ^ 2 := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  -- the coefficients decrease to `k = 1`, `v = V`
  have hd1 := fh_Aq_sub_le ht (by linarith) hx hk hv1
  have hd2 := fh_Bq_le ht hx hk
  have hd3 := fh_Aq_mono_v (t := t) ht hx hvV
  set η := fhEta t x
  set α := fhAq t x k v
  set α1 := fhAq t x 1 (fhVq t x)
  set β := fhBq t x k
  set β1 := fhBq t x 1
  have c0 : fhQC0 η α1 β1 ≤ fhQC0 η α β := by unfold fhQC0; linarith
  have c1 : fhQC1 η α1 β1 ≤ fhQC1 η α β := by unfold fhQC1; linarith
  have c2 : fhQC2 η α1 β1 ≤ fhQC2 η α β := by unfold fhQC2; linarith
  -- the certificates at `k = 1`, `v = V`
  have hD : 0 < t * (t + x) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) * (1 + 2 * t * x + x ^ 2) := by positivity
  have hC2 : 0 < fhQC2 η α1 β1 := by
    have h := fhCQC_pos (2 / 5 - t) (2 * t + x - 1) 0 (by linarith) (by linarith) hj0 hj1 le_rfl
      (by norm_num)
    rw [← fh_QC_link t x ht hx] at h
    exact pos_of_mul_pos_right h hD.le
  have hΔ : 0 < 4 * fhQC0 η α1 β1 * fhQC2 η α1 β1 - fhQC1 η α1 β1 ^ 2 := by
    have h := fhCQD_pos (2 / 5 - t) (2 * t + x - 1) 0 (by linarith) (by linarith) hj0 hj1 le_rfl
      (by norm_num)
    rw [← fh_QD_link t x ht hx] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hq1 : 0 < fhQC0 η α1 β1 + fhQC1 η α1 β1 * y + fhQC2 η α1 β1 * y ^ 2 := by
    have : 4 * fhQC2 η α1 β1 * (fhQC0 η α1 β1 + fhQC1 η α1 β1 * y + fhQC2 η α1 β1 * y ^ 2) =
        (2 * fhQC2 η α1 β1 * y + fhQC1 η α1 β1) ^ 2 + (4 * fhQC0 η α1 β1 * fhQC2 η α1 β1 - fhQC1 η α1 β1 ^ 2) := by
      ring
    have h4 : 0 < 4 * fhQC2 η α1 β1 * (fhQC0 η α1 β1 + fhQC1 η α1 β1 * y + fhQC2 η α1 β1 * y ^ 2) := by
      rw [this]; positivity
    exact pos_of_mul_pos_right h4 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right c1 hy, mul_le_mul_of_nonneg_right c2 (sq_nonneg y)]

/-- **The factor elimination** (`MIXED_NONSHORT_FORWARD_Q_ELIMINATION` (5)): for `q > 1`,
`h(q) - h(1) < F_η(q) - g`, `h(q) - h(1) = log q + α(q - 1) + β(1/q - 1)`, `g = 1 - η + η²`. -/
theorem fh_qelim {t x k q v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hv1 : v ≤ 1) (hvV : v ≤ fhVq t x) (hq : 1 < q) :
    Real.log q + fhAq t x k v * (q - 1) + fhBq t x k * (1 / q - 1) <
      m2F (fhEta t x) q - (1 - fhEta t x + fhEta t x ^ 2) := by
  have hx : 0 < x := by linarith
  have hy : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hη : 0 < fhEta t x := by unfold fhEta; positivity
  have hQ := fh_qelim_quad ht0 ht1 hj0 hj1 hk hv1 hvV hy.le
  have hid := fh_qelim_id (fhEta t x) (fhAq t x k v) (fhBq t x k) (q - 1) hy
  rw [show 1 + (q - 1) = q by ring] at hid
  have hLp := nh_log_lt_Lp hq
  have hcoef : 0 < 1 + fhEta t x * q / (q - 1) := by positivity
  have hpos : 0 < (q - 1) / (6 * (q - 1 + 1) * (q - 1 + 2)) := by
    apply div_pos hy; nlinarith
  rw [m2F_of_ne hq.ne']
  have key : 1 + fhEta t x ^ 2 * q - fhEta t x * q * Real.log q / (q - 1) - (1 - fhEta t x + fhEta t x ^ 2)
      - (Real.log q + fhAq t x k v * (q - 1) + fhBq t x k * (1 / q - 1)) =
      fhEta t x + (fhEta t x ^ 2 - fhAq t x k v) * (q - 1) + fhBq t x k * (q - 1) / q
        - (1 + fhEta t x * q / (q - 1)) * Real.log q := by
    field_simp; ring
  have m := mul_lt_mul_of_pos_left hLp hcoef
  nlinarith [mul_pos hpos hQ]

end SmoothedOctagon
'''
open(LEAN + 'QElim.lean', 'w').write(s)

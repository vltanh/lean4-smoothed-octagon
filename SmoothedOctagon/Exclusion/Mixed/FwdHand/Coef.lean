module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Basic

/-!
# Case M2, forward successor by hand: the affine structure of the combined residual

`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` §§3, 5 and `MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS`
§§4-5. The combined residual `fhComb α M t x k q v L F` is affine in the incoming norm `v`, in the
logarithm `L` and in the floor `F`, and a concave quadratic in the shape `k` with leading
coefficient `-tq⁴(qJ - pW)`.

## Main API

* `fhCv`, `fh_comb_sub_v`: the `v`-coefficient; `fhCL`, `fh_comb_sub_L`; `fh_comb_sub_F`.
* `fh_comb_concave`: the exact three-point identity in `k`; `fh_comb_min`: a value of `k` in
  `[k₁, k₂]` gives at least the smaller endpoint value.
* `fh_Cv_le`: the coefficient bound
  `fhCv ≤ 4q((α + 1)W² - Jq²)N_v + 4q²W²k(qJ - pW) - 4qW²M` (`k ≥ 2t`, `qJ ≥ pW`), with
  `-N_v ≥ xqk` (`fh_Nv_le`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The `v`-coefficient of the cleared transport part:
`4(qJ - pW)(W² - q²Y)(kq² - t(W² - q²Y))`. -/
noncomputable def fhTPv (t x k q : ℝ) : ℝ :=
  4 * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) * ((1 + x) ^ 2 - q ^ 2 * (x * (x + 2))) *
    (k * q ^ 2 - t * ((1 + x) ^ 2 - q ^ 2 * (x * (x + 2))))

/-- The `v`-coefficient of `fhComb`. -/
noncomputable def fhCv (α M t x k q : ℝ) : ℝ :=
  4 * q * ((α + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nhNv t x k q + fhTPv t x k q
    - 4 * q * (1 + x) ^ 2 * M

/-- The `L`-coefficient of `fhComb`. -/
noncomputable def fhCL (α t x k q : ℝ) : ℝ :=
  4 * q * ((α + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nhNL t x k q

theorem fh_comb_sub_v (α M t x k q v v' L F : ℝ) :
    fhComb α M t x k q v L F - fhComb α M t x k q v' L F = (v - v') * fhCv α M t x k q := by
  unfold fhComb fhCv fhTPv fhTP fhKt fhHt
  rw [nhN_sub_v t x k q v v' L]
  ring

theorem fh_comb_sub_L (α M t x k q v L L' F : ℝ) :
    fhComb α M t x k q v L F - fhComb α M t x k q v L' F = (L - L') * fhCL α t x k q := by
  unfold fhComb fhCL
  rw [nhN_sub_L t x k q v L L']
  ring

theorem fh_comb_sub_F (α M t x k q v L F F' : ℝ) :
    fhComb α M t x k q v L F - fhComb α M t x k q v L F' = (F - F') * (4 * q * (1 + x) ^ 2 * M) := by
  unfold fhComb; ring

/-- **Concavity in the shape** (`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (6)): the exact three-point
identity of a quadratic with leading coefficient `-tq⁴(qJ - pW)`. -/
theorem fh_comb_concave (α M t x q v L F k k1 k2 : ℝ) :
    (k2 - k1) * fhComb α M t x k q v L F =
      (k2 - k) * fhComb α M t x k1 q v L F + (k - k1) * fhComb α M t x k2 q v L F
        + (k2 - k1) * (k - k1) * (k2 - k) * (t * q ^ 4 * (q * (t + x * (x + 2)) - (t + x) * (1 + x))) := by
  unfold fhComb fhTP fhKt fhHt fhE0 nhN
  ring

/-- **The endpoint principle**: on `[k₁, k₂]`, with `qJ ≥ pW`, the combined residual is at least
the smaller of its endpoint values; in particular it is positive if both are. -/
theorem fh_comb_pos_of_ends {α M t x q v L F k k1 k2 : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2))) (hk1 : k1 ≤ k) (hk2 : k ≤ k2)
    (h1 : 0 < fhComb α M t x k1 q v L F) (h2 : 0 < fhComb α M t x k2 q v L F) :
    0 < fhComb α M t x k q v L F := by
  have e := fh_comb_concave α M t x q v L F k k1 k2
  rcases eq_or_lt_of_le (hk1.trans hk2) with h12 | h12
  · have : k = k1 := le_antisymm (h12 ▸ hk2) hk1
    rw [this]; exact h1
  have hc : 0 ≤ t * q ^ 4 * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) := by
    have : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x) := by linarith
    positivity
  have h3 : 0 ≤ (k2 - k1) * (k - k1) * (k2 - k) := by
    have := sub_nonneg.2 hk1; have := sub_nonneg.2 hk2; have := sub_nonneg.2 h12.le; positivity
  have h4 : 0 ≤ (k2 - k) * fhComb α M t x k1 q v L F := mul_nonneg (by linarith) h1.le
  have h5 : 0 ≤ (k - k1) * fhComb α M t x k2 q v L F := mul_nonneg (by linarith) h2.le
  have h6 : 0 < (k2 - k) * fhComb α M t x k1 q v L F + (k - k1) * fhComb α M t x k2 q v L F := by
    rcases eq_or_lt_of_le hk2 with he | he
    · rw [he]; simp; exact mul_pos (by linarith) h2
    · have := mul_pos (sub_pos.2 he) h1; linarith
  have : 0 < (k2 - k1) * fhComb α M t x k q v L F := by
    rw [e]; nlinarith [mul_nonneg h3 hc]
  exact pos_of_mul_pos_right this (by linarith)

/-- `-N_v ≥ xqk` for `k ≥ 2t`, `q ≥ 1`. -/
theorem fh_Nv_le {t x k q : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) (hq : 1 ≤ q) (hk : 2 * t ≤ k) :
    nhNv t x k q ≤ -(x * q * k) := by
  unfold nhNv
  have h1 : 0 ≤ t * (1 + x) * (k - 2 * t) := by
    apply mul_nonneg (by positivity); linarith
  have h2 : 0 ≤ (q - 1) * (k * (x + 2) + t * x * (x + 2) ^ 2) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ k := by linarith
    positivity
  have h3 : 0 ≤ t * x := by positivity
  have : x * q * k ≤ x * q * (k + t * x + t * (1 + x) * (k - 2 * t)
      + (q - 1) * (k * (x + 2) + t * x * (x + 2) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

/-- **The coefficient bound** (`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (7)-(9)): the transport
contribution to the `v`-coefficient is at most `4q²W²k(qJ - pW)`. -/
theorem fh_Cv_le {α M t x k q : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k)
    (hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2))) (hxx : 0 ≤ x * (x + 2)) :
    fhCv α M t x k q ≤ 4 * q * ((α + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nhNv t x k q
      + 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x))
      - 4 * q * (1 + x) ^ 2 * M := by
  unfold fhCv fhTPv
  set b := (1 + x) ^ 2 - q ^ 2 * (x * (x + 2))
  have hb : b ≤ (1 + x) ^ 2 := by
    have : 0 ≤ q ^ 2 * (x * (x + 2)) := by positivity
    linarith
  have key : b * (k * q ^ 2 - t * b) ≤ k * q ^ 2 * (1 + x) ^ 2 := by
    have hkq : 0 ≤ k * q ^ 2 := by positivity
    rcases le_total 0 b with h0 | h0
    · nlinarith [mul_le_mul_of_nonneg_left hb hkq, mul_nonneg ht (sq_nonneg b)]
    · nlinarith [mul_nonneg ht (sq_nonneg b), mul_nonneg hkq (sq_nonneg (1 + x))]
  have hD' : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left key hD']

end SmoothedOctagon

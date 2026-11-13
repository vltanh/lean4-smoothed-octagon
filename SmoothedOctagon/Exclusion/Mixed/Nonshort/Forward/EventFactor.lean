module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Casimir
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor.Barrier

/-!
# Case M2, forward successor: elimination of the event factor

With `η = p/W`, `α = B(w_U - 1)/(pW)` and `β = pW/B`, the event comparison
reduces to a quadratic in `y = q - 1`. Shape and norm monotonicity lower its
coefficients to unit shape and the reciprocal-mean secant ceiling.

Write `ρ = η² - η/2 - α + β - 1` for the boundary gap and
`L = 12β - 6 - 2η` for the displacement. The gap inequality
`L² < 10(12 + L)ρ` controls the only possibly negative coefficient;
completing a square then proves the quadratic positive.
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

/-- The geometric ratios stay in a fixed interval on the small-gap strip. -/
private theorem nsf_event_unit_bounds {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30) :
    1 / 2 ≤ nsfEta t x ∧ nsfEta t x ≤ 31 / 60 ∧
      3 / 5 ≤ nsfBq t x 1 ∧ nsfBq t x 1 ≤ 7 / 10 := by
  let h := 1 - 2 * t
  let j := 2 * t + x - 1
  have hh : 1 / 5 ≤ h := by dsimp [h]; linarith only [ht1]
  have hh1 : h ≤ 1 / 3 := by dsimp [h]; linarith only [ht]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hj0 : 0 ≤ j := hj
  have hx : 0 < x := by linarith only [ht1, hj]
  have ht0 : 0 < t := by linarith only [ht]
  have hW : 0 < 1 + x := by positivity
  have hB : 0 < 1 + 2 * t * x + x ^ 2 := by positivity
  constructor
  · unfold nsfEta
    rw [le_div_iff₀ hW]
    linarith only [hj]
  constructor
  · unfold nsfEta
    rw [div_le_iff₀ hW]
    linarith only [hj1, hx]
  constructor
  · have heq : nsfBq t x 1 - (1 + h) / 2 = j * (2 + (h + j) * (1 - h)) / (2 * (1 + 2 * t * x + x ^ 2)) := by
      dsimp [h, j, nsfBq]
      field_simp
      ring
    have hs : 0 ≤ 1 - h := by linarith only [hh1]
    have hgap : 0 ≤ nsfBq t x 1 - (1 + h) / 2 := by rw [heq]; positivity
    linarith only [hgap, hh]
  · have hh2 : h ^ 2 ≤ 1 / 9 := by nlinarith only [hh0, hh1, sq_nonneg (h - 1 / 3)]
    have hj2 : j ^ 2 ≤ 1 / 900 := by
      have := pow_le_pow_left₀ hj0 hj1 2
      norm_num at this
      exact this
    have hhj : h * j ≤ 1 / 90 := by
      have := mul_le_mul hh1 hj1 hj0 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      nlinarith only [this]
    have heq : 7 * (1 + 2 * t * x + x ^ 2) - 10 * (t + x) * (1 + x) = 2 - 5 * h ^ 2 - 3 * h - 8 * h * j - 3 * j ^ 2 - 8 * j := by
      dsimp [h, j]; ring
    unfold nsfBq
    rw [div_le_iff₀ hB]
    have hpos : 0 ≤ 7 * (1 + 2 * t * x + x ^ 2) - 10 * (t + x) * (1 + x) := by
      rw [heq]
      linarith only [hh2, hh1, hhj, hj2, hj1]
    linarith only [hpos]

/-- Clearing the boundary-gap inequality uses only one secant denominator. -/
private theorem nsf_event_unit_gap {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30) :
    (12 * nsfBq t x 1 - 6 - 2 * nsfEta t x) ^ 2 <
      10 * (12 + (12 * nsfBq t x 1 - 6 - 2 * nsfEta t x)) *
        (nsfEta t x ^ 2 - nsfEta t x / 2 - nsfAq t x 1 (nsfVq t x) + nsfBq t x 1 - 1) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hx : 0 < x := by linarith only [ht1, hj]
  have hp : 0 < t + x := by positivity
  have hW : 0 < 1 + x := by positivity
  have hB : 0 < 1 + 2 * t * x + x ^ 2 := by positivity
  have hD : 0 < x ^ 2 + 6 * x + 6 := by positivity
  have hP := nsfEventBarrier_pos (h := 1 - 2 * t) (j := 2 * t + x - 1)
    (by linarith only [ht1]) (by linarith only [ht]) hj hj1
  have heq : nsfEventBarrier (1 - 2 * t) (2 * t + x - 1) =
      8 * t * (t + x) * (1 + x) ^ 3 * (1 + 2 * t * x + x ^ 2) ^ 2 * (x ^ 2 + 6 * x + 6) *
      (10 * (12 + (12 * nsfBq t x 1 - 6 - 2 * nsfEta t x)) *
        (nsfEta t x ^ 2 - nsfEta t x / 2 - nsfAq t x 1 (nsfVq t x) + nsfBq t x 1 - 1)
        -(12 * nsfBq t x 1 - 6 - 2 * nsfEta t x) ^ 2) := by
    unfold nsfEventBarrier nsfBq nsfEta nsfAq nsfwU nsfVq
    field_simp
    ring
  rw [heq] at hP
  have := pos_of_mul_pos_right hP (by positivity :
    0 ≤ 8 * t * (t + x) * (1 + x) ^ 3 * (1 + 2 * t * x + x ^ 2) ^ 2 * (x ^ 2 + 6 * x + 6))
  linarith only [this]

/-- A boundary gap dominates the only possibly negative coefficient. -/
private theorem event_gap_quad_pos {ρ L ε y : ℝ} (hL : 0 ≤ L) (hL1 : L ≤ 7 / 5)
    (hε : 0 ≤ ε) (hgap : L ^ 2 < 10 * (12 + L) * ρ) (hy : 0 ≤ y) :
    0 < 12 * ρ + (18 * ρ - L) * y + ((5 - L) / 2 + ε + 6 * ρ) * y ^ 2 := by
  have hρ : 0 < ρ := by
    by_contra hc
    push Not at hc
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 10 * (12 + L) by linarith only [hL]) hc
    nlinarith only [hgap, hm, sq_nonneg L]
  have hC : 0 < (5 - L) / 2 + ε + 6 * ρ := by linarith only [hL1, hε, hρ]
  by_cases hlinear : 0 ≤ 18 * ρ - L
  · positivity
  · have hdelta : 0 < 4 * (12 * ρ) * ((5 - L) / 2 + ε + 6 * ρ) - (18 * ρ - L) ^ 2 := by
      have hrem : 0 ≤ 2 * ρ * (L - 18 * ρ) := mul_nonneg (by positivity) (by linarith only [hlinear])
      have heps : 0 ≤ 48 * ε * ρ := by positivity
      nlinarith only [hgap, hrem, heps]
    have heq : 4 * ((5 - L) / 2 + ε + 6 * ρ) * (12 * ρ + (18 * ρ - L) * y + ((5 - L) / 2 + ε + 6 * ρ) * y ^ 2) =
        (2 * ((5 - L) / 2 + ε + 6 * ρ) * y + (18 * ρ - L)) ^ 2 +
        (4 * (12 * ρ) * ((5 - L) / 2 + ε + 6 * ρ) - (18 * ρ - L) ^ 2) := by ring
    have hpos : 0 < 4 * ((5 - L) / 2 + ε + 6 * ρ) * (12 * ρ + (18 * ρ - L) * y + ((5 - L) / 2 + ε + 6 * ρ) * y ^ 2) := by
      rw [heq]
      positivity
    exact pos_of_mul_pos_right hpos (by linarith only [hC])

/-- **The event-factor quadratic is positive**: `C₀ + C₁y + C₂y² > 0` for `y ≥ 0`. -/
theorem nsf_qelim_quad {t x k v y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hv1 : v ≤ 1) (hvV : v ≤ nsfVq t x) (hy : 0 ≤ y) :
    0 < nsfQC0 (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) + nsfQC1 (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) * y
       + nsfQC2 (nsfEta t x) (nsfAq t x k v) (nsfBq t x k) * y ^ 2 := by
  have ht : 0 < t := by linarith only [ht0]
  have hx : 0 < x := by linarith only [ht1, hj0]
  have hd1 := nsf_Aq_sub_le ht (by linarith only [ht1]) hx hk hv1
  have hd2 := nsf_Bq_le ht hx hk
  have hd3 := nsf_Aq_mono_v (t := t) ht hx hvV
  set η := nsfEta t x
  set α := nsfAq t x k v
  set α1 := nsfAq t x 1 (nsfVq t x)
  set β := nsfBq t x k
  set β1 := nsfBq t x 1
  have c0 : nsfQC0 η α1 β1 ≤ nsfQC0 η α β := by unfold nsfQC0; linarith only [hd1, hd2, hd3]
  have c1 : nsfQC1 η α1 β1 ≤ nsfQC1 η α β := by unfold nsfQC1; linarith only [hd1, hd2, hd3]
  have c2 : nsfQC2 η α1 β1 ≤ nsfQC2 η α β := by unfold nsfQC2; linarith only [hd1, hd2, hd3]
  obtain ⟨hη, hη1, hβ, hβ1⟩ := nsf_event_unit_bounds ht0 ht1 hj0 hj1
  let ρ := η ^ 2 - η / 2 - α1 + β1 - 1
  let L := 12 * β1 - 6 - 2 * η
  let ε := η - 1 / 2
  have hL : 0 ≤ L := by dsimp [L, η, β1]; linarith only [hη1, hβ]
  have hL1 : L ≤ 7 / 5 := by dsimp [L, η, β1]; linarith only [hη, hβ1]
  have hε : 0 ≤ ε := by dsimp [ε, η]; linarith only [hη]
  have hgap : L ^ 2 < 10 * (12 + L) * ρ := nsf_event_unit_gap ht0 ht1 hj0 hj1
  have hunit := event_gap_quad_pos hL hL1 hε hgap hy
  have hid : 12 * ρ + (18 * ρ - L) * y + ((5 - L) / 2 + ε + 6 * ρ) * y ^ 2 =
      nsfQC0 η α1 β1 + nsfQC1 η α1 β1 * y + nsfQC2 η α1 β1 * y ^ 2 := by
    dsimp [ρ, L, ε, nsfQC0, nsfQC1, nsfQC2]
    ring
  rw [hid] at hunit
  nlinarith only [hunit, c0, mul_le_mul_of_nonneg_right c1 hy,
    mul_le_mul_of_nonneg_right c2 (sq_nonneg y)]

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

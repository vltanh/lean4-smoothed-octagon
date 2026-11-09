module

public import SmoothedOctagon.Terminal.Words
public import SmoothedOctagon.Terminal.Analysis.FiveEnvelope

/-!
# Terminal comparison: five mixed pieces

A closed cycle with the word `0 1 0 2 0` has factors `(P(u), Q(u), r, Q(v), P(v))`,
`P(t) = (1 + t²)/(2t)`, `Q(t) = (1 + t²)/(1 - t²)`, `r = 4uv/((1 - u²)(1 - v²)) > 1`, for
`u, v ∈ (0, 1)` with `u + v + uv > 1` (tangent closure), initial margins `(2/√N)(A, d, B)` with
`d = (1 - u)(1 - v)`, `N = d(4 - d)`, `A = (1 + u)(1 - v)`, `B = (1 - u)(1 + v)` (state closure),
and raw cost `8 δ(u, v)`, `δ(u, v) = [2(d + 2) - (d/2)(F(u) + F(v))]/(4 - d)`. The strict
inequality `δ(u, v) > δ_oct` follows from the envelope bound on `F(u) + F(v)` and from
`d < d* = (2 - √2)²`.

* `Term.fiveF`, `Term.fiveDensity`, `Term.fivePiece_density_gt`, from `Term.fiveEnvelope`
  (`F(t) + 2 log(1 - t) ≤ F(t*) + 2 log(1 - t*)`, proved as `ra_five_envelope` in
  `Terminal/Analysis/FiveEnvelope`).
* `Term.Cycle.five_param` (closure, forced state and cost algebra),
  `Term.Cycle.five_rawCost_gt`.
-/

@[expose] public section

namespace SmoothedOctagon

namespace Term

open SmoothedPolygons

/-- `F(t) = ((1+t)/(1-t))² log((1+t²)/(2t)) + t⁻² log((1+t²)/(1-t²)) + log(2t/(1-t²))`. -/
noncomputable def fiveF (t : ℝ) : ℝ :=
  ((1 + t) / (1 - t)) ^ 2 * Real.log ((1 + t ^ 2) / (2 * t)) +
    Real.log ((1 + t ^ 2) / (1 - t ^ 2)) / t ^ 2 + Real.log (2 * t / (1 - t ^ 2))

/-- The density `δ(u, v)` of the mixed five-piece family. -/
noncomputable def fiveDensity (u v : ℝ) : ℝ :=
  (2 * ((1 - u) * (1 - v) + 2) - (1 - u) * (1 - v) / 2 * (fiveF u + fiveF v)) /
    (4 - (1 - u) * (1 - v))

/-- **The envelope**: `F(t) + 2 log(1 - t) ≤ F(t*) + 2 log(1 - t*)`,
`t* = √2 - 1`, `F(t*) = (3 + 2√2) log 2`. -/
theorem fiveEnvelope {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    fiveF t + 2 * Real.log (1 - t) ≤ (3 + 2 * √2) * Real.log 2 + 2 * Real.log (2 - √2) :=
  ra_five_envelope ht0 ht1

private lemma five_sqrt32 : √32 = 4 * √2 := by
  rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

private lemma five_sqrt8 : √8 = 2 * √2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- `d = (1 - u)(1 - v) < d* = (2 - √2)²` when `u + v + uv > 1`. -/
private lemma five_d_lt {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (huv : 1 < u + v + u * v) : (1 - u) * (1 - v) < (2 - √2) ^ 2 := by
  have hx : 0 < 1 - u := by linarith
  have hy : 0 < 1 - v := by linarith
  have hd : 0 < (1 - u) * (1 - v) := mul_pos hx hy
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2lo : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hw := Real.sqrt_nonneg ((1 - u) * (1 - v))
  have hw2 : √((1 - u) * (1 - v)) ^ 2 = (1 - u) * (1 - v) := Real.sq_sqrt hd.le
  have hsum : 2 * √((1 - u) * (1 - v)) ≤ (1 - u) + (1 - v) := by
    rw [Real.sqrt_mul hx.le]
    nlinarith [sq_nonneg (√(1 - u) - √(1 - v)), Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
  have hw1 : √((1 - u) * (1 - v)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  have hwlt : √((1 - u) * (1 - v)) < 2 - √2 := by nlinarith
  rw [← hw2]
  exact pow_lt_pow_left₀ hwlt hw (by norm_num)

/-- The numerical gap `3 + δ_oct < (3 + 2√2) log 2`. -/
private lemma five_gap : 3 + octagonDensity < (3 + 2 * √2) * Real.log 2 := by
  have h2lo : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl2lo := Real.log_two_gt_d9
  have hD : 0 < 2 * √2 - 1 := by linarith
  rw [octagonDensity, five_sqrt32, five_sqrt8, ← lt_sub_iff_add_lt', div_lt_iff₀ hD]
  nlinarith [mul_pos (sub_pos.2 h2lo) (sub_pos.2 hl2lo)]

/-- `B(d*) = δ_oct`: `2d* + 4 - K d* = δ_oct (4 - d*)`, `K = (3 + 2√2) log 2`. -/
private lemma five_boundary :
    2 * (2 - √2) ^ 2 + 4 - (3 + 2 * √2) * Real.log 2 * (2 - √2) ^ 2 =
      octagonDensity * (4 - (2 - √2) ^ 2) := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hK : (3 + 2 * √2) * Real.log 2 * (2 - √2) ^ 2 = 2 * Real.log 2 := by
    linear_combination (2 * √2 - 5) * Real.log 2 * hs2
  have hds : (2 - √2) ^ 2 = 6 - 4 * √2 := by linear_combination hs2
  have h2lo : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hD : 2 * √2 - 1 ≠ 0 := by linarith
  rw [hK, hds, octagonDensity, five_sqrt32, five_sqrt8]
  field_simp
  ring

/-- **The five-piece density inequality**: `δ(u, v) > δ_oct`. The envelope bound for `F(u)` and
`F(v)` gives `δ(u, v) ≥ B(d) = [2d + 4 - K d + d log(d/d*)]/(4 - d)` with `d = (1 - u)(1 - v)`,
`K = (3 + 2√2) log 2` and `d* = (2 - √2)²`. The tangent-line inequality
`d log d ≥ d log d* + d - d*`, the value `B(d*) = δ_oct` and the gap `3 + δ_oct < K` then give
`B(d) > δ_oct`, since `d < d*`. -/
theorem fivePiece_density_gt {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (huv : 1 < u + v + u * v) : octagonDensity < fiveDensity u v := by
  have hx : 0 < 1 - u := by linarith
  have hy : 0 < 1 - v := by linarith
  have hdlt := five_d_lt hu0 hu1 hv0 hv1 huv
  have hgap := five_gap
  have hbd := five_boundary
  have hFu := fiveEnvelope hu0 hu1
  have hFv := fiveEnvelope hv0 hv1
  have hlogd : Real.log ((1 - u) * (1 - v)) = Real.log (1 - u) + Real.log (1 - v) :=
    Real.log_mul hx.ne' hy.ne'
  have h2lo : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2hi : √2 < (1.4143 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hds0 : 0 < (2 - √2) ^ 2 := pow_pos (by linarith) 2
  have hd : 0 < (1 - u) * (1 - v) := mul_pos hx hy
  have hlogds : Real.log ((2 - √2) ^ 2) = 2 * Real.log (2 - √2) := by
    rw [Real.log_pow]; push_cast; ring
  have hds4 : (2 - √2) ^ 2 < 4 := by nlinarith
  rw [fiveDensity]
  generalize (1 - u) * (1 - v) = d at hdlt hlogd hd ⊢
  generalize (2 - √2) ^ 2 = ds at hdlt hbd hds0 hlogds hds4
  generalize (3 + 2 * √2) * Real.log 2 = K at hgap hbd hFu hFv
  have hF : fiveF u + fiveF v ≤ 2 * (K + Real.log ds) - 2 * Real.log d := by
    rw [hlogds, hlogd]; linarith
  have htan : d * Real.log d ≥ d * Real.log ds + d - ds := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hd hds0)
    rw [Real.log_div hd.ne' hds0.ne', inv_div] at this
    have h' : d * (1 - ds / d) ≤ d * (Real.log d - Real.log ds) :=
      mul_le_mul_of_nonneg_left this hd.le
    rw [mul_sub, mul_div_cancel₀ _ hd.ne', mul_one] at h'
    linarith
  have h4d : 0 < 4 - d := by linarith
  rw [lt_div_iff₀ h4d]
  have hmul : d / 2 * (fiveF u + fiveF v) ≤ d / 2 * (2 * (K + Real.log ds) - 2 * Real.log d) :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  nlinarith [mul_pos (sub_pos.2 hgap) (sub_pos.2 hdlt)]

private lemma tm_entries5 {M : Mat2} (h : M = triR) :
    M 0 0 = 0 ∧ M 0 1 = 1 ∧ M 1 0 = -1 ∧ M 1 1 = 1 := by
  subst h; simp [triR]

theorem five_closure {p q r s z : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s)
    (hz : 1 < z)
    (h : triFactor 0 p * (triFactor 1 q * (triFactor 0 r * (triFactor 2 s * triFactor 0 z))) =
      triR) :
    p ^ 2 * (q ^ 2 - 1) = q ^ 2 ∧ z ^ 2 * (s ^ 2 - 1) = s ^ 2 ∧
      r ^ 2 = (q ^ 2 - 1) * (s ^ 2 - 1) := by
  have p0 : 0 < p := by linarith
  have q0 : 0 < q := by linarith
  have r0 : 0 < r := by linarith
  have s0 : 0 < s := by linarith
  have z0 : 0 < z := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries5 h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  field_simp at e00 e01 e10 e11
  have hr2 : r ^ 2 = (q ^ 2 - 1) * (s ^ 2 - 1) := by
    rcases e00 with h | h
    · linarith
    · have : z * (r ^ 2 + (q ^ 2 - 1) * (1 - s ^ 2)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · linarith
  refine ⟨?_, ?_, hr2⟩
  · have : s * (p ^ 2 * (q ^ 2 - 1) - q ^ 2) = 0 := by linear_combination p * e01 - q * e11
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : q * (z ^ 2 * (s ^ 2 - 1) - s ^ 2) = 0 := by linear_combination (-z) * e10 - s * e11
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith

/-- The twist residuals of the word `0 1 0 2 0`, as polynomials. -/
private lemma five_key {u v x0 x1 x2 m11 m12 m20 m22 m31 m32 m40 m41 m50 m51 : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (s0g : m11 = (x0 + x1) * ((1 + u ^ 2) / (2 * u)) - x0)
    (s0d : m12 = (x0 + x2) / ((1 + u ^ 2) / (2 * u)) - x0)
    (s1g : m22 = (m11 + m12) * ((1 + u ^ 2) / (1 - u ^ 2)) - m11)
    (s1d : m20 = (m11 + x0) / ((1 + u ^ 2) / (1 - u ^ 2)) - m11)
    (s2g : m31 = (m20 + m11) * (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) - m20)
    (s2d : m32 = (m20 + m22) / (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) - m20)
    (s3g : m40 = (m32 + m20) * ((1 + v ^ 2) / (1 - v ^ 2)) - m32)
    (s3d : m41 = (m32 + m31) / ((1 + v ^ 2) / (1 - v ^ 2)) - m32)
    (s4g : m51 = (m40 + m41) * ((1 + v ^ 2) / (2 * v)) - m40)
    (s4a : m50 = m40) :
    m50 - x2 = u ^ 2 * v * x0 + u ^ 2 * v * x1 - 2 * u * v * x0 - u * x0 - u * x1 + v * x0 +
        v * x2 + x0 - x2 ∧
      m51 - x0 = u ^ 2 * v ^ 2 * x0 + u ^ 2 * v ^ 2 * x1 - u ^ 2 * v * x0 - u ^ 2 * v * x1 -
        2 * u * v ^ 2 * x0 - 2 * u * v * x1 + u * x0 + u * x1 + v ^ 2 * x0 + v ^ 2 * x2 +
        v * x0 - v * x2 - x0 + x1 := by
  have h1 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - v ^ 2 ≠ 0 := by nlinarith
  have h3 : 1 + u ^ 2 ≠ 0 := by positivity
  have h4 : 1 + v ^ 2 ≠ 0 := by positivity
  have hu := hu0.ne'
  have hv := hv0.ne'
  constructor
  · rw [s4a, s3g, s2d, s1g, s1d, s0g, s0d]
    field_simp
    ring
  · rw [s4g, s3g, s3d, s2d, s2g, s1g, s1d, s0g, s0d]
    field_simp
    ring

/-- `rawArc` is homogeneous of degree two in the margins. -/
private lemma rawArc_smul (l X Y Z q : ℝ) :
    rawArc (l * X) (l * Y) (l * Z) q =
      l ^ 2 * (X * ((X + Y) * (q - 1) + (X + Z) * (1 - q⁻¹)) - X ^ 2 * Real.log q) := by
  unfold rawArc; ring

/-- The algebraic part of the five-piece cost. -/
private lemma five_alg {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    (2 * ((1 + u) * (1 - v))) * (((2 * ((1 + u) * (1 - v))) + (2 * ((1 - u) * (1 - v)))) * (((1 + u ^ 2) / (2 * u)) - 1) + ((2 * ((1 + u) * (1 - v))) + (2 * ((1 - u) * (1 + v)))) * (1 - ((1 + u ^ 2) / (2 * u))⁻¹)) +
      (2 * ((1 - u) * (1 - v)) / u) * (((2 * ((1 - u) * (1 - v)) / u) + (2 * (u - 1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 2 * u - v + 1) / (u ^ 2 + 1))) * (((1 + u ^ 2) / (1 - u ^ 2)) - 1) + ((2 * ((1 - u) * (1 - v)) / u) + (2 * ((1 + u) * (1 - v)))) * (1 - ((1 + u ^ 2) / (1 - u ^ 2))⁻¹)) +
      (2 * ((1 - u) * (1 - v))) * (((2 * ((1 - u) * (1 - v))) + (2 * ((1 - u) * (1 - v)) / u)) * ((4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) - 1) + ((2 * ((1 - u) * (1 - v))) + (-(2 * (u ^ 2 * v - u ^ 2 - 4 * u - v + 1)) / (u + 1))) * (1 - (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2)))⁻¹)) +
      (2 * ((1 - u) * (1 - v)) / v) * (((2 * ((1 - u) * (1 - v)) / v) + (2 * ((1 - u) * (1 - v)))) * (((1 + v ^ 2) / (1 - v ^ 2)) - 1) + ((2 * ((1 - u) * (1 - v)) / v) + (-(2 * (u * v ^ 2 - u - v ^ 2 - 4 * v + 1)) / (v + 1))) * (1 - ((1 + v ^ 2) / (1 - v ^ 2))⁻¹)) +
      (2 * ((1 - u) * (1 + v))) * (((2 * ((1 - u) * (1 + v))) + (2 * (v - 1) * (u * v ^ 2 - 2 * u * v - u - v ^ 2 - 2 * v + 1) / (v ^ 2 + 1))) * (((1 + v ^ 2) / (2 * v)) - 1) + ((2 * ((1 - u) * (1 + v))) + (2 * ((1 - u) * (1 - v)) / v)) * (1 - ((1 + v ^ 2) / (2 * v))⁻¹)) =
      16 * ((1 - u) * (1 - v)) * ((1 - u) * (1 - v) + 2) := by
  have h1 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - v ^ 2 ≠ 0 := by nlinarith
  have h1' : 1 - u ≠ 0 := by linarith
  have h2' : 1 - v ≠ 0 := by linarith
  have h3 : u + 1 ≠ 0 := by linarith
  have h4 : v + 1 ≠ 0 := by linarith
  have h5 : u ^ 2 + 1 ≠ 0 := by positivity
  have h6 : v ^ 2 + 1 ≠ 0 := by positivity
  have hu := hu0.ne'
  have hv := hv0.ne'
  field_simp
  ring

/-- The logarithmic part of the five-piece cost. -/
private lemma five_log {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    (2 * ((1 + u) * (1 - v))) ^ 2 * Real.log ((1 + u ^ 2) / (2 * u)) +
      (2 * ((1 - u) * (1 - v)) / u) ^ 2 * Real.log ((1 + u ^ 2) / (1 - u ^ 2)) +
      (2 * ((1 - u) * (1 - v))) ^ 2 * Real.log (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) +
      (2 * ((1 - u) * (1 - v)) / v) ^ 2 * Real.log ((1 + v ^ 2) / (1 - v ^ 2)) +
      (2 * ((1 - u) * (1 + v))) ^ 2 * Real.log ((1 + v ^ 2) / (2 * v)) =
      4 * ((1 - u) * (1 - v)) ^ 2 * (fiveF u + fiveF v) := by
  unfold fiveF
  have h1 : 0 < 1 - u ^ 2 := by nlinarith
  have h2 : 0 < 1 - v ^ 2 := by nlinarith
  have hr : Real.log (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) =
      Real.log (2 * u / (1 - u ^ 2)) + Real.log (2 * v / (1 - v ^ 2)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  rw [hr]
  have h1' : 1 - u ≠ 0 := by linarith
  have h2' : 1 - v ≠ 0 := by linarith
  have hu := hu0.ne'
  have hv := hv0.ne'
  field_simp
  ring


private lemma five_cost {u v l : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hl : l ^ 2 * (((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) = 1) :
    rawArc (l * (2 * ((1 + u) * (1 - v)))) (l * (2 * ((1 - u) * (1 - v)))) (l * (2 * ((1 - u) * (1 + v)))) ((1 + u ^ 2) / (2 * u)) +
      rawArc (l * (2 * ((1 - u) * (1 - v)) / u)) (l * (2 * (u - 1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 2 * u - v + 1) / (u ^ 2 + 1))) (l * (2 * ((1 + u) * (1 - v)))) ((1 + u ^ 2) / (1 - u ^ 2)) +
      rawArc (l * (2 * ((1 - u) * (1 - v)))) (l * (2 * ((1 - u) * (1 - v)) / u)) (l * (-(2 * (u ^ 2 * v - u ^ 2 - 4 * u - v + 1)) / (u + 1))) (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) +
      rawArc (l * (2 * ((1 - u) * (1 - v)) / v)) (l * (2 * ((1 - u) * (1 - v)))) (l * (-(2 * (u * v ^ 2 - u - v ^ 2 - 4 * v + 1)) / (v + 1))) ((1 + v ^ 2) / (1 - v ^ 2)) +
      rawArc (l * (2 * ((1 - u) * (1 + v)))) (l * (2 * (v - 1) * (u * v ^ 2 - 2 * u * v - u - v ^ 2 - 2 * v + 1) / (v ^ 2 + 1))) (l * (2 * ((1 - u) * (1 - v)) / v)) ((1 + v ^ 2) / (2 * v)) = 8 * fiveDensity u v := by
  have key : rawArc (l * (2 * ((1 + u) * (1 - v)))) (l * (2 * ((1 - u) * (1 - v)))) (l * (2 * ((1 - u) * (1 + v)))) ((1 + u ^ 2) / (2 * u)) +
      rawArc (l * (2 * ((1 - u) * (1 - v)) / u)) (l * (2 * (u - 1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 2 * u - v + 1) / (u ^ 2 + 1))) (l * (2 * ((1 + u) * (1 - v)))) ((1 + u ^ 2) / (1 - u ^ 2)) +
      rawArc (l * (2 * ((1 - u) * (1 - v)))) (l * (2 * ((1 - u) * (1 - v)) / u)) (l * (-(2 * (u ^ 2 * v - u ^ 2 - 4 * u - v + 1)) / (u + 1))) (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) +
      rawArc (l * (2 * ((1 - u) * (1 - v)) / v)) (l * (2 * ((1 - u) * (1 - v)))) (l * (-(2 * (u * v ^ 2 - u - v ^ 2 - 4 * v + 1)) / (v + 1))) ((1 + v ^ 2) / (1 - v ^ 2)) +
      rawArc (l * (2 * ((1 - u) * (1 + v)))) (l * (2 * (v - 1) * (u * v ^ 2 - 2 * u * v - u - v ^ 2 - 2 * v + 1) / (v ^ 2 + 1))) (l * (2 * ((1 - u) * (1 - v)) / v)) ((1 + v ^ 2) / (2 * v)) = l ^ 2 * (((2 * ((1 + u) * (1 - v))) * (((2 * ((1 + u) * (1 - v))) + (2 * ((1 - u) * (1 - v)))) * (((1 + u ^ 2) / (2 * u)) - 1) + ((2 * ((1 + u) * (1 - v))) + (2 * ((1 - u) * (1 + v)))) * (1 - ((1 + u ^ 2) / (2 * u))⁻¹)) +
      (2 * ((1 - u) * (1 - v)) / u) * (((2 * ((1 - u) * (1 - v)) / u) + (2 * (u - 1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 2 * u - v + 1) / (u ^ 2 + 1))) * (((1 + u ^ 2) / (1 - u ^ 2)) - 1) + ((2 * ((1 - u) * (1 - v)) / u) + (2 * ((1 + u) * (1 - v)))) * (1 - ((1 + u ^ 2) / (1 - u ^ 2))⁻¹)) +
      (2 * ((1 - u) * (1 - v))) * (((2 * ((1 - u) * (1 - v))) + (2 * ((1 - u) * (1 - v)) / u)) * ((4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) - 1) + ((2 * ((1 - u) * (1 - v))) + (-(2 * (u ^ 2 * v - u ^ 2 - 4 * u - v + 1)) / (u + 1))) * (1 - (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2)))⁻¹)) +
      (2 * ((1 - u) * (1 - v)) / v) * (((2 * ((1 - u) * (1 - v)) / v) + (2 * ((1 - u) * (1 - v)))) * (((1 + v ^ 2) / (1 - v ^ 2)) - 1) + ((2 * ((1 - u) * (1 - v)) / v) + (-(2 * (u * v ^ 2 - u - v ^ 2 - 4 * v + 1)) / (v + 1))) * (1 - ((1 + v ^ 2) / (1 - v ^ 2))⁻¹)) +
      (2 * ((1 - u) * (1 + v))) * (((2 * ((1 - u) * (1 + v))) + (2 * (v - 1) * (u * v ^ 2 - 2 * u * v - u - v ^ 2 - 2 * v + 1) / (v ^ 2 + 1))) * (((1 + v ^ 2) / (2 * v)) - 1) + ((2 * ((1 - u) * (1 + v))) + (2 * ((1 - u) * (1 - v)) / v)) * (1 - ((1 + v ^ 2) / (2 * v))⁻¹))) - ((2 * ((1 + u) * (1 - v))) ^ 2 * Real.log ((1 + u ^ 2) / (2 * u)) +
      (2 * ((1 - u) * (1 - v)) / u) ^ 2 * Real.log ((1 + u ^ 2) / (1 - u ^ 2)) +
      (2 * ((1 - u) * (1 - v))) ^ 2 * Real.log (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) +
      (2 * ((1 - u) * (1 - v)) / v) ^ 2 * Real.log ((1 + v ^ 2) / (1 - v ^ 2)) +
      (2 * ((1 - u) * (1 + v))) ^ 2 * Real.log ((1 + v ^ 2) / (2 * v)))) := by
    simp only [rawArc_smul]; ring
  have h4 : 4 - (1 - u) * (1 - v) ≠ 0 := by nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - u) (by linarith : (0:ℝ) < 1 - v)]
  rw [key, five_alg hu0 hu1 hv0 hv1, five_log hu0 hu1 hv0 hv1, fiveDensity, ← mul_div_assoc,
    eq_div_iff h4]
  linear_combination (16 * ((1 - u) * (1 - v) + 2) - 4 * ((1 - u) * (1 - v)) * (fiveF u + fiveF v)) * hl

/-- State closure for `0 1 0 2 0`, linear part: `d x₀ = A x₁` and `d x₂ = B x₁`. -/
private lemma five_lin {u v x0 x1 x2 m11 m12 m20 m22 m31 m32 m40 m41 m50 m51 : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (s0g : m11 = (x0 + x1) * ((1 + u ^ 2) / (2 * u)) - x0)
    (s0d : m12 = (x0 + x2) / ((1 + u ^ 2) / (2 * u)) - x0)
    (s1g : m22 = (m11 + m12) * ((1 + u ^ 2) / (1 - u ^ 2)) - m11)
    (s1d : m20 = (m11 + x0) / ((1 + u ^ 2) / (1 - u ^ 2)) - m11)
    (s2g : m31 = (m20 + m11) * (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) - m20)
    (s2d : m32 = (m20 + m22) / (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) - m20)
    (s3g : m40 = (m32 + m20) * ((1 + v ^ 2) / (1 - v ^ 2)) - m32)
    (s3d : m41 = (m32 + m31) / ((1 + v ^ 2) / (1 - v ^ 2)) - m32)
    (s4g : m51 = (m40 + m41) * ((1 + v ^ 2) / (2 * v)) - m40)
    (s4a : m50 = m40) (tw0 : m50 = x2) (tw1 : m51 = x0) :
    (1 - u) * (1 - v) * x0 = (1 + u) * (1 - v) * x1 ∧ (1 - u) * (1 - v) * x2 = (1 - u) * (1 + v) * x1 := by
  obtain ⟨k0, k1⟩ := five_key hu0 hu1 hv0 hv1 s0g s0d s1g s1d s2g s2d s3g s3d s4g s4a
  rw [tw0, sub_self] at k0
  rw [tw1, sub_self] at k1
  have huv : u * v - 1 ≠ 0 := by nlinarith [mul_lt_mul'' hu1 hv1 hu0.le hv0.le]
  constructor
  · have : (u * v - 1) * ((1 - u) * (1 - v) * x0 - (1 + u) * (1 - v) * x1) = 0 := by
      linear_combination (-(v ^ 2 - v)) * k0 - (1 - v) * k1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h huv
    · linarith
  · have : (u * v - 1) * ((1 - u) * (1 - v) * x2 - (1 - u) * (1 + v) * x1) = 0 := by
      linear_combination (-(-u ^ 2 * v ^ 2 + u ^ 2 * v + 2 * u * v ^ 2 - u - v ^ 2 - v + 1)) * k0 -
        (u ^ 2 * v - 2 * u * v - u + v + 1) * k1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h huv
    · linarith

/-- State closure for `0 1 0 2 0`, scale: the quadric gives the margins `(2/√N)(A, d, B)`. -/
private lemma five_scale {u v x0 x1 x2 : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v)
    (hv1 : v < 1) (hx1 : 0 < x1) (e0 : (1 - u) * (1 - v) * x0 = (1 + u) * (1 - v) * x1) (e1 : (1 - u) * (1 - v) * x2 = (1 - u) * (1 + v) * x1)
    (hq4 : x0 * x1 + x1 * x2 + x2 * x0 = 4) :
    x0 = 2 * ((1 + u) * (1 - v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) ∧ x1 = 2 * ((1 - u) * (1 - v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) ∧ x2 = 2 * ((1 - u) * (1 + v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) := by
  have hd : 0 < (1 - u) * (1 - v) := mul_pos (by linarith) (by linarith)
  have hN : 0 < ((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v)) := mul_pos hd (by nlinarith)
  have hsq : x1 ^ 2 * (((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) = (2 * ((1 - u) * (1 - v))) ^ 2 := by
    linear_combination ((1 - u) * (1 - v)) ^ 2 * hq4 - ((1 - u) * (1 - v) * x1 + (1 - u) * (1 + v) * x1) * e0 - ((1 - u) * (1 - v) * x1 + (1 - u) * (1 - v) * x0) * e1
  have hsN : 0 < √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) := Real.sqrt_pos.2 hN
  have hsN2 : √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) ^ 2 = ((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v)) := Real.sq_sqrt hN.le
  have hx1' : x1 * √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) = 2 * ((1 - u) * (1 - v)) := by
    rw [← hsN2, ← mul_pow] at hsq
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  have hx1e : x1 = 2 * ((1 - u) * (1 - v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) := by rw [eq_div_iff hsN.ne', hx1']
  refine ⟨?_, hx1e, ?_⟩
  · rw [hx1e] at e0; field_simp at e0 ⊢; nlinarith
  · rw [hx1e] at e1; field_simp at e1 ⊢; nlinarith

private lemma five_u {q : ℝ} (hq : 1 < q) : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ q = (1 + u ^ 2) / (1 - u ^ 2) := by
  have h0 : 0 ≤ (q - 1) / (q + 1) := div_nonneg (by linarith) (by linarith)
  refine ⟨√((q - 1) / (q + 1)), Real.sqrt_pos.2 (div_pos (by linarith) (by linarith)), ?_, ?_⟩
  · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]; linarith
  · rw [Real.sq_sqrt h0]
    have : q + 1 ≠ 0 := by linarith
    field_simp
    ring

private lemma five_P {p q u : ℝ} (hp : 0 < p) (hu0 : 0 < u) (hu1 : u < 1)
    (hq : q = (1 + u ^ 2) / (1 - u ^ 2)) (h : p ^ 2 * (q ^ 2 - 1) = q ^ 2) :
    p = (1 + u ^ 2) / (2 * u) := by
  have h1 : 0 < 1 - u ^ 2 := by nlinarith
  rw [hq] at h
  field_simp at h
  have h2 : (p * (2 * u)) ^ 2 = (1 + u ^ 2) ^ 2 := by nlinarith [h]
  have h3 := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h2
  rw [eq_div_iff (by positivity), h3]

private lemma five_R {r q s u v : ℝ} (hr : 0 < r) (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v)
    (hv1 : v < 1) (hq : q = (1 + u ^ 2) / (1 - u ^ 2)) (hs : s = (1 + v ^ 2) / (1 - v ^ 2))
    (h : r ^ 2 = (q ^ 2 - 1) * (s ^ 2 - 1)) : r = 4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2)) := by
  have h1 : 0 < 1 - u ^ 2 := by nlinarith
  have h2 : 0 < 1 - v ^ 2 := by nlinarith
  rw [hq, hs] at h
  field_simp at h
  have h3 : (r * ((1 - u ^ 2) * (1 - v ^ 2))) ^ 2 = (4 * u * v) ^ 2 := by nlinarith [h]
  have h4 := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h3
  rw [eq_div_iff (by positivity), h4]

namespace Cycle

/-- Tangent closure of `0 1 0 2 0`: the factors are `(P(u), Q(u), r, Q(v), P(v))`. -/
private lemma five_factors (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) :
    ∃ u v : ℝ, 0 < u ∧ u < 1 ∧ 0 < v ∧ v < 1 ∧ 1 < u + v + u * v ∧ c.q 0 = ((1 + u ^ 2) / (2 * u)) ∧
      c.q 1 = ((1 + u ^ 2) / (1 - u ^ 2)) ∧ c.q 2 = (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) ∧ c.q 3 = ((1 + v ^ 2) / (1 - v ^ 2)) ∧ c.q 4 = ((1 + v ^ 2) / (2 * v)) := by
  have hcl := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at hcl
  simp only [Matrix.mul_assoc, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, h0, h1, h2,
    h3, h4] at hcl
  obtain ⟨hp2, hz2, hr2⟩ := five_closure (c.one_lt_q 0) (c.one_lt_q 1) (c.one_lt_q 2)
    (c.one_lt_q 3) (c.one_lt_q 4) hcl
  obtain ⟨u, hu0, hu1, hq1⟩ := five_u (c.one_lt_q 1)
  obtain ⟨v, hv0, hv1, hq3⟩ := five_u (c.one_lt_q 3)
  have hq0 := five_P (c.q_pos 0) hu0 hu1 hq1 hp2
  have hq4 := five_P (c.q_pos 4) hv0 hv1 hq3 hz2
  have hq2 := five_R (c.q_pos 2) hu0 hu1 hv0 hv1 hq1 hq3 hr2
  have huv : 1 < u + v + u * v := by
    have hr1 := c.one_lt_q 2
    have h1u : 0 < 1 - u ^ 2 := by nlinarith
    have h1v : 0 < 1 - v ^ 2 := by nlinarith
    rw [hq2, lt_div_iff₀ (by positivity)] at hr1
    have key : (u + v + u * v - 1) * (u + v + 1 - u * v) = 4 * u * v - (1 - u ^ 2) * (1 - v ^ 2) := by
      ring
    have hpos : 0 < u + v + 1 - u * v := by nlinarith [mul_lt_mul'' hu1 hv1 hu0.le hv0.le]
    have : 0 < (u + v + u * v - 1) * (u + v + 1 - u * v) := by rw [key]; linarith
    have := pos_of_mul_pos_left this hpos.le
    linarith
  exact ⟨u, v, hu0, hu1, hv0, hv1, huv, hq0, hq1, hq2, hq3, hq4⟩

/-- State closure of `0 1 0 2 0`: the initial margins are `(2/√N)(A, d, B)`. -/
private lemma five_margins (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hv0 : 0 < v) (hv1 : v < 1) (hq0 : c.q 0 = ((1 + u ^ 2) / (2 * u))) (hq1 : c.q 1 = ((1 + u ^ 2) / (1 - u ^ 2)))
    (hq2 : c.q 2 = (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2)))) (hq3 : c.q 3 = ((1 + v ^ 2) / (1 - v ^ 2)))
    (hq4 : c.q 4 = ((1 + v ^ 2) / (2 * v))) :
    c.m 0 0 = 2 * ((1 + u) * (1 - v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) ∧ c.m 0 1 = 2 * ((1 - u) * (1 - v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) ∧
      c.m 0 2 = 2 * ((1 - u) * (1 + v)) / √(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) := by
  have s0a := c.m_act 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0] at s0a
  have s0g := c.m_grow 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0, hq0, show (0 : Fin 3) + 1 = 1 from rfl] at s0g
  have s0d := c.m_decr 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0, hq0, show (0 : Fin 3) - 1 = 2 from rfl] at s0d
  have s1a := c.m_act 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1] at s1a
  have s1g := c.m_grow 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1, hq1, show (1 : Fin 3) + 1 = 2 from rfl] at s1g
  have s1d := c.m_decr 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1, hq1, show (1 : Fin 3) - 1 = 0 from rfl] at s1d
  have s2a := c.m_act 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2] at s2a
  have s2g := c.m_grow 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2, hq2, show (0 : Fin 3) + 1 = 1 from rfl] at s2g
  have s2d := c.m_decr 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2, hq2, show (0 : Fin 3) - 1 = 2 from rfl] at s2d
  have s3a := c.m_act 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3] at s3a
  have s3g := c.m_grow 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3, hq3, show (2 : Fin 3) + 1 = 0 from rfl] at s3g
  have s3d := c.m_decr 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3, hq3, show (2 : Fin 3) - 1 = 1 from rfl] at s3d
  have s4a := c.m_act 4
  simp only [show (4 : ℤ) + 1 = 5 by norm_num, h4] at s4a
  have s4g := c.m_grow 4
  simp only [show (4 : ℤ) + 1 = 5 by norm_num, h4, hq4, show (0 : Fin 3) + 1 = 1 from rfl] at s4g
  have s4d := c.m_decr 4
  simp only [show (4 : ℤ) + 1 = 5 by norm_num, h4, hq4, show (0 : Fin 3) - 1 = 2 from rfl] at s4d
  have tw0 := c.m_add 0 0
  have tw1 := c.m_add 0 1
  simp only [show ((0:ℤ) + ((5:ℕ):ℤ)) = 5 by norm_num, show (0 : Fin 3) - 1 = 2 from rfl,
    show (1 : Fin 3) - 1 = 0 from rfl] at tw0 tw1
  rw [s0a] at s1d
  rw [s1a] at s2g
  rw [s2a] at s3g
  obtain ⟨e0, e1⟩ := five_lin hu0 hu1 hv0 hv1 s0g s0d s1g s1d s2g s2d s3g s3d s4g s4a tw0 tw1
  obtain ⟨hx0, hx1, hx2⟩ := five_scale hu0 hu1 hv0 hv1 (c.m_pos 0 1) e0 e1 (c.m_quad 0)
  exact ⟨hx0, hx1, hx2⟩

/-- The raw cost of a `0 1 0 2 0` cycle with the forced margins, written out piece by piece. -/
private lemma five_rawCost (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) {u v l : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hv0 : 0 < v) (hv1 : v < 1) (hq0 : c.q 0 = ((1 + u ^ 2) / (2 * u))) (hq1 : c.q 1 = ((1 + u ^ 2) / (1 - u ^ 2)))
    (hq2 : c.q 2 = (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2)))) (hq3 : c.q 3 = ((1 + v ^ 2) / (1 - v ^ 2)))
    (hq4 : c.q 4 = ((1 + v ^ 2) / (2 * v)))
    (hx0' : c.m 0 0 = l * (2 * ((1 + u) * (1 - v)))) (hx1' : c.m 0 1 = l * (2 * ((1 - u) * (1 - v))))
    (hx2' : c.m 0 2 = l * (2 * ((1 - u) * (1 + v)))) :
    c.rawCost = rawArc (l * (2 * ((1 + u) * (1 - v)))) (l * (2 * ((1 - u) * (1 - v)))) (l * (2 * ((1 - u) * (1 + v)))) ((1 + u ^ 2) / (2 * u)) +
      rawArc (l * (2 * ((1 - u) * (1 - v)) / u)) (l * (2 * (u - 1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 2 * u - v + 1) / (u ^ 2 + 1))) (l * (2 * ((1 + u) * (1 - v)))) ((1 + u ^ 2) / (1 - u ^ 2)) +
      rawArc (l * (2 * ((1 - u) * (1 - v)))) (l * (2 * ((1 - u) * (1 - v)) / u)) (l * (-(2 * (u ^ 2 * v - u ^ 2 - 4 * u - v + 1)) / (u + 1))) (4 * u * v / ((1 - u ^ 2) * (1 - v ^ 2))) +
      rawArc (l * (2 * ((1 - u) * (1 - v)) / v)) (l * (2 * ((1 - u) * (1 - v)))) (l * (-(2 * (u * v ^ 2 - u - v ^ 2 - 4 * v + 1)) / (v + 1))) ((1 + v ^ 2) / (1 - v ^ 2)) +
      rawArc (l * (2 * ((1 - u) * (1 + v)))) (l * (2 * (v - 1) * (u * v ^ 2 - 2 * u * v - u - v ^ 2 - 2 * v + 1) / (v ^ 2 + 1))) (l * (2 * ((1 - u) * (1 - v)) / v)) ((1 + v ^ 2) / (2 * v)) := by
  have hu := hu0.ne'
  have hv := hv0.ne'
  have hu2 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have hv2 : 1 - v ^ 2 ≠ 0 := by nlinarith
  have hu3 : u + 1 ≠ 0 := by linarith
  have hv3 : v + 1 ≠ 0 := by linarith
  have hu4 : u ^ 2 + 1 ≠ 0 := by positivity
  have hv4 : v ^ 2 + 1 ≠ 0 := by positivity
  have s0a := c.m_act 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0] at s0a
  have s0g := c.m_grow 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0, hq0, show (0 : Fin 3) + 1 = 1 from rfl] at s0g
  have s0d := c.m_decr 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0, hq0, show (0 : Fin 3) - 1 = 2 from rfl] at s0d
  have s1a := c.m_act 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1] at s1a
  have s1g := c.m_grow 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1, hq1, show (1 : Fin 3) + 1 = 2 from rfl] at s1g
  have s1d := c.m_decr 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1, hq1, show (1 : Fin 3) - 1 = 0 from rfl] at s1d
  have s2a := c.m_act 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2] at s2a
  have s2g := c.m_grow 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2, hq2, show (0 : Fin 3) + 1 = 1 from rfl] at s2g
  have s2d := c.m_decr 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2, hq2, show (0 : Fin 3) - 1 = 2 from rfl] at s2d
  have s3a := c.m_act 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3] at s3a
  have s3g := c.m_grow 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3, hq3, show (2 : Fin 3) + 1 = 0 from rfl] at s3g
  have s3d := c.m_decr 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3, hq3, show (2 : Fin 3) - 1 = 1 from rfl] at s3d
  have s4a := c.m_act 4
  simp only [show (4 : ℤ) + 1 = 5 by norm_num, h4] at s4a
  have s4g := c.m_grow 4
  simp only [show (4 : ℤ) + 1 = 5 by norm_num, h4, hq4, show (0 : Fin 3) + 1 = 1 from rfl] at s4g
  have s4d := c.m_decr 4
  simp only [show (4 : ℤ) + 1 = 5 by norm_num, h4, hq4, show (0 : Fin 3) - 1 = 2 from rfl] at s4d
  have tw0 := c.m_add 0 0
  have tw1 := c.m_add 0 1
  simp only [show ((0:ℤ) + ((5:ℕ):ℤ)) = 5 by norm_num, show (0 : Fin 3) - 1 = 2 from rfl,
    show (1 : Fin 3) - 1 = 0 from rfl] at tw0 tw1
  rw [s0a] at s1d
  rw [s1a] at s2g
  rw [s2a] at s3g
  have n10 : c.m 1 0 = l * (2 * ((1 + u) * (1 - v))) := by rw [s0a, hx0']
  have n11 : c.m 1 1 = l * (2 * ((1 - u) * (1 - v)) / u) := by rw [s0g, hx0', hx1']; field_simp; ring
  have n12 : c.m 1 2 = l * (2 * (u - 1) * (u ^ 2 * v - u ^ 2 - 2 * u * v - 2 * u - v + 1) / (u ^ 2 + 1)) := by rw [s0d, hx0', hx2']; field_simp; ring
  have n20 : c.m 2 0 = l * (2 * ((1 - u) * (1 - v))) := by rw [s1d, n11, hx0']; field_simp; ring
  have n21 : c.m 2 1 = l * (2 * ((1 - u) * (1 - v)) / u) := by rw [s1a, n11]
  have n22 : c.m 2 2 = l * (-(2 * (u ^ 2 * v - u ^ 2 - 4 * u - v + 1)) / (u + 1)) := by rw [s1g, n11, n12]; field_simp; ring
  have n30 : c.m 3 0 = l * (2 * ((1 - u) * (1 - v))) := by rw [s2a, n20]
  have n31 : c.m 3 1 = l * (-(2 * (u * v ^ 2 - u - v ^ 2 - 4 * v + 1)) / (v + 1)) := by rw [s2g, n20, n11]; field_simp; ring
  have n32 : c.m 3 2 = l * (2 * ((1 - u) * (1 - v)) / v) := by rw [s2d, n20, n22]; field_simp; ring
  have n40 : c.m 4 0 = l * (2 * ((1 - u) * (1 + v))) := by rw [s3g, n32, n20]; field_simp; ring
  have n41 : c.m 4 1 = l * (2 * (v - 1) * (u * v ^ 2 - 2 * u * v - u - v ^ 2 - 2 * v + 1) / (v ^ 2 + 1)) := by rw [s3d, n32, n31]; field_simp; ring
  have n42 : c.m 4 2 = l * (2 * ((1 - u) * (1 - v)) / v) := by rw [s3a, n32]
  simp only [Cycle.rawCost, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Cycle.arc,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, h0, h1, h2, h3, h4, hq0, hq1, hq2, hq3, hq4,
    show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) - 1 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) - 1 = 1 from rfl,
    hx0', hx1', hx2', n11, n12, n10, n20, n21, n22, n30, n31, n32, n40, n41, n42]



/-- **The mixed five-piece cycles**: a closed cycle with the word `0 1 0 2 0` has raw cost
`8 δ(u, v)` for some `u, v ∈ (0, 1)` with `u + v + uv > 1`. Tangent closure gives the factors
(`five_factors`), state closure the initial margins (`five_margins`), and the cost is summed piece
by piece (`five_rawCost`, `five_cost`). -/
theorem five_param (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) :
    ∃ u v : ℝ, 0 < u ∧ u < 1 ∧ 0 < v ∧ v < 1 ∧ 1 < u + v + u * v ∧
      c.rawCost = 8 * fiveDensity u v := by
  obtain ⟨u, v, hu0, hu1, hv0, hv1, huv, hq0, hq1, hq2, hq3, hq4⟩ := five_factors c h0 h1 h2 h3 h4
  obtain ⟨hx0, hx1, hx2⟩ := five_margins c h0 h1 h2 h3 h4 hu0 hu1 hv0 hv1 hq0 hq1 hq2 hq3 hq4
  refine ⟨u, v, hu0, hu1, hv0, hv1, huv, ?_⟩
  have hd : 0 < (1 - u) * (1 - v) := mul_pos (by linarith) (by linarith)
  have hN : 0 < ((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v)) := mul_pos hd (by nlinarith)
  set l := (√(((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))))⁻¹ with hl_def
  have hl : l ^ 2 * (((1 - u) * (1 - v)) * (4 - (1 - u) * (1 - v))) = 1 := by
    rw [hl_def, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']
  rw [five_rawCost (l := l) c h0 h1 h2 h3 h4 hu0 hu1 hv0 hv1 hq0 hq1 hq2 hq3 hq4
    (by rw [hx0, hl_def]; ring) (by rw [hx1, hl_def]; ring) (by rw [hx2, hl_def]; ring)]
  exact five_cost hu0 hu1 hv0 hv1 hl

/-- **Five-piece bound**: `8 δ_oct < rawCost` for the word `0 1 0 2 0`. -/
theorem five_rawCost_gt (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) : 8 * octagonDensity < c.rawCost := by
  obtain ⟨u, v, hu0, hu1, hv0, hv1, huv, hcost⟩ := c.five_param h0 h1 h2 h3 h4
  rw [hcost]
  linarith [fivePiece_density_gt hu0 hu1 hv0 hv1 huv]

end Cycle

end Term

end SmoothedOctagon

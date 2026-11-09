module

public import SmoothedOctagon.Exclusion.ShortRun.Gap.Log

/-!
# Case M1 angle gap: the two-variable core

After the boundary reductions of `ag_phi_le` and `ag_sigma_superadd`, a reverse centre with
`cos φ ≥ 3/10` produces `S ∈ [0, 1)`, `z ∈ (0, 1]` and `E` with
`E ≤ (1 - S)(1 - z/4) + log z`, `E ≥ (3/5)√Q`, `Q = uv = 3(3 + S²)/16`, `ρ = (1 - S)z/4`.
The core inequality says that the Gram determinant then exceeds the competitive cap.

Proof: `S ≤ 2/5` and `z ≥ 31/50` are forced by `E ≥ 9/20`. On each of the four `z`-intervals
`[31/50, 7/10]`, `[7/10, 4/5]`, `[4/5, 9/10]`, `[9/10, 1]` the logarithm is replaced by a tangent
line `T`; with a multiplier `μ(S) ≥ 0` the S-procedure function
`G = (4 + 9μ/25) Q - (1 + μ) T² - 16 K (1 - ρ)²` is a concave quadratic in `z`, so it is positive
once it is positive at the two interval ends, which are cubic polynomials in `S ∈ [0, 2/5]` with
positive Bernstein coefficients.

## Main API

* `ag_core`: `16 K (1 - (1 - S)z/4)² < 4Q - E²` with `K = 97969/529200`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The S-procedure function on one tangent piece. -/
private noncomputable def agG (l zk μ0 μ1 S z : ℝ) : ℝ :=
  (4 + 9 / 25 * (μ0 + μ1 * S)) * (3 * (3 + S ^ 2) / 16)
    - (1 + (μ0 + μ1 * S)) * ((1 - S) * (1 - z / 4) + l + z / zk - 1) ^ 2
    - 16 * (97969 / 529200) * (1 - (1 - S) * z / 4) ^ 2

/-- `agG` is a concave quadratic in `z`. -/
private lemma ag_concave {l zk μ0 μ1 S z a b : ℝ} (hab : a < b) (ha : a ≤ z) (hb : z ≤ b)
    (hμ : 0 ≤ 1 + (μ0 + μ1 * S)) (hGa : 0 < agG l zk μ0 μ1 S a)
    (hGb : 0 < agG l zk μ0 μ1 S b) : 0 < agG l zk μ0 μ1 S z := by
  have key : agG l zk μ0 μ1 S z * (b - a) =
      (b - z) * agG l zk μ0 μ1 S a + (z - a) * agG l zk μ0 μ1 S b +
        (b - a) * ((1 + (μ0 + μ1 * S)) * (1 / zk - (1 - S) / 4) ^ 2 +
          97969 / 529200 * (1 - S) ^ 2) * ((z - a) * (b - z)) := by
    unfold agG; ring
  have hc : 0 ≤ (1 + (μ0 + μ1 * S)) * (1 / zk - (1 - S) / 4) ^ 2 +
      97969 / 529200 * (1 - S) ^ 2 :=
    add_nonneg (mul_nonneg hμ (sq_nonneg _)) (by positivity)
  have h1 : 0 ≤ (b - a) * ((1 + (μ0 + μ1 * S)) * (1 / zk - (1 - S) / 4) ^ 2 +
      97969 / 529200 * (1 - S) ^ 2) * ((z - a) * (b - z)) :=
    mul_nonneg (mul_nonneg (by linarith) hc) (mul_nonneg (by linarith) (by linarith))
  have h2 : 0 < (b - z) * agG l zk μ0 μ1 S a + (z - a) * agG l zk μ0 μ1 S b := by
    rcases le_total (agG l zk μ0 μ1 S a) (agG l zk μ0 μ1 S b) with h | h
    · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 h)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 h)]
  have h3 : 0 < agG l zk μ0 μ1 S z * (b - a) := by rw [key]; linarith
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg (by linarith : (0 : ℝ) ≤ b - a)]

/-- One tangent piece: positivity of `agG` gives the core inequality. -/
private lemma ag_step {S z E l zk μ0 μ1 : ℝ} (hz : 0 < z) (hzk : 0 < zk)
    (hl : Real.log zk ≤ l) (hμ : 0 ≤ μ0 + μ1 * S)
    (hE : E ≤ (1 - S) * (1 - z / 4) + Real.log z) (hE0 : 0 < E)
    (hE2 : 9 / 25 * (3 * (3 + S ^ 2) / 16) ≤ E ^ 2) (hG : 0 < agG l zk μ0 μ1 S z) :
    16 * (97969 / 529200) * (1 - (1 - S) * z / 4) ^ 2 < 4 * (3 * (3 + S ^ 2) / 16) - E ^ 2 := by
  have hT := ag_log_le_tangent hz hzk hl
  unfold agG at hG
  set T := (1 - S) * (1 - z / 4) + l + z / zk - 1 with hTdef
  have hET : E ≤ T := by linarith
  have hT2 : E ^ 2 ≤ T ^ 2 := by nlinarith
  have hm : 0 ≤ (μ0 + μ1 * S) * (T ^ 2 - 9 / 25 * (3 * (3 + S ^ 2) / 16)) :=
    mul_nonneg hμ (by linarith)
  nlinarith

private lemma ag_e1a {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (-10712 / 27783) (17 / 25) (41 / 200) (9 / 20) S (31 / 50) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e1b {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (-10712 / 27783) (17 / 25) (41 / 200) (9 / 20) S (7 / 10) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e2a {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (-296 / 1029) (3 / 4) (3 / 50) (3 / 5) S (7 / 10) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e2b {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (-296 / 1029) (3 / 4) (3 / 50) (3 / 5) S (4 / 5) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e3a {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (-8232 / 50653) (17 / 20) (1 / 100) (3 / 20) S (4 / 5) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e3b {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (-8232 / 50653) (17 / 20) (1 / 100) (3 / 20) S (9 / 10) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e4a {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (0) (1) (0) (0) S (9 / 10) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]

private lemma ag_e4b {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 2 / 5) :
    0 < agG (0) (1) (0) (0) S (1) := by
  have hy : 0 ≤ 2 / 5 - S := by linarith
  unfold agG
  nlinarith [pow_nonneg h0 3, pow_nonneg hy 3, mul_nonneg (mul_nonneg h0 h0) hy,
    mul_nonneg (mul_nonneg h0 hy) hy, mul_nonneg h0 hy, sq_nonneg S, sq_nonneg (2 / 5 - S)]


/-- **The two-variable core of the angle gap.** -/
theorem ag_core {S z E : ℝ} (hS0 : 0 ≤ S) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (hE : E ≤ (1 - S) * (1 - z / 4) + Real.log z) (hE0 : 0 < E)
    (hE2 : 9 / 25 * (3 * (3 + S ^ 2) / 16) ≤ E ^ 2) :
    16 * (97969 / 529200) * (1 - (1 - S) * z / 4) ^ 2 < 4 * (3 * (3 + S ^ 2) / 16) - E ^ 2 := by
  have hE45 : 9 / 20 ≤ E := by nlinarith
  have hlz : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz0
  have hS : S ≤ 2 / 5 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hz1) (by linarith : (0 : ℝ) ≤ S + 3)]
  have l1 : Real.log (17 / 25) ≤ -10712 / 27783 := by
    have := ag_log_le_atanh (z := 17 / 25) (by norm_num) (by norm_num); norm_num at this; linarith
  have l2 : Real.log (3 / 4) ≤ -296 / 1029 := by
    have := ag_log_le_atanh (z := 3 / 4) (by norm_num) (by norm_num); norm_num at this; linarith
  have l3 : Real.log (17 / 20) ≤ -8232 / 50653 := by
    have := ag_log_le_atanh (z := 17 / 20) (by norm_num) (by norm_num); norm_num at this; linarith
  have l4 : Real.log 1 ≤ 0 := by rw [Real.log_one]
  by_cases hA : z < 31 / 50
  · exfalso
    have hT := ag_log_le_tangent hz0 (by norm_num : (0 : ℝ) < 17 / 25) l1
    nlinarith [mul_nonneg hS0 (by linarith : (0 : ℝ) ≤ 1 - z / 4)]
  rw [not_lt] at hA
  rcases le_or_gt z (7 / 10) with hB | hB
  · exact ag_step hz0 (by norm_num) l1 (by positivity) hE hE0 hE2
      (ag_concave (by norm_num) hA hB (by positivity) (ag_e1a hS0 hS) (ag_e1b hS0 hS))
  rcases le_or_gt z (4 / 5) with hC | hC
  · exact ag_step hz0 (by norm_num) l2 (by positivity) hE hE0 hE2
      (ag_concave (by norm_num) hB.le hC (by positivity) (ag_e2a hS0 hS) (ag_e2b hS0 hS))
  rcases le_or_gt z (9 / 10) with hD | hD
  · exact ag_step hz0 (by norm_num) l3 (by positivity) hE hE0 hE2
      (ag_concave (by norm_num) hC.le hD (by positivity) (ag_e3a hS0 hS) (ag_e3b hS0 hS))
  · exact ag_step hz0 (by norm_num) l4 (by positivity) hE hE0 hE2
      (ag_concave (by norm_num) hD.le hz1 (by positivity) (ag_e4a hS0 hS) (ag_e4b hS0 hS))

end SmoothedOctagon

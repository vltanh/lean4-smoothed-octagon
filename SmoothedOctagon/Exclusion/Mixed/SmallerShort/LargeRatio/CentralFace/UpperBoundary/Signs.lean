module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.UpperBoundary.Polynomials

/-!
# The signs of the upper-boundary coefficients

Endpoint power bounds control most coefficients. Six quadratic minorants
cover the remaining ones; completing a square proves each minorant positive.
The positive constant coefficient then gives the sign for every `u ≥ 0`.
-/

@[expose] public section
namespace SmoothedOctagon.S0Central

private theorem coefficient2_0_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 10 ^ 12 * (6 * e ^ 2 - 7 * e + 5/2) ≤ coefficient2 0 e := by
  have lo (n : ℕ) : 0 ≤ e ^ n := pow_nonneg he0 n
  have tail (n : ℕ) (hn : 2 ≤ n) : e ^ n ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hn
  norm_num [normalization, coefficient2]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    tail 3 (by norm_num), tail 4 (by norm_num), tail 5 (by norm_num),
    tail 6 (by norm_num), tail 7 (by norm_num)]

private theorem coefficient2_0_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient2 0 e := by
  apply lt_of_lt_of_le _ (coefficient2_0_floor he0 he1)
  apply mul_pos (by norm_num [normalization])
  nlinarith only [sq_nonneg (12 * e - 7)]

private theorem coefficient2_1_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 10 ^ 13 * (5 * e ^ 2 - 6 * e + 3) ≤ coefficient2 1 e := by
  have lo (n : ℕ) : 0 ≤ e ^ n := pow_nonneg he0 n
  have tail (n : ℕ) (hn : 2 ≤ n) : e ^ n ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hn
  norm_num [normalization, coefficient2]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    tail 3 (by norm_num), tail 4 (by norm_num), tail 5 (by norm_num),
    tail 6 (by norm_num), tail 7 (by norm_num)]

private theorem coefficient2_1_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient2 1 e := by
  apply lt_of_lt_of_le _ (coefficient2_1_floor he0 he1)
  apply mul_pos (by norm_num [normalization])
  nlinarith only [sq_nonneg (5 * e - 3)]

private theorem coefficient2_2_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 10 ^ 14 * (3 * e ^ 2/2 - 5 * e/2 + 3/2) ≤ coefficient2 2 e := by
  have lo (n : ℕ) : 0 ≤ e ^ n := pow_nonneg he0 n
  have tail (n : ℕ) (hn : 2 ≤ n) : e ^ n ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hn
  norm_num [normalization, coefficient2]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    tail 3 (by norm_num), tail 4 (by norm_num), tail 5 (by norm_num),
    tail 6 (by norm_num), tail 7 (by norm_num)]

private theorem coefficient2_2_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient2 2 e := by
  apply lt_of_lt_of_le _ (coefficient2_2_floor he0 he1)
  apply mul_pos (by norm_num [normalization])
  nlinarith only [sq_nonneg (6 * e - 5)]

private theorem coefficient2_3_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 10 ^ 14 * (3 * e ^ 2 - 5 * e + 5) ≤ coefficient2 3 e := by
  have lo (n : ℕ) : 0 ≤ e ^ n := pow_nonneg he0 n
  have tail (n : ℕ) (hn : 2 ≤ n) : e ^ n ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hn
  norm_num [normalization, coefficient2]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    tail 3 (by norm_num), tail 4 (by norm_num), tail 5 (by norm_num),
    tail 6 (by norm_num), tail 7 (by norm_num)]

private theorem coefficient2_3_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient2 3 e := by
  apply lt_of_lt_of_le _ (coefficient2_3_floor he0 he1)
  apply mul_pos (by norm_num [normalization])
  nlinarith only [sq_nonneg (6 * e - 5)]

private theorem coefficient8_0_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 10 ^ 12 * (23 * e ^ 2/4 - 10 * e + 9/2) ≤ coefficient8 0 e := by
  have lo (n : ℕ) : 0 ≤ e ^ n := pow_nonneg he0 n
  have tail (n : ℕ) (hn : 2 ≤ n) : e ^ n ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hn
  norm_num [normalization, coefficient8]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    tail 3 (by norm_num), tail 4 (by norm_num), tail 5 (by norm_num),
    tail 6 (by norm_num), tail 7 (by norm_num)]

private theorem coefficient8_0_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient8 0 e := by
  apply lt_of_lt_of_le _ (coefficient8_0_floor he0 he1)
  apply mul_pos (by norm_num [normalization])
  nlinarith only [sq_nonneg (23 * e - 20)]

private theorem coefficient8_1_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 10 ^ 13 * (4 * e ^ 2 - 8 * e + 6) ≤ coefficient8 1 e := by
  have lo (n : ℕ) : 0 ≤ e ^ n := pow_nonneg he0 n
  have tail (n : ℕ) (hn : 2 ≤ n) : e ^ n ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hn
  norm_num [normalization, coefficient8]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    tail 3 (by norm_num), tail 4 (by norm_num), tail 5 (by norm_num),
    tail 6 (by norm_num), tail 7 (by norm_num)]

private theorem coefficient8_1_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient8 1 e := by
  apply lt_of_lt_of_le _ (coefficient8_1_floor he0 he1)
  apply mul_pos (by norm_num [normalization])
  nlinarith only [sq_nonneg (e - 1)]

theorem coefficient2_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 18) : 0 ≤ coefficient2 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  · exact (coefficient2_0_pos he0 he1).le
  · exact (coefficient2_1_pos he0 he1).le
  · exact (coefficient2_2_pos he0 he1).le
  · exact (coefficient2_3_pos he0 he1).le
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), first 7 (by norm_num)]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), first 7 (by norm_num)]
  · norm_num [coefficient2]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), first 7 (by norm_num)]

theorem coefficient2_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient2 0 e := by
  exact coefficient2_0_pos he0 he1

theorem value2_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < value2 u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficient2 i e * u ^ i)
    (fun i hi => mul_nonneg (coefficient2_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 19 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficient2_zero_pos he0 he1).trans_le hm

theorem coefficientT_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 18) : 0 ≤ coefficientT n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficientT]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]

theorem coefficientT_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientT 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  norm_num [coefficientT]
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]

theorem valueT_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueT u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientT i e * u ^ i)
    (fun i hi => mul_nonneg (coefficientT_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 19 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientT_zero_pos he0 he1).trans_le hm

theorem coefficient8_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 18) : 0 ≤ coefficient8 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  · exact (coefficient8_0_pos he0 he1).le
  · exact (coefficient8_1_pos he0 he1).le
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]
  · norm_num [coefficient8]
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]

theorem coefficient8_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient8 0 e := by
  exact coefficient8_0_pos he0 he1

theorem value8_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < value8 u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficient8 i e * u ^ i)
    (fun i hi => mul_nonneg (coefficient8_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 19 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficient8_zero_pos he0 he1).trans_le hm

end SmoothedOctagon.S0Central

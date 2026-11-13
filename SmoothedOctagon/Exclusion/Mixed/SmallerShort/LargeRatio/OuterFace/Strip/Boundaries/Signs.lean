module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip.Boundaries.Polynomials

/-!
# Signs at the two outer-strip boundaries

Every coefficient has a positive constant lower bound on `0 ≤ e ≤ 1`:
drop positive nonconstant terms and replace negative powers by their
value at one. The constant coefficient gives strict positivity for `X ≥ 0`.
-/

@[expose] public section
namespace SmoothedOctagon.S0Outer.Boundaries

theorem coefficientLower2_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 10) : 0 ≤ coefficientLower2 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientLower2]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem coefficientLower2_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientLower2 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  all_goals norm_num [coefficientLower2]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem valueLower2_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueLower2 X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientLower2 i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientLower2_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 11 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientLower2_zero_pos he0 he1).trans_le hm

theorem clearedLower2_pos {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < clearedLower2 x a := by
  have hp := valueLower2_pos (sub_nonneg.mpr hx) (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueLower2_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalizationLower])).mp hp

theorem coefficientLowerT_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 10) : 0 ≤ coefficientLowerT n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientLowerT]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem coefficientLowerT_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientLowerT 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  all_goals norm_num [coefficientLowerT]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem valueLowerT_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueLowerT X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientLowerT i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientLowerT_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 11 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientLowerT_zero_pos he0 he1).trans_le hm

theorem clearedLowerT_pos {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < clearedLowerT x a := by
  have hp := valueLowerT_pos (sub_nonneg.mpr hx) (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueLowerT_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalizationLower])).mp hp

theorem coefficientLower8_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 10) : 0 ≤ coefficientLower8 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientLower8]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem coefficientLower8_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientLower8 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  all_goals norm_num [coefficientLower8]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem valueLower8_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueLower8 X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientLower8 i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientLower8_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 11 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientLower8_zero_pos he0 he1).trans_le hm

theorem clearedLower8_pos {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < clearedLower8 x a := by
  have hp := valueLower8_pos (sub_nonneg.mpr hx) (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueLower8_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalizationLower])).mp hp

theorem coefficientUpper2_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 18) : 0 ≤ coefficientUpper2 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientUpper2]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem coefficientUpper2_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientUpper2 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  all_goals norm_num [coefficientUpper2]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem valueUpper2_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueUpper2 X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientUpper2 i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientUpper2_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 19 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientUpper2_zero_pos he0 he1).trans_le hm

theorem clearedUpper2_pos {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < clearedUpper2 x a := by
  have hp := valueUpper2_pos (sub_nonneg.mpr hx) (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueUpper2_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalizationUpper])).mp hp

theorem coefficientUpperT_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 18) : 0 ≤ coefficientUpperT n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientUpperT]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem coefficientUpperT_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientUpperT 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  all_goals norm_num [coefficientUpperT]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem valueUpperT_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueUpperT X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientUpperT i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientUpperT_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 19 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientUpperT_zero_pos he0 he1).trans_le hm

theorem clearedUpperT_pos {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < clearedUpperT x a := by
  have hp := valueUpperT_pos (sub_nonneg.mpr hx) (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueUpperT_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalizationUpper])).mp hp

theorem coefficientUpper8_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 18) : 0 ≤ coefficientUpper8 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientUpper8]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem coefficientUpper8_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientUpper8 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  all_goals norm_num [coefficientUpper8]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, hi 1, hi 2, hi 3, hi 4, hi 5, hi 6]

theorem valueUpper8_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueUpper8 X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientUpper8 i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientUpper8_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 19 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientUpper8_zero_pos he0 he1).trans_le hm

theorem clearedUpper8_pos {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < clearedUpper8 x a := by
  have hp := valueUpper8_pos (sub_nonneg.mpr hx) (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueUpper8_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalizationUpper])).mp hp

end SmoothedOctagon.S0Outer.Boundaries

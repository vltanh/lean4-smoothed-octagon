module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.Coordinates

/-!
# The two central residue polynomials

Normalize alpha to its order interval. Both residue polynomials have
nonnegative coefficients in `x - 12/5`, with positive constant terms.
The coefficient signs follow from `0 ≤ e^j ≤ 1` and `e^j ≤ e`.
-/

@[expose] public section
namespace SmoothedOctagon

/-- The `τ = 2` residue polynomial `Φ₂ = 4SMK²α(k(x - 1)³ + r)/(x - 1)³`:
`30αSMh² + 10αh²(x - 1)² + 7((5/2)αc²(c² - S³) + cK² - αK(2c² - S³))`, `h = x - α`, `c = α + 1`
(the residue normalization `A*` of `lgrr2`, cleared). -/
noncomputable def lgrPhi2f (x a : ℝ) : ℝ :=
  30 * a * (x + 1) * (35 * x + 13) * (x - a) ^ 2 + 10 * a * (x - a) ^ 2 * (x - 1) ^ 2 +
    7 * (5 / 2 * a * (a + 1) ^ 2 * ((a + 1) ^ 2 - (x + 1) ^ 3) +
      (a + 1) * (x ^ 2 + 2 * x + a ^ 2) ^ 2 - a * (x ^ 2 + 2 * x + a ^ 2) * (2 * (a + 1) ^ 2 - (x + 1) ^ 3))

/-- `4SM(Q + α²K)` cleared: with `U_I = 3SM + (x - 1)² = 4SMu_∞`,
`J_J = 7(x - 1)³ = 4SMJ`, `E₀' = S³(U_I - 4SM) + 4SM(3S - 1)`, `c = α + 1`, `δ = 2(α - x)`. -/
noncomputable def lgrQnf (x a : ℝ) : ℝ :=
  let S := x + 1
  let F4 := 4 * (x + 1) * (35 * x + 13)
  let UI := 3 * (x + 1) * (35 * x + 13) + (x - 1) ^ 2
  let JJ := 7 * (x - 1) ^ 3
  let c := a + 1
  let δ := 2 * (a - x)
  let K := x ^ 2 + 2 * x + a ^ 2
  let E0 := S ^ 3 * (UI - F4) + F4 * (3 * S - 1)
  UI * δ ^ 2 * c ^ 2 - c * (2 * c ^ 2 * δ * UI + JJ * δ ^ 2 - δ * E0) +
    (F4 * (S ^ 2 * (S ^ 2 - S + 1)) + (c ^ 2) ^ 2 * UI + 2 * JJ * c ^ 2 * δ - c ^ 2 * E0 -
      S ^ 3 * JJ * δ) - F4 * K ^ 2 - JJ * c * (c ^ 2 - S ^ 3) + F4 * a ^ 2 * K

namespace S0Central.Convexity

noncomputable def normalization : ℝ := 2 * 12 ^ 6 * 5 ^ 10

def coefficientPhi {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => 2520000000000 * e ^ 5 + 73080000000000 * e ^ 4 + 21368681280000000 * e ^ 3 - 128718953280000000 * e ^ 2 - 176576885452800000 * e + 1245911509785600000
  | 1 => 15750000000000 * e ^ 5 + 365400000000000 * e ^ 4 + 93403292400000000 * e ^ 3 - 541748152800000000 * e ^ 2 - 152848912896000000 * e + 2600113219200000000
  | 2 => 39375000000000 * e ^ 5 + 685125000000000 * e ^ 4 + 151989223500000000 * e ^ 3 - 852193912500000000 * e ^ 2 + 398314130400000000 * e + 1934236454400000000
  | 3 => 49218750000000 * e ^ 5 + 570937500000000 * e ^ 4 + 111638098125000000 * e ^ 3 - 610825657500000000 * e ^ 2 + 549975096000000000 * e + 606854592000000000
  | 4 => 30761718750000 * e ^ 5 + 178417968750000 * e ^ 4 + 35482471875000000 * e ^ 3 - 193536337500000000 * e ^ 2 + 220721760000000000 * e + 69575760000000000
  | 5 => 7690429687500 * e ^ 5 + 3913734375000000 * e ^ 3 - 22138312500000000 * e ^ 2 + 28955880000000000 * e + 408240000000000
  | 6 => -44296875000000 * e ^ 3 + 170100000000000 * e
  | _ => 0

def valuePhi {R : Type*} [CommRing R] (u e : R) : R :=
  ∑ i ∈ Finset.range 7, coefficientPhi i e * u ^ i

theorem valuePhi_eq (u e : ℝ) :
    normalization * lgrPhi2f (12 / 5 + u) (1 + e / 12 * (5 * (12 / 5 + u) - 8)) = valuePhi u e := by
  norm_num only [valuePhi, Finset.sum_range_succ, Finset.sum_range_zero, coefficientPhi]
  unfold normalization lgrPhi2f
  ring

theorem coefficientPhi_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 6) : 0 ≤ coefficientPhi n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  all_goals norm_num [coefficientPhi]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficientPhi_zero_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 16000 < coefficientPhi 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  all_goals norm_num [coefficientPhi, normalization]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficientPhi_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientPhi 0 e :=
  lt_trans (by norm_num [normalization]) (coefficientPhi_zero_floor he0 he1)

theorem valuePhi_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valuePhi u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientPhi i e * u ^ i)
    (fun i hi => mul_nonneg (coefficientPhi_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 7 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientPhi_zero_pos he0 he1).trans_le hm

theorem phi_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : 0 < lgrPhi2f x a :=
  positive_of_coordinates (by norm_num [normalization]) valuePhi_eq
    (fun _ _ hu he0 he1 => valuePhi_pos hu he0 he1) hx ha ha1

def coefficientContinuation {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => 713779200000000 * e ^ 4 - 12032979840000000 * e ^ 3 - 167154218956800000 * e ^ 2 + 519084801008640000 * e + 4662146658742272000
  | 1 => 4037472000000000 * e ^ 4 - 61650007200000000 * e ^ 3 - 610783431552000000 * e ^ 2 + 2201586418310400000 * e + 10640243225180160000
  | 2 => 9110880000000000 * e ^ 4 - 125346933000000000 * e ^ 3 - 818817718320000000 * e ^ 2 + 3476334454272000000 * e + 9865836852019200000
  | 3 => 10350900000000000 * e ^ 4 - 128032278750000000 * e ^ 3 - 502618608000000000 * e ^ 2 + 2628675050400000000 * e + 4863019265280000000
  | 4 => 6118875000000000 * e ^ 4 - 68434368750000000 * e ^ 3 - 151234290000000000 * e ^ 2 + 1056408480000000000 * e + 1392224371200000000
  | 5 => 1740234375000000 * e ^ 4 - 17974406250000000 * e ^ 3 - 24127470000000000 * e ^ 2 + 233195436000000000 * e + 234553708800000000
  | 6 => 186328125000000 * e ^ 4 - 1818281250000000 * e ^ 3 - 3061800000000000 * e ^ 2 + 27585360000000000 * e + 21648384000000000
  | 7 => -344250000000000 * e ^ 2 + 1482300000000000 * e + 816480000000000
  | _ => 0

def valueContinuation {R : Type*} [CommRing R] (u e : R) : R :=
  ∑ i ∈ Finset.range 8, coefficientContinuation i e * u ^ i

theorem valueContinuation_eq (u e : ℝ) :
    normalization * lgrQnf (12 / 5 + u) (1 + e / 12 * (5 * (12 / 5 + u) - 8)) = valueContinuation u e := by
  norm_num only [valueContinuation, Finset.sum_range_succ, Finset.sum_range_zero, coefficientContinuation]
  unfold normalization lgrQnf
  ring

theorem coefficientContinuation_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 7) : 0 ≤ coefficientContinuation n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  all_goals norm_num [coefficientContinuation]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficientContinuation_zero_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 76000 < coefficientContinuation 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  all_goals norm_num [coefficientContinuation, normalization]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficientContinuation_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientContinuation 0 e :=
  lt_trans (by norm_num [normalization]) (coefficientContinuation_zero_floor he0 he1)

theorem valueContinuation_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueContinuation u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientContinuation i e * u ^ i)
    (fun i hi => mul_nonneg (coefficientContinuation_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 8 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientContinuation_zero_pos he0 he1).trans_le hm

theorem continuation_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : 0 < lgrQnf x a :=
  positive_of_coordinates (by norm_num [normalization]) valueContinuation_eq
    (fun _ _ hu he0 he1 => valueContinuation_pos hu he0 he1) hx ha ha1

end S0Central.Convexity
end SmoothedOctagon

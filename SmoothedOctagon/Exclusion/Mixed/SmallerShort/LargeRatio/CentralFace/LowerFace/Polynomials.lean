module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace

/-!
# Central numerators at beta equal to x

In the normalized order coordinates, each numerator has degree ten in
`x - 12/5` and degree six in `e`. Endpoint power bounds and charging
negative higher powers to `e` or `e²` give nonnegative coefficients.
The positive constant coefficients give the strict signs.
-/

@[expose] public section
namespace SmoothedOctagon.S0Central.Lower

noncomputable def normalization : ℝ := 2 * 12 ^ 6 * 5 ^ 10

noncomputable def numerator2 (x a : ℝ) : ℝ :=
  lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x)
    (lgrUc x x) (lgrVc x x) (ssDg x x a)

def coefficient2 {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => -5804180480000000 * e ^ 6 - 593052493824000000 * e ^ 5 - 12129073138667520000 * e ^ 4 - 45592102380109824000 * e ^ 3 + 128181786882224947200 * e ^ 2 + 126740119889909514240 * e + 24279167002910883840
  | 1 => -51625331200000000 * e ^ 6 - 4730803837440000000 * e ^ 5 - 84414615348326400000 * e ^ 4 - 247818374399324160000 * e ^ 3 + 814891777522532352000 * e ^ 2 + 505294405777494835200 * e + 292331120892479078400
  | 2 => -200253016000000000 * e ^ 6 - 16300135814400000000 * e ^ 5 - 250386931472832000000 * e ^ 4 - 544135994505446400000 * e ^ 3 + 2147598487451750400000 * e ^ 2 + 803809007047222272000 * e + 1029582236279291904000
  | 3 => -443268400000000000 * e ^ 6 - 31706430024000000000 * e ^ 5 - 413255932371360000000 * e ^ 4 - 614239583473440000000 * e ^ 3 + 3063393501627340800000 * e ^ 2 + 718517058963102720000 * e + 1786585072536944640000
  | 4 => -614765837500000000 * e ^ 6 - 38190165765000000000 * e ^ 5 - 416195159665050000000 * e ^ 4 - 371834250400440000000 * e ^ 3 + 2597214031062336000000 * e ^ 2 + 523372372068787200000 * e + 1795566947912294400000
  | 5 => -551498031250000000 * e ^ 6 - 29390620331250000000 * e ^ 5 - 264363257893500000000 * e ^ 4 - 110144721304800000000 * e ^ 3 + 1356462900748800000000 * e ^ 2 + 414458696778624000000 * e + 1114663830460416000000
  | 6 => -318310410156250000 * e ^ 6 - 14382776437500000000 * e ^ 5 - 105962723628750000000 * e ^ 4 - 9456516639000000000 * e ^ 3 + 437332021300800000000 * e ^ 2 + 281282950788480000000 * e + 434435821148160000000
  | 7 => -113312792968750000 * e ^ 6 - 4301120625000000000 * e ^ 5 - 26050255425000000000 * e ^ 4 + 313513740000000000 * e ^ 3 + 84520026720000000000 * e ^ 2 + 125616150172800000000 * e + 103643579289600000000
  | 8 => -22458496093750000 * e ^ 6 - 712729687500000000 * e ^ 5 - 3656842593750000000 * e ^ 4 - 1270076625000000000 * e ^ 3 + 9203618520000000000 * e ^ 2 + 33327473328000000000 * e + 13844281536000000000
  | 9 => -1887207031250000 * e ^ 6 - 49933593750000000 * e ^ 5 - 248768437500000000 * e ^ 4 - 509503500000000000 * e ^ 3 + 537062400000000000 * e ^ 2 + 4768379280000000000 * e + 793618560000000000
  | 10 => -5125781250000000 * e ^ 4 - 53308125000000000 * e ^ 3 + 19683000000000000 * e ^ 2 + 283435200000000000 * e
  | _ => 0

def value2 {R : Type*} [CommRing R] (u e : R) : R :=
  ∑ i ∈ Finset.range 11, coefficient2 i e * u ^ i

theorem value2_eq (u e : ℝ) :
    normalization * numerator2 (12 / 5 + u) (1 + e / 12 * (5 * (12 / 5 + u) - 8)) = value2 u e := by
  norm_num only [value2, Finset.sum_range_succ, Finset.sum_range_zero, coefficient2]
  unfold normalization numerator2 lgrN2 lgrWN lgrLN lgrUc lgrVc ssDg
  ring

theorem coefficient2_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 10) : 0 ≤ coefficient2 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  all_goals norm_num [coefficient2]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficient2_zero_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 400000 < coefficient2 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  all_goals norm_num [coefficient2, normalization]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficient2_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient2 0 e :=
  lt_trans (by norm_num [normalization]) (coefficient2_zero_floor he0 he1)

theorem value2_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < value2 u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficient2 i e * u ^ i)
    (fun i hi => mul_nonneg (coefficient2_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 11 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficient2_zero_pos he0 he1).trans_le hm

theorem numerator2_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : 0 < numerator2 x a :=
  positive_of_coordinates (by norm_num [normalization]) value2_eq
    (fun _ _ hu he0 he1 => value2_pos hu he0 he1) hx ha ha1

noncomputable def numeratorT (x a : ℝ) : ℝ :=
  lgrNT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x)
    (lgrUc x x) (lgrVc x x) (ssDg x x a)

def coefficientT {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => -7024640000000 * e ^ 6 - 13144965120000000 * e ^ 5 - 273131239772160000 * e ^ 4 - 949039046000640000 * e ^ 3 + 2901832323283353600 * e ^ 2 + 24929632477996646400 * e + 6388621765182849024
  | 1 => -67737600000000 * e ^ 6 - 105872332800000000 * e ^ 5 - 1915446433075200000 * e ^ 4 - 5142838412390400000 * e ^ 3 + 17834859988586496000 * e ^ 2 + 114422099357454336000 * e + 58794578741787033600
  | 2 => -288288000000000 * e ^ 6 - 369033024000000000 * e ^ 5 - 5734893398976000000 * e ^ 4 - 11223021792384000000 * e ^ 3 + 45865107826905600000 * e ^ 2 + 223216578226529280000 * e + 188592874397319168000
  | 3 => -710400000000000 * e ^ 6 - 727975200000000000 * e ^ 5 - 9575371752480000000 * e ^ 4 - 12518377541280000000 * e ^ 3 + 64526175270374400000 * e ^ 2 + 244977331450752000000 * e + 317375639690526720000
  | 4 => -1116450000000000 * e ^ 6 - 891987600000000000 * e ^ 5 - 9782929024650000000 * e ^ 4 - 7414628830200000000 * e ^ 3 + 54792247601088000000 * e ^ 2 + 168280671146112000000 * e + 324651374211686400000
  | 5 => -1159875000000000 * e ^ 6 - 700975875000000000 * e ^ 5 - 6325687638000000000 * e ^ 4 - 2149316964000000000 * e ^ 3 + 29491866979200000000 * e ^ 2 + 75927509861760000000 * e + 215350891381555200000
  | 6 => -796171875000000 * e ^ 6 - 351835781250000000 * e ^ 5 - 2592159536250000000 * e ^ 4 - 278035335000000000 * e ^ 3 + 10445595278400000000 * e ^ 2 + 22834246550400000000 * e + 94877506621440000000
  | 7 => -348046875000000 * e ^ 6 - 108405468750000000 * e ^ 5 - 655573275000000000 * e ^ 4 - 122021100000000000 * e ^ 3 + 2567045520000000000 * e ^ 2 + 4487136912000000000 * e + 27603518515200000000
  | 8 => -87890625000000 * e ^ 6 - 18574218750000000 * e ^ 5 - 95920593750000000 * e ^ 4 - 88772625000000000 * e ^ 3 + 469764360000000000 * e ^ 2 + 530809200000000000 * e + 5098707648000000000
  | 9 => -9765625000000 * e ^ 6 - 1347656250000000 * e ^ 5 - 7081875000000000 * e ^ 4 - 24367500000000000 * e ^ 3 + 62629200000000000 * e ^ 2 + 29062800000000000 * e + 541676160000000000
  | 10 => -189843750000000 * e ^ 4 - 2278125000000000 * e ^ 3 + 4374000000000000 * e ^ 2 + 25194240000000000
  | _ => 0

def valueT {R : Type*} [CommRing R] (u e : R) : R :=
  ∑ i ∈ Finset.range 11, coefficientT i e * u ^ i

theorem valueT_eq (u e : ℝ) :
    normalization * numeratorT (12 / 5 + u) (1 + e / 12 * (5 * (12 / 5 + u) - 8)) = valueT u e := by
  norm_num only [valueT, Finset.sum_range_succ, Finset.sum_range_zero, coefficientT]
  unfold normalization numeratorT lgrNT lgrWN lgrLN lgrUc lgrVc ssDg
  ring

theorem coefficientT_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 10) : 0 ≤ coefficientT n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  all_goals norm_num [coefficientT]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficientT_zero_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 80000 < coefficientT 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  all_goals norm_num [coefficientT, normalization]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficientT_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientT 0 e :=
  lt_trans (by norm_num [normalization]) (coefficientT_zero_floor he0 he1)

theorem valueT_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueT u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientT i e * u ^ i)
    (fun i hi => mul_nonneg (coefficientT_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 11 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientT_zero_pos he0 he1).trans_le hm

theorem numeratorT_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : 0 < numeratorT x a :=
  positive_of_coordinates (by norm_num [normalization]) valueT_eq
    (fun _ _ hu he0 he1 => valueT_pos hu he0 he1) hx ha ha1

noncomputable def numerator8 (x a : ℝ) : ℝ :=
  lgrN8 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + x)
    (lgrUc x x) (lgrVc x x) (ssDg x x a)

def coefficient8 {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => -492423680000000 * e ^ 6 - 110732461056000000 * e ^ 5 - 2413011619307520000 * e ^ 4 - 7960695345856512000 * e ^ 3 + 25098342862653849600 * e ^ 2 + 156054112374121758720 * e + 43279057074389778432
  | 1 => -4405459200000000 * e ^ 6 - 888273711360000000 * e ^ 5 - 16918924215398400000 * e ^ 4 - 42694458785095680000 * e ^ 3 + 155011975318480896000 * e ^ 2 + 725573892483695001600 * e + 481094619283309363200
  | 2 => -17212956000000000 * e ^ 6 - 3081330153600000000 * e ^ 5 - 50650666353792000000 * e ^ 4 - 91569690526003200000 * e ^ 3 + 400370394829766400000 * e ^ 2 + 1436683067958445056000 * e + 1596571978179760128000
  | 3 => -38453400000000000 * e ^ 6 - 6043296756000000000 * e ^ 5 - 84577086092160000000 * e ^ 4 - 98801176956480000000 * e ^ 3 + 565600616846726400000 * e ^ 2 + 1606832650850319360000 * e + 2695315641863270400000
  | 4 => -53969493750000000 * e ^ 6 - 7353202972500000000 * e ^ 5 - 86444958030300000000 * e ^ 4 - 54040627903320000000 * e ^ 3 + 482425195504608000000 * e ^ 2 + 1134586165519641600000 * e + 2740987325823897600000
  | 5 => -49186078125000000 * e ^ 6 - 5729975278125000000 * e ^ 5 - 55943451407250000000 * e ^ 4 - 11619692654400000000 * e ^ 3 + 261058170520800000000 * e ^ 2 + 534626645645952000000 * e + 1802494771717017600000
  | 6 => -29005869140625000 * e ^ 6 - 2847185906250000000 * e ^ 5 - 22953259710000000000 * e ^ 4 + 792773703000000000 * e ^ 3 + 93003861938400000000 * e ^ 2 + 172244841171840000000 * e + 786734312302080000000
  | 7 => -10640185546875000 * e ^ 6 - 867096562500000000 * e ^ 5 - 5807963643750000000 * e ^ 4 - 78521130000000000 * e ^ 3 + 22911736140000000000 * e ^ 2 + 37667969654400000000 * e + 226770190963200000000
  | 8 => -2200927734375000 * e ^ 6 - 146688281250000000 * e ^ 5 - 844964156250000000 * e ^ 4 - 576021375000000000 * e ^ 3 + 4156260660000000000 * e ^ 2 + 5280304464000000000 * e + 41509609920000000000
  | 9 => -196533203125000 * e ^ 6 - 10505859375000000 * e ^ 5 - 60204375000000000 * e ^ 4 - 189141750000000000 * e ^ 3 + 542999700000000000 * e ^ 2 + 404565840000000000 * e + 4371200640000000000
  | 10 => -1328906250000000 * e ^ 4 - 18680625000000000 * e ^ 3 + 37179000000000000 * e ^ 2 + 10497600000000000 * e + 201553920000000000
  | _ => 0

def value8 {R : Type*} [CommRing R] (u e : R) : R :=
  ∑ i ∈ Finset.range 11, coefficient8 i e * u ^ i

theorem value8_eq (u e : ℝ) :
    normalization * numerator8 (12 / 5 + u) (1 + e / 12 * (5 * (12 / 5 + u) - 8)) = value8 u e := by
  norm_num only [value8, Finset.sum_range_succ, Finset.sum_range_zero, coefficient8]
  unfold normalization numerator8 lgrN8 lgrWN lgrLN lgrUc lgrVc ssDg
  ring

theorem coefficient8_nonneg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 10) : 0 ≤ coefficient8 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  interval_cases n
  all_goals norm_num [coefficient8]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficient8_zero_floor {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    normalization * 500000 < coefficient8 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  have first (i : ℕ) (hi : 1 ≤ i) : e ^ i ≤ e :=
    by simpa only [pow_one] using pow_le_pow_of_le_one he0 he1 hi
  have tail (i : ℕ) (hi : 2 ≤ i) : e ^ i ≤ e ^ 2 := pow_le_pow_of_le_one he0 he1 hi
  all_goals norm_num [coefficient8, normalization]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6,
      hi 1, hi 2, hi 3, hi 4, hi 5, hi 6,
      first 2 (by norm_num), first 3 (by norm_num), first 4 (by norm_num), first 5 (by norm_num), first 6 (by norm_num), tail 3 (by norm_num),
      tail 4 (by norm_num), tail 5 (by norm_num), tail 6 (by norm_num)]

theorem coefficient8_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficient8 0 e :=
  lt_trans (by norm_num [normalization]) (coefficient8_zero_floor he0 he1)

theorem value8_pos {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < value8 u e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficient8 i e * u ^ i)
    (fun i hi => mul_nonneg (coefficient8_nonneg he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hu i))
    (show 0 ∈ Finset.range 11 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficient8_zero_pos he0 he1).trans_le hm

theorem numerator8_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : 0 < numerator8 x a :=
  positive_of_coordinates (by norm_num [normalization]) value8_eq
    (fun _ _ hu he0 he1 => value8_pos hu he0 he1) hx ha ha1

end SmoothedOctagon.S0Central.Lower

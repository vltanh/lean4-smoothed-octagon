module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip.Coordinates

/-!
# Residue signs on the outer strip

The normalized alpha interval is `0 ≤ e ≤ 1`. Two residue polynomials
have nonnegative coefficients in `X = x - 12/5`. The duration residue
has two negative top coefficients; the bound `X ≤ 7` absorbs that tail.
-/

@[expose] public section
namespace SmoothedOctagon

/-- `98α⁴(U_T + 5/2) = (14αc + c²)(c² - Q₀) + 98α³c - 14α²(2c² - Q₀) + 245α⁴`, `c = α + 1`,
`Q₀ = M₀S`. -/
noncomputable def lgrQTf (x a : ℝ) : ℝ :=
  (14 * a * (a + 1) + (a + 1) ^ 2) * ((a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1)) + 98 * a ^ 3 * (a + 1) -
    14 * a ^ 2 * (2 * (a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1)) + 245 * a ^ 4

/-- `98α⁴U₂ = 5c²(c² - Q₀) + 98α³c - 14α²(2c² - Q₀)`. -/
noncomputable def lgrQ2f (x a : ℝ) : ℝ :=
  5 * (a + 1) ^ 2 * ((a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1)) + 98 * a ^ 3 * (a + 1) -
    14 * a ^ 2 * (2 * (a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1))

/-- `84α³SM(R_T - x²/3)` at the continued value `û(-α)`: `3·4SM·Q + 84α⁴SM - 28α³SMx²`, the
continued norm `4SM·Q` cleared with `U_I = 4SMu_∞`, `J_J = 4SMJ`, `P₀' = 4SM·P₀`. -/
noncomputable def lgrSRf (x a : ℝ) : ℝ :=
  let S := x + 1
  let F4 := 4 * (x + 1) * (35 * x + 13)
  let UI := 3 * (x + 1) * (35 * x + 13) + (x - 1) ^ 2
  let JJ := 7 * (x - 1) ^ 3
  let c := a + 1
  let δ := 2 * (a - x)
  let M0 := 6 * a ^ 2 + 1
  let Q0 := M0 * S
  let P0 := 4 * (35 * x + 13) * (M0 * (1 - S ^ 2) + (2 * S - 1) * S)
  let C0 := M0 ^ 2 - M0 * S + S ^ 2
  3 * (UI * δ ^ 2 * c ^ 2 - c * (UI * δ * (2 * c ^ 2 - Q0) + JJ * δ ^ 2 - δ * P0) +
      (F4 * C0 - c ^ 2 * P0 + UI * c ^ 2 * (c ^ 2 - Q0) + JJ * δ * (2 * c ^ 2 - Q0)) -
      F4 * (49 * a ^ 4) - JJ * c * (c ^ 2 - Q0)) +
    84 * a ^ 4 * (x + 1) * (35 * x + 13) - 28 * a ^ 3 * (x + 1) * (35 * x + 13) * x ^ 2

namespace S0Outer.Residues

noncomputable def normalization : ℝ := 55 ^ 4 * 5 ^ 7

def coefficientQT {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => 690819187500 * e ^ 4 + 13223797925000 * e ^ 3 + 92023496898125 * e ^ 2 + 265693190421750 * e + 243233904226700
  | 1 => -13387968750 * e ^ 4 + 3470161500000 * e ^ 3 + 49112338478125 * e ^ 2 + 210963554392500 * e + 252691515904375
  | 2 => -90626250000 * e ^ 3 + 5747098500000 * e ^ 2 + 52611260487500 * e + 93468663062500
  | 3 => -230051250000 * e ^ 2 + 3029598000000 * e + 12471931312500
  | 4 => -259545000000 * e - 179685000000
  | 5 => -109807500000
  | _ => 0

def valueQT {R : Type*} [CommRing R] (X e : R) : R :=
  ∑ i ∈ Finset.range 6, coefficientQT i e * X ^ i

theorem valueQT_eq (X e : ℝ) :
    normalization * lgrQTf (12 / 5 + X) ((22 * (12 / 5 + X) + 20 + 13 * e) / 55) =
      valueQT X e := by
  norm_num only [valueQT, Finset.sum_range_succ, Finset.sum_range_zero, coefficientQT]
  unfold normalization lgrQTf
  ring

noncomputable def floorQT (n : ℕ) : ℝ :=
  match n with
  | 0 => 300
  | 3 => 17
  | 4 => -1
  | 5 => -1 / 5
  | _ => 0

theorem coefficientQT_bound {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 5) : normalization * floorQT n ≤ coefficientQT n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientQT, normalization, floorQT]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, hi 1, hi 2, hi 3, hi 4]

theorem valueQT_pos {X e : ℝ} (hX : 0 ≤ X) (hX7 : X ≤ 7)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : 0 < valueQT X e := by
  have hm := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range 6) =>
    mul_le_mul_of_nonneg_right (coefficientQT_bound he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
  have heq : (∑ i ∈ Finset.range 6, normalization * floorQT i * X ^ i) =
      normalization * (300 + X ^ 3 * (17 - X - X ^ 2 / 5)) := by
    norm_num [Finset.sum_range_succ, floorQT]
    ring
  rw [heq] at hm
  have ht : 0 ≤ 17 - X - X ^ 2 / 5 := by
    nlinarith only [hX, hX7, mul_nonneg hX (sub_nonneg.mpr hX7)]
  apply lt_of_lt_of_le _ hm
  exact mul_pos (by norm_num [normalization]) (by positivity)

theorem QT_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) 
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < lgrQTf x a := by
  have hp := valueQT_pos (sub_nonneg.mpr hx) (by linarith only [hx9]) 
    (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueQT_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalization])).mp hp

def coefficientQ2 {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => 577021453125 * e ^ 4 + 11584767268750 * e ^ 3 + 83279935448125 * e ^ 2 + 245811525891750 * e + 223306029804700
  | 1 => 120491718750 * e ^ 4 + 6038591812500 * e ^ 3 + 71132209321875 * e ^ 2 + 302139904998750 * e + 395675329466875
  | 2 => 815636250000 * e ^ 3 + 20742257250000 * e ^ 2 + 141222139987500 * e + 272807834750000
  | 3 => 2070461250000 * e ^ 2 + 29509086750000 * e + 91422238187500
  | 4 => 2335905000000 * e + 15068583750000
  | 5 => 988267500000
  | _ => 0

def valueQ2 {R : Type*} [CommRing R] (X e : R) : R :=
  ∑ i ∈ Finset.range 6, coefficientQ2 i e * X ^ i

theorem valueQ2_eq (X e : ℝ) :
    normalization * lgrQ2f (12 / 5 + X) ((22 * (12 / 5 + X) + 20 + 13 * e) / 55) =
      valueQ2 X e := by
  norm_num only [valueQ2, Finset.sum_range_succ, Finset.sum_range_zero, coefficientQ2]
  unfold normalization lgrQ2f
  ring

theorem coefficientQ2_bound {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 5) : 0 ≤ coefficientQ2 n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientQ2]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, hi 1, hi 2, hi 3, hi 4]

theorem coefficientQ2_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientQ2 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  norm_num [coefficientQ2]
  linarith only [lo 1, lo 2, lo 3, lo 4, hi 1, hi 2, hi 3, hi 4]

theorem valueQ2_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueQ2 X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientQ2 i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientQ2_bound he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 6 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientQ2_zero_pos he0 he1).trans_le hm

theorem Q2_pos {x a : ℝ} (hx : 12 / 5 ≤ x) 
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < lgrQ2f x a := by
  have hp := valueQ2_pos (sub_nonneg.mpr hx) 
    (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueQ2_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalization])).mp hp

def coefficientSR {R : Type*} [CommRing R] (n : ℕ) (e : R) : R :=
  match n with
  | 0 => -75533420235000 * e ^ 4 - 1882560040788375 * e ^ 3 - 13227167615201475 * e ^ 2 - 13208023805482740 * e + 95243578178103804
  | 1 => -67003570481250 * e ^ 4 - 2085538963243125 * e ^ 3 - 16041045955715625 * e ^ 2 - 810282508728225 * e + 231064349891344545
  | 2 => -18119276906250 * e ^ 4 - 822939620384375 * e ^ 3 - 7220176826728125 * e ^ 2 + 15038896769836875 * e + 228788354856355775
  | 3 => -1365572812500 * e ^ 4 - 136516190484375 * e ^ 3 - 1506567682546875 * e ^ 2 + 10988749502128125 * e + 120602818705175625
  | 4 => -8129929843750 * e ^ 3 - 154292933437500 * e ^ 2 + 3164026819078125 * e + 36671712103571875
  | 5 => -7745058750000 * e ^ 2 + 397949140875000 * e + 6436386907225000
  | 6 => 17162413125000 * e + 602305617375000
  | 7 => 23022972500000
  | _ => 0

def valueSR {R : Type*} [CommRing R] (X e : R) : R :=
  ∑ i ∈ Finset.range 8, coefficientSR i e * X ^ i

theorem valueSR_eq (X e : ℝ) :
    normalization * lgrSRf (12 / 5 + X) ((22 * (12 / 5 + X) + 20 + 13 * e) / 55) =
      valueSR X e := by
  norm_num only [valueSR, Finset.sum_range_succ, Finset.sum_range_zero, coefficientSR]
  unfold normalization lgrSRf
  ring

theorem coefficientSR_bound {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (n : ℕ) (hn : n ≤ 7) : 0 ≤ coefficientSR n e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  interval_cases n
  all_goals norm_num [coefficientSR]
  all_goals
    linarith only [lo 1, lo 2, lo 3, lo 4, hi 1, hi 2, hi 3, hi 4]

theorem coefficientSR_zero_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < coefficientSR 0 e := by
  have lo (i : ℕ) : 0 ≤ e ^ i := pow_nonneg he0 i
  have hi (i : ℕ) : e ^ i ≤ 1 := by simpa using pow_le_pow_left₀ he0 he1 i
  norm_num [coefficientSR]
  linarith only [lo 1, lo 2, lo 3, lo 4, hi 1, hi 2, hi 3, hi 4]

theorem valueSR_pos {X e : ℝ} (hX : 0 ≤ X) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 < valueSR X e := by
  have hm := Finset.single_le_sum
    (f := fun i => coefficientSR i e * X ^ i)
    (fun i hi => mul_nonneg (coefficientSR_bound he0 he1 i
      (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hX i))
    (show 0 ∈ Finset.range 8 by decide)
  norm_num only [pow_zero, mul_one] at hm
  exact (coefficientSR_zero_pos he0 he1).trans_le hm

theorem SR_pos {x a : ℝ} (hx : 12 / 5 ≤ x) 
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : 0 < lgrSRf x a := by
  have hp := valueSR_pos (sub_nonneg.mpr hx) 
    (position_nonneg ha) (position_le_one ham)
  rw [← normalization_eq valueSR_eq x a] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num [normalization])).mp hp

end S0Outer.Residues
end SmoothedOctagon

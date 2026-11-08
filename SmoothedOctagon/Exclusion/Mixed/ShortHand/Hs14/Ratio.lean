module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Envelope
public import SmoothedOctagon.Exclusion.Mixed.Short.Calc

/-!
# Gate S1 helper: the derivative ratio `7/96` on the order strip

`MIXED_SMALLER_SHORT_SHARP_LOW_RATIO_CORRECTED_CAP` (4)-(15); inventory HS-S01 C11, C13, C14.

## Main API

* `hs14P`, `hs14_P_bern`, `hs14_P_pos`: the polynomial `P` of (11) is positive on the order strip
  `x + (8/17)(α - 1) ≤ β ≤ x + (4/5)(α - 1)` (Bernstein form (15)).
* `hs14_ratio_strip`: the statement of `hs1_ratio` with the strip (13) as extra hypotheses.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The polynomial `P` of `SHARP_LOW_RATIO_CORRECTED_CAP` (11)**:
`P = 49SαH_N - 4B(17x² + 20x + 17)(6α² + 1 - SD)`, `H_N = [3S² - (x - 1)²]B² - 12S²αB + 12S²α²`,
`B = α + β`. -/
noncomputable def hs14P (x al be : ℝ) : ℝ :=
  49 * (1 + x) * al * ((3 * (1 + x) ^ 2 - (x - 1) ^ 2) * (al + be) ^ 2 -
    12 * (1 + x) ^ 2 * al * (al + be) + 12 * (1 + x) ^ 2 * al ^ 2) -
    4 * (al + be) * (17 * x ^ 2 + 20 * x + 17) * (6 * al ^ 2 + 1 - (1 + x) * hsDg x be al)

/-- A sextic `432 + c₁z + ⋯ + c₆z⁶` of `SHARP_LOW_RATIO_CORRECTED_CAP` (15). -/
noncomputable def hs14H (c₁ c₂ c₃ c₄ c₅ c₆ z : ℝ) : ℝ :=
  432 + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3 + c₄ * z ^ 4 + c₅ * z ^ 5 + c₆ * z ^ 6

/-- **A sextic is at least `300` on `[0, 1]`**: bound `cᵢzⁱ ≥ dᵢz²` (`dᵢ ≤ min(cᵢ, 0)`, `i ≥ 3`); the
remaining concave quadratic `432 + c₁z + (c₂ + Σdᵢ)z²` is at least `300` at both ends. -/
theorem hs14H_ge {c₁ c₂ c₃ c₄ c₅ c₆ d₃ d₄ d₅ d₆ z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (h₁ : 0 ≤ c₁)
    (e₃ : d₃ ≤ c₃) (e₄ : d₄ ≤ c₄) (e₅ : d₅ ≤ c₅) (e₆ : d₆ ≤ c₆) (f₃ : d₃ ≤ 0) (f₄ : d₄ ≤ 0)
    (f₅ : d₅ ≤ 0) (f₆ : d₆ ≤ 0) (hs : 0 ≤ 132 + c₁ + c₂ + d₃ + d₄ + d₅ + d₆) :
    0 ≤ hs14H c₁ c₂ c₃ c₄ c₅ c₆ z - 300 := by
  unfold hs14H
  have p2 : z ^ 2 ≤ z := by nlinarith
  have p3 : z ^ 3 ≤ z ^ 2 := by nlinarith
  have p4 : z ^ 4 ≤ z ^ 2 := by nlinarith
  have p5 : z ^ 5 ≤ z ^ 2 := by nlinarith [pow_nonneg hz 3, pow_nonneg hz 4]
  have p6 : z ^ 6 ≤ z ^ 2 := by nlinarith [pow_nonneg hz 4, pow_nonneg hz 5]
  have k3 : d₃ * z ^ 2 ≤ c₃ * z ^ 3 := by nlinarith [pow_nonneg hz 3, pow_nonneg hz 2]
  have k4 : d₄ * z ^ 2 ≤ c₄ * z ^ 4 := by nlinarith [pow_nonneg hz 4, pow_nonneg hz 2]
  have k5 : d₅ * z ^ 2 ≤ c₅ * z ^ 5 := by nlinarith [pow_nonneg hz 5, pow_nonneg hz 2]
  have k6 : d₆ * z ^ 2 ≤ c₆ * z ^ 6 := by nlinarith [pow_nonneg hz 6, pow_nonneg hz 2]
  have hc1 : 0 ≤ c₁ * z := mul_nonneg h₁ hz
  rcases le_total (c₂ + d₃ + d₄ + d₅ + d₆) 0 with hm | hm
  · have k2 : (c₂ + d₃ + d₄ + d₅ + d₆) * z ≤ (c₂ + d₃ + d₄ + d₅ + d₆) * z ^ 2 :=
      mul_le_mul_of_nonpos_left p2 hm
    have := mul_nonneg hs hz
    nlinarith
  · have := mul_nonneg hm (pow_nonneg hz 2)
    nlinarith

/-- Nonnegativity of a Bernstein combination with nonnegative weights. -/
private theorem hs14_bern_nonneg {a a' t t' e0 e10 e11 e12 e20 e21 e22 e30 e31 e32 : ℝ}
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (ht : 0 ≤ t) (ht' : 0 ≤ t') (h0 : 0 ≤ e0) (h10 : 0 ≤ e10)
    (h11 : 0 ≤ e11) (h12 : 0 ≤ e12) (h20 : 0 ≤ e20) (h21 : 0 ≤ e21) (h22 : 0 ≤ e22) (h30 : 0 ≤ e30)
    (h31 : 0 ≤ e31) (h32 : 0 ≤ e32) :
    0 ≤ a' ^ 3 * e0 + 3 * a * a' ^ 2 * t' ^ 2 * e10 + 6 * a * a' ^ 2 * t * t' * e11 +
      3 * a * a' ^ 2 * t ^ 2 * e12 + 3 * a ^ 2 * a' * t' ^ 2 * e20 + 6 * a ^ 2 * a' * t * t' * e21 +
      3 * a ^ 2 * a' * t ^ 2 * e22 + a ^ 3 * t' ^ 2 * e30 + 2 * a ^ 3 * t * t' * e31 +
      a ^ 3 * t ^ 2 * e32 := by
  positivity

/-- **`P ≥ 300` on the enlarged strip** (`SHARP_LOW_RATIO_CORRECTED_CAP` (14)-(15)): in the
coordinates `x = 1 + z`, `α = 1 + za`, `β = 1 + z + (8/17 + 28t/85)za`, `z, a, t ∈ [0, 1]`, `P` is
the Bernstein combination `Σ B_{j,3}(a)B_{k,2}(t)H_{jk}(z)` of the ten displayed sextics, each at
least `300` on `[0, 1]` (`hs14H_ge`). -/
theorem hs14_P_bern {z a t : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) : 300 ≤ hs14P (1 + z) (1 + z * a) (1 + z + (8 / 17 + 28 * t / 85) * z * a) := by
  have g0 := hs14H_ge (c₁ := 2376) (c₂ := 2000) (c₃ := (-804)) (c₄ := (-1844)) (c₅ := (-878)) (c₆ := (-136)) (d₃ := (-804)) (d₄ := (-1844)) (d₅ := (-878)) (d₆ := (-136)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g10 := hs14H_ge (c₁ := (32400 / 17)) (c₂ := (36232 / 17)) (c₃ := (-5432 / 17)) (c₄ := (-81680 / 51)) (c₅ := (-14690 / 17)) (c₆ := (-146)) (d₃ := (-5432 / 17)) (d₄ := (-81680 / 51)) (d₅ := (-14690 / 17)) (d₆ := (-146)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g11 := hs14H_ge (c₁ := (163008 / 85)) (c₂ := (189112 / 85)) (c₃ := (-28336 / 85)) (c₄ := (-147128 / 85)) (c₅ := (-241126 / 255)) (c₆ := (-2414 / 15)) (d₃ := (-28336 / 85)) (d₄ := (-147128 / 85)) (d₅ := (-241126 / 255)) (d₆ := (-2414 / 15)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g12 := hs14H_ge (c₁ := (9648 / 5)) (c₂ := (11592 / 5)) (c₃ := (-1736 / 5)) (c₄ := (-27904 / 15)) (c₅ := (-15406 / 15)) (c₆ := (-2638 / 15)) (d₃ := (-1736 / 5)) (d₄ := (-27904 / 15)) (d₅ := (-15406 / 15)) (d₆ := (-2638 / 15)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g20 := hs14H_ge (c₁ := (24408 / 17)) (c₂ := (475112 / 289)) (c₃ := (-11264 / 289)) (c₄ := (-394420 / 289)) (c₅ := (-762508 / 867)) (c₆ := (-9008 / 51)) (d₃ := (-11264 / 289)) (d₄ := (-394420 / 289)) (d₅ := (-762508 / 867)) (d₆ := (-9008 / 51)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g21 := hs14H_ge (c₁ := (124056 / 85)) (c₂ := (153864 / 85)) (c₃ := (8928 / 85)) (c₄ := (-358124 / 255)) (c₅ := (-242612 / 255)) (c₆ := (-3320 / 17)) (d₃ := 0) (d₄ := (-358124 / 255)) (d₅ := (-242612 / 255)) (d₆ := (-3320 / 17)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g22 := hs14H_ge (c₁ := (7416 / 5)) (c₂ := (50472 / 25)) (c₃ := (1408 / 5)) (c₄ := (-36564 / 25)) (c₅ := (-26132 / 25)) (c₆ := (-5472 / 25)) (d₃ := 0) (d₄ := (-36564 / 25)) (d₅ := (-26132 / 25)) (d₆ := (-5472 / 25)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g30 := hs14H_ge (c₁ := (16416 / 17)) (c₂ := (155504 / 289)) (c₃ := (-88260 / 289)) (c₄ := (-200932 / 289)) (c₅ := (-139868 / 289)) (c₆ := (-28476 / 289)) (d₃ := (-88260 / 289)) (d₄ := (-200932 / 289)) (d₅ := (-139868 / 289)) (d₆ := (-28476 / 289)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g31 := hs14H_ge (c₁ := (85104 / 85)) (c₂ := (64256 / 85)) (c₃ := (8244 / 85)) (c₄ := (-7244 / 17)) (c₅ := (-2204 / 5)) (c₆ := (-8876 / 85)) (d₃ := 0) (d₄ := (-7244 / 17)) (d₅ := (-2204 / 5)) (d₆ := (-8876 / 85)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have g32 := hs14H_ge (c₁ := (5184 / 5)) (c₂ := (27536 / 25)) (c₃ := (4092 / 5)) (c₄ := (2988 / 25)) (c₅ := (-7548 / 25)) (c₆ := (-2492 / 25)) (d₃ := 0) (d₄ := 0) (d₅ := (-7548 / 25)) (d₆ := (-2492 / 25)) hz hz1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have key : hs14P (1 + z) (1 + z * a) (1 + z + (8 / 17 + 28 * t / 85) * z * a) - 300 =
      (fun a' t' : ℝ => a' ^ 3 * (hs14H 2376 2000 (-804) (-1844) (-878) (-136) z - 300) +
      3 * a * a' ^ 2 * t' ^ 2 * (hs14H (32400 / 17) (36232 / 17) (-5432 / 17) (-81680 / 51) (-14690 / 17) (-146) z - 300) +
      6 * a * a' ^ 2 * t * t' * (hs14H (163008 / 85) (189112 / 85) (-28336 / 85) (-147128 / 85) (-241126 / 255) (-2414 / 15) z - 300) +
      3 * a * a' ^ 2 * t ^ 2 * (hs14H (9648 / 5) (11592 / 5) (-1736 / 5) (-27904 / 15) (-15406 / 15) (-2638 / 15) z - 300) +
      3 * a ^ 2 * a' * t' ^ 2 * (hs14H (24408 / 17) (475112 / 289) (-11264 / 289) (-394420 / 289) (-762508 / 867) (-9008 / 51) z - 300) +
      6 * a ^ 2 * a' * t * t' * (hs14H (124056 / 85) (153864 / 85) (8928 / 85) (-358124 / 255) (-242612 / 255) (-3320 / 17) z - 300) +
      3 * a ^ 2 * a' * t ^ 2 * (hs14H (7416 / 5) (50472 / 25) (1408 / 5) (-36564 / 25) (-26132 / 25) (-5472 / 25) z - 300) +
      a ^ 3 * t' ^ 2 * (hs14H (16416 / 17) (155504 / 289) (-88260 / 289) (-200932 / 289) (-139868 / 289) (-28476 / 289) z - 300) +
      2 * a ^ 3 * t * t' * (hs14H (85104 / 85) (64256 / 85) (8244 / 85) (-7244 / 17) (-2204 / 5) (-8876 / 85) z - 300) +
      a ^ 3 * t ^ 2 * (hs14H (5184 / 5) (27536 / 25) (4092 / 5) (2988 / 25) (-7548 / 25) (-2492 / 25) z - 300)) (1 - a) (1 - t) := by
    simp only [hs14P, hs14H, hsDg]; ring
  have : 0 ≤ hs14P (1 + z) (1 + z * a) (1 + z + (8 / 17 + 28 * t / 85) * z * a) - 300 := by
    rw [key]
    beta_reduce
    exact hs14_bern_nonneg ha (sub_nonneg.mpr ha1) ht (sub_nonneg.mpr ht1) g0 g10 g11 g12 g20 g21 g22 g30 g31 g32
  linarith

/-- **`P > 0` on the order strip** (`SHARP_LOW_RATIO_CORRECTED_CAP` (13)-(15)). -/
theorem hs14_P_pos {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al ≤ x)
    (hlo : x + 8 / 17 * (al - 1) ≤ be) (hhi : be ≤ x + 4 / 5 * (al - 1)) : 0 < hs14P x al be := by
  have hz : 0 < x - 1 := by linarith
  have ha0 : 0 ≤ (al - 1) / (x - 1) := div_nonneg (by linarith) hz.le
  have ha1 : (al - 1) / (x - 1) ≤ 1 := by rw [div_le_one hz]; linarith
  have e1 : 1 + (x - 1) = x := by ring
  have e2 : 1 + (x - 1) * ((al - 1) / (x - 1)) = al := by field_simp; ring
  rcases eq_or_lt_of_le hal with h | h
  · have hbe : be = x := by rw [← h] at hlo hhi; linarith
    have := hs14_P_bern (z := x - 1) hz.le (by linarith) ha0 ha1 le_rfl zero_le_one
    have e3 : 1 + (x - 1) + (8 / 17 + 28 * 0 / 85) * (x - 1) * ((al - 1) / (x - 1)) = be := by
      rw [hbe, ← h]; ring
    rw [e3, e2, e1] at this
    linarith
  · have hal1 : 0 < al - 1 := by linarith
    have ht0 : 0 ≤ ((be - x) / (al - 1) - 8 / 17) * (85 / 28) := by
      apply mul_nonneg _ (by norm_num)
      rw [sub_nonneg, le_div_iff₀ hal1]; linarith
    have ht1 : ((be - x) / (al - 1) - 8 / 17) * (85 / 28) ≤ 1 := by
      have : (be - x) / (al - 1) ≤ 4 / 5 := by rw [div_le_iff₀ hal1]; linarith
      linarith
    have := hs14_P_bern (z := x - 1) hz.le (by linarith) ha0 ha1 ht0 ht1
    have e3 : 1 + (x - 1) + (8 / 17 + 28 * (((be - x) / (al - 1) - 8 / 17) * (85 / 28)) / 85) *
        (x - 1) * ((al - 1) / (x - 1)) = be := by
      field_simp; ring
    rw [e3, e2, e1] at this
    linarith

/-- **`F(1/7) > 0` on the strip** (`SHARP_LOW_RATIO_CORRECTED_CAP` (10)-(12)): with
`b₇ = (6α² + 1 - SD)/(7Sα²)`, `J_A - (2u - 6/7)b₇ > 0` for `u ≤ u₀`
(decreasing in `u`; at `u₀` it is `P/(588S³α²(α + β))`). -/
theorem hs14_F7_pos {x be al u : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al ≤ x)
    (hlo : x + 8 / 17 * (al - 1) ≤ be) (hhi : be ≤ x + 4 / 5 * (al - 1)) (hu0 : u ≤ hsU0 x)
    (hb7 : -2 / 7 ≤ (6 * al ^ 2 + 1 - (1 + x) * hsDg x be al) / (7 * (1 + x) * al ^ 2)) :
    0 < (m2U (hsRA al be) - u) / hsRA al be -
      (2 * u - 6 / 7) * ((6 * al ^ 2 + 1 - (1 + x) * hsDg x be al) / (7 * (1 + x) * al ^ 2)) := by
  have hal0 : 0 < al := by linarith
  have hS : 0 < 1 + x := by linarith
  have hB : 0 < al + be := by linarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hrA2 : 1 / hsRA al be ≥ 2 := by
    unfold hsRA; rw [one_div_div, ge_iff_le, le_div_iff₀ hal0]; linarith
  set b₇ := (6 * al ^ 2 + 1 - (1 + x) * hsDg x be al) / (7 * (1 + x) * al ^ 2) with hb₇
  have hP := hs14_P_pos hx hx2 hal hax hlo hhi
  have e : (m2U (hsRA al be) - hsU0 x) / hsRA al be - (2 * hsU0 x - 6 / 7) * b₇ =
      hs14P x al be / (588 * (1 + x) ^ 3 * al ^ 2 * (al + be)) := by
    rw [hb₇]; unfold m2U hsRA hsU0 hs14P
    field_simp
    ring
  have h0 : 0 < (m2U (hsRA al be) - hsU0 x) / hsRA al be - (2 * hsU0 x - 6 / 7) * b₇ := by
    rw [e]; positivity
  have e2 : (m2U (hsRA al be) - u) / hsRA al be - (2 * u - 6 / 7) * b₇ -
      ((m2U (hsRA al be) - hsU0 x) / hsRA al be - (2 * hsU0 x - 6 / 7) * b₇) =
      (hsU0 x - u) * (1 / hsRA al be + 2 * b₇) := by
    field_simp; ring
  have : 0 ≤ (hsU0 x - u) * (1 / hsRA al be + 2 * b₇) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- **`F` decreases on `[0, 1/7]`** (`SHARP_LOW_RATIO_CORRECTED_CAP` (9), inventory HS-S01 C13
step 6): `F(s) = (7/12)(1 - s)²(1 + 2b(s)) - 2ub(s) - 3s`, `b(s) = 1/S - sK`, with `0 ≤ K ≤ 9/2`,
`b(1/7) ≥ -2/7`, `u ≤ 41/54`: `F(1/7) ≤ F(q)` for `0 ≤ q ≤ 1/7`. -/
theorem hs14_F_anti {S K u q : ℝ} (hK0 : 0 ≤ K) (hK : K ≤ 9 / 2) (hb : -2 / 7 ≤ 1 / S - K / 7)
    (hu : u ≤ 41 / 54) (hq0 : 0 ≤ q) (hq7 : q ≤ 1 / 7) :
    7 / 12 * (1 - 1 / 7) ^ 2 * (1 + 2 * (1 / S - 1 / 7 * K)) - 2 * u * (1 / S - 1 / 7 * K) -
        3 * (1 / 7) ≤
      7 / 12 * (1 - q) ^ 2 * (1 + 2 * (1 / S - q * K)) - 2 * u * (1 / S - q * K) - 3 * q := by
  have h := ss_le_of_deriv (f := fun s => -(7 / 12 * (1 - s) ^ 2 * (1 + 2 * (1 / S - s * K)) -
      2 * u * (1 / S - s * K) - 3 * s))
    (f' := fun s => 7 / 6 * (1 - s) * (1 + 2 * (1 / S - s * K)) + 7 / 6 * (1 - s) ^ 2 * K -
      2 * u * K + 3) hq7 (fun s _ => by
      have h0 := (hasDerivAt_id' s).const_sub 1
      have h1 := h0.mul h0
      have h2 := ((hasDerivAt_id' s).mul_const K).const_sub (1 / S)
      have := ((((h1.const_mul (7 / 12)).mul ((h2.const_mul 2).const_add 1)).sub
        (h2.const_mul (2 * u))).sub ((hasDerivAt_id' s).const_mul 3)).neg
      convert this using 1
      · funext s; simp only [Pi.mul_apply, Pi.neg_apply, Pi.sub_apply]; ring
      · simp only [Pi.mul_apply]; ring) (fun s hs => by
      have hs7 : s ≤ 1 / 7 := hs.2.le
      have hs0 : 0 ≤ s := hq0.trans hs.1.le
      have hbs : -2 / 7 ≤ 1 / S - s * K := by nlinarith
      have hC : 3 / 7 ≤ 7 / 12 * (1 - s) ^ 2 := by nlinarith
      have h1 : 0 ≤ 7 / 6 * (1 - s) * (1 + 2 * (1 / S - s * K)) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 2 * K * (u - 7 / 12 * (1 - s) ^ 2) ≤ 2 * K * (41 / 54 - 3 / 7) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h3 : 2 * K * (41 / 54 - 3 / 7) ≤ 3 := by nlinarith
      nlinarith)
  linarith

/-- **The derivative ratio is at most `7/96` on the order strip** (`SHARP_LOW_RATIO_CORRECTED_CAP`
(4)-(15), inventory HS-S01 C13-C14): the statement of `hs1_ratio` with the strip (13). -/
theorem hs14_ratio_strip {x be al u rho τ t EL : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (hD : 0 < hsDg x be al) (hu : 3 / 4 ≤ u) (hu0 : u ≤ hsU0 x)
    (hurA : u ≤ m2U (hsRA al be)) (hρ : 0 < rho) (hq7 : hsQ al rho ≤ 1 / 7) (hτ : 2 ≤ τ)
    (hτq : τ * hsQ al rho < hsRA al be) (_ht : 0 < t) (htr : t ≤ 1 / (1 + x))
    (hB : 0 < 1 + τ * (hsLam al rho * t - hsLam al rho * rho * hsDg x be al))
    (hEL : EL ≤ 3 * hsQ al rho - (m2U (hsRA al be) - u) / hsRA al be)
    (hlo : x + 8 / 17 * (al - 1) ≤ be) (hhi : be ≤ x + 4 / 5 * (al - 1)) :
    2 * u * (hsLam al rho * t - hsLam al rho * rho * hsDg x be al) + EL ≤
      7 / 12 * (1 - hsQ al rho) ^ 2 *
        (1 + τ * (hsLam al rho * t - hsLam al rho * rho * hsDg x be al)) := by
  have hal0 : 0 < al := by linarith
  have hS : 0 < 1 + x := by linarith
  have hτ0 : 0 < τ := by linarith
  obtain ⟨-, hlam, hd⟩ := hs_scale_coords (x := x) (be := be) hal hρ
  set q := hsQ al rho with hqdef
  set D := hsDg x be al with hDdef
  set rA := hsRA al be with hrAdef
  set JA := (m2U rA - u) / rA with hJA
  have hlam0 : 0 < hsLam al rho := by
    unfold hsLam; apply div_pos one_pos
    have : 0 ≤ rho * (al ^ 2 - 1) := mul_nonneg hρ.le (by nlinarith)
    linarith
  have hq0 : 0 < q := by rw [hqdef]; unfold hsQ; exact mul_pos (mul_pos (by positivity) hlam0) hρ
  have hrA : 0 < rA := by rw [hrAdef]; unfold hsRA; exact div_pos hal0 (by linarith)
  have hrA2 : rA < 1 / 2 := by
    rw [hrAdef]; unfold hsRA; rw [div_lt_iff₀ (by linarith)]; linarith
  have hJA0 : 0 ≤ JA := by rw [hJA]; exact div_nonneg (by linarith) hrA.le
  have hu41 : u ≤ 41 / 54 := by
    have : (x - 1) ^ 2 / (12 * (x + 1) ^ 2) ≤ 1 / 108 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    unfold hsU0 at hu0; linarith
  -- `K = (1 - α⁻²)/S + D/α²` and `b₀ = 1/S - qK`
  set K := (1 - 1 / al ^ 2) / (1 + x) + D / al ^ 2 with hK
  have hDle : D ≤ 4 * al ^ 2 := by
    rw [hDdef]; unfold hsDg
    have h1 : 2 * be * (al - x) ≤ 2 * x * (al - x) :=
      mul_le_mul_of_nonpos_right (by linarith) (by linarith)
    nlinarith
  have ha1 : 1 / al ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hK0 : 0 ≤ K := by
    rw [hK]; apply add_nonneg (div_nonneg (by linarith) hS.le) (div_nonneg hD.le (by positivity))
  have hK9 : K ≤ 9 / 2 := by
    rw [hK]
    have : (1 - 1 / al ^ 2) / (1 + x) ≤ 1 / 2 := by
      rw [div_le_iff₀ hS]; have : 0 < 1 / al ^ 2 := by positivity
      linarith
    have : D / al ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hb7 : -2 / 7 ≤ 1 / (1 + x) - K / 7 := by
    rw [hK]
    have : 6 / 7 / 3 ≤ (1 - (1 - 1 / al ^ 2) / 7) / (1 + x) := by
      rw [div_le_div_iff₀ (by norm_num) hS]
      have : 0 < 1 / al ^ 2 := by positivity
      nlinarith
    have : D / al ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    have e : 1 / (1 + x) - ((1 - 1 / al ^ 2) / (1 + x) + D / al ^ 2) / 7 =
        (1 - (1 - 1 / al ^ 2) / 7) / (1 + x) - D / al ^ 2 / 7 := by ring
    rw [e]; linarith
  set b := hsLam al rho * t - hsLam al rho * rho * D with hb
  set b₀ := 1 / (1 + x) - q * K with hb₀
  clear_value q D rA JA K b b₀
  have hbb₀ : b ≤ b₀ := by
    rw [hb, hb₀, hd, hlam, hK]
    have : (1 - (1 - 1 / al ^ 2) * q) * t ≤ (1 - (1 - 1 / al ^ 2) * q) * (1 / (1 + x)) := by
      apply mul_le_mul_of_nonneg_left htr; rw [← hlam]; exact hlam0.le
    have e : (1 - (1 - 1 / al ^ 2) * q) * (1 / (1 + x)) - q * (D / al ^ 2) =
        1 / (1 + x) - q * ((1 - 1 / al ^ 2) / (1 + x) + D / al ^ 2) := by ring
    linarith
  -- the reduction to `f(b₀) ≥ 0`
  have hτE : τ * (3 * q - JA) < 2 * u := by
    have : τ * (3 * q - JA) ≤ 3 * (τ * q) := by have := mul_nonneg hτ0.le hJA0; linarith
    linarith
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ,
      f = fun c => 7 / 12 * (1 - q) ^ 2 * (1 + τ * c) - 2 * u * c - (3 * q - JA) := ⟨_, rfl⟩
  have hfb₀ : 0 ≤ f b₀ := by
    rcases le_or_gt b₀ 0 with h0 | h0
    · have e : f b₀ = (1 + τ * b₀) * (7 / 12 * (1 - q) ^ 2 - (3 * q - JA)) +
          b₀ * (τ * (3 * q - JA) - 2 * u) := by simp only [hf]; ring
      rw [e]
      have h1 : 0 < 1 + τ * b₀ := by
        have := mul_le_mul_of_nonneg_left hbb₀ hτ0.le; linarith
      have h2 : 0 ≤ 7 / 12 * (1 - q) ^ 2 - 3 * q := by
        have e2 : 7 / 12 * (1 - q) ^ 2 - 3 * q = 7 / 12 * ((1 / 7 - q) * (7 - q)) := by ring
        rw [e2]; apply mul_nonneg (by norm_num); apply mul_nonneg <;> linarith
      apply add_nonneg (mul_nonneg h1.le (by linarith))
      exact mul_nonneg_of_nonpos_of_nonpos h0 (by linarith)
    · have hF := hs14_F_anti hK0 hK9 hb7 hu41 hq0.le hq7
      have hF7 := hs14_F7_pos hx hx2 hal hax.le hlo hhi hu0 (by
        have e : (6 * al ^ 2 + 1 - (1 + x) * hsDg x be al) / (7 * (1 + x) * al ^ 2) =
            1 / (1 + x) - K / 7 := by rw [hK, hDdef]; field_simp; ring
        rw [e]; exact hb7)
      have e7 : 7 / 12 * (1 - 1 / 7) ^ 2 * (1 + 2 * (1 / (1 + x) - 1 / 7 * K)) -
          2 * u * (1 / (1 + x) - 1 / 7 * K) - 3 * (1 / 7) + JA =
          JA - (2 * u - 6 / 7) * ((6 * al ^ 2 + 1 - (1 + x) * hsDg x be al) /
            (7 * (1 + x) * al ^ 2)) := by
        rw [hK, hDdef]; field_simp; ring
      have h2 : 0 ≤ 7 / 12 * (1 - q) ^ 2 * (τ - 2) * b₀ :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) h0.le
      have e3 : f b₀ = 7 / 12 * (1 - q) ^ 2 * (1 + 2 * (1 / (1 + x) - q * K)) -
          2 * u * (1 / (1 + x) - q * K) - 3 * q + JA + 7 / 12 * (1 - q) ^ 2 * (τ - 2) * b₀ := by
        simp only [hf]; rw [hb₀]; ring
      rw [e3]
      rw [hJA, hrAdef] at e7
      rw [hJA, hrAdef]
      linarith
  have hfneg : 0 < 2 * u - τ * (3 * q - JA) := by linarith
  have hcomb : (1 + τ * b₀) * f b = (b₀ - b) * (2 * u - τ * (3 * q - JA)) + (1 + τ * b) * f b₀ := by
    simp only [hf]; ring
  have hfb : 0 ≤ f b := by
    have h1 : 0 < 1 + τ * b₀ := by
      have := mul_le_mul_of_nonneg_left hbb₀ hτ0.le; linarith
    have : (1 + τ * b₀) * 0 ≤ (1 + τ * b₀) * f b := by
      rw [mul_zero, hcomb]
      exact add_nonneg (mul_nonneg (by linarith) hfneg.le) (mul_nonneg hB.le hfb₀)
    exact le_of_mul_le_mul_left this h1
  have : 2 * u * b + EL ≤ 2 * u * b + (3 * q - JA) := by linarith
  simp only [hf] at hfb
  linarith

end SmoothedOctagon

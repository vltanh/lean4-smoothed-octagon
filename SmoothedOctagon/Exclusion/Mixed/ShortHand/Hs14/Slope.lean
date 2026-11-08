module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Envelope

/-!
# Gates S1/S4 helpers: the lower norm endpoint of the two slope inequalities

At `u = 3/4` the slope inequalities `κH(2S - 1) < 3α²L(p)` reduce, with `p = α/(α + β₀ + k)`, to
explicit polynomial identities in `z = α - 1`, `y = x - α`, `k ≥ 0` with nonnegative coefficients
(`CORRECTED_CAP_SCALE` (5)-(7) for `κ = 4`, `β₀ = x`; `SHARP_LOW_RATIO_CORRECTED_CAP` (18)-(19) for
`κ = 7`, `β₀ = x(9x + 8α)/(9x + 8)`).

## Main API

* `hs14_bot_ccs`: `4H(2S - 1) < 3α²L(p)` at `β = x`, `u = 3/4`, `0 < p ≤ α/(α + x)`.
* `hs14_bot_sharp`: `7H(2S - 1) < 3α²L(p)` at `β = β₀`, `u = 3/4`, `0 < p ≤ α/(α + β₀)`.
-/

@[expose] public section

namespace SmoothedOctagon

private theorem hs14_ccs_id {z y k al x : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y) (hk : 0 ≤ k) (ha : al = 1 + z)
    (hx : x = 1 + z + y) :
    4 * (1 + x) * al * (al + x + k) * (3 * al ^ 2 * hsLp x x al (3 / 4) (al / (al + x + k)) -
      4 * ((1 + x) * (m2U (1 / (1 + x)) - 3 / 4)) * (2 * (1 + x) - 1)) =
    12 * (1 + x) * al ^ 2 * k ^ 2 + al * (3 * z ^ 4 + 6 * z ^ 3 * y + 3 * z ^ 2 * y ^ 2 + 28 * z ^ 3 + 78 * z ^ 2 * y + 78 * z * y ^ 2 + 28 * y ^ 3 + 72 * z ^ 2 + 192 * z * y + 108 * y ^ 2 + 48 * z + 96 * y) * k +
    (8 * z ^ 3 + 72 * y ^ 2 + (3 * z ^ 6 + 15 * z ^ 5 * y + 27 * z ^ 4 * y ^ 2 + 21 * z ^ 3 * y ^ 3 + 6 * z ^ 2 * y ^ 4 + 11 * z ^ 5 + 88 * z ^ 4 * y + 222 * z ^ 3 * y ^ 2 + 257 * z ^ 2 * y ^ 3 + 148 * z * y ^ 4 + 36 * y ^ 5 + 16 * z ^ 4 + 208 * z ^ 3 * y + 516 * z ^ 2 * y ^ 2 + 466 * z * y ^ 3 + 148 * y ^ 4 + 180 * z ^ 2 * y + 372 * z * y ^ 2 + 188 * y ^ 3 + 48 * z * y)) := by
  subst ha hx
  have h1 : (1 + z) ≠ 0 := by positivity
  have h2 : (1 + z + (1 + z + y) + k) ≠ 0 := by positivity
  have h3 : (1 + (1 + z + y)) ≠ 0 := by positivity
  unfold hsLp hsA2 hsA3 hsE0 hsDg m2U
  field_simp
  ring

/-- **The lower norm endpoint of the slope inequality at `β = x`** (`CORRECTED_CAP_SCALE` (5)-(7)). -/
theorem hs14_bot_ccs {x al p : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x) (hp : 0 < p)
    (hpr : p ≤ al / (al + x)) :
    4 * ((1 + x) * (m2U (1 / (1 + x)) - 3 / 4)) * (2 * (1 + x) - 1) <
      3 * al ^ 2 * hsLp x x al (3 / 4) p := by
  have hal0 : 0 < al := by linarith
  set k := al / p - al - x with hkdef
  have hk : 0 ≤ k := by
    have : al + x ≤ al / p := by
      rw [le_div_iff₀ hp]; rw [le_div_iff₀ (by linarith)] at hpr; linarith
    linarith
  have hpk : p = al / (al + x + k) := by
    have : al + x + k = al / p := by rw [hkdef]; ring
    rw [this]; field_simp
  have hz : 0 ≤ al - 1 := by linarith
  have hy : 0 ≤ x - al := by linarith
  have hid := hs14_ccs_id (z := al - 1) (y := x - al) (al := al) (x := x) hz hy hk (by ring) (by ring)
  rw [← hpk] at hid
  have hQ : 0 < 8 * (al - 1) ^ 3 + 72 * (x - al) ^ 2 := by
    rcases eq_or_lt_of_le hy with h | h
    · have : 0 < al - 1 := by linarith
      positivity
    · positivity
  have hpos : 0 < 4 * (1 + x) * al * (al + x + k) := by positivity
  have hR : 0 < 12 * (1 + x) * al ^ 2 * k ^ 2 + al * (3 * (al - 1) ^ 4 + 6 * (al - 1) ^ 3 * (x - al) + 3 * (al - 1) ^ 2 * (x - al) ^ 2 + 28 * (al - 1) ^ 3 + 78 * (al - 1) ^ 2 * (x - al) + 78 * (al - 1) * (x - al) ^ 2 + 28 * (x - al) ^ 3 + 72 * (al - 1) ^ 2 + 192 * (al - 1) * (x - al) + 108 * (x - al) ^ 2 + 48 * (al - 1) + 96 * (x - al)) * k +
    (8 * (al - 1) ^ 3 + 72 * (x - al) ^ 2 + (3 * (al - 1) ^ 6 + 15 * (al - 1) ^ 5 * (x - al) + 27 * (al - 1) ^ 4 * (x - al) ^ 2 + 21 * (al - 1) ^ 3 * (x - al) ^ 3 + 6 * (al - 1) ^ 2 * (x - al) ^ 4 + 11 * (al - 1) ^ 5 + 88 * (al - 1) ^ 4 * (x - al) + 222 * (al - 1) ^ 3 * (x - al) ^ 2 + 257 * (al - 1) ^ 2 * (x - al) ^ 3 + 148 * (al - 1) * (x - al) ^ 4 + 36 * (x - al) ^ 5 + 16 * (al - 1) ^ 4 + 208 * (al - 1) ^ 3 * (x - al) + 516 * (al - 1) ^ 2 * (x - al) ^ 2 + 466 * (al - 1) * (x - al) ^ 3 + 148 * (x - al) ^ 4 + 180 * (al - 1) ^ 2 * (x - al) + 372 * (al - 1) * (x - al) ^ 2 + 188 * (x - al) ^ 3 + 48 * (al - 1) * (x - al))) := by
    have := hQ
    positivity
  rw [← hid] at hR
  have := pos_of_mul_pos_right hR hpos.le
  linarith

private theorem hs14_sharp_id {z y k al x : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y) (hk : 0 ≤ k) (ha : al = 1 + z)
    (hx : x = 1 + z + y) :
    4 * (1 + x) * al * (al * (9 * x + 8) + x * (9 * x + 8 * al) + k * (9 * x + 8)) * (9 * x + 8) *
      (3 * al ^ 2 * hsLp x (x * (9 * x + 8 * al) / (9 * x + 8)) al (3 / 4)
        (al * (9 * x + 8) / (al * (9 * x + 8) + x * (9 * x + 8 * al) + k * (9 * x + 8))) -
      7 * ((1 + x) * (m2U (1 / (1 + x)) - 3 / 4)) * (2 * (1 + x) - 1)) =
    12 * (1 + x) * al ^ 2 * (9 * x + 8) ^ 2 * k ^ 2 + (243 * z ^ 7 + 972 * z ^ 6 * y + 1458 * z ^ 5 * y ^ 2 + 972 * z ^ 4 * y ^ 3 + 243 * z ^ 3 * y ^ 4 + 4671 * z ^ 6 + 19926 * z ^ 5 * y + 33534 * z ^ 4 * y ^ 2 + 27756 * z ^ 3 * y ^ 3 + 11259 * z ^ 2 * y ^ 4 + 1782 * z * y ^ 5 + 27306 * z ^ 5 + 104832 * z ^ 4 * y + 149949 * z ^ 3 * y ^ 2 + 96408 * z ^ 2 * y ^ 3 + 25767 * z * y ^ 4 + 1782 * y ^ 5 + 74098 * z ^ 4 + 241308 * z ^ 3 * y + 266511 * z ^ 2 * y ^ 2 + 114052 * z * y ^ 3 + 14751 * y ^ 4 + 103891 * z ^ 3 + 272820 * z ^ 2 * y + 206625 * z * y ^ 2 + 44428 * y ^ 3 + 73071 * z ^ 2 + 145134 * z * y + 57987 * y ^ 2 + 20400 * z + 27744 * y) * k +
    (2862 * z ^ 2 + 16524 * z * y + 15606 * y ^ 2 + (459 * z ^ 8 + 2997 * z ^ 7 * y + 7884 * z ^ 6 * y ^ 2 + 10746 * z ^ 5 * y ^ 3 + 8019 * z ^ 4 * y ^ 4 + 3105 * z ^ 3 * y ^ 5 + 486 * z ^ 2 * y ^ 6 + 4029 * z ^ 7 + 30336 * z ^ 6 * y + 90999 * z ^ 5 * y ^ 2 + 145041 * z ^ 4 * y ^ 3 + 134970 * z ^ 3 * y ^ 4 + 74223 * z ^ 2 * y ^ 5 + 22518 * z * y ^ 6 + 2916 * y ^ 7 + 14791 * z ^ 6 + 119770 * z ^ 5 * y + 346533 * z ^ 4 * y ^ 2 + 491947 * z ^ 3 * y ^ 3 + 371938 * z ^ 2 * y ^ 4 + 144063 * z * y ^ 5 + 22518 * y ^ 6 + 28339 * z ^ 5 + 231539 * z ^ 4 * y + 587286 * z ^ 3 * y ^ 2 + 659095 * z ^ 2 * y ^ 3 + 342392 * z * y ^ 4 + 67383 * y ^ 5 + 29180 * z ^ 4 + 227323 * z ^ 3 * y + 466764 * z ^ 2 * y ^ 2 + 363497 * z * y ^ 3 + 96514 * y ^ 4 + 14924 * z ^ 3 + 104547 * z ^ 2 * y + 157974 * z * y ^ 2 + 64787 * y ^ 3)) := by
  subst ha hx
  have h1 : (1 + z) ≠ 0 := by positivity
  have h3 : (1 + (1 + z + y)) ≠ 0 := by positivity
  have h4 : (9 * (1 + z + y) + 8) ≠ 0 := by positivity
  have h2 : ((1 + z) * (9 * (1 + z + y) + 8) + (1 + z + y) * (9 * (1 + z + y) + 8 * (1 + z)) +
    k * (9 * (1 + z + y) + 8)) ≠ 0 := by positivity
  unfold hsLp hsA2 hsA3 hsE0 hsDg m2U
  field_simp
  ring

/-- **The lower norm endpoint of the sharper slope at `β₀ = x(9x + 8α)/(9x + 8)`**
(`SHARP_LOW_RATIO_CORRECTED_CAP` (18)-(19)). -/
theorem hs14_bot_sharp {x al p : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x) (hp : 0 < p)
    (hpr : p ≤ al / (al + x * (9 * x + 8 * al) / (9 * x + 8))) :
    7 * ((1 + x) * (m2U (1 / (1 + x)) - 3 / 4)) * (2 * (1 + x) - 1) <
      3 * al ^ 2 * hsLp x (x * (9 * x + 8 * al) / (9 * x + 8)) al (3 / 4) p := by
  have hal0 : 0 < al := by linarith
  have hM : 0 < 9 * x + 8 := by linarith
  have hb0 : 0 < x * (9 * x + 8 * al) / (9 * x + 8) := by positivity
  set k := al / p - al - x * (9 * x + 8 * al) / (9 * x + 8) with hkdef
  have hk : 0 ≤ k := by
    have : al + x * (9 * x + 8 * al) / (9 * x + 8) ≤ al / p := by
      rw [le_div_iff₀ hp]; rw [le_div_iff₀ (by linarith)] at hpr; linarith
    linarith
  have hpk : p = al * (9 * x + 8) / (al * (9 * x + 8) + x * (9 * x + 8 * al) + k * (9 * x + 8)) := by
    have : al * (9 * x + 8) + x * (9 * x + 8 * al) + k * (9 * x + 8) = (al / p) * (9 * x + 8) := by
      rw [hkdef]; field_simp; ring
    rw [this]; field_simp
  have hz : 0 ≤ al - 1 := by linarith
  have hy : 0 ≤ x - al := by linarith
  have hid := hs14_sharp_id (z := al - 1) (y := x - al) (al := al) (x := x) hz hy hk (by ring)
    (by ring)
  rw [← hpk] at hid
  have hQ : 0 < 2862 * (al - 1) ^ 2 + 16524 * (al - 1) * (x - al) + 15606 * (x - al) ^ 2 := by
    rcases eq_or_lt_of_le hy with h | h
    · have : 0 < al - 1 := by linarith
      positivity
    · positivity
  have hpos : 0 < 4 * (1 + x) * al * (al * (9 * x + 8) + x * (9 * x + 8 * al) + k * (9 * x + 8)) *
      (9 * x + 8) := by positivity
  have hR : 0 < 12 * (1 + x) * al ^ 2 * (9 * x + 8) ^ 2 * k ^ 2 + (243 * (al - 1) ^ 7 + 972 * (al - 1) ^ 6 * (x - al) + 1458 * (al - 1) ^ 5 * (x - al) ^ 2 + 972 * (al - 1) ^ 4 * (x - al) ^ 3 + 243 * (al - 1) ^ 3 * (x - al) ^ 4 + 4671 * (al - 1) ^ 6 + 19926 * (al - 1) ^ 5 * (x - al) + 33534 * (al - 1) ^ 4 * (x - al) ^ 2 + 27756 * (al - 1) ^ 3 * (x - al) ^ 3 + 11259 * (al - 1) ^ 2 * (x - al) ^ 4 + 1782 * (al - 1) * (x - al) ^ 5 + 27306 * (al - 1) ^ 5 + 104832 * (al - 1) ^ 4 * (x - al) + 149949 * (al - 1) ^ 3 * (x - al) ^ 2 + 96408 * (al - 1) ^ 2 * (x - al) ^ 3 + 25767 * (al - 1) * (x - al) ^ 4 + 1782 * (x - al) ^ 5 + 74098 * (al - 1) ^ 4 + 241308 * (al - 1) ^ 3 * (x - al) + 266511 * (al - 1) ^ 2 * (x - al) ^ 2 + 114052 * (al - 1) * (x - al) ^ 3 + 14751 * (x - al) ^ 4 + 103891 * (al - 1) ^ 3 + 272820 * (al - 1) ^ 2 * (x - al) + 206625 * (al - 1) * (x - al) ^ 2 + 44428 * (x - al) ^ 3 + 73071 * (al - 1) ^ 2 + 145134 * (al - 1) * (x - al) + 57987 * (x - al) ^ 2 + 20400 * (al - 1) + 27744 * (x - al)) * k +
    (2862 * (al - 1) ^ 2 + 16524 * (al - 1) * (x - al) + 15606 * (x - al) ^ 2 + (459 * (al - 1) ^ 8 + 2997 * (al - 1) ^ 7 * (x - al) + 7884 * (al - 1) ^ 6 * (x - al) ^ 2 + 10746 * (al - 1) ^ 5 * (x - al) ^ 3 + 8019 * (al - 1) ^ 4 * (x - al) ^ 4 + 3105 * (al - 1) ^ 3 * (x - al) ^ 5 + 486 * (al - 1) ^ 2 * (x - al) ^ 6 + 4029 * (al - 1) ^ 7 + 30336 * (al - 1) ^ 6 * (x - al) + 90999 * (al - 1) ^ 5 * (x - al) ^ 2 + 145041 * (al - 1) ^ 4 * (x - al) ^ 3 + 134970 * (al - 1) ^ 3 * (x - al) ^ 4 + 74223 * (al - 1) ^ 2 * (x - al) ^ 5 + 22518 * (al - 1) * (x - al) ^ 6 + 2916 * (x - al) ^ 7 + 14791 * (al - 1) ^ 6 + 119770 * (al - 1) ^ 5 * (x - al) + 346533 * (al - 1) ^ 4 * (x - al) ^ 2 + 491947 * (al - 1) ^ 3 * (x - al) ^ 3 + 371938 * (al - 1) ^ 2 * (x - al) ^ 4 + 144063 * (al - 1) * (x - al) ^ 5 + 22518 * (x - al) ^ 6 + 28339 * (al - 1) ^ 5 + 231539 * (al - 1) ^ 4 * (x - al) + 587286 * (al - 1) ^ 3 * (x - al) ^ 2 + 659095 * (al - 1) ^ 2 * (x - al) ^ 3 + 342392 * (al - 1) * (x - al) ^ 4 + 67383 * (x - al) ^ 5 + 29180 * (al - 1) ^ 4 + 227323 * (al - 1) ^ 3 * (x - al) + 466764 * (al - 1) ^ 2 * (x - al) ^ 2 + 363497 * (al - 1) * (x - al) ^ 3 + 96514 * (x - al) ^ 4 + 14924 * (al - 1) ^ 3 + 104547 * (al - 1) ^ 2 * (x - al) + 157974 * (al - 1) * (x - al) ^ 2 + 64787 * (x - al) ^ 3)) := by
    have := hQ
    positivity
  rw [← hid] at hR
  have := pos_of_mul_pos_right hR hpos.le
  linarith

end SmoothedOctagon

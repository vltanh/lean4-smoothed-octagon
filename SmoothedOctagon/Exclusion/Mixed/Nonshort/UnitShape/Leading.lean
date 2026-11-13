module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Cubic

/-!
# The leading coefficient on the unit face

The order gap is `r = 1 - 2t - x`. Its two upper bounds,
`r ≤ x(1+x)` and `r ≤ 1-x`, control the leading coefficient.
For small `x`, a direct bound suffices. For larger `x`, the quadratic
part and the full cubic have positive endpoint values. Interpolation
then proves positivity throughout the interval.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

def lead0 {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 8 + 21 * x ^ 7 + 67 * x ^ 6 + 98 * x ^ 5 + 36 * x ^ 4
    - 47 * x ^ 3 - 24 * x ^ 2 + 42 * x + 36

def lead1 {R : Type*} [CommRing R] (x : R) : R :=
  9 * x ^ 8 + 62 * x ^ 7 + 160 * x ^ 6 + 254 * x ^ 5 + 320 * x ^ 4
    + 292 * x ^ 3 + 133 * x ^ 2 - 42 * x - 66

def lead2 {R : Type*} [CommRing R] (x : R) : R :=
  9 * x ^ 8 + 63 * x ^ 7 + 123 * x ^ 6 + 74 * x ^ 5 - 24 * x ^ 4
    - 69 * x ^ 3 - 88 * x ^ 2 - 42 * x + 12

def lead3 {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 4 - 2 * x ^ 3 - 7 * x ^ 2 - 2 * x + 3

def leading {R : Type*} [CommRing R] (x r : R) : R :=
  x * ((1 + x) ^ 2 * lead0 x + (1 + x) * lead1 x * r
    + lead2 x * r ^ 2 + (1 + x) * (x ^ 2 + 6 * x + 6) * lead3 x * r ^ 3)

private theorem power_charge {x : ℝ} (hx : 0 ≤ x) {b : ℝ} (hb : x ≤ b) (n : ℕ) :
    x ^ (n + 2) ≤ x ^ 2 * b ^ n := by
  have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hb n) (sq_nonneg x)
  simpa [pow_add, mul_comm] using this

private theorem lead0_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 < lead0 x := by
  have e : lead0 x = 7 + (1 - x) * (47 * x ^ 2 + 71 * x + 29)
      + x ^ 4 * (36 + 98 * x + 67 * x ^ 2 + 21 * x ^ 3 + 3 * x ^ 4) := by
    unfold lead0; ring
  rw [e]
  have : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

private theorem lead3_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 0 ≤ lead3 x := by
  have e : lead3 x = 3 * x ^ 4 + (1 - 2 * x) * (1 + x) * (x + 3) := by
    unfold lead3; ring
  rw [e]
  have : 0 ≤ 1 - 2 * x := by linarith only [hx1]
  positivity

private theorem quadratic_pos {a b c r R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) (he : 0 < a + b * R + c * R ^ 2)
    (hbc : 0 ≤ b ∨ c ≤ 0) : 0 < a + b * r + c * r ^ 2 := by
  by_cases hr0 : r = 0
  · subst r; simpa using ha
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hgap : 0 ≤ R - r := sub_nonneg.mpr hrR
  rcases hbc with hb | hc
  · have hdiff : 0 ≤ R ^ 2 - r ^ 2 := by nlinarith only [hr, hrR, hR]
    have h1 := mul_nonneg hdiff ha.le
    have h2 := mul_pos (sq_pos_of_pos hrp) he
    have h3 : 0 ≤ b * R * r * (R - r) := by positivity
    have e : R ^ 2 * (a + b * r + c * r ^ 2) =
        (R ^ 2 - r ^ 2) * a + r ^ 2 * (a + b * R + c * R ^ 2) + b * R * r * (R - r) := by ring
    exact pos_of_mul_pos_right (by linarith only [e, h1, h2, h3]) (sq_nonneg R)
  · have h1 := mul_nonneg hgap ha.le
    have h2 := mul_pos hrp he
    have hc' : 0 ≤ -c := neg_nonneg.mpr hc
    have h3 : 0 ≤ -c * R * r * (R - r) := by positivity
    have e : R * (a + b * r + c * r ^ 2) =
        (R - r) * a + r * (a + b * R + c * R ^ 2) - c * R * r * (R - r) := by ring
    exact pos_of_mul_pos_right (by linarith only [e, h1, h2, h3]) hR.le

private theorem cubic_pos {a b c e r R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hq : 0 < a + b * R + c * R ^ 2)
    (hf : 0 < a + b * R + c * R ^ 2 + e * R ^ 3)
    (hbc : 0 ≤ b ∨ (c ≤ 0 ∧ 0 ≤ e)) :
    0 < a + b * r + c * r ^ 2 + e * r ^ 3 := by
  by_cases he : 0 ≤ e
  · have hq' := quadratic_pos ha hR hr hrR hq (hbc.imp id And.left)
    have htail : 0 ≤ e * r ^ 3 := by positivity
    linarith only [hq', htail]
  have he : e < 0 := lt_of_not_ge he
  have he' : 0 ≤ -e := neg_nonneg.mpr he.le
  have hb : 0 ≤ b := hbc.resolve_right (fun h => (not_le.mpr he) h.2)
  by_cases hr0 : r = 0
  · subst r; simpa using ha
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hgap : 0 ≤ R - r := sub_nonneg.mpr hrR
  have hdiff : 0 ≤ R ^ 2 - r ^ 2 := by nlinarith only [hr, hrR, hR]
  have h1 := mul_nonneg hdiff ha.le
  have h2 := mul_pos (sq_pos_of_pos hrp) hf
  have h3 : 0 ≤ b * R * r * (R - r) := by positivity
  have h4 : 0 ≤ -e * R ^ 2 * r ^ 2 * (R - r) := by positivity
  have hid : R ^ 2 * (a + b * r + c * r ^ 2 + e * r ^ 3) =
      (R ^ 2 - r ^ 2) * a + r ^ 2 * (a + b * R + c * R ^ 2 + e * R ^ 3)
      + b * R * r * (R - r) - e * R ^ 2 * r ^ 2 * (R - r) := by ring
  exact pos_of_mul_pos_right (by linarith only [hid, h1, h2, h3, h4]) (sq_nonneg R)

/-- The order and switching bounds suffice for positivity of the leading coefficient. -/
theorem leading_pos {x r : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hr : 0 ≤ r) (hrx : r ≤ x * (1 + x)) (hr1 : r ≤ 1 - x) : 0 < leading x r := by
  have hx0 := hx.le
  have hW : 0 < 1 + x := by linarith only [hx]
  have hD : 0 < x ^ 2 + 6 * x + 6 := by positivity
  by_cases hsmall : x ≤ 1 / 3
  · have h2 : x ^ 2 ≤ x / 3 := by nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hsmall)]
    have h3 : x ^ 3 ≤ x / 9 := by
      nlinarith only [power_charge hx0 hsmall 1, h2]
    have ha : 36 ≤ lead0 x := by
      have hp : 0 ≤ 3 * x ^ 8 + 21 * x ^ 7 + 67 * x ^ 6 + 98 * x ^ 5 + 36 * x ^ 4 := by positivity
      unfold lead0
      linarith only [hp, h2, h3, hx0]
    have hb : -80 ≤ lead1 x := by
      have hp : 0 ≤ 9 * x ^ 8 + 62 * x ^ 7 + 160 * x ^ 6 + 254 * x ^ 5
          + 320 * x ^ 4 + 292 * x ^ 3 + 133 * x ^ 2 := by positivity
      unfold lead1
      linarith only [hp, hsmall]
    have hc : -16 ≤ lead2 x := by
      have hp : 0 ≤ 9 * x ^ 8 + 63 * x ^ 7 + 123 * x ^ 6 + 74 * x ^ 5 := by positivity
      have h4 := power_charge hx0 hsmall 2
      unfold lead2
      nlinarith only [hp, hsmall, h2, h3, h4]
    have he := lead3_nonneg hx0 (show x ≤ 1 / 2 by linarith only [hsmall])
    have hr2 : r ^ 2 ≤ x ^ 2 * (1 + x) ^ 2 := by nlinarith only [hrx, hr, hx, hW]
    have hb' := mul_le_mul_of_nonneg_left hb (mul_nonneg hW.le hr)
    have hc' := mul_le_mul_of_nonneg_left hc (sq_nonneg r)
    have ha' := mul_le_mul_of_nonneg_left ha (sq_nonneg (1 + x))
    have ht : 0 ≤ (1 + x) * (x ^ 2 + 6 * x + 6) * lead3 x * r ^ 3 := by positivity
    have hshort : 7 ≤ 36 - 80 * x - 16 * x ^ 2 := by nlinarith only [hsmall, h2]
    have hh := mul_le_mul_of_nonneg_left hshort (sq_nonneg (1 + x))
    have hbcap := mul_le_mul_of_nonneg_left hrx (show 0 ≤ 80 * (1 + x) by positivity)
    have hcore : 0 < (1 + x) ^ 2 * lead0 x + (1 + x) * lead1 x * r + lead2 x * r ^ 2
        + (1 + x) * (x ^ 2 + 6 * x + 6) * lead3 x * r ^ 3 := by
      nlinarith only [ha', hb', hc', ht, hh, hbcap, hr2, sq_pos_of_pos hW]
    exact mul_pos hx hcore
  have hxthird : 1 / 3 ≤ x := le_of_lt (lt_of_not_ge hsmall)
  have hR : 0 < 1 - x := sub_pos.mpr hx1
  have ha : 0 < (1 + x) ^ 2 * lead0 x := mul_pos (sq_pos_of_pos hW) (lead0_pos hx0 hx1.le)
  have hQ : 0 < (1 + x) ^ 2 * lead0 x + (1 + x) * lead1 x * (1 - x)
      + lead2 x * (1 - x) ^ 2 := by
    have e : (1 + x) ^ 2 * lead0 x + (1 + x) * lead1 x * (1 - x)
        + lead2 x * (1 - x) ^ 2 =
        -18 + 6 * x + 303 * x ^ 2 + 346 * x ^ 3 + 131 * x ^ 4 + 138 * x ^ 5
        + x ^ 6 * (9 + (1 - x) * (81 + 33 * x)) + 10 * x ^ 9 + 3 * x ^ 10 := by
      unfold lead0 lead1 lead2; ring
    have hp : 0 ≤ 6 * x + 346 * x ^ 3 + 131 * x ^ 4 + 138 * x ^ 5
        + x ^ 6 * (9 + (1 - x) * (81 + 33 * x)) + 10 * x ^ 9 + 3 * x ^ 10 := by positivity
    rw [e]
    nlinarith only [hp, hxthird]
  have hF : 0 < (1 + x) ^ 2 * lead0 x + (1 + x) * lead1 x * (1 - x)
      + lead2 x * (1 - x) ^ 2
      + (1 + x) * (x ^ 2 + 6 * x + 6) * lead3 x * (1 - x) ^ 3 := by
    have e : (1 + x) ^ 2 * lead0 x + (1 + x) * lead1 x * (1 - x)
        + lead2 x * (1 - x) ^ 2
        + (1 + x) * (x ^ 2 + 6 * x + 6) * lead3 x * (1 - x) ^ 3 =
        4 * x * (12 * x ^ 4 + 59 * x ^ 3 + 107 * x ^ 2 + 60 * x - 6) := by
      unfold lead0 lead1 lead2 lead3; ring
    rw [e]
    apply mul_pos (by positivity)
    have hp : 0 ≤ 12 * x ^ 4 + 59 * x ^ 3 + 107 * x ^ 2 := by positivity
    linarith only [hp, hxthird]
  have hbc : 0 ≤ (1 + x) * lead1 x ∨
      (lead2 x ≤ 0 ∧ 0 ≤ (1 + x) * (x ^ 2 + 6 * x + 6) * lead3 x) := by
    by_cases hxhalf : 1 / 2 ≤ x
    · left
      have h2 : x / 2 ≤ x ^ 2 := by nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hxhalf)]
      have h3 : x / 4 ≤ x ^ 3 := by
        have := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxhalf)
        nlinarith only [this, h2]
      have h4 : x / 8 ≤ x ^ 4 := by
        have := mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr hxhalf)
        nlinarith only [this, h3]
      have hp : 0 ≤ 9 * x ^ 8 + 62 * x ^ 7 + 160 * x ^ 6 + 254 * x ^ 5 := by positivity
      have hb : 0 ≤ lead1 x := by
        unfold lead1
        linarith only [hp, h2, h3, h4, hxhalf]
      exact mul_nonneg hW.le hb
    · right
      have hxhalf : x ≤ 1 / 2 := le_of_lt (lt_of_not_ge hxhalf)
      have h5 := power_charge hx0 hxhalf 3
      have h6 := power_charge hx0 hxhalf 4
      have h7 := power_charge hx0 hxhalf 5
      have h8 := power_charge hx0 hxhalf 6
      have hc : lead2 x ≤ 0 := by
        have hp : 0 ≤ 24 * x ^ 4 + 69 * x ^ 3 := by positivity
        unfold lead2
        linarith only [h5, h6, h7, h8, hp, hxthird, sq_nonneg x]
      exact ⟨hc, mul_nonneg (mul_nonneg hW.le hD.le) (lead3_nonneg hx0 hxhalf)⟩
  exact mul_pos hx (cubic_pos ha hR hr hr1 hQ hF hbc)

end SmoothedOctagon.UnitShape

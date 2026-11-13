module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Bounds

/-!
# The slope at the crossing point

The combination `3 value - cross` increases with the order gap.
The lower-boundary values are positive by monotonicity on the order
edge and concavity on the cap edge.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

private def slope0 {R : Type*} [CommRing R] (x : R) : R :=
  12 * x ^ 7 + 111 * x ^ 6 + 469 * x ^ 5 + 1067 * x ^ 4 + 1329 * x ^ 3
    + 814 * x ^ 2 + 96 * x - 96

private def slope1 {R : Type*} [CommRing R] (x : R) : R :=
  36 * x ^ 9 + 329 * x ^ 8 + 1243 * x ^ 7 + 2723 * x ^ 6 + 4301 * x ^ 5
    + 5620 * x ^ 4 + 5752 * x ^ 3 + 3648 * x ^ 2 + 912 * x - 72

private def slope2 {R : Type*} [CommRing R] (x : R) : R :=
  36 * x ^ 9 + 333 * x ^ 8 + 1131 * x ^ 7 + 1901 * x ^ 6 + 1671 * x ^ 5
    + 510 * x ^ 4 - 604 * x ^ 3 - 924 * x ^ 2 - 492 * x - 72

private def slope3 {R : Type*} [CommRing R] (x : R) : R :=
  12 * x ^ 5 + 79 * x ^ 4 + 100 * x ^ 3 - 72 * x ^ 2 - 168 * x - 60

private theorem slope_eq (x r : ℝ) :
    slope x r = x ^ 2 * (1 + x) ^ 2 * slope0 x + (1 + x) * slope1 x * r
      + slope2 x * r ^ 2 + x * (1 + x) ^ 2 * slope3 x * r ^ 3 := by
  unfold slope value cross value0 value1 value2 value3 cross0 cross1 cross2 cross3
    slope0 slope1 slope2 slope3
  ring

private theorem slope_mono {x u v : ℝ} (hx : 1 / 10 ≤ x) (hu : 0 ≤ u) (huv : u ≤ v)
    (hvx : v ≤ x * (1 + x)) (hv1 : v ≤ 1 - x) : slope x u ≤ slope x v := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hv0 : 0 ≤ v := hu.trans huv
  have hW : 0 ≤ 1 + x := by positivity
  have h1 : -72 + 840 * x + 4560 * x ^ 2 + 9400 * x ^ 3 + 11372 * x ^ 4
      + 5620 * x ^ 5 ≤ (1 + x) * slope1 x := by
    have hp : 0 ≤ 36 * x ^ 10 + 365 * x ^ 9 + 1572 * x ^ 8 + 3966 * x ^ 7
        + 7024 * x ^ 6 + 4301 * x ^ 5 := by positivity
    unfold slope1
    nlinarith only [hp]
  have h2 : -(72 + 492 * x + 924 * x ^ 2 + 604 * x ^ 3) ≤ slope2 x := by
    have hp : 0 ≤ 36 * x ^ 9 + 333 * x ^ 8 + 1131 * x ^ 7 + 1901 * x ^ 6
        + 1671 * x ^ 5 + 510 * x ^ 4 := by positivity
    unfold slope2
    linarith only [hp]
  have h3 : -(60 + 168 * x + 72 * x ^ 2) ≤ slope3 x := by
    have hp : 0 ≤ 12 * x ^ 5 + 79 * x ^ 4 + 100 * x ^ 3 := by positivity
    unfold slope3
    linarith only [hp]
  have huW : 0 ≤ (1 + x) * u := by positivity
  have hvW : 0 ≤ (1 + x) * v := by positivity
  have hvW1 : (1 + x) * v ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hv1 hW
    nlinarith only [this, sq_nonneg x]
  have huW1 : (1 + x) * u ≤ 1 :=
    (mul_le_mul_of_nonneg_left huv hW).trans hvW1
  have hsq1 : ((1 + x) * u) ^ 2 ≤ 1 := by nlinarith only [huW, huW1]
  have hsq2 : ((1 + x) * v) ^ 2 ≤ 1 := by nlinarith only [hvW, hvW1]
  have hmix : ((1 + x) * u) * ((1 + x) * v) ≤ 1 :=
    (mul_le_mul huW1 hvW1 hvW (by norm_num)).trans_eq (by norm_num)
  have htail : (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) ≤ 3 := by
    nlinarith only [hsq1, hsq2, hmix]
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ u + v by positivity)
  have h3' := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ x * (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) by positivity)
  have hcap2 := mul_le_mul_of_nonneg_left (show u + v ≤ 2 * x * (1 + x) by linarith only [huv, hvx])
    (show 0 ≤ 72 + 492 * x + 924 * x ^ 2 + 604 * x ^ 3 by positivity)
  have hcap3 := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ x * (60 + 168 * x + 72 * x ^ 2) by positivity)
  have hlow : 0 ≤ -72 + 516 * x + 2928 * x ^ 2 + 6352 * x ^ 3 + 8316 * x ^ 4 + 4412 * x ^ 5 := by
    have hp : 0 ≤ 6352 * x ^ 3 + 8316 * x ^ 4 + 4412 * x ^ 5 := by positivity
    nlinarith only [hx, hp]
  have hs : 0 ≤ (1 + x) * slope1 x + (u + v) * slope2 x
      + x * (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) * slope3 x := by
    nlinarith only [h1, h2', h3', hcap2, hcap3, hlow]
  have he : slope x v - slope x u = (v - u) * ((1 + x) * slope1 x
      + (u + v) * slope2 x + x * (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) * slope3 x) := by
    rw [slope_eq, slope_eq]
    ring
  have hp := mul_nonneg (sub_nonneg.mpr huv) hs
  linarith only [he, hp]

private def capSlope {R : Type*} [CommRing R] (x : R) : R :=
  -384 * x ^ 9 - 7956 * x ^ 8 - 63429 * x ^ 7 - 227730 * x ^ 6 - 423253 * x ^ 5
    - 403756 * x ^ 4 - 151812 * x ^ 3 + 20928 * x ^ 2 + 18324 * x - 1440

private theorem slope_boundary {x : ℝ} (hx : 1 / 10 ≤ x) :
    0 < slope x (max 0 (1 / 4 - x)) := by
  have hx0 : 0 < x := by linarith only [hx]
  by_cases hq : 1 / 4 ≤ x
  · rw [max_eq_left (by linarith only [hq]), slope_eq]
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), add_zero]
    have hm : slope0 (1 / 4 : ℝ) ≤ slope0 x := by unfold slope0; gcongr
    have hp : 0 < slope0 x := by
      have hc : 0 < slope0 (1 / 4 : ℝ) := by norm_num [slope0]
      linarith only [hm, hc]
    positivity
  · have hxq : x ≤ 1 / 4 := le_of_lt (lt_of_not_ge hq)
    rw [max_eq_right (by linarith only [hxq])]
    let p : Polynomial ℝ := capSlope Polynomial.X
    have hc : ∀ z, 1 / 10 ≤ z → z ≤ 1 / 4 → p.derivative.derivative.eval z ≤ 0 := by
      intro z hz _
      have hz0 : 0 ≤ z := by linarith only [hz]
      have hn : 0 ≤ 27648 * z ^ 7 + 445536 * z ^ 6 + 2664018 * z ^ 5
          + 6831900 * z ^ 4 + 8465060 * z ^ 3 + 4845072 * z ^ 2 := by positivity
      norm_num [p, capSlope, Polynomial.derivative_mul, Polynomial.derivative_pow]
      linarith only [hn, hz]
    have hfloor := polynomial_floor (p := p) (m := 1) hx hxq hc
      (by norm_num [p, capSlope]) (by norm_num [p, capSlope])
    have he : 64 * slope x (1 / 4 - x) = p.eval x := by
      simp only [p]
      simp only [capSlope, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X]
      unfold slope value cross value0 value1 value2 value3 cross0 cross1 cross2 cross3
      ring
    linarith only [hfloor, he]

theorem slope_pos {x r : ℝ} (hx : 1 / 10 ≤ x) (hr : 0 ≤ r)
    (hr0 : 1 / 4 - x ≤ r) (hrx : r ≤ x * (1 + x)) (hr1 : r ≤ 1 - x) : 0 < slope x r := by
  have hp := slope_boundary hx
  have hm := slope_mono hx (le_max_left _ _) (max_le hr hr0) hrx hr1
  exact hp.trans_le hm

end SmoothedOctagon.UnitShape

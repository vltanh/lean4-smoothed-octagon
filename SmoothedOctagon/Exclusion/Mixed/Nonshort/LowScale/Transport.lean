module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Unit
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Transport from the unit face to the increasing-shape face

The two faces meet at `t=1/4`. Along `k=2t+1/2`, the incoming
coefficients, both margins, and the cubic coefficient increase in `t`.
For `1/4≤t≤3/8` and `1/2≤x≤1`, this follows from the elementary
bounds `0≤t-1/4≤1/8` and `0≤2x-1≤1` on their derivatives.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

def highQuadraticMargin {R : Type*} [CommRing R] (t x : R) : R :=
  high2 t x + 54 * high0 t x

def highCubicMargin {R : Type*} [CommRing R] (t x : R) : R :=
  high3 t x + 4 * high2 t x

private theorem transport {f d : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (d t) t)
    (hn : ∀ t, 1 / 4 ≤ t → t ≤ 3 / 8 → 0 ≤ d t)
    {t : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8) : f (1 / 4) ≤ f t := by
  have hm : MonotoneOn f (Set.Icc (1 / 4) (3 / 8)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    exact hn s hs.1.le hs.2.le
  exact hm ⟨le_rfl, by norm_num⟩ ⟨ht, ht1⟩ ht

private def highDerivative0 (h z : ℝ) : ℝ :=
  (2368 * h + 138)
    + (1932 * h + 115) * z ^ 1
    + (604 * h + 23) * z ^ 2
    + (84 * h - 3) * z ^ 3
    + (4 * h - 1) * z ^ 4

private theorem highDerivative0_nonneg {h z : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 8)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ highDerivative0 h z := by
  have hsq : h ^ 2 ≤ 1 / 64 := by nlinarith only [hh, hh1]
  have hc0 : 0 ≤ (2368 * h + 138) - (138 : ℝ) := by nlinarith only [hh, hsq]
  have hc1 : 0 ≤ (1932 * h + 115) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc2 : 0 ≤ (604 * h + 23) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc3 : 0 ≤ (84 * h - 3) - (-3 : ℝ) := by nlinarith only [hh, hsq]
  have hc4 : 0 ≤ (4 * h - 1) - (-1 : ℝ) := by nlinarith only [hh, hsq]
  have hp : 0 ≤ ((2368 * h + 138) - (138 : ℝ))
      + ((1932 * h + 115) - (0 : ℝ)) * z ^ 1
      + ((604 * h + 23) - (0 : ℝ)) * z ^ 2
      + ((84 * h - 3) - (-3 : ℝ)) * z ^ 3
      + ((4 * h - 1) - (-1 : ℝ)) * z ^ 4 := by positivity
  have hz3 := pow_le_pow_left₀ hz hz1 3
  norm_num at hz3
  have hz4 := pow_le_pow_left₀ hz hz1 4
  norm_num at hz4
  unfold highDerivative0
  nlinarith only [hp, hz3, hz4]

private theorem highIncoming0_deriv (t x : ℝ) :
    HasDerivAt (fun s => highIncoming0 s x) (highDerivative0 (t - 1 / 4) (2 * x - 1) / 16) t := by
  let p : Polynomial ℝ := highIncoming0 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext s; simp [p, highIncoming0]; ring
  · norm_num [p, highIncoming0, highDerivative0, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring

/-- The highIncoming0 bound transports from the common quarter-scale face. -/
theorem highIncoming0_quarter_le {t x : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8)
    (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1) : highIncoming0 (1 / 4) x ≤ highIncoming0 t x := by
  apply transport (fun s => highIncoming0_deriv s x) (t := t) ?_ ht ht1
  intro s hs hs1
  have hh : 0 ≤ s - 1 / 4 := sub_nonneg.mpr hs
  have hh1 : s - 1 / 4 ≤ 1 / 8 := by linarith only [hs1]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have hz1 : 2 * x - 1 ≤ 1 := by linarith only [hx1]
  exact div_nonneg (highDerivative0_nonneg hh hh1 hz hz1) (by norm_num)

private def highDerivative1 (h z : ℝ) : ℝ :=
  (-134976 * h ^ 2 + 167040 * h + 15660)
    + (-411600 * h ^ 2 + 315064 * h + 24483) * z ^ 1
    + (-335424 * h ^ 2 + 220768 * h + 11948) * z ^ 2
    + (-128064 * h ^ 2 + 78496 * h + 3036) * z ^ 3
    + (-25632 * h ^ 2 + 14608 * h + 574) * z ^ 4
    + (-2544 * h ^ 2 + 1192 * h + 97) * z ^ 5
    + (-96 * h ^ 2 + 16 * h + 10) * z ^ 6

private theorem highDerivative1_nonneg {h z : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 8)
    (hz : 0 ≤ z) : 0 ≤ highDerivative1 h z := by
  have hsq : h ^ 2 ≤ 1 / 64 := by nlinarith only [hh, hh1]
  have hc0 : 0 ≤ (-134976 * h ^ 2 + 167040 * h + 15660) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc1 : 0 ≤ (-411600 * h ^ 2 + 315064 * h + 24483) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc2 : 0 ≤ (-335424 * h ^ 2 + 220768 * h + 11948) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc3 : 0 ≤ (-128064 * h ^ 2 + 78496 * h + 3036) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc4 : 0 ≤ (-25632 * h ^ 2 + 14608 * h + 574) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc5 : 0 ≤ (-2544 * h ^ 2 + 1192 * h + 97) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc6 : 0 ≤ (-96 * h ^ 2 + 16 * h + 10) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hp : 0 ≤ ((-134976 * h ^ 2 + 167040 * h + 15660) - (0 : ℝ))
      + ((-411600 * h ^ 2 + 315064 * h + 24483) - (0 : ℝ)) * z ^ 1
      + ((-335424 * h ^ 2 + 220768 * h + 11948) - (0 : ℝ)) * z ^ 2
      + ((-128064 * h ^ 2 + 78496 * h + 3036) - (0 : ℝ)) * z ^ 3
      + ((-25632 * h ^ 2 + 14608 * h + 574) - (0 : ℝ)) * z ^ 4
      + ((-2544 * h ^ 2 + 1192 * h + 97) - (0 : ℝ)) * z ^ 5
      + ((-96 * h ^ 2 + 16 * h + 10) - (0 : ℝ)) * z ^ 6 := by positivity
  unfold highDerivative1
  nlinarith only [hp]

private theorem highIncoming1_deriv (t x : ℝ) :
    HasDerivAt (fun s => highIncoming1 s x) (highDerivative1 (t - 1 / 4) (2 * x - 1) / 256) t := by
  let p : Polynomial ℝ := highIncoming1 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext s; simp [p, highIncoming1]; ring
  · norm_num [p, highIncoming1, highDerivative1, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring

/-- The highIncoming1 bound transports from the common quarter-scale face. -/
theorem highIncoming1_quarter_le {t x : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8)
    (hx : 1 / 2 ≤ x) : highIncoming1 (1 / 4) x ≤ highIncoming1 t x := by
  apply transport (fun s => highIncoming1_deriv s x) (t := t) ?_ ht ht1
  intro s hs hs1
  have hh : 0 ≤ s - 1 / 4 := sub_nonneg.mpr hs
  have hh1 : s - 1 / 4 ≤ 1 / 8 := by linarith only [hs1]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  exact div_nonneg (highDerivative1_nonneg hh hh1 hz) (by norm_num)

private def highDerivative2 (h z : ℝ) : ℝ :=
  (-8823168 * h ^ 2 + 4948800 * h + 343404)
    + (-26131680 * h ^ 2 + 13754816 * h + 859494) * z ^ 1
    + (-28049040 * h ^ 2 + 14257128 * h + 756383) * z ^ 2
    + (-13837680 * h ^ 2 + 7102824 * h + 282513) * z ^ 3
    + (-3536352 * h ^ 2 + 1945520 * h + 46758) * z ^ 4
    + (-465408 * h ^ 2 + 295728 * h - 1132) * z ^ 5
    + (-26640 * h ^ 2 + 20520 * h - 1041) * z ^ 6
    + (-432 * h ^ 2 + 168 * h + 21) * z ^ 7

private theorem highDerivative2_nonneg {h z : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 8)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ highDerivative2 h z := by
  have hsq : h ^ 2 ≤ 1 / 64 := by nlinarith only [hh, hh1]
  have hc0 : 0 ≤ (-8823168 * h ^ 2 + 4948800 * h + 343404) - (204800 : ℝ) := by nlinarith only [hh, hsq]
  have hc1 : 0 ≤ (-26131680 * h ^ 2 + 13754816 * h + 859494) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc2 : 0 ≤ (-28049040 * h ^ 2 + 14257128 * h + 756383) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc3 : 0 ≤ (-13837680 * h ^ 2 + 7102824 * h + 282513) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc4 : 0 ≤ (-3536352 * h ^ 2 + 1945520 * h + 46758) - (-10240 : ℝ) := by nlinarith only [hh, hsq]
  have hc5 : 0 ≤ (-465408 * h ^ 2 + 295728 * h - 1132) - (-10240 : ℝ) := by nlinarith only [hh, hsq]
  have hc6 : 0 ≤ (-26640 * h ^ 2 + 20520 * h - 1041) - (-10240 : ℝ) := by nlinarith only [hh, hsq]
  have hc7 : 0 ≤ (-432 * h ^ 2 + 168 * h + 21) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hp : 0 ≤ ((-8823168 * h ^ 2 + 4948800 * h + 343404) - (204800 : ℝ))
      + ((-26131680 * h ^ 2 + 13754816 * h + 859494) - (0 : ℝ)) * z ^ 1
      + ((-28049040 * h ^ 2 + 14257128 * h + 756383) - (0 : ℝ)) * z ^ 2
      + ((-13837680 * h ^ 2 + 7102824 * h + 282513) - (0 : ℝ)) * z ^ 3
      + ((-3536352 * h ^ 2 + 1945520 * h + 46758) - (-10240 : ℝ)) * z ^ 4
      + ((-465408 * h ^ 2 + 295728 * h - 1132) - (-10240 : ℝ)) * z ^ 5
      + ((-26640 * h ^ 2 + 20520 * h - 1041) - (-10240 : ℝ)) * z ^ 6
      + ((-432 * h ^ 2 + 168 * h + 21) - (0 : ℝ)) * z ^ 7 := by positivity
  have hz4 := pow_le_pow_left₀ hz hz1 4
  norm_num at hz4
  have hz5 := pow_le_pow_left₀ hz hz1 5
  norm_num at hz5
  have hz6 := pow_le_pow_left₀ hz hz1 6
  norm_num at hz6
  unfold highDerivative2
  nlinarith only [hp, hz4, hz5, hz6]

private theorem highQuadraticMargin_deriv (t x : ℝ) :
    HasDerivAt (fun s => highQuadraticMargin s x) (highDerivative2 (t - 1 / 4) (2 * x - 1) / 256) t := by
  let p : Polynomial ℝ := highQuadraticMargin Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext s; simp [p, highQuadraticMargin, high2, high0, highIncoming0]; ring
  · norm_num [p, highQuadraticMargin, high2, high0, highIncoming0, highDerivative2, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring

/-- The highQuadraticMargin bound transports from the common quarter-scale face. -/
theorem highQuadraticMargin_quarter_le {t x : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8)
    (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1) : highQuadraticMargin (1 / 4) x ≤ highQuadraticMargin t x := by
  apply transport (fun s => highQuadraticMargin_deriv s x) (t := t) ?_ ht ht1
  intro s hs hs1
  have hh : 0 ≤ s - 1 / 4 := sub_nonneg.mpr hs
  have hh1 : s - 1 / 4 ≤ 1 / 8 := by linarith only [hs1]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have hz1 : 2 * x - 1 ≤ 1 := by linarith only [hx1]
  exact div_nonneg (highDerivative2_nonneg hh hh1 hz hz1) (by norm_num)

private def highDerivative3 (h z : ℝ) : ℝ :=
  (2786544 * h ^ 2 + 5616360 * h + 595215)
    + (1326096 * h ^ 2 + 14673576 * h + 1422441) * z ^ 1
    + (-4744944 * h ^ 2 + 15368536 * h + 1290501) * z ^ 2
    + (-5041584 * h ^ 2 + 8409416 * h + 564845) * z ^ 3
    + (-2128944 * h ^ 2 + 2627576 * h + 156265) * z ^ 4
    + (-454416 * h ^ 2 + 459864 * h + 36103) * z ^ 5
    + (-47568 * h ^ 2 + 38856 * h + 6639) * z ^ 6
    + (-1872 * h ^ 2 + 952 * h + 675) * z ^ 7
    + (20) * z ^ 8

private theorem highDerivative3_nonneg {h z : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 8)
    (hz : 0 ≤ z) : 0 ≤ highDerivative3 h z := by
  have hsq : h ^ 2 ≤ 1 / 64 := by nlinarith only [hh, hh1]
  have hc0 : 0 ≤ (2786544 * h ^ 2 + 5616360 * h + 595215) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc1 : 0 ≤ (1326096 * h ^ 2 + 14673576 * h + 1422441) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc2 : 0 ≤ (-4744944 * h ^ 2 + 15368536 * h + 1290501) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc3 : 0 ≤ (-5041584 * h ^ 2 + 8409416 * h + 564845) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc4 : 0 ≤ (-2128944 * h ^ 2 + 2627576 * h + 156265) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc5 : 0 ≤ (-454416 * h ^ 2 + 459864 * h + 36103) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc6 : 0 ≤ (-47568 * h ^ 2 + 38856 * h + 6639) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc7 : 0 ≤ (-1872 * h ^ 2 + 952 * h + 675) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc8 : 0 ≤ (20) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hp : 0 ≤ ((2786544 * h ^ 2 + 5616360 * h + 595215) - (0 : ℝ))
      + ((1326096 * h ^ 2 + 14673576 * h + 1422441) - (0 : ℝ)) * z ^ 1
      + ((-4744944 * h ^ 2 + 15368536 * h + 1290501) - (0 : ℝ)) * z ^ 2
      + ((-5041584 * h ^ 2 + 8409416 * h + 564845) - (0 : ℝ)) * z ^ 3
      + ((-2128944 * h ^ 2 + 2627576 * h + 156265) - (0 : ℝ)) * z ^ 4
      + ((-454416 * h ^ 2 + 459864 * h + 36103) - (0 : ℝ)) * z ^ 5
      + ((-47568 * h ^ 2 + 38856 * h + 6639) - (0 : ℝ)) * z ^ 6
      + ((-1872 * h ^ 2 + 952 * h + 675) - (0 : ℝ)) * z ^ 7
      + ((20) - (0 : ℝ)) * z ^ 8 := by positivity
  unfold highDerivative3
  nlinarith only [hp]

private theorem highCubicMargin_deriv (t x : ℝ) :
    HasDerivAt (fun s => highCubicMargin s x) (highDerivative3 (t - 1 / 4) (2 * x - 1) / 256) t := by
  let p : Polynomial ℝ := highCubicMargin Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext s; simp [p, highCubicMargin, high3, high2]; ring
  · norm_num [p, highCubicMargin, high3, high2, highDerivative3, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring

/-- The highCubicMargin bound transports from the common quarter-scale face. -/
theorem highCubicMargin_quarter_le {t x : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8)
    (hx : 1 / 2 ≤ x) : highCubicMargin (1 / 4) x ≤ highCubicMargin t x := by
  apply transport (fun s => highCubicMargin_deriv s x) (t := t) ?_ ht ht1
  intro s hs hs1
  have hh : 0 ≤ s - 1 / 4 := sub_nonneg.mpr hs
  have hh1 : s - 1 / 4 ≤ 1 / 8 := by linarith only [hs1]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  exact div_nonneg (highDerivative3_nonneg hh hh1 hz) (by norm_num)

private def highDerivative4 (h z : ℝ) : ℝ :=
  (1252080 * h ^ 2 + 1373160 * h + 248031)
    + (2152080 * h ^ 2 + 3396904 * h + 678849) * z ^ 1
    + (1137744 * h ^ 2 + 3388984 * h + 764953) * z ^ 2
    + (169488 * h ^ 2 + 1791656 * h + 469001) * z ^ 3
    + (-51888 * h ^ 2 + 547896 * h + 179185) * z ^ 4
    + (-23568 * h ^ 2 + 96024 * h + 44519) * z ^ 5
    + (-3216 * h ^ 2 + 8616 * h + 6915) * z ^ 6
    + (-144 * h ^ 2 + 280 * h + 591) * z ^ 7
    + (20) * z ^ 8

private theorem highDerivative4_nonneg {h z : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 8)
    (hz : 0 ≤ z) : 0 ≤ highDerivative4 h z := by
  have hsq : h ^ 2 ≤ 1 / 64 := by nlinarith only [hh, hh1]
  have hc0 : 0 ≤ (1252080 * h ^ 2 + 1373160 * h + 248031) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc1 : 0 ≤ (2152080 * h ^ 2 + 3396904 * h + 678849) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc2 : 0 ≤ (1137744 * h ^ 2 + 3388984 * h + 764953) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc3 : 0 ≤ (169488 * h ^ 2 + 1791656 * h + 469001) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc4 : 0 ≤ (-51888 * h ^ 2 + 547896 * h + 179185) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc5 : 0 ≤ (-23568 * h ^ 2 + 96024 * h + 44519) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc6 : 0 ≤ (-3216 * h ^ 2 + 8616 * h + 6915) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc7 : 0 ≤ (-144 * h ^ 2 + 280 * h + 591) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hc8 : 0 ≤ (20) - (0 : ℝ) := by nlinarith only [hh, hsq]
  have hp : 0 ≤ ((1252080 * h ^ 2 + 1373160 * h + 248031) - (0 : ℝ))
      + ((2152080 * h ^ 2 + 3396904 * h + 678849) - (0 : ℝ)) * z ^ 1
      + ((1137744 * h ^ 2 + 3388984 * h + 764953) - (0 : ℝ)) * z ^ 2
      + ((169488 * h ^ 2 + 1791656 * h + 469001) - (0 : ℝ)) * z ^ 3
      + ((-51888 * h ^ 2 + 547896 * h + 179185) - (0 : ℝ)) * z ^ 4
      + ((-23568 * h ^ 2 + 96024 * h + 44519) - (0 : ℝ)) * z ^ 5
      + ((-3216 * h ^ 2 + 8616 * h + 6915) - (0 : ℝ)) * z ^ 6
      + ((-144 * h ^ 2 + 280 * h + 591) - (0 : ℝ)) * z ^ 7
      + ((20) - (0 : ℝ)) * z ^ 8 := by positivity
  unfold highDerivative4
  nlinarith only [hp]

private theorem high3_deriv (t x : ℝ) :
    HasDerivAt (fun s => high3 s x) (highDerivative4 (t - 1 / 4) (2 * x - 1) / 256) t := by
  let p : Polynomial ℝ := high3 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext s; simp [p, high3]; ring
  · norm_num [p, high3, highDerivative4, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring

/-- The high3 bound transports from the common quarter-scale face. -/
theorem high3_quarter_le {t x : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8)
    (hx : 1 / 2 ≤ x) : high3 (1 / 4) x ≤ high3 t x := by
  apply transport (fun s => high3_deriv s x) (t := t) ?_ ht ht1
  intro s hs hs1
  have hh : 0 ≤ s - 1 / 4 := sub_nonneg.mpr hs
  have hh1 : s - 1 / 4 ≤ 1 / 8 := by linarith only [hs1]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  exact div_nonneg (highDerivative4_nonneg hh hh1 hz) (by norm_num)

end SmoothedOctagon.LowScale

module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Transport

/-!
# The increasing-shape low-scale face

At `t=1/4` this face is the unit face. Its coefficient inequalities
then follow by monotone transport. The same norm slack guarantees
that the common boundary is feasible.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

/-- Positivity of the quartic transports from the common unit boundary. -/
theorem high_quartic_pos {t x y : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8)
    (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) (hy : 0 ≤ y) :
    0 < high0 t x + high1 t x * y + high2 t x * y ^ 2 + high3 t x * y ^ 3 + high4 t x * y ^ 4 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx7 : x ≤ 7 / 3 := by linarith only [hx1]
  have hD : 0 ≤ x ^ 2 + 6 * x + 6 := by positivity
  have hTq : 1 / 4 * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2 :=
    (mul_le_mul_of_nonneg_right ht hD).trans hT
  have h0base := incoming0_pos (t := 1 / 4) le_rfl hx hx7 hTq
  have h1base := incoming1_pos (t := 1 / 4) (by norm_num) le_rfl hx hx7 hTq
  have h0 : 0 < high0 t x := by
    have hm := highIncoming0_quarter_le ht ht1 hx hx1
    have he : highIncoming0 (1 / 4) x = 3 / 2 * incoming0 (1 / 4) x := by
      unfold highIncoming0 incoming0
      ring
    have hp : 0 < highIncoming0 t x := by linarith only [hm, he, h0base]
    have ht0 : 0 < 1 - t := by linarith only [ht1]
    unfold high0
    positivity
  have h1 : 0 ≤ high1 t x := by
    have hm := highIncoming1_quarter_le ht ht1 hx
    have he : highIncoming1 (1 / 4) x = 3 / 2 * incoming1 (1 / 4) x := by
      unfold highIncoming1 incoming1
      ring
    have hp : 0 < highIncoming1 t x := by linarith only [hm, he, h1base]
    unfold high1
    positivity
  have h2 : 0 ≤ highQuadraticMargin t x := by
    have hm := highQuadraticMargin_quarter_le ht ht1 hx hx1
    have he : highQuadraticMargin (1 / 4) x = quadraticMargin (1 / 4) x := by
      unfold highQuadraticMargin high2 high0 highIncoming0 quadraticMargin unit2 unit0 incoming0
      ring
    have hb := quadraticMargin_pos (t := 1 / 4) le_rfl hx hx7 hTq
    linarith only [hm, he, hb]
  have h3 : 0 ≤ highCubicMargin t x := by
    have hm := highCubicMargin_quarter_le ht ht1 hx
    have he : highCubicMargin (1 / 4) x = cubicMargin (1 / 4) x := by
      unfold highCubicMargin high3 high2 cubicMargin unit3 unit2
      ring
    have hb := cubicMargin_pos (t := 1 / 4) (by norm_num) le_rfl hx hx7 hTq
    linarith only [hm, he, hb]
  have hc : 0 ≤ high3 t x := by
    have hm := high3_quarter_le ht ht1 hx
    have he : high3 (1 / 4) x = unit3 (1 / 4) x := by unfold high3 unit3; ring
    have hb := unit3_pos (t := 1 / 4) (by norm_num) le_rfl hx
    linarith only [hm, he, hb]
  have h4 : 0 ≤ high4 t x := by
    have ht0 : 0 ≤ t := by linarith only [ht]
    have hg : 0 ≤ 6 * t + 5 * x - 1 := by linarith only [ht, hx]
    unfold high4
    positivity
  exact nsr_quartic_cubic_tail h0 h1 hc h4 h2 h3 hy

end SmoothedOctagon.LowScale

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip.Boundaries.Signs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.UpperBoundary

/-!
# Signs at the outer-strip beta boundaries

The lower boundary is `x + 3(a-1)/5`; the upper one is the exact
strong-order boundary. Positivity of the two cleared numerators gives
the three test signs at both ends of the beta interval.
-/

@[expose] public section
namespace SmoothedOctagon.S0Outer.Boundaries

noncomputable def lowerBeta (x a : ℝ) : ℝ := x + 3 / 5 * (a - 1)

theorem lowerBeta_eq (x a : ℝ) : lowerBeta x a = (5 * x + 3 * (a - 1)) / 5 := by
  unfold lowerBeta
  ring

theorem lower2_neg {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) :
    lgrO2 x a (lowerBeta x a) (ssUhat x (lowerBeta x a)) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have ha1 : 1 < a := by linarith only [hx, ha]
  have hb1 : 1 < lowerBeta x a := by unfold lowerBeta; linarith only [hx, ha1]
  have hb0 : 0 < lowerBeta x a := by linarith only [hb1]
  have hbsub : 0 < lowerBeta x a - 1 := by linarith only [hb1]
  have hV : 0 < lgrVc x (lowerBeta x a) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb1]
  apply lgr_O2_neg hx0 (by linarith only [ha1]) hb0 hV
  have hp := clearedLower2_pos hx ha ham
  unfold clearedLower2 at hp
  have he := numerator2_link x a 5 (5 * x + 3 * (a - 1)) (by norm_num)
  rw [← lowerBeta_eq x a] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 5 ^ 4)).mp hp

theorem upper2_neg {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) :
    lgrO2 x a (S0Central.upperBeta x a) (ssUhat x (S0Central.upperBeta x a)) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have ha1 : 1 < a := by linarith only [hx, ha]
  have hxb := S0Central.upperBeta_ge hx0.le ha1.le
  have hb1 : 1 < S0Central.upperBeta x a := by linarith only [hx, hxb]
  have hb0 : 0 < S0Central.upperBeta x a := by linarith only [hb1]
  have hbsub : 0 < S0Central.upperBeta x a - 1 := by linarith only [hb1]
  have hV : 0 < lgrVc x (S0Central.upperBeta x a) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb1]
  apply lgr_O2_neg hx0 (by linarith only [ha1]) hb0 hV
  have hq := S0Central.denominator_pos hx0.le
  have hp := clearedUpper2_pos hx ha ham
  unfold clearedUpper2 at hp
  have he := numerator2_link x a (S0Central.gapDenominator x) (S0Central.betaNumerator x a) hq.ne'
  rw [← S0Central.upperBeta_eq x a hq.ne'] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq 4)).mp hp

theorem lowerT_neg {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) :
    lgrOT x a (lowerBeta x a) (ssUhat x (lowerBeta x a)) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have ha1 : 1 < a := by linarith only [hx, ha]
  have hb1 : 1 < lowerBeta x a := by unfold lowerBeta; linarith only [hx, ha1]
  have hb0 : 0 < lowerBeta x a := by linarith only [hb1]
  have hbsub : 0 < lowerBeta x a - 1 := by linarith only [hb1]
  have hV : 0 < lgrVc x (lowerBeta x a) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb1]
  apply lgr_OT_neg hx0 (by linarith only [ha1]) hb0 hV
  have hp := clearedLowerT_pos hx ha ham
  unfold clearedLowerT at hp
  have he := numeratorT_link x a 5 (5 * x + 3 * (a - 1)) (by norm_num)
  rw [← lowerBeta_eq x a] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 5 ^ 4)).mp hp

theorem upperT_neg {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) :
    lgrOT x a (S0Central.upperBeta x a) (ssUhat x (S0Central.upperBeta x a)) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have ha1 : 1 < a := by linarith only [hx, ha]
  have hxb := S0Central.upperBeta_ge hx0.le ha1.le
  have hb1 : 1 < S0Central.upperBeta x a := by linarith only [hx, hxb]
  have hb0 : 0 < S0Central.upperBeta x a := by linarith only [hb1]
  have hbsub : 0 < S0Central.upperBeta x a - 1 := by linarith only [hb1]
  have hV : 0 < lgrVc x (S0Central.upperBeta x a) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb1]
  apply lgr_OT_neg hx0 (by linarith only [ha1]) hb0 hV
  have hq := S0Central.denominator_pos hx0.le
  have hp := clearedUpperT_pos hx ha ham
  unfold clearedUpperT at hp
  have he := numeratorT_link x a (S0Central.gapDenominator x) (S0Central.betaNumerator x a) hq.ne'
  rw [← S0Central.upperBeta_eq x a hq.ne'] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq 4)).mp hp

theorem lower8_neg {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) :
    lgrO8 x a (lowerBeta x a) (ssUhat x (lowerBeta x a)) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have ha1 : 1 < a := by linarith only [hx, ha]
  have hb1 : 1 < lowerBeta x a := by unfold lowerBeta; linarith only [hx, ha1]
  have hb0 : 0 < lowerBeta x a := by linarith only [hb1]
  have hbsub : 0 < lowerBeta x a - 1 := by linarith only [hb1]
  have hV : 0 < lgrVc x (lowerBeta x a) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb1]
  apply lgr_O8_neg hx0 (by linarith only [ha1]) hb0 hV
  have hp := clearedLower8_pos hx ha ham
  unfold clearedLower8 at hp
  have he := numerator8_link x a 5 (5 * x + 3 * (a - 1)) (by norm_num)
  rw [← lowerBeta_eq x a] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 5 ^ 4)).mp hp

theorem upper8_neg {x a : ℝ} (hx : 12 / 5 ≤ x)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) :
    lgrO8 x a (S0Central.upperBeta x a) (ssUhat x (S0Central.upperBeta x a)) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 < x := by linarith only [hx]
  have ha1 : 1 < a := by linarith only [hx, ha]
  have hxb := S0Central.upperBeta_ge hx0.le ha1.le
  have hb1 : 1 < S0Central.upperBeta x a := by linarith only [hx, hxb]
  have hb0 : 0 < S0Central.upperBeta x a := by linarith only [hb1]
  have hbsub : 0 < S0Central.upperBeta x a - 1 := by linarith only [hb1]
  have hV : 0 < lgrVc x (S0Central.upperBeta x a) := by unfold lgrVc; positivity
  rw [lgr_uhat_UV hx1 hb1]
  apply lgr_O8_neg hx0 (by linarith only [ha1]) hb0 hV
  have hq := S0Central.denominator_pos hx0.le
  have hp := clearedUpper8_pos hx ha ham
  unfold clearedUpper8 at hp
  have he := numerator8_link x a (S0Central.gapDenominator x) (S0Central.betaNumerator x a) hq.ne'
  rw [← S0Central.upperBeta_eq x a hq.ne'] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq 4)).mp hp

end SmoothedOctagon.S0Outer.Boundaries

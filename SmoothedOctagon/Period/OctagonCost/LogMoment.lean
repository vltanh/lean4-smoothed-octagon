module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Log moment

The five reciprocal moments below `log 2`, proved by a positive geometric remainder.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

/-- The five exact reciprocal moments used by the octagon cost comparison. -/
noncomputable def octagonLogMoment : ℝ :=
  2*((1/3:ℝ)+(1/3)^3/3+(1/3)^5/5+(1/3)^7/7+(1/3)^9/9)

/-- The displayed moment definition equals the paper's finite sum. -/
theorem octagonLogMoment_eq_sum : octagonLogMoment =
    2*∑ j ∈ Finset.range 5, 1/(((2:ℝ)*j+1)*3^(2*j+1)) := by
  norm_num [octagonLogMoment,Finset.sum_range_succ]

private noncomputable def omTrunc (t : ℝ) : ℝ := 2*(1+t^2+t^4+t^6+t^8)
private noncomputable def omPrimitive (t : ℝ) : ℝ :=
  2*(t+t^3/3+t^5/5+t^7/7+t^9/9)

private theorem om_den_pos {t : ℝ} (ht : t ∈ Icc (0:ℝ) (1/3)) : 0 < 1-t^2 := by
  nlinarith only [ht.1,ht.2]

/-- The exact positive geometric remainder, without an enclosure for log2. -/
theorem octagon_log_geometric_remainder {t : ℝ} (ht : 1-t^2 ≠ 0) :
    2/(1-t^2)-2*(1+t^2+t^4+t^6+t^8) = 2*t^10/(1-t^2) := by
  field_simp
  ring

private theorem omPrimitive_hasDerivAt (t : ℝ) : HasDerivAt omPrimitive (omTrunc t) t := by
  have h := (((((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 3)).add
    ((hasDerivAt_pow 5 t).div_const 5)).add ((hasDerivAt_pow 7 t).div_const 7)).add
    ((hasDerivAt_pow 9 t).div_const 9)).const_mul 2
  refine h.congr_deriv ?_
  unfold omTrunc
  norm_num

/-- Integrating the truncated reciprocal gives exactly the retained moments. -/
theorem octagonLogMoment_eq_integral : octagonLogMoment =
    ∫ t in (0:ℝ)..(1/3), 2*(1+t^2+t^4+t^6+t^8) := by
  have hc : Continuous omTrunc := by unfold omTrunc; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => omPrimitive_hasDerivAt t) (hc.intervalIntegrable 0 (1/3))
  symm
  simpa [omPrimitive,omTrunc,octagonLogMoment] using hi

/-- The original reciprocal integral is log2, with its entire domain positive. -/
theorem octagon_log_reciprocal_integral :
    (∫ t in (0:ℝ)..(1/3), 2/(1-t^2)) = log 2 := by
  have hc : ContinuousOn (fun t : ℝ => 2/(1-t^2)) (Icc 0 (1/3)) := by
    apply continuousOn_const.div
    · fun_prop
    · intro t ht
      exact (om_den_pos ht).ne'
  have hd : ∀ t ∈ uIcc (0:ℝ) (1/3), HasDerivAt
      (fun t : ℝ => log (1+t)-log (1-t)) (2/(1-t^2)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/3)] at ht
    have hp : 0 < 1+t := by linarith only [ht.1]
    have hm : 0 < 1-t := by linarith only [ht.2]
    have hden : 1-t^2 ≠ 0 := (om_den_pos ht).ne'
    have h := (((hasDerivAt_id' t).const_add 1).log hp.ne').sub
      (((hasDerivAt_id' t).const_sub 1).log hm.ne')
    refine h.congr_deriv ?_
    field_simp [hden]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1/3))
  rw [hi]
  norm_num
  rw [← Real.log_div (by norm_num : (4/3:ℝ) ≠ 0) (by norm_num : (2/3:ℝ) ≠ 0)]
  norm_num

/-- The five moments are strictly below log2 by their positive integral
remainder. In particular this uses no numerical logarithm enclosure. -/
theorem octagonLogMoment_lt_log_two : octagonLogMoment < log 2 := by
  have hp : Continuous (fun t : ℝ => 2*(1+t^2+t^4+t^6+t^8)) := by fun_prop
  have hk : ContinuousOn (fun t : ℝ => 2/(1-t^2)) (Icc 0 (1/3)) := by
    apply continuousOn_const.div
    · fun_prop
    · intro t ht
      exact (om_den_pos ht).ne'
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0:ℝ) < 1/3) hp.continuousOn hk (fun t ht => by
      have hd := om_den_pos (show t ∈ Icc (0:ℝ) (1/3) from ⟨ht.1.le,ht.2⟩)
      have hid := octagon_log_geometric_remainder hd.ne'
      have hrem : 0 ≤ 2*t^10/(1-t^2) := by positivity
      linarith only [hid,hrem]) (by
      refine ⟨(1/3:ℝ),⟨by norm_num,le_rfl⟩,?_⟩
      have hid := octagon_log_geometric_remainder (t := (1/3:ℝ)) (by norm_num)
      have hrem : 0 < 2*(1/3:ℝ)^10/(1-(1/3:ℝ)^2) := by norm_num
      linarith only [hid,hrem])
  rw [← octagonLogMoment_eq_integral,octagon_log_reciprocal_integral] at hi
  exact hi

end SmoothedOctagon

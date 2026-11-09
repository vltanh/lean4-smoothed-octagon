module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The strict reciprocal midpoint bound

The reciprocal lies above its tangent at the midpoint of a positive interval.
The difference is a square divided by a positive denominator. Integrating gives
`log b - log a > 2(b - a)/(a + b)`, and hence an exact lower bound for `log 2`.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

/-- The reciprocal integral lies strictly above its midpoint tangent. -/
theorem ra_log_midpoint_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    2*(b-a)/(a+b) < log b-log a := by
  have hb : 0 < b := ha.trans hab
  have hs : 0 < a+b := by positivity
  let f : ℝ → ℝ := fun x => 4/(a+b)-4*x/(a+b)^2
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : ContinuousOn (fun x : ℝ => 1/x) (Icc a b) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hpoint : ∀ x ∈ Icc a b, 1/x-f x = (a+b-2*x)^2/(x*(a+b)^2) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    dsimp [f]
    field_simp
    ring
  have hcmp := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hf.continuousOn hg (fun x hx => by
      have hid := hpoint x ⟨hx.1.le,hx.2⟩
      have hn : 0 ≤ (a+b-2*x)^2/(x*(a+b)^2) := by
        apply div_nonneg (sq_nonneg _) (mul_nonneg (ha.trans hx.1).le (sq_nonneg _))
      linarith only [hid,hn]) (by
      refine ⟨a,⟨le_rfl,hab.le⟩,?_⟩
      have hid := hpoint a ⟨le_rfl,hab.le⟩
      have hp : 0 < (a+b-2*a)^2/(a*(a+b)^2) := by
        apply div_pos
        · exact sq_pos_of_ne_zero (by linarith)
        · positivity
      linarith only [hid,hp])
  have hfi : (∫ x in a..b, f x) = 2*(b-a)/(a+b) := by
    have hd : ∀ x : ℝ, HasDerivAt
        (fun x : ℝ => 4*x/(a+b)-2*x^2/(a+b)^2) (f x) x := by
      intro x
      have h := (((hasDerivAt_id' x).const_mul 4).div_const (a+b)).sub
        (((hasDerivAt_id' x).pow 2).const_mul 2 |>.div_const ((a+b)^2))
      refine h.congr_deriv ?_
      dsimp [f]
      ring
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) (hf.intervalIntegrable a b)
    rw [hi]
    field_simp
    ring
  have hgi : (∫ x : ℝ in a..b, 1/x) = log b-log a := by
    have hd : ∀ x ∈ uIcc a b, HasDerivAt log (1/x) x := by
      intro x hx
      have hx1 : a ≤ x := by
        rw [uIcc_of_le hab.le] at hx
        exact hx.1
      simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt (ha.trans_le hx1))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hg.intervalIntegrable_of_Icc hab.le)
  rwa [hfi,hgi] at hcmp

/-- The strict reciprocal midpoint bound on `[1, √2]`. -/
theorem ra_log_two_gt_midpoint :
    4*(sqrt 2-1)/(sqrt 2+1) < log 2 := by
  have hr : (1:ℝ) < sqrt 2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have h := ra_log_midpoint_lt (a := 1) (by norm_num) hr
  rw [log_sqrt (by norm_num),log_one,sub_zero] at h
  have hid : 4*(sqrt 2-1)/(sqrt 2+1) = 2*(2*(sqrt 2-1)/(1+sqrt 2)) := by ring
  linarith only [h,hid]

end SmoothedOctagon

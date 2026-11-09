module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# S6 corner scores from a reciprocal moment

A tangent bound for the weighted reciprocal integral gives a strict Jensen
lower bound for each exact angle. Four rational substitutions then finish the
corner comparisons.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

noncomputable def s6AngleJensen (z : ℝ) : ℝ :=
  (1-(161/54)/3)*z+(161/54)*z^3/(27*(1+z^2/5))

private noncomputable def s6AngleMoment (z : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..z, t^2/(3+t^2)

private noncomputable def s6AngleTangent (z t : ℝ) : ℝ :=
  t^2/(3+3*z^2/5)-t^2*(t^2-3*z^2/5)/(3+3*z^2/5)^2

private theorem s6_angle_tangent_le (z t : ℝ) :
    s6AngleTangent z t ≤ t^2/(3+t^2) := by
  have hp : 0 < 3+3*z^2/5 := by positivity
  have ht : 0 < 3+t^2 := by positivity
  have hid : t^2/(3+t^2)-s6AngleTangent z t =
      t^2*(t^2-3*z^2/5)^2/((3+t^2)*(3+3*z^2/5)^2) := by
    unfold s6AngleTangent
    field_simp
    ring
  have hh : 0 ≤ t^2*(t^2-3*z^2/5)^2/((3+t^2)*(3+3*z^2/5)^2) := by positivity
  linarith only [hid,hh]

private theorem s6_angle_tangent_mid_lt {z : ℝ} (hz : 0 < z) :
    s6AngleTangent z (z/2) < (z/2)^2/(3+(z/2)^2) := by
  have hp : 0 < 3+3*z^2/5 := by positivity
  have ht : 0 < 3+(z/2)^2 := by positivity
  have hd : (z/2)^2-3*z^2/5 ≠ 0 := by nlinarith only [sq_pos_of_pos hz]
  have hid : (z/2)^2/(3+(z/2)^2)-s6AngleTangent z (z/2) =
      (z/2)^2*((z/2)^2-3*z^2/5)^2/((3+(z/2)^2)*(3+3*z^2/5)^2) := by
    unfold s6AngleTangent
    field_simp
    ring
  have hh : 0 < (z/2)^2*((z/2)^2-3*z^2/5)^2/((3+(z/2)^2)*(3+3*z^2/5)^2) := by
    exact div_pos (mul_pos (sq_pos_of_pos (by positivity)) (sq_pos_of_ne_zero hd))
      (mul_pos ht (sq_pos_of_pos hp))
  linarith only [hid,hh]

private theorem s6_angle_moment_gt {z : ℝ} (hz : 0 < z) :
    z^3/(9*(1+z^2/5)) < s6AngleMoment z := by
  have hp : 0 < 3+3*z^2/5 := by positivity
  have hc : Continuous (fun t : ℝ => t^2/(3+t^2)) := by
    exact Continuous.div (by fun_prop) (by fun_prop)
      (fun t => ne_of_gt (by positivity : 0 < 3+t^2))
  have ht : Continuous (s6AngleTangent z) := by unfold s6AngleTangent; fun_prop
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hz
    ht.continuousOn hc.continuousOn (fun t _ => s6_angle_tangent_le z t)
    ⟨z/2,⟨by linarith only [hz],by linarith only [hz]⟩,s6_angle_tangent_mid_lt hz⟩
  let P : ℝ → ℝ := fun t => t^3/(3*(3+3*z^2/5))-
    (t^5/5-(3*z^2/5)*t^3/3)/(3+3*z^2/5)^2
  have hd (t : ℝ) : HasDerivAt P (s6AngleTangent z t) t := by
    have hh := ((hasDerivAt_pow 3 t).div_const (3*(3+3*z^2/5))).sub
      ((((hasDerivAt_pow 5 t).div_const 5).sub
        (((hasDerivAt_pow 3 t).const_mul (3*z^2/5)).div_const 3)).div_const
          ((3+3*z^2/5)^2))
    refine hh.congr_deriv ?_
    unfold s6AngleTangent
    norm_num
    field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (ht.intervalIntegrable 0 z)
  have hv : P z-P 0=z^3/(9*(1+z^2/5)) := by
    dsimp [P]
    field_simp
    ring
  rw [he,hv] at hi
  exact hi

/-- The original arctangent contribution is the reciprocal moment. -/
private theorem s6_angle_moment_eq (z : ℝ) :
    s6AngleMoment z = (3/(161/54))*(costLExact z-(1-(161/54)/3)*z) := by
  let P : ℝ → ℝ := fun t => (3/(161/54))*(costLExact t-(1-(161/54)/3)*t)
  have hc : Continuous (fun t : ℝ => t^2/(3+t^2)) := by
    exact Continuous.div (by fun_prop) (by fun_prop)
      (fun t => ne_of_gt (by positivity : 0 < 3+t^2))
  have hd (t : ℝ) : HasDerivAt P (t^2/(3+t^2)) t := by
    have hh := ((costLExact_hasDerivAt t).sub
      ((hasDerivAt_id t).const_mul (1-(161/54)/3))).const_mul (3/(161/54))
    refine hh.congr_deriv ?_
    field_simp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 z)
  simpa [s6AngleMoment,P,costLExact] using he

/-- The strict weighted-Jensen lower bound used in the four corner comparisons. -/
theorem s6_angle_jensen_lt {z : ℝ} (hz : 0 < z) : s6AngleJensen z < costLExact z := by
  have hm := s6_angle_moment_gt hz
  rw [s6_angle_moment_eq] at hm
  have hm2 := mul_lt_mul_of_pos_left hm (by norm_num : (0:ℝ) < (161/54)/3)
  have hid : ((161/54)/3)*(z^3/(9*(1+z^2/5))) = (161/54)*z^3/(27*(1+z^2/5)) := by
    field_simp
    ring
  rw [hid] at hm2
  unfold s6AngleJensen
  norm_num at hm2
  linarith only [hm2]

/-- A rational lower score, obtained only by applying weighted Jensen to both angles. -/
noncomputable def s6RationalScore (R d e : ℝ) : ℝ :=
  let T := costT R d e
  let u := s6VarianceFloor R d
  s6AngleJensen R+s6AngleJensen T-
    ((1-4*u/(3+R^2))*R+(1-4*u/(3+T^2))*T)/2-
    ((1-4*u/(3+R^2))+(1-4*u/(3+T^2)))*costZU R d/8-
    (161/54)*((R^2-T^2)/(3+T^2))^2/(8*costZL R d)

theorem s6_rationalScore_lt {R d e : ℝ} (hR : 0 < R) (hT : 0 < costT R d e) :
    s6RationalScore R d e < s6FinalScore R d e := by
  have hh := add_lt_add (s6_angle_jensen_lt hR) (s6_angle_jensen_lt hT)
  dsimp [s6RationalScore,s6FinalScore,costBExact]
  linarith only [hh]

/-- These are the four substitutions after the two analytic monotonicity reductions. -/
theorem s6_rational_four_corners {R e : ℝ} (hR : R=1/3 ∨ R=7/19)
    (he : e=13/5 ∨ e=3) : 9/4000 < s6RationalScore R (1/19) e := by
  rcases hR with rfl | rfl <;> rcases he with rfl | rfl <;>
    norm_num [s6RationalScore,s6AngleJensen,s6VarianceFloor,costT,costZU,costZL]

/-- The four exact-angle corner scores, with strict inequality throughout. -/
theorem s6_final_four_corners {R e : ℝ} (hR : R=1/3 ∨ R=7/19)
    (he : e=13/5 ∨ e=3) : 9/4000 < s6FinalScore R (1/19) e := by
  have hRp : 0 < R := by rcases hR with rfl | rfl <;> norm_num
  have hTp : 0 < costT R (1/19) e := by
    rcases hR with rfl | rfl <;> rcases he with rfl | rfl <;> norm_num [costT]
  exact (s6_rational_four_corners hR he).trans (s6_rationalScore_lt hRp hTp)

end SmoothedOctagon

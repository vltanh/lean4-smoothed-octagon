module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Reciprocal moments for the opposite neighbour floor

Integral moments give derivative signs and weighted Jensen bounds.
Their positive square remainders control the first two scale derivatives.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

noncomputable def asymReciprocalMoment (n : ℕ) (t : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..1, r^n/(1-t*r)^(n+1)

private theorem asym_moment_den {t r : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hr : r ∈ Icc (0:ℝ) 1) : 0 < 1-t*r := by
  have hm := mul_le_of_le_one_right ht hr.2
  linarith only [hm,ht1]

private theorem asym_moment_cont (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    ContinuousOn (fun r : ℝ => r^n/(1-t*r)^(n+1)) (Icc 0 1) := by
  apply (continuousOn_id.pow n).div
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).pow (n+1))
  intro r hr
  exact pow_ne_zero _ (asym_moment_den ht ht1 hr).ne'

/-- Bounding the denominator gives the elementary upper moment on the full unit interval. -/
theorem asymReciprocalMoment_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    asymReciprocalMoment n t ≤ 1/(((n:ℝ)+1)*(1-t)^(n+1)) := by
  have hd : 0 < 1-t := by linarith only [ht1]
  have hc : Continuous (fun r : ℝ => r^n/(1-t)^(n+1)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((asym_moment_cont n ht ht1).intervalIntegrable_of_Icc (by norm_num))
    (hc.intervalIntegrable 0 1) (fun r hr => ?_)
  · have hi : (∫ r in (0:ℝ)..1, r^n/(1-t)^(n+1)) =
        1/(((n:ℝ)+1)*(1-t)^(n+1)) := by
      have hni : (∫ r in (0:ℝ)..1, r^n)=1/((n:ℝ)+1) := by
        have hnc : 0 < (n:ℝ)+1 := by positivity
        have hd (r : ℝ) : HasDerivAt (fun u : ℝ => u^(n+1)/((n:ℝ)+1)) (r^n) r := by
          have he := (hasDerivAt_pow (n+1) r).div_const ((n:ℝ)+1)
          refine he.congr_deriv ?_
          simp only [Nat.add_sub_cancel_right,Nat.cast_add,Nat.cast_one]
          field_simp
        have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
          ((continuous_id.pow n).intervalIntegrable 0 1)
        simpa only [one_pow,zero_pow (Nat.succ_ne_zero n),zero_div,sub_zero] using he
      rw [intervalIntegral.integral_div,hni,div_div]
    exact hm.trans hi.le
  · have hden := asym_moment_den ht ht1 hr
    have hh : 1-t ≤ 1-t*r := by
      have hp := mul_le_of_le_one_right ht hr.2
      linarith only [hp]
    exact div_le_div_of_nonneg_left (pow_nonneg hr.1 n) (by positivity)
      (pow_le_pow_left₀ hd.le hh (n+1))

/-- The first weighted reciprocal tangent has a positive square remainder. -/
theorem asym_moment_one_jensen {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    1/(2*(1-2*t/3)^2) ≤ asymReciprocalMoment 1 t := by
  let b := 1-2*t/3
  let p : ℝ → ℝ := fun r => r/b^2+2*t*r*(r-2/3)/b^3
  have hb : 0 < b := by dsimp [b]; linarith only [ht1]
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hp.intervalIntegrable 0 1)
    ((asym_moment_cont 1 ht ht1).intervalIntegrable_of_Icc (by norm_num)) (fun r hr => ?_)
  · have hi : (∫ r in (0:ℝ)..1, p r)=1/(2*b^2) := by
      let P : ℝ → ℝ := fun r => r^2/(2*b^2)+2*t/b^3*(r^3/3-r^2/3)
      have hd (r : ℝ) : HasDerivAt P (p r) r := by
        have he := ((hasDerivAt_pow 2 r).div_const (2*b^2)).add
          ((((hasDerivAt_pow 3 r).div_const 3).sub
            ((hasDerivAt_pow 2 r).div_const 3)).const_mul (2*t/b^3))
        refine he.congr_deriv ?_
        dsimp [p]
        norm_num
        field_simp [hb.ne']
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
        (hp.intervalIntegrable 0 1)
      simpa [P] using he
    rw [hi] at hm
    exact hm
  · have hv := asym_moment_den ht ht1 hr
    have hr0 : 0 ≤ r := hr.1
    have hv1 : 1-r*t ≠ 0 := by nlinarith only [hv]
    have he : r/(1-t*r)^2-p r =
        t^2*r*(r-2/3)^2*(b+2*(1-t*r))/(b^3*(1-t*r)^2) := by
      dsimp [p]
      field_simp [hb.ne',hv.ne',hv1]
      dsimp [b]
      ring
    have hn : 0 ≤ t^2*r*(r-2/3)^2*(b+2*(1-t*r))/(b^3*(1-t*r)^2) := by
      positivity
    simp only [pow_one]
    linarith only [he,hn]

/-- The second weighted reciprocal tangent uses the mean 3/4. -/
theorem asym_moment_two_jensen {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    1/(3*(1-3*t/4)^3) ≤ asymReciprocalMoment 2 t := by
  let b := 1-3*t/4
  let p : ℝ → ℝ := fun r => r^2/b^3+3*t*r^2*(r-3/4)/b^4
  have hb : 0 < b := by dsimp [b]; linarith only [ht1]
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hp.intervalIntegrable 0 1)
    ((asym_moment_cont 2 ht ht1).intervalIntegrable_of_Icc (by norm_num)) (fun r hr => ?_)
  · have hi : (∫ r in (0:ℝ)..1, p r)=1/(3*b^3) := by
      let P : ℝ → ℝ := fun r => r^3/(3*b^3)+3*t/b^4*(r^4/4-r^3/4)
      have hd (r : ℝ) : HasDerivAt P (p r) r := by
        have he := ((hasDerivAt_pow 3 r).div_const (3*b^3)).add
          ((((hasDerivAt_pow 4 r).div_const 4).sub
            ((hasDerivAt_pow 3 r).div_const 4)).const_mul (3*t/b^4))
        refine he.congr_deriv ?_
        dsimp [p]
        norm_num
        field_simp [hb.ne']
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
        (hp.intervalIntegrable 0 1)
      simpa [P] using he
    rw [hi] at hm
    exact hm
  · have hv := asym_moment_den ht ht1 hr
    have hr0 : 0 ≤ r := hr.1
    have hv1 : 1-r*t ≠ 0 := by nlinarith only [hv]
    have he : r^2/(1-t*r)^3-p r =
        t^2*r^2*(r-3/4)^2*(b^2+2*b*(1-t*r)+3*(1-t*r)^2)/(b^4*(1-t*r)^3) := by
      dsimp [p]
      field_simp [hb.ne',hv.ne',hv1]
      dsimp [b]
      ring
    have hn : 0 ≤ t^2*r^2*(r-3/4)^2*(b^2+2*b*(1-t*r)+3*(1-t*r)^2)/(b^4*(1-t*r)^3) := by
      positivity
    linarith only [he,hn]

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set MeasureTheory

local syntax "asym_deriv" : tactic
macro_rules
| `(tactic| asym_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> asym_deriv
  | apply HasDerivAt.sub <;> asym_deriv
  | apply HasDerivAt.pow <;> asym_deriv
  | apply HasDerivAt.mul <;> asym_deriv
  | apply HasDerivAt.div <;> first | asym_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> asym_deriv
  | apply HasDerivAt.log <;> first | asym_deriv | positivity | assumption)

noncomputable def asymMomentPrimitive1 (t r : ℝ) : ℝ :=
  (1/(1-t*r)+log (1-t*r)-1)/t^2
noncomputable def asymMomentPrimitive2 (t r : ℝ) : ℝ :=
  (1/(2*(1-t*r)^2)-2/(1-t*r)-log (1-t*r)+3/2)/t^3
noncomputable def asymMomentPrimitive3 (t r : ℝ) : ℝ :=
  (1/(3*(1-t*r)^3)-3/(2*(1-t*r)^2)+3/(1-t*r)+log (1-t*r)-11/6)/t^4

theorem asymMomentPrimitive1_deriv {t r : ℝ} (ht : 0 < t) (hv : 0 < 1-t*r) :
    HasDerivAt (asymMomentPrimitive1 t) (r^1/(1-t*r)^2) r := by
  unfold asymMomentPrimitive1
  apply HasDerivAt.congr_deriv
  · asym_deriv
  · norm_num [npowRec]; field_simp; ring

theorem asym_moment_1_eq {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    asymReciprocalMoment 1 t = asymMomentPrimitive1 t 1 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => asymMomentPrimitive1_deriv ht (asym_moment_den ht.le ht1 (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hr)))
    ((asym_moment_cont 1 ht.le ht1).intervalIntegrable_of_Icc (by norm_num))
  have hz : asymMomentPrimitive1 t 0 = 0 := by norm_num [asymMomentPrimitive1]
  change asymReciprocalMoment 1 t = asymMomentPrimitive1 t 1-asymMomentPrimitive1 t 0 at hi
  simpa only [hz,sub_zero] using hi

theorem asymMomentPrimitive2_deriv {t r : ℝ} (ht : 0 < t) (hv : 0 < 1-t*r) :
    HasDerivAt (asymMomentPrimitive2 t) (r^2/(1-t*r)^3) r := by
  unfold asymMomentPrimitive2
  apply HasDerivAt.congr_deriv
  · asym_deriv
  · norm_num [npowRec]; field_simp; ring

theorem asym_moment_2_eq {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    asymReciprocalMoment 2 t = asymMomentPrimitive2 t 1 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => asymMomentPrimitive2_deriv ht (asym_moment_den ht.le ht1 (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hr)))
    ((asym_moment_cont 2 ht.le ht1).intervalIntegrable_of_Icc (by norm_num))
  have hz : asymMomentPrimitive2 t 0 = 0 := by norm_num [asymMomentPrimitive2]
  change asymReciprocalMoment 2 t = asymMomentPrimitive2 t 1-asymMomentPrimitive2 t 0 at hi
  simpa only [hz,sub_zero] using hi

theorem asymMomentPrimitive3_deriv {t r : ℝ} (ht : 0 < t) (hv : 0 < 1-t*r) :
    HasDerivAt (asymMomentPrimitive3 t) (r^3/(1-t*r)^4) r := by
  unfold asymMomentPrimitive3
  apply HasDerivAt.congr_deriv
  · asym_deriv
  · norm_num [npowRec]; field_simp; ring

theorem asym_moment_3_eq {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    asymReciprocalMoment 3 t = asymMomentPrimitive3 t 1 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => asymMomentPrimitive3_deriv ht (asym_moment_den ht.le ht1 (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hr)))
    ((asym_moment_cont 3 ht.le ht1).intervalIntegrable_of_Icc (by norm_num))
  have hz : asymMomentPrimitive3 t 0 = 0 := by norm_num [asymMomentPrimitive3]
  change asymReciprocalMoment 3 t = asymMomentPrimitive3 t 1-asymMomentPrimitive3 t 0 at hi
  simpa only [hz,sub_zero] using hi

noncomputable def asymFloorT (t : ℝ) : ℝ :=
  1+(4/7)^2/(1-t)+(4/7)*log (1-t)/t
noncomputable def asymFloorT1 (t : ℝ) : ℝ :=
  (4/7)^2/(1-t)^2-(4/7)*asymMomentPrimitive1 t 1
noncomputable def asymFloorT2 (t : ℝ) : ℝ :=
  2*((4/7)^2/(1-t)^3-(4/7)*asymMomentPrimitive2 t 1)
noncomputable def asymFloorT3 (t : ℝ) : ℝ :=
  6*((4/7)^2/(1-t)^4-(4/7)*asymMomentPrimitive3 t 1)

theorem asymFloorT_deriv1 {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt asymFloorT (asymFloorT1 t) t := by
  have hv : 0 < 1-t := by linarith only [ht1]
  unfold asymFloorT asymFloorT1 asymMomentPrimitive1
  apply HasDerivAt.congr_deriv
  · asym_deriv
  · norm_num [npowRec]; field_simp; ring

theorem asymFloorT_deriv2 {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt asymFloorT1 (asymFloorT2 t) t := by
  have hv : 0 < 1-t := by linarith only [ht1]
  unfold asymFloorT1 asymFloorT2 asymMomentPrimitive1 asymMomentPrimitive2
  simp only [mul_one]
  apply HasDerivAt.congr_deriv
  · asym_deriv
  · norm_num [npowRec]; field_simp; ring

theorem asymFloorT_deriv3 {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt asymFloorT2 (asymFloorT3 t) t := by
  have hv : 0 < 1-t := by linarith only [ht1]
  unfold asymFloorT2 asymFloorT3 asymMomentPrimitive2 asymMomentPrimitive3
  simp only [mul_one]
  apply HasDerivAt.congr_deriv
  · asym_deriv
  · norm_num [npowRec]; field_simp; ring

/-- The positive-order opposite-floor kernels are positive by their actual integrals. -/
theorem asym_floor_kernel_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    0 < (4/7)^2/(1-t)^(n+1)-(4/7)*asymReciprocalMoment n t := by
  have hd : 0 < (1-t)^(n+1) := pow_pos (sub_pos.mpr ht1) _
  have hc : (2:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (show 2 ≤ n+1 by omega)
  have hI := asymReciprocalMoment_le n ht ht1
  have hI1 : asymReciprocalMoment n t ≤ 1/(2*(1-t)^(n+1)) := by
    refine hI.trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hc hd.le)
  have hI2 : (4/7)*asymReciprocalMoment n t ≤ (4/7)/(2*(1-t)^(n+1)) := by
    have hp := mul_le_mul_of_nonneg_left hI1 (by norm_num : (0:ℝ) ≤ 4/7)
    calc (4/7)*asymReciprocalMoment n t ≤ (4/7)*(1/(2*(1-t)^(n+1))) := hp
         _ = (4/7)/(2*(1-t)^(n+1)) := by ring
  have he : (4/7)^2/(1-t)^(n+1)-(4/7)/(2*(1-t)^(n+1)) = (2/49)/(1-t)^(n+1) := by field_simp; norm_num
  have hp : 0 < (2/49)/(1-t)^(n+1) := by positivity
  linarith only [hI2,he,hp]

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set

theorem asymFloorT1_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 < asymFloorT1 t := by
  unfold asymFloorT1
  rw [← asym_moment_1_eq ht ht1]
  exact asym_floor_kernel_pos (by norm_num) ht.le ht1

theorem asymFloorT2_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 < asymFloorT2 t := by
  unfold asymFloorT2
  rw [← asym_moment_2_eq ht ht1]
  exact mul_pos (by norm_num) (asym_floor_kernel_pos (by norm_num) ht.le ht1)

theorem asymFloorT3_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : 0 < asymFloorT3 t := by
  unfold asymFloorT3
  rw [← asym_moment_3_eq ht ht1]
  exact mul_pos (by norm_num) (asym_floor_kernel_pos (by norm_num) ht.le ht1)

theorem asymFloorT1_strictMono : StrictMonoOn asymFloorT1 (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro t ht; exact (asymFloorT_deriv2 ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(asymFloorT_deriv2 ht.1 ht.2).deriv]
    exact asymFloorT2_pos ht.1 ht.2

theorem asymFloorT2_strictMono : StrictMonoOn asymFloorT2 (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro t ht; exact (asymFloorT_deriv3 ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(asymFloorT_deriv3 ht.1 ht.2).deriv]
    exact asymFloorT3_pos ht.1 ht.2

/-- The density-2r reciprocal tangent gives the natural first scale-derivative cap. -/
theorem asym_floor_first_cap {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/4) :
    (9/49)*asymFloorT1 t < 1/30 := by
  have hj := asym_moment_one_jensen (t := 1/4) (by norm_num) (by norm_num)
  rw [asym_moment_1_eq (by norm_num) (by norm_num)] at hj
  norm_num at hj
  have hb : (9/49)*asymFloorT1 (1/4) < 1/30 := by
    dsimp [asymFloorT1]
    norm_num
    linarith only [hj]
  have hm := asymFloorT1_strictMono.monotoneOn
    (show t ∈ Ioo (0:ℝ) 1 by constructor <;> linarith)
    (by norm_num : (1/4:ℝ) ∈ Ioo (0:ℝ) 1) ht1
  exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 9/49)).trans_lt hb

/-- The density-3r² reciprocal tangent gives the natural second scale-derivative cap. -/
theorem asym_floor_second_cap {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/4) :
    (9/49)^2*asymFloorT2 t < 1/32 := by
  have hj := asym_moment_two_jensen (t := 1/4) (by norm_num) (by norm_num)
  rw [asym_moment_2_eq (by norm_num) (by norm_num)] at hj
  norm_num at hj
  have hb : (9/49)^2*asymFloorT2 (1/4) < 1/32 := by
    dsimp [asymFloorT2]
    norm_num
    linarith only [hj]
  have hm := asymFloorT2_strictMono.monotoneOn
    (show t ∈ Ioo (0:ℝ) 1 by constructor <;> linarith)
    (by norm_num : (1/4:ℝ) ∈ Ioo (0:ℝ) 1) ht1
  exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ (9/49)^2)).trans_lt hb

end SmoothedOctagon

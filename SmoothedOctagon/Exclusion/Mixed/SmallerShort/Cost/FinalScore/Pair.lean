module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactShape
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# S6 final score: reciprocal angle floors and the pair term
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

/-- The exact arctangent score at the genuine variance floor. -/
noncomputable def s6FinalScore (R d e : ℝ) : ℝ :=
  costBExact R (costT R d e) (s6VarianceFloor R d) (costZU R d) (costZL R d)

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


/-! The score decomposition used in the displacement and final-face arguments. -/
noncomputable def s6FinalG (a : ℝ) : ℝ := a/(2*(3+a^2))
noncomputable def s6FinalG1 (a : ℝ) : ℝ := (3-a^2)/(2*(3+a^2)^2)
noncomputable def s6FinalG2 (a : ℝ) : ℝ := a*(a^2-9)/(3+a^2)^3
noncomputable def s6FinalK (a : ℝ) : ℝ := costLExact a-a^3/(2*(3+a^2))
noncomputable def s6FinalK1 (a : ℝ) : ℝ :=
  1-(161/54)/(3+a^2)-a^2*(9+a^2)/(2*(3+a^2)^2)
noncomputable def s6FinalK2 (a : ℝ) : ℝ :=
  a*(2*(161/54)*(3+a^2)-3*(9-a^2))/(3+a^2)^3
noncomputable def s6FinalV (R d : ℝ) : ℝ := 4*s6VarianceFloor R d-3
noncomputable def s6FinalPair (R d e : ℝ) : ℝ :=
  s6FinalK R+s6FinalK (costT R d e)+s6FinalV R d*(s6FinalG R+s6FinalG (costT R d e))
noncomputable def s6FinalShearLoss (R d e : ℝ) : ℝ :=
  costZU R d*((1-4*s6VarianceFloor R d/(3+R^2))+
    (1-4*s6VarianceFloor R d/(3+(costT R d e)^2)))/8
noncomputable def s6FinalAnisotropyLoss (R d e : ℝ) : ℝ :=
  (161/54)*((R^2-(costT R d e)^2)/(3+(costT R d e)^2))^2/(8*costZL R d)

theorem s6_final_score_decomposition (R d e : ℝ) :
    s6FinalScore R d e=s6FinalPair R d e-s6FinalShearLoss R d e-
      s6FinalAnisotropyLoss R d e := by
  unfold s6FinalScore costBExact s6FinalPair s6FinalShearLoss s6FinalAnisotropyLoss
    s6FinalK s6FinalG s6FinalV
  field_simp
  ring

theorem s6_final_g_deriv (a : ℝ) : HasDerivAt s6FinalG (s6FinalG1 a) a := by
  have hp : 3+a^2 ≠ 0 := ne_of_gt (by positivity)
  have hh := (hasDerivAt_id' a).div
    (((hasDerivAt_pow 2 a).const_add 3).const_mul 2) (mul_ne_zero (by norm_num) hp)
  refine hh.congr_deriv ?_
  unfold s6FinalG1
  norm_num
  field_simp
  ring

theorem s6_final_g1_deriv (a : ℝ) : HasDerivAt s6FinalG1 (s6FinalG2 a) a := by
  have hp : 3+a^2 ≠ 0 := ne_of_gt (by positivity)
  have hh := ((hasDerivAt_pow 2 a).const_sub 3).div
    ((((hasDerivAt_pow 2 a).const_add 3).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))
  refine hh.congr_deriv ?_
  unfold s6FinalG2
  norm_num
  field_simp
  ring

theorem s6_final_k_deriv (a : ℝ) : HasDerivAt s6FinalK (s6FinalK1 a) a := by
  have hp : 3+a^2 ≠ 0 := ne_of_gt (by positivity)
  have hh := (costLExact_hasDerivAt a).sub ((hasDerivAt_pow 3 a).div
    (((hasDerivAt_pow 2 a).const_add 3).const_mul 2) (mul_ne_zero (by norm_num) hp))
  refine hh.congr_deriv ?_
  unfold s6FinalK1
  norm_num
  field_simp
  ring

theorem s6_final_k1_deriv (a : ℝ) : HasDerivAt s6FinalK1 (s6FinalK2 a) a := by
  have hp : 3+a^2 ≠ 0 := ne_of_gt (by positivity)
  have hfirst := (hasDerivAt_const a (1:ℝ)).sub
    ((hasDerivAt_const a ((161/54):ℝ)).div ((hasDerivAt_pow 2 a).const_add 3) hp)
  have hn := (hasDerivAt_pow 2 a).mul ((hasDerivAt_pow 2 a).const_add 9)
  have hd := (((hasDerivAt_pow 2 a).const_add 3).pow 2).const_mul 2
  have hh := hfirst.sub (hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)))
  refine hh.congr_deriv ?_
  unfold s6FinalK2
  norm_num
  field_simp
  ring

/-- The zero-displacement variance excess, as two increasing positive terms. -/
noncomputable def s6FinalV0 (R : ℝ) : ℝ :=
  16*R^2*(1+R)/(3*(4+3*R)^2)+3*R^4/(80*(1+R)^3)
noncomputable def s6FinalV01 (R : ℝ) : ℝ :=
  16*R*(3*R^2+12*R+8)/(3*(3*R+4)^3)+3*R^3*(R+4)/(80*(R+1)^4)

theorem s6_final_v0_deriv {R : ℝ} (hR : 0 ≤ R) :
    HasDerivAt s6FinalV0 (s6FinalV01 R) R := by
  have hp : 4+3*R ≠ 0 := ne_of_gt (by positivity)
  have hq : 1+R ≠ 0 := ne_of_gt (by positivity)
  have hnum := ((hasDerivAt_pow 2 R).const_mul 16).mul ((hasDerivAt_id' R).const_add 1)
  have hden := ((((hasDerivAt_id' R).const_mul 3).const_add 4).pow 2).const_mul 3
  have hnum2 := (hasDerivAt_pow 4 R).const_mul 3
  have hden2 := (((hasDerivAt_id' R).const_add 1).pow 3).const_mul 80
  have hh := (hnum.div hden (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))).add
    (hnum2.div hden2 (mul_ne_zero (by norm_num) (pow_ne_zero 3 hq)))
  refine hh.congr_deriv ?_
  unfold s6FinalV01
  norm_num
  field_simp
  ring

/-- The full displacement dependence of the genuine variance floor. -/
theorem s6_final_v_eq {R d : ℝ} (hR : 0 < R) (hd : 0 ≤ d) :
    s6FinalV R d=s6FinalV0 R*(2*R)/(2*R+(1+R)*d) := by
  have hM : 0 < 2*R+(1+R)*d := by positivity
  have hp : 0 < 1+R := by positivity
  have hq : 0 < 4+3*R := by positivity
  unfold s6FinalV s6VarianceFloor s6FinalV0
  field_simp
  ring

theorem s6_final_v_bounds {R d : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) :
    0 < s6FinalV R d ∧ s6FinalV R d < 1/25 := by
  have hRp : 0 < R := by linarith only [hR]
  have hv0 : 0 < s6FinalV0 R := by unfold s6FinalV0; positivity
  have hv0b := ss_le_of_deriv (f := s6FinalV0) (f' := s6FinalV01)
    (show R ≤ 3/8 by linarith only [hR1])
    (fun z hz => s6_final_v0_deriv (by linarith only [hz.1,hRp]))
    (fun z hz => by
      have hz0 : 0 < z := by linarith only [hz.1,hRp]
      unfold s6FinalV01
      positivity)
  have hv0u : s6FinalV0 R < 1/25 := by
    norm_num [s6FinalV0] at hv0b
    change s6FinalV0 R ≤ _ at hv0b
    linarith only [hv0b]
  have hM : 0 < 2*R+(1+R)*d := by positivity
  have hq : (2*R)/(2*R+(1+R)*d) ≤ 1 := by
    rw [div_le_one hM]
    have : 0 ≤ (1+R)*d := by positivity
    linarith only [this]
  rw [s6_final_v_eq hRp hd]
  refine ⟨by positivity,?_⟩
  simpa only [mul_div_assoc] using (mul_le_of_le_one_right hv0.le hq).trans_lt hv0u


noncomputable def s6FinalF (a : ℝ) : ℝ := 9*a*(a^2-1)/(3+a^2)^3
noncomputable def s6FinalF1 (a : ℝ) : ℝ :=
  -9*(3*a^4-14*a^2+3)/(3+a^2)^4

theorem s6_final_f_deriv (a : ℝ) : HasDerivAt s6FinalF (s6FinalF1 a) a := by
  have hp : 3+a^2 ≠ 0 := ne_of_gt (by positivity)
  have hn := ((hasDerivAt_id' a).const_mul 9).mul ((hasDerivAt_pow 2 a).sub_const 1)
  have hd := ((hasDerivAt_pow 2 a).const_add 3).pow 3
  have hh := hn.div hd (pow_ne_zero 3 hp)
  refine hh.congr_deriv ?_
  unfold s6FinalF1
  norm_num
  field_simp
  ring

theorem s6_final_interval {a : ℝ} (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) :
    0 < a ∧ 2/7 < a ∧ a^2 < 1/7 := by
  have hapos : 0 < a := by linarith only [ha]
  have hasq : a^2 ≤ (7/19:ℝ)^2 := by nlinarith only [hapos,ha1]
  exact ⟨hapos,by linarith only [ha],by norm_num at hasq ⊢; linarith only [hasq]⟩

theorem s6_final_k2_upper {a : ℝ} (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) :
    s6FinalK2 a < -2/25 := by
  have hh := s6_final_interval ha ha1
  have hp : 0 < 3+a^2 := by positivity
  have hid : s6FinalK2 a=s6FinalF a-a/(27*(3+a^2)^2) := by
    unfold s6FinalK2 s6FinalF
    field_simp
    ring
  have hsmall : 0 < a/(27*(3+a^2)^2) := by positivity
  have hmono := ss_le_of_deriv (f := fun z => -s6FinalF z)
    (f' := fun z => -s6FinalF1 z) hh.2.1.le
    (fun z _ => (s6_final_f_deriv z).neg) (fun z hz => ?_)
  · have hbase : s6FinalF (2/7) < -2/25 := by norm_num [s6FinalF]
    linarith only [hid,hsmall,hmono,hbase]
  · unfold s6FinalF1
    have hz0 : 0 < z := by linarith only [hz.1]
    have hzs : z^2 < 1/7 := by nlinarith only [hz.2,hh.2.2,hz0,hh.1]
    have hnum : 0 < 3*z^4-14*z^2+3 := by nlinarith only [hzs,sq_nonneg (z^2)]
    have hdiv : 0 < 9*(3*z^4-14*z^2+3)/(3+z^2)^4 := by positivity
    convert hdiv.le using 1; ring

theorem s6_final_g_bounds {a : ℝ} (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) :
    0 < s6FinalG a ∧ 1/7 < s6FinalG1 a ∧ s6FinalG1 a < 2/13 ∧ s6FinalG2 a < 0 := by
  have hh := s6_final_interval ha ha1
  have hp : 0 < 3+a^2 := by positivity
  have hs0 : 0 ≤ a^2 := sq_nonneg a
  have hs1 : a^2 < 1/7 := hh.2.2
  have hslo : (4/49:ℝ) < a^2 := by nlinarith only [hh.2.1,hh.1]
  have hs2 : (a^2)^2 < (1/7:ℝ)^2 := by nlinarith only [hs0,hs1]
  refine ⟨?_,?_,?_,?_⟩
  · unfold s6FinalG
    positivity
  · unfold s6FinalG1
    rw [lt_div_iff₀ (by positivity : 0 < 2*(3+a^2)^2)]
    nlinarith only [hs1,hs2]
  · unfold s6FinalG1
    rw [div_lt_iff₀ (by positivity : 0 < 2*(3+a^2)^2)]
    nlinarith only [hslo,sq_nonneg (a^2)]
  · unfold s6FinalG2
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg hh.1 (by linarith only [hs1])
    · positivity

/-- The pair term has a uniform small positive g-sum. -/
theorem s6_final_g_sum_bounds {R T : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hT : 9/31 ≤ T) (hTR : T ≤ R) :
    0 < s6FinalG R+s6FinalG T ∧ s6FinalG R+s6FinalG T < 2/17 := by
  have hgR := s6_final_g_bounds (show 9/31 ≤ R by linarith only [hR]) hR1
  have hgT := s6_final_g_bounds hT (hTR.trans hR1)
  have hmax (a : ℝ) (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) : s6FinalG a ≤ s6FinalG (7/19) := by
    exact ss_le_of_deriv ha1 (fun z _ => s6_final_g_deriv z)
      (fun z hz => by
        have hh := (s6_final_g_bounds (ha.trans hz.1.le) hz.2.le).2.1
        linarith only [hh])
  have hRb := hmax R (by linarith only [hR]) hR1
  have hTb := hmax T hT (hTR.trans hR1)
  refine ⟨by linarith only [hgR.1,hgT.1],?_⟩
  norm_num [s6FinalG] at hRb hTb
  change s6FinalG R ≤ _ at hRb
  change s6FinalG T ≤ _ at hTb
  linarith only [hRb,hTb]


private theorem s6_final_k2_neg {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    s6FinalK2 a < 0 := by
  unfold s6FinalK2
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg ha
    have hs : a^2 < 1 := by nlinarith only [ha,ha1]
    nlinarith only [hs]
  · positivity

theorem s6_final_k1_neg {a : ℝ} (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) :
    s6FinalK1 a < 0 := by
  have hmono := ss_le_of_deriv (f := fun z => -s6FinalK1 z)
    (f' := fun z => -s6FinalK2 z) (show 1/4 ≤ a by linarith only [ha])
    (fun z _ => (s6_final_k1_deriv z).neg) (fun z hz => by
      have hh := s6_final_k2_neg (show 0 < z by linarith only [hz.1])
        (show z < 1 by linarith only [hz.2,ha1])
      linarith only [hh])
  have hbase : s6FinalK1 (1/4) < 0 := by norm_num [s6FinalK1]
  linarith only [hmono,hbase]

noncomputable def s6FinalH (s : ℝ) : ℝ := (-27*s^2+80*s-3)/(54*s*(3+s)^2)
noncomputable def s6FinalH1 (s : ℝ) : ℝ := (27*s^3-241*s^2+9*s+9)/(54*s^2*(3+s)^3)

private theorem s6_final_h_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt s6FinalH (s6FinalH1 s) s := by
  have hp : 3+s ≠ 0 := ne_of_gt (by positivity)
  have hn := (((hasDerivAt_pow 2 s).const_mul (-27)).add
    ((hasDerivAt_id' s).const_mul 80)).sub_const 3
  have hd := ((hasDerivAt_id' s).const_mul 54).mul
    (((hasDerivAt_id' s).const_add 3).pow 2)
  have hh := hn.div hd (by positivity : 54*s*(3+s)^2 ≠ 0)
  refine hh.congr_deriv ?_
  unfold s6FinalH1
  norm_num
  field_simp
  ring

/-- The exact logarithmic-free bound for the initial pair derivative. -/
theorem s6_final_k1_lower {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    -(5/48)*R^2 < s6FinalK1 R := by
  have hRp : 0 < R := by linarith only [hR]
  have hs : 0 < R^2 := sq_pos_of_pos hRp
  have hs1 : R^2 < 1/7 := (s6_final_interval (by linarith only [hR]) hR1).2.2
  have hm := ss_le_of_deriv (f := s6FinalH) (f' := s6FinalH1) hs1.le
    (fun s hs0 => s6_final_h_deriv (hs.trans_le hs0.1)) (fun s hs0 => ?_)
  · have hb : s6FinalH (1/7) < 5/48 := by norm_num [s6FinalH]
    have hid : s6FinalK1 R= -R^2*s6FinalH (R^2) := by
      unfold s6FinalK1 s6FinalH
      field_simp
      ring
    have hh := mul_lt_mul_of_pos_left (hm.trans_lt hb) hs
    nlinarith only [hid,hh]
  · have hsp : 0 < s := hs.trans_le hs0.1.le
    have hss : s^2 < (1/7:ℝ)^2 := by nlinarith only [hs0.2,hsp]
    unfold s6FinalH1
    apply div_nonneg
    · have h3 : 0 < s^3 := by positivity
      nlinarith only [hss,hsp,h3]
    · positivity

noncomputable def s6FinalFloorFactor (R : ℝ) : ℝ := (1+R)/(3*(1+3*R/4)^2)
theorem s6_final_floor_factor_deriv {R : ℝ} (hR : 0 ≤ R) :
    HasDerivAt s6FinalFloorFactor (-(16*(3*R+2))/(3*(3*R+4)^3)) R := by
  have hp : 1+3*R/4 ≠ 0 := ne_of_gt (by positivity)
  have hn := (hasDerivAt_id' R).const_add 1
  have hd := (((((hasDerivAt_id' R).const_mul 3).div_const 4).const_add 1).pow 2).const_mul 3
  have hh := hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))
  refine hh.congr_deriv ?_
  norm_num
  field_simp
  ring

theorem s6_final_v0_lower {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    (5/18)*R^2 < s6FinalV0 R := by
  have hRp : 0 < R := by linarith only [hR]
  have hf := ss_le_of_deriv (f := fun r => -s6FinalFloorFactor r)
    (f' := fun r => (16*(3*r+2))/(3*(3*r+4)^3))
    (show R ≤ 3/8 by linarith only [hR1])
    (fun r hr => by
      have hh := (s6_final_floor_factor_deriv (show 0 ≤ r by linarith only [hr.1,hRp])).neg
      convert hh using 1; ring)
    (fun r hr => by
      have hrp : 0 < r := by linarith only [hr.1,hRp]
      positivity)
  have hff : (5/18:ℝ) < s6FinalFloorFactor R := by
    have hnum : (5/18:ℝ) < s6FinalFloorFactor (3/8) := by norm_num [s6FinalFloorFactor]
    linarith only [hf,hnum]
  have hid : s6FinalV0 R=R^2*s6FinalFloorFactor R+3*R^4/(80*(1+R)^3) := by
    unfold s6FinalV0 s6FinalFloorFactor
    field_simp
    ring
  have htail : 0 < 3*R^4/(80*(1+R)^3) := by positivity
  have hh := mul_lt_mul_of_pos_left hff (sq_pos_of_pos hRp)
  nlinarith only [hid,htail,hh]


noncomputable def s6FinalGamma (R e : ℝ) : ℝ := e+1-(e-1)*R
noncomputable def s6FinalL (R d e : ℝ) : ℝ := 2+s6FinalGamma R e*d
noncomputable def s6FinalM (R d : ℝ) : ℝ := 2*R+(1+R)*d
noncomputable def s6FinalChi (R d e : ℝ) : ℝ :=
  (s6FinalL R d e)^2/(2*(e-1)*(1-R)*s6FinalM R d)

theorem s6_final_box_denoms {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < R ∧ 0 < 1-R ∧ 0 < e-1 ∧ 3 < s6FinalGamma R e ∧
    s6FinalGamma R e < 4 ∧ 0 < s6FinalL R d e ∧ 0 < s6FinalM R d ∧ s6FinalL R d e < 3 := by
  have hRp : 0 < R := by linarith only [hR]
  have hRone : 0 < 1-R := by linarith only [hR1]
  have hep : 0 < e-1 := by linarith only [he]
  have hprod := mul_le_mul (show (8/5:ℝ) ≤ e-1 by linarith only [he])
    (show (12/19:ℝ) ≤ 1-R by linarith only [hR1]) (by norm_num) hep.le
  have hGammaId : s6FinalGamma R e=2+(e-1)*(1-R) := by unfold s6FinalGamma; ring
  have hGlow : 3 < s6FinalGamma R e := by linarith only [hprod,hGammaId]
  have hGhi : s6FinalGamma R e < 4 := by
    have hmul := mul_le_mul (show e-1 ≤ 2 by linarith only [he1])
      (show 1-R ≤ 2/3 by linarith only [hR]) hRone.le (by norm_num : (0:ℝ) ≤ 2)
    linarith only [hmul,hGammaId]
  have hL : 0 < s6FinalL R d e := by unfold s6FinalL; nlinarith only [hGlow,hd]
  have hM : 0 < s6FinalM R d := by unfold s6FinalM; positivity
  refine ⟨hRp,hRone,hep,hGlow,hGhi,hL,hM,?_⟩
  unfold s6FinalL
  nlinarith only [hGhi,hd,hd1]

noncomputable def s6FinalChiD (R d e : ℝ) : ℝ :=
  s6FinalChi R d e*(2*s6FinalGamma R e/s6FinalL R d e-(1+R)/s6FinalM R d)
noncomputable def s6FinalChiR (R d e : ℝ) : ℝ :=
  s6FinalChi R d e*(-2*(e-1)*d/s6FinalL R d e+
    (4*R-2+2*R*d)/((1-R)*s6FinalM R d))
noncomputable def s6FinalChiE (R d e : ℝ) : ℝ :=
  s6FinalChi R d e*((e-1)*(1-R)*d-2-2*d)/((e-1)*s6FinalL R d e)

private theorem s6_final_chi_deriv_d {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalChi R d e) (s6FinalChiD R d e) d := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hLn : 2+s6FinalGamma R e*d ≠ 0 := hLp.ne'
  have hMn : 2*R+(1+R)*d ≠ 0 := hMp.ne'
  have hn := ((((hasDerivAt_id' d).const_mul (s6FinalGamma R e)).const_add 2).pow 2)
  have hh := hn.div (((((hasDerivAt_id' d).const_mul (1+R)).const_add (2*R)).const_mul
    (2*(e-1)*(1-R)))) (by dsimp [s6FinalM] at hMp; positivity)
  refine hh.congr_deriv ?_
  unfold s6FinalChiD s6FinalChi s6FinalL s6FinalM
  norm_num
  field_simp [hLn,hMn,hep.ne',hRm.ne']

private theorem s6_final_chi_deriv_r {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun R => s6FinalChi R d e) (s6FinalChiR R d e) R := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hLn : 2+s6FinalGamma R e*d ≠ 0 := hLp.ne'
  have hMn : 2*R+(1+R)*d ≠ 0 := hMp.ne'
  have hn := (((((hasDerivAt_id' R).const_mul (e-1)).const_sub (e+1)).mul_const d).const_add 2).pow 2
  have hd0 := (((hasDerivAt_id' R).const_sub 1).const_mul (2*(e-1))).mul
    (((hasDerivAt_id' R).const_mul 2).add (((hasDerivAt_id' R).const_add 1).mul_const d))
  have hh := hn.div hd0 (by dsimp; positivity)
  refine hh.congr_deriv ?_
  unfold s6FinalChiR s6FinalChi s6FinalL s6FinalM
  norm_num
  field_simp [hLn,hMn,hep.ne',hRm.ne']
  unfold s6FinalGamma
  ring

private theorem s6_final_chi_deriv_e {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun e => s6FinalChi R d e) (s6FinalChiE R d e) e := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hLn : 2+s6FinalGamma R e*d ≠ 0 := hLp.ne'
  have hMn : 2*R+(1+R)*d ≠ 0 := hMp.ne'
  have hn := (((((hasDerivAt_id' e).const_add 1).sub
    (((hasDerivAt_id' e).sub_const 1).mul_const R)).mul_const d).const_add 2).pow 2
  have hd0 := ((((hasDerivAt_id' e).sub_const 1).const_mul 2).mul_const (1-R)).mul_const (s6FinalM R d)
  have hh := hn.div hd0 (by dsimp; positivity)
  convert hh using 1
  · funext z
    dsimp [s6FinalChi,s6FinalL,s6FinalGamma]
    ring
  · unfold s6FinalChiE s6FinalChi s6FinalL s6FinalM
    norm_num
    field_simp [hLn,hMn,hep.ne',hRm.ne']
    unfold s6FinalGamma
    ring


private theorem s6_final_chi_signs {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalChi R d e ∧ 0 < s6FinalChiD R d e ∧
    s6FinalChiR R d e < 0 ∧ s6FinalChiE R d e < 0 := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hc : 0 < s6FinalChi R d e := by unfold s6FinalChi; positivity
  have hD : 0 < s6FinalChiD R d e := by
    unfold s6FinalChiD
    apply mul_pos hc
    apply sub_pos.2
    rw [div_lt_div_iff₀ hMp hLp]
    have hprod := mul_le_mul (show (3:ℝ) ≤ s6FinalGamma R e by linarith only [hGlo])
      hR (by norm_num) (by linarith only [hGlo] : 0 ≤ s6FinalGamma R e)
    have hterm : 0 ≤ s6FinalGamma R e*(1+R)*d := by positivity
    dsimp [s6FinalL,s6FinalM]
    nlinarith only [hprod,hR1,hterm]
  have hDR : s6FinalChiR R d e < 0 := by
    have hprod := mul_le_mul hR1 hd1 hd (by norm_num : (0:ℝ) ≤ 7/19)
    have hnum : 4*R-2+2*R*d < 0 := by nlinarith only [hR1,hprod]
    have hfrac : (4*R-2+2*R*d)/((1-R)*s6FinalM R d) < 0 := by
      exact div_neg_of_neg_of_pos hnum (mul_pos hRm hMp)
    have hfirst : -2*(e-1)*d/s6FinalL R d e ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ 2*(e-1)*d := by positivity
        linarith only [this]
      · exact hLp.le
    unfold s6FinalChiR
    exact mul_neg_of_pos_of_neg hc (by linarith only [hfirst,hfrac])
  have hDE : s6FinalChiE R d e < 0 := by
    have hprod := mul_le_mul (show e-1 ≤ 2 by linarith only [he1])
      (show 1-R ≤ 2/3 by linarith only [hR]) hRm.le (by norm_num : (0:ℝ) ≤ 2)
    have hprod2 := mul_le_mul hprod hd1 hd (by norm_num : (0:ℝ) ≤ 2*(2/3))
    have hnum : (e-1)*(1-R)*d-2-2*d < 0 := by nlinarith only [hprod2,hd]
    unfold s6FinalChiE
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc hnum) (mul_pos hep hLp)
  exact ⟨hc,hD,hDR,hDE⟩

/-- The three partial derivatives reduce chi to the natural far corner. -/
theorem s6_final_chi_bounds {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalChi R d e ∧ s6FinalChi R d e < 3 ∧ 0 < s6FinalChiD R d e := by
  have hb := s6_final_chi_signs hR hR1 hd hd1 he he1
  have hmd := ss_le_of_deriv hd1
    (fun y hy => s6_final_chi_deriv_d hR hR1 (hd.trans hy.1) hy.2 he he1)
    (fun y hy => (s6_final_chi_signs hR hR1 (hd.trans hy.1.le) hy.2.le he he1).2.1.le)
  have hmr := ss_le_of_deriv (f := fun R => -s6FinalChi R (1/19) e)
    (f' := fun R => -s6FinalChiR R (1/19) e) hR
    (fun y hy => (s6_final_chi_deriv_r hy.1 (hy.2.trans hR1) (by norm_num)
      (by norm_num) he he1).neg)
    (fun y hy => by
      have hs := (s6_final_chi_signs (R:=y) (d:=1/19) (e:=e) hy.1.le (hy.2.le.trans hR1)
        (by norm_num) (by norm_num) he he1).2.2.1
      linarith only [hs])
  have hme := ss_le_of_deriv (f := fun e => -s6FinalChi (1/3) (1/19) e)
    (f' := fun e => -s6FinalChiE (1/3) (1/19) e) he
    (fun y hy => (s6_final_chi_deriv_e (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hy.1 (hy.2.trans he1)).neg)
    (fun y hy => by
      have hs := (s6_final_chi_signs (R:=1/3) (d:=1/19) (e:=y) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hy.1.le (hy.2.le.trans he1)).2.2.2
      linarith only [hs])
  have hcorner : s6FinalChi (1/3) (1/19) (13/5) < 3 := by
    norm_num [s6FinalChi,s6FinalL,s6FinalM,s6FinalGamma]
  exact ⟨hb.1,by linarith only [hmd,hmr,hme,hcorner],hb.2.1⟩


noncomputable def s6FinalTD (R d e : ℝ) : ℝ :=
  -2*(e-1)*(1-R^2)/(s6FinalL R d e)^2
noncomputable def s6FinalVNum (R : ℝ) : ℝ :=
  (2*(1+R)*R^3/3)*(1/(1+3*R/4)^2+9*R^2/(80*(1+R)^4))

private theorem s6_final_v_num_eq (R d : ℝ) :
    s6FinalV R d=s6FinalVNum R/s6FinalM R d := by
  unfold s6FinalV s6VarianceFloor s6FinalVNum s6FinalM
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem s6_final_t_displacement_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => costT R d e) (s6FinalTD R d e) d := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hn := ((hasDerivAt_id' d).const_mul ((e+1)*R-(e-1))).const_add (2*R)
  have hd0 := ((hasDerivAt_id' d).const_mul (s6FinalGamma R e)).const_add 2
  have hh := hn.div hd0 hLp.ne'
  refine hh.congr_deriv ?_
  unfold s6FinalTD s6FinalL s6FinalGamma
  norm_num
  field_simp
  ring

theorem s6_final_v_displacement_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalV R d)
      (s6FinalV R d*s6FinalChi R d e*s6FinalTD R d e) d := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hd0 := ((hasDerivAt_id' d).const_mul (1+R)).const_add (2*R)
  have hh := (hasDerivAt_const d (s6FinalVNum R)).div hd0 hMp.ne'
  have hfun : (fun d => s6FinalV R d)=(fun d => s6FinalVNum R/s6FinalM R d) :=
    funext (fun d => s6_final_v_num_eq R d)
  rw [hfun]
  refine hh.congr_deriv ?_
  rw [s6_final_v_num_eq]
  unfold s6FinalChi s6FinalTD
  have hLn : 2+s6FinalGamma R e*d ≠ 0 := hLp.ne'
  have hMn : 2*R+(1+R)*d ≠ 0 := hMp.ne'
  unfold s6FinalL s6FinalM
  norm_num
  field_simp [hLn,hMn,hep.ne',hRm.ne']
  ring

theorem s6_final_td_neg {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : s6FinalTD R d e < 0 := by
  rcases s6_final_box_denoms hR hR1 hd hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hRs : R^2 < 1 := by nlinarith only [hRp,hRm]
  unfold s6FinalTD
  exact div_neg_of_neg_of_pos (by nlinarith only [mul_pos hep (sub_pos.2 hRs)]) (sq_pos_of_pos hLp)

noncomputable def s6FinalPairSlope (R d e : ℝ) : ℝ :=
  s6FinalK1 (costT R d e)+s6FinalV R d*s6FinalG1 (costT R d e)+
    s6FinalV R d*s6FinalChi R d e*(s6FinalG R+s6FinalG (costT R d e))
noncomputable def s6FinalPairSlopeD (R d e : ℝ) : ℝ :=
  s6FinalTD R d e*(s6FinalK2 (costT R d e)+
    2*s6FinalV R d*s6FinalChi R d e*s6FinalG1 (costT R d e)+
    s6FinalV R d*(s6FinalChi R d e)^2*(s6FinalG R+s6FinalG (costT R d e))+
    s6FinalV R d*s6FinalG2 (costT R d e))+
    s6FinalV R d*s6FinalChiD R d e*(s6FinalG R+s6FinalG (costT R d e))

private theorem s6_final_pair_displacement_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalPair R d e)
      (s6FinalTD R d e*s6FinalPairSlope R d e) d := by
  have hT := s6_final_t_displacement_deriv hR hR1 hd hd1 he he1
  have hV := s6_final_v_displacement_deriv hR hR1 hd hd1 he he1
  have hK := (s6_final_k_deriv (costT R d e)).comp d hT
  have hG := (s6_final_g_deriv (costT R d e)).comp d hT
  have hh := ((hasDerivAt_const d (s6FinalK R)).add hK).add
    (hV.mul ((hasDerivAt_const d (s6FinalG R)).add hG))
  refine hh.congr_deriv ?_
  unfold s6FinalPairSlope
  dsimp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply]
  ring

private theorem s6_final_pair_slope_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalPairSlope R d e) (s6FinalPairSlopeD R d e) d := by
  have hT := s6_final_t_displacement_deriv hR hR1 hd hd1 he he1
  have hV := s6_final_v_displacement_deriv hR hR1 hd hd1 he he1
  have hC := s6_final_chi_deriv_d hR hR1 hd hd1 he he1
  have hK := (s6_final_k1_deriv (costT R d e)).comp d hT
  have hG1 := (s6_final_g1_deriv (costT R d e)).comp d hT
  have hG := (s6_final_g_deriv (costT R d e)).comp d hT
  have hh := (hK.add (hV.mul hG1)).add
    ((hV.mul hC).mul ((hasDerivAt_const d (s6FinalG R)).add hG))
  refine hh.congr_deriv ?_
  unfold s6FinalPairSlopeD
  dsimp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply]
  ring

/-- The positive pair-slope derivative uses only the paper's four uniform bounds. -/
private theorem s6_final_pair_slopeD_pos {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : 0 < s6FinalPairSlopeD R d e := by
  have hT := costT_correlated_bounds hR hR1 hd hd1 he he1
  have hTlo : 9/31 ≤ costT R d e := by linarith only [hT.1,hR]
  have hThi := hT.2.trans hR1
  have hV := s6_final_v_bounds hR hR1 hd
  have hC := s6_final_chi_bounds hR hR1 hd hd1 he he1
  have hG := s6_final_g_bounds hTlo hThi
  have hGs := s6_final_g_sum_bounds hR hR1 hTlo hT.2
  have hK := s6_final_k2_upper hTlo hThi
  have hvp := hV.1
  have hcp := hC.1
  have hcdp := hC.2.2
  have hgsp := hGs.1
  have hgp : 0 < s6FinalG1 (costT R d e) := by linarith only [hG.2.1]
  have hA : 2*s6FinalV R d*s6FinalChi R d e*s6FinalG1 (costT R d e) <
      2*(1/25)*3*(2/13) := by
    gcongr
    all_goals first | exact hV.2 | exact hC.2.1 | exact hG.2.2.1
  have hB : s6FinalV R d*(s6FinalChi R d e)^2*(s6FinalG R+s6FinalG (costT R d e)) <
      (1/25)*3^2*(2/17) := by
    gcongr
    all_goals first | exact hV.2 | exact hC.2.1 | exact hGs.2
  have hCneg : s6FinalV R d*s6FinalG2 (costT R d e) < 0 :=
    mul_neg_of_pos_of_neg hV.1 hG.2.2.2
  have hbracket : s6FinalK2 (costT R d e)+
      2*s6FinalV R d*s6FinalChi R d e*s6FinalG1 (costT R d e)+
      s6FinalV R d*(s6FinalChi R d e)^2*(s6FinalG R+s6FinalG (costT R d e))+
      s6FinalV R d*s6FinalG2 (costT R d e) < 0 := by
    linarith only [hK,hA,hB,hCneg]
  have hterm := mul_pos_of_neg_of_neg (s6_final_td_neg hR hR1 hd hd1 he he1) hbracket
  have htail : 0 < s6FinalV R d*s6FinalChiD R d e*(s6FinalG R+s6FinalG (costT R d e)) := by positivity
  unfold s6FinalPairSlopeD
  linarith only [hterm,htail]


private theorem s6_final_initial_bracket {R e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    3/8 < s6FinalG1 R+1/((e-1)*(1-R)*(3+R^2)) := by
  have hRp : 0 < R := by linarith only [hR]
  have hRm : 0 < 1-R := by linarith only [hR1]
  have hep : 0 < e-1 := by linarith only [he]
  have hfactor : 0 ≤ (3*R-1)*(9*R^2-6*R+25) := by
    have hsecond : 0 < 9*R^2-6*R+25 := by nlinarith only [sq_nonneg (3*R-1)]
    exact mul_nonneg (by linarith only [hR]) hsecond.le
  have hbase : (1-R)*(3+R^2) ≤ 56/27 := by nlinarith only [hfactor]
  have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ e-1 by linarith only [he])
  have hden : (e-1)*(1-R)*(3+R^2) ≤ 112/27 := by nlinarith only [hmul,he1]
  have hinv : (27/112:ℝ) ≤ 1/((e-1)*(1-R)*(3+R^2)) := by
    rw [le_div_iff₀ (by positivity : 0 < (e-1)*(1-R)*(3+R^2))]
    nlinarith only [hden]
  have hg := (s6_final_g_bounds (show 9/31 ≤ R by linarith only [hR]) hR1).2.1
  linarith only [hinv,hg]

private theorem s6_final_initial_slope_eq {R e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he : 13/5 ≤ e) :
    s6FinalPairSlope R 0 e=s6FinalK1 R+s6FinalV0 R*
      (s6FinalG1 R+1/((e-1)*(1-R)*(3+R^2))) := by
  have hRp : 0 < R := by linarith only [hR]
  have hRm : 0 < 1-R := by linarith only [hR1]
  have hep : 0 < e-1 := by linarith only [he]
  unfold s6FinalPairSlope
  rw [costT_zero_displacement,s6_final_v_eq hRp (by norm_num)]
  unfold s6FinalChi s6FinalL s6FinalM s6FinalG
  norm_num
  field_simp [hRp.ne',hRm.ne',hep.ne']
  ring

private theorem s6_final_initial_slope_pos {R e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalPairSlope R 0 e := by
  have hRp : 0 < R := by linarith only [hR]
  have hk := s6_final_k1_lower hR hR1
  have hv := s6_final_v0_lower hR hR1
  have hb := s6_final_initial_bracket hR hR1 he he1
  have hbp : 0 < s6FinalG1 R+1/((e-1)*(1-R)*(3+R^2)) := by linarith only [hb]
  have hmul := mul_lt_mul_of_pos_right hv hbp
  have hmul2 := mul_lt_mul_of_pos_left hb (show 0 < (5/18:ℝ)*R^2 by positivity)
  rw [s6_final_initial_slope_eq hR hR1 he]
  nlinarith only [hk,hmul,hmul2]

/-- The entire pair term strictly decreases in displacement, including the d=0 derivative. -/
theorem s6_final_pair_derivative_neg {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalTD R d e*s6FinalPairSlope R d e < 0 := by
  have hm := ss_le_of_deriv (f := fun d => s6FinalPairSlope R d e)
    (f' := fun d => s6FinalPairSlopeD R d e) hd
    (fun y hy => s6_final_pair_slope_deriv hR hR1 hy.1 (hy.2.trans hd1) he he1)
    (fun y hy => (s6_final_pair_slopeD_pos hR hR1 hy.1.le (hy.2.le.trans hd1) he he1).le)
  have hinit := s6_final_initial_slope_pos hR hR1 he he1
  have hpos : 0 < s6FinalPairSlope R d e := by linarith only [hm,hinit]
  exact mul_neg_of_neg_of_pos (s6_final_td_neg hR hR1 hd hd1 he he1) hpos

theorem s6_final_pair_antitone_displacement {R d v e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hdv : d ≤ v) (hv : v ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : s6FinalPair R v e ≤ s6FinalPair R d e := by
  have hm := ss_le_of_deriv (f := fun d => -s6FinalPair R d e)
    (f' := fun d => -(s6FinalTD R d e*s6FinalPairSlope R d e)) hdv
    (fun y hy => (s6_final_pair_displacement_deriv hR hR1 (hd.trans hy.1) (hy.2.trans hv) he he1).neg)
    (fun y hy => by
      have hs := s6_final_pair_derivative_neg hR hR1 (hd.trans hy.1.le) (hy.2.le.trans hv) he he1
      linarith only [hs])
  linarith only [hm]

end SmoothedOctagon

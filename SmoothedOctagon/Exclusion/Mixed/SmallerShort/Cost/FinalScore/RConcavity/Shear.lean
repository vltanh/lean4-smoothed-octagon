module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Basic

/-!
# S6 maximal displacement: shear-loss curvature

The upper shear envelope and the two norm deficits have positive first and
second derivatives. The full product rule gives curvature above `2/45`.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRZ01 (R : ℝ) : ℝ := -4*R-8+72/(3-R)^2
noncomputable def s6FinalRZ02 (R : ℝ) : ℝ := -4+144/(3-R)^3
noncomputable def s6FinalRZ1 (R : ℝ) : ℝ := s6FinalRZ01 R+1/(19*(1-R)^2)
noncomputable def s6FinalRZ2 (R : ℝ) : ℝ := s6FinalRZ02 R+2/(19*(1-R)^3)

private theorem s6_final_rz_derivatives {R : ℝ} (_hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    HasDerivAt (fun R => costZU R (1/19)) (s6FinalRZ1 R) R ∧
    HasDerivAt s6FinalRZ1 (s6FinalRZ2 R) R ∧
    HasDerivAt s6FinalRZ01 (s6FinalRZ02 R) R := by
  have ha : 3-R ≠ 0 := by linarith only [hR1]
  have hb : 1-R ≠ 0 := by linarith only [hR1]
  have hid := hasDerivAt_id R
  have h0 := (((hid.const_mul 4).neg.sub_const 8).add
    ((hasDerivAt_const R (72:ℝ)).div ((hid.const_sub 3).pow 2) (pow_ne_zero 2 ha)))
  have h0' : HasDerivAt s6FinalRZ01 (s6FinalRZ02 R) R := by
    convert h0 using 1
    · ext x; simp only [s6FinalRZ01,id,Pi.add_apply,Pi.div_apply,Pi.pow_apply,Pi.neg_apply]; ring
    · simp only [s6FinalRZ02,id,Pi.pow_apply]
      field_simp
      ring
  have hz01 : HasDerivAt (fun R => 2*R^2*(1+R)/(3-R)) (s6FinalRZ01 R) R := by
    have hh := (((hasDerivAt_pow 2 R).const_mul 2).mul (hid.const_add 1)).div
      (hid.const_sub 3) ha
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRZ01,id,Pi.mul_apply]
      field_simp
      ring
  have hA := ((hasDerivAt_const R (1:ℝ)).add (hid.const_mul 2)).div
    ((hid.const_sub 1).const_mul 3) (by simpa using mul_ne_zero (show (3:ℝ)≠0 by norm_num) hb)
  have hZ := ((hz01.add (hA.mul_const (1/19))).sub_const ((3/2:ℝ)*(1/19)^2))
  have hZ' := h0'.add ((hasDerivAt_const R (1:ℝ)).div
    (((hid.const_sub 1).pow 2).const_mul 19) (by simpa using mul_ne_zero (show (19:ℝ)≠0 by norm_num) (pow_ne_zero 2 hb)))
  refine ⟨?_,?_,h0'⟩
  · convert hZ using 1
    · ext x; rfl
    · simp only [s6FinalRZ1,id,s6FinalRZ01,Pi.add_apply]
      field_simp
      ring
  · convert hZ' using 1
    · ext x; rfl
    · simp only [s6FinalRZ2,id,Pi.pow_apply]
      field_simp
      ring

private theorem s6_final_rz_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    1/9 < costZU R (1/19) ∧ 3/4 < s6FinalRZ1 R ∧ 0 < s6FinalRZ2 R := by
  have hR0 : 0 < R := by linarith only [hR]
  have hRm : 0 < 1-R := by linarith only [hR1]
  have hR3 : 0 < 3-R := by linarith only [hR1]
  have h02 (z : ℝ) (hz : 1/3 ≤ z) (hz1 : z ≤ 7/19) : 0 < s6FinalRZ02 z := by
    have hz3 : 0 < 3-z := by linarith only [hz1]
    have hb : (144/(8/3)^3:ℝ) ≤ 144/(3-z)^3 := by gcongr ; linarith only [hz,hz1]
    unfold s6FinalRZ02
    linarith only [hb]
  have hm := ss_le_of_deriv (f := s6FinalRZ01) (f' := s6FinalRZ02) hR
    (fun z hz => (s6_final_rz_derivatives hz.1 (hz.2.trans hR1)).2.2)
    (fun z hz => (h02 z hz.1.le (hz.2.le.trans hR1)).le)
  have hz01 : 19/24 ≤ s6FinalRZ01 R := by
    norm_num [s6FinalRZ01] at hm
    simpa only [s6FinalRZ01,neg_mul] using hm
  have hZ0 : (1/9:ℝ) ≤ 2*R^2*(1+R)/(3-R) := by
    have hb : (2*(1/3)^2*(4/3)/(8/3):ℝ) ≤ 2*R^2*(1+R)/(3-R) := by
      gcongr <;> linarith only [hR,hR1]
    norm_num at hb
    exact hb
  have hA : (5/6:ℝ) ≤ (1+2*R)/(3*(1-R)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hR]
  refine ⟨?_,?_,?_⟩
  · unfold costZU
    linarith only [hZ0,hA]
  · unfold s6FinalRZ1
    have hh : 0 < 1/(19*(1-R)^2) := by positivity
    linarith only [hz01,hh]
  · unfold s6FinalRZ2
    have hh : 0 < 2/(19*(1-R)^3) := by positivity
    linarith only [h02 R hR hR1,hh]

noncomputable def s6FinalRB (a v : ℝ) : ℝ := 1-(3+v)/(3+a^2)
noncomputable def s6FinalRB1 (a a1 v v1 : ℝ) : ℝ :=
  2*a*a1*(3+v)/(3+a^2)^2-v1/(3+a^2)
noncomputable def s6FinalRB2 (a a1 a2 v v1 v2 : ℝ) : ℝ :=
  6*(3+v)*(1-a^2)*a1^2/(3+a^2)^3+
  (2*a*(3+v)*a2+4*a*a1*v1)/(3+a^2)^2-v2/(3+a^2)

private theorem s6_final_rb_deriv {f v : ℝ → ℝ} {a a1 b b1 x : ℝ}
    (hf : HasDerivAt f a1 x) (hv : HasDerivAt v b1 x) (heq : f x=a) (heqv : v x=b) :
    HasDerivAt (fun x => s6FinalRB (f x) (v x)) (s6FinalRB1 a a1 b b1) x := by
  have hp : 3+(f x)^2 ≠ 0 := ne_of_gt (by positivity)
  have hh := (hasDerivAt_const x (1:ℝ)).sub
    ((hv.const_add 3).div ((hf.pow 2).const_add 3) hp)
  convert hh using 1
  · ext x; rfl
  · simp only [s6FinalRB1, Pi.pow_apply, heq, heqv]
    field_simp
    ring

private theorem s6_final_rb1_deriv {f f1 v v1 : ℝ → ℝ} {a a1 a2 b b1 b2 x : ℝ}
    (hf : HasDerivAt f a1 x) (hf1 : HasDerivAt f1 a2 x)
    (hv : HasDerivAt v b1 x) (hv1 : HasDerivAt v1 b2 x)
    (ha : f x=a) (ha1 : f1 x=a1) (hb : v x=b) (hb1 : v1 x=b1) :
    HasDerivAt (fun x => s6FinalRB1 (f x) (f1 x) (v x) (v1 x))
      (s6FinalRB2 a a1 a2 b b1 b2) x := by
  have hp : 3+(f x)^2 ≠ 0 := ne_of_gt (by positivity)
  have hh := ((((hf.const_mul 2).mul hf1).mul (hv.const_add 3)).div
    (((hf.pow 2).const_add 3).pow 2) (pow_ne_zero 2 hp)).sub
    (hv1.div ((hf.pow 2).const_add 3) hp)
  convert hh using 1
  · ext x; rfl
  · simp only [s6FinalRB2, Pi.pow_apply, Pi.mul_apply, ha, ha1, hb, hb1]
    field_simp
    ring

private theorem s6_final_rb_bounds {a a1 a2 v v1 v2 : ℝ}
    (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) (hf1 : 1 ≤ a1) (hf2 : 0 ≤ a2)
    (hv : 0 < v) (hv0 : v < 1/25) (hv1 : 0 < v1) (hv1u : v1 < 1/5)
    (hv2 : v2 < 3/5) :
    0 < s6FinalRB a v ∧ 1/10 < s6FinalRB1 a a1 v v1 ∧
      1/4 < s6FinalRB2 a a1 a2 v v1 v2 := by
  have hap : 0 < a := by linarith only [ha]
  have ha1p : 0 < a1 := by linarith only [hf1]
  have hasq : a^2 < 1/7 := by nlinarith only [hap,ha1]
  have hd : 0 < 3+a^2 := by positivity
  have hden : 3+a^2 ≤ 22/7 := by linarith only [hasq]
  have hb0 : 0 < s6FinalRB a v := by
    unfold s6FinalRB
    rw [sub_pos,div_lt_one hd]
    nlinarith only [ha,hap,hv0]
  have hb1 : 1/10 < s6FinalRB1 a a1 v v1 := by
    have hfirst : (6*(9/31)/(22/7)^2:ℝ) ≤ 2*a*a1*(3+v)/(3+a^2)^2 := by
      have hthree : (3:ℝ)≤3+v := by linarith only [hv]
      calc
        (6*(9/31)/(22/7)^2:ℝ) = 2*(9/31)*1*3/(22/7)^2 := by norm_num
        _ ≤ 2*a*a1*(3+v)/(3+a^2)^2 := by gcongr
    have hlast : v1/(3+a^2)<1/15 := by
      rw [div_lt_iff₀ hd]
      nlinarith only [hv1u,sq_nonneg a]
    unfold s6FinalRB1
    linarith only [hfirst,hlast]
  have hb2 : 1/4 < s6FinalRB2 a a1 a2 v v1 v2 := by
    have hfirst : (18*(6/7)/(22/7)^3:ℝ) ≤ 6*(3+v)*(1-a^2)*a1^2/(3+a^2)^3 := by
      have hthree : (3:ℝ)≤3+v := by linarith only [hv]
      have hnum : (6/7:ℝ)≤1-a^2 := by linarith only [hasq]
      have has : (1:ℝ)≤a1^2 := by nlinarith only [hf1]
      calc
        (18*(6/7)/(22/7)^3:ℝ) = 6*3*(6/7)*1/(22/7)^3 := by norm_num
        _ ≤ 6*(3+v)*(1-a^2)*a1^2/(3+a^2)^3 := by gcongr
    have hmid : 0 ≤ (2*a*(3+v)*a2+4*a*a1*v1)/(3+a^2)^2 := by positivity
    have hlast : v2/(3+a^2)<1/5 := by
      rw [div_lt_iff₀ hd]
      nlinarith only [hv2,sq_nonneg a]
    unfold s6FinalRB2
    linarith only [hfirst,hmid,hlast]
  exact ⟨hb0,hb1,hb2⟩


noncomputable def s6FinalRBSum (e R : ℝ) : ℝ :=
  s6FinalRB R (s6FinalV R (1/19))+
  s6FinalRB (s6FinalRT (s6FinalRP e) R) (s6FinalV R (1/19))
noncomputable def s6FinalRBSum1 (e R : ℝ) : ℝ :=
  s6FinalRB1 R 1 (s6FinalV R (1/19)) (s6FinalRV1 R)+
  s6FinalRB1 (s6FinalRT (s6FinalRP e) R) (s6FinalRT1 (s6FinalRP e) R)
    (s6FinalV R (1/19)) (s6FinalRV1 R)
noncomputable def s6FinalRBSum2 (e R : ℝ) : ℝ :=
  s6FinalRB2 R 1 0 (s6FinalV R (1/19)) (s6FinalRV1 R) (s6FinalRV2 R)+
  s6FinalRB2 (s6FinalRT (s6FinalRP e) R) (s6FinalRT1 (s6FinalRP e) R)
    (s6FinalRT2 (s6FinalRP e) R) (s6FinalV R (1/19)) (s6FinalRV1 R) (s6FinalRV2 R)
noncomputable def s6FinalRShear1 (e R : ℝ) : ℝ :=
  (s6FinalRZ1 R*s6FinalRBSum e R+costZU R (1/19)*s6FinalRBSum1 e R)/8
noncomputable def s6FinalRShear2 (e R : ℝ) : ℝ :=
  (s6FinalRZ2 R*s6FinalRBSum e R+2*s6FinalRZ1 R*s6FinalRBSum1 e R+
    costZU R (1/19)*s6FinalRBSum2 e R)/8

theorem s6_final_rshear_derivatives {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    HasDerivAt (fun R => s6FinalShearLoss R (1/19) e) (s6FinalRShear1 e R) R ∧
    HasDerivAt (s6FinalRShear1 e) (s6FinalRShear2 e R) R := by
  have hp := s6_final_rp_bounds he he1
  have hR0 : 0 < R := by linarith only [hR]
  have hden : 1-s6FinalRP e*R ≠ 0 := by
    have hh : s6FinalRP e*R ≤ (1/21)*(7/19) := mul_le_mul hp.2 hR1 hR0.le (by norm_num)
    linarith only [hh]
  have hT := s6_final_rt_deriv hden
  have hT1 := s6_final_rt1_deriv hden
  have hv := s6_final_rv_derivatives hR0
  have hz := s6_final_rz_derivatives hR hR1
  have hB1 := s6_final_rb_deriv (hasDerivAt_id R) hv.1 rfl rfl
  have hB2 := s6_final_rb_deriv hT hv.1 rfl rfl
  have hBB1 := s6_final_rb1_deriv (hasDerivAt_id R) (hasDerivAt_const R (1:ℝ)) hv.1 hv.2 rfl rfl rfl rfl
  have hBB2 := s6_final_rb1_deriv hT hT1 hv.1 hv.2 rfl rfl rfl rfl
  have hb : HasDerivAt (s6FinalRBSum e) (s6FinalRBSum1 e R) R := by
    convert hB1.add hB2 using 1 <;> rfl
  have hb1 : HasDerivAt (s6FinalRBSum1 e) (s6FinalRBSum2 e R) R := by
    convert hBB1.add hBB2 using 1 <;> rfl
  constructor
  · have hh := (hz.1.mul hb).div_const 8
    convert hh using 1
    · ext x
      simp only [s6FinalShearLoss,s6FinalRBSum,s6FinalRB,s6FinalV,
        s6_final_rt_eq he,Pi.mul_apply]
      ring
    · rfl
  · have hh := ((hz.2.1.mul hb).add (hz.1.mul hb1)).div_const 8
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRShear2]
      ring

theorem s6_final_rshear_second_lower {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    2/45 < s6FinalRShear2 e R := by
  have hp := s6_final_rp_bounds he he1
  have ht := s6_final_rt_bounds hp.1 hp.2 hR hR1
  have hv := s6_final_rv_bounds hR hR1
  have hv0 := s6_final_v_bounds hR hR1 (show (0:ℝ)≤1/19 by norm_num)
  have hz := s6_final_rz_bounds hR hR1
  have hb1 := s6_final_rb_bounds (show 9/31 ≤ R by linarith only [hR]) hR1
    (show (1:ℝ)≤1 by norm_num) (show (0:ℝ)≤0 by norm_num) hv0.1 hv0.2 hv.1 hv.2.1 hv.2.2
  have hb2 := s6_final_rb_bounds ht.1 (ht.2.1.trans hR1)
    ht.2.2.1.le ht.2.2.2.2.1.le hv0.1 hv0.2 hv.1 hv.2.1 hv.2.2
  have hbs : 0 < s6FinalRBSum e R := by
    unfold s6FinalRBSum
    linarith only [hb1.1,hb2.1]
  have hbs1 : (1/5:ℝ) < s6FinalRBSum1 e R := by
    unfold s6FinalRBSum1
    linarith only [hb1.2.1,hb2.2.1]
  have hbs2 : (1/2:ℝ) < s6FinalRBSum2 e R := by
    unfold s6FinalRBSum2
    linarith only [hb1.2.2,hb2.2.2]
  have hterm0 := mul_pos hz.2.2 hbs
  have hterm1a := mul_lt_mul_of_pos_right hz.2.1 (show 0 < s6FinalRBSum1 e R by linarith only [hbs1])
  have hterm1b := mul_lt_mul_of_pos_left hbs1 (by norm_num : (0:ℝ)<3/4)
  have hterm2a := mul_lt_mul_of_pos_right hz.1 (show 0 < s6FinalRBSum2 e R by linarith only [hbs2])
  have hterm2b := mul_lt_mul_of_pos_left hbs2 (by norm_num : (0:ℝ)<1/9)
  unfold s6FinalRShear2
  nlinarith only [hterm0,hterm1a,hterm1b,hterm2a,hterm2b]

end SmoothedOctagon

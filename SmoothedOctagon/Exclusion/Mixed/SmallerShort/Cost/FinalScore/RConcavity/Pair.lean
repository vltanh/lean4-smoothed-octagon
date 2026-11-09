module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Basic
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Pair

/-!
# S6 maximal displacement: pair curvature

The product rule separates the pair curvature into its kernel, variance and
shape contributions. Their natural bounds give a total below `1/25`.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRPair1 (e R : ℝ) : ℝ :=
  let p := s6FinalRP e; let T := s6FinalRT p R; let T1 := s6FinalRT1 p R
  s6FinalK1 R+s6FinalK1 T*T1+
    s6FinalRV1 R*(s6FinalG R+s6FinalG T)+
    s6FinalV R (1/19)*(s6FinalG1 R+s6FinalG1 T*T1)
noncomputable def s6FinalRPair2 (e R : ℝ) : ℝ :=
  let p := s6FinalRP e; let T := s6FinalRT p R
  let T1 := s6FinalRT1 p R; let T2 := s6FinalRT2 p R
  s6FinalK2 R+s6FinalK2 T*T1^2+s6FinalK1 T*T2+
    s6FinalRV2 R*(s6FinalG R+s6FinalG T)+
    2*s6FinalRV1 R*(s6FinalG1 R+s6FinalG1 T*T1)+
    s6FinalV R (1/19)*(s6FinalG2 R+s6FinalG2 T*T1^2+s6FinalG1 T*T2)

theorem s6_final_rpair_derivatives {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    HasDerivAt (fun R => s6FinalPair R (1/19) e) (s6FinalRPair1 e R) R ∧
    HasDerivAt (s6FinalRPair1 e) (s6FinalRPair2 e R) R := by
  have hp := s6_final_rp_bounds he he1
  have hR0 : 0 < R := by linarith only [hR]
  have hden : 1-s6FinalRP e*R ≠ 0 := by
    have hh : s6FinalRP e*R ≤ (1/21)*(7/19) := mul_le_mul hp.2 hR1 hR0.le (by norm_num)
    linarith only [hh]
  have hT := s6_final_rt_deriv hden
  have hT1 := s6_final_rt1_deriv hden
  have hv := s6_final_rv_derivatives hR0
  have hg := (s6_final_g_deriv R).add ((s6_final_g_deriv (s6FinalRT (s6FinalRP e) R)).comp R hT)
  have hgg := (s6_final_g1_deriv R).add
    (((s6_final_g1_deriv (s6FinalRT (s6FinalRP e) R)).comp R hT).mul hT1)
  constructor
  · have hh := ((s6_final_k_deriv R).add
      ((s6_final_k_deriv (s6FinalRT (s6FinalRP e) R)).comp R hT)).add (hv.1.mul hg)
    convert hh using 1
    · ext x
      simp only [s6FinalPair,s6_final_rt_eq he,Pi.add_apply,Pi.mul_apply,Function.comp_apply]
    · simp only [s6FinalRPair1, Pi.add_apply, Function.comp_apply]
      ring
  · have hh := (((s6_final_k1_deriv R).add
      (((s6_final_k1_deriv (s6FinalRT (s6FinalRP e) R)).comp R hT).mul hT1)).add
        (hv.2.mul hg)).add (hv.1.mul hgg)
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRPair2, Pi.add_apply, Pi.mul_apply, Function.comp_apply]
      ring

theorem s6_final_rpair_second_upper {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6FinalRPair2 e R < 1/25 := by
  let p := s6FinalRP e
  let T := s6FinalRT p R
  let t1 := s6FinalRT1 p R
  let t2 := s6FinalRT2 p R
  have hp := s6_final_rp_bounds he he1
  have ht := s6_final_rt_bounds hp.1 hp.2 hR hR1
  change 9/31 ≤ T ∧ T ≤ R ∧ 1 < t1 ∧ t1 < 21/20 ∧ 0 < t2 ∧ t2 < 1/9 at ht
  have hRlo : 9/31 ≤ R := by linarith only [hR]
  have ht1p : 0 < t1 := by linarith only [ht.2.2.1]
  have hv := s6_final_rv_bounds hR hR1
  have hv0 := s6_final_v_bounds hR hR1 (show (0:ℝ)≤1/19 by norm_num)
  have hgR := s6_final_g_bounds hRlo hR1
  have hgT := s6_final_g_bounds ht.1 (ht.2.1.trans hR1)
  have hgs := s6_final_g_sum_bounds hR hR1 ht.1 ht.2.1
  have hkR := s6_final_k2_upper hRlo hR1
  have hkT := mul_lt_mul_of_pos_right (s6_final_k2_upper ht.1 (ht.2.1.trans hR1)) (sq_pos_of_pos ht1p)
  have hkt : s6FinalK2 T*t1^2 < -2/25 := by nlinarith only [hkT,ht.2.2.1]
  have hkt2 := mul_neg_of_neg_of_pos (s6_final_k1_neg ht.1 (ht.2.1.trans hR1)) ht.2.2.2.2.1
  have hv2 := mul_lt_mul_of_pos_right hv.2.2 hgs.1
  have hv2u := mul_lt_mul_of_pos_left hgs.2 (by norm_num : (0:ℝ)<3/5)
  have hg1t := mul_lt_mul_of_pos_right hgT.2.2.1 ht1p
  have hg1tu := mul_lt_mul_of_pos_left ht.2.2.2.1 (by norm_num : (0:ℝ)<2/13)
  have hgu : s6FinalG1 R+s6FinalG1 T*t1 < (2/13)*(1+21/20) := by
    linarith only [hgR.2.2.1,hg1t,hg1tu]
  have hgp : 0 < s6FinalG1 R+s6FinalG1 T*t1 := by
    have htgp : 0 < s6FinalG1 T*t1 := mul_pos (by linarith only [hgT.2.1]) ht1p
    linarith only [hgR.2.1,htgp]
  have hcross := mul_lt_mul_of_pos_right hv.2.1 hgp
  have hcrossu := mul_lt_mul_of_pos_left hgu (by norm_num : (0:ℝ)<1/5)
  have hneg := mul_neg_of_neg_of_pos hgT.2.2.2 (sq_pos_of_pos ht1p)
  have hgneg : s6FinalV R (1/19)*(s6FinalG2 R+s6FinalG2 T*t1^2)<0 := by
    apply mul_neg_of_pos_of_neg hv0.1
    linarith only [hgR.2.2.2,hneg]
  have hlast1 := mul_lt_mul_of_pos_right hgT.2.2.1 ht.2.2.2.2.1
  have hlast2 := mul_lt_mul_of_pos_left ht.2.2.2.2.2 (by norm_num : (0:ℝ)<2/13)
  have hlastp : 0 < s6FinalG1 T*t2 := mul_pos (by linarith only [hgT.2.1]) ht.2.2.2.2.1
  have hlast3 := mul_lt_mul_of_pos_right hv0.2 hlastp
  have hlast4 : (1/25:ℝ)*(s6FinalG1 T*t2)<(1/25)*(2/13)*(1/9) := by
    linarith only [hlast1,hlast2]
  change s6FinalK2 R+s6FinalK2 T*t1^2+s6FinalK1 T*t2+
    s6FinalRV2 R*(s6FinalG R+s6FinalG T)+
    2*s6FinalRV1 R*(s6FinalG1 R+s6FinalG1 T*t1)+
    s6FinalV R (1/19)*(s6FinalG2 R+s6FinalG2 T*t1^2+s6FinalG1 T*t2)<1/25
  nlinarith only [hkR,hkt,hkt2,hv2,hv2u,hcross,hcrossu,hgneg,hlast3,hlast4]

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactShape

/-!
# S6 final score: definitions and shared calculus

The exact score is a pair term minus shear and anisotropy losses. The variance
excess and the Möbius shape coordinate supply the shared first derivatives;
the sign arguments are proved in the modules that use them.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

/-- The exact arctangent score at the genuine variance floor. -/
noncomputable def s6FinalScore (R d e : ℝ) : ℝ :=
  costBExact R (costT R d e) (s6VarianceFloor R d) (costZU R d) (costZL R d)

/-! ### Score decomposition and angle kernels -/
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
  convert (costAngleKernel_hasDerivAt a).div_const 2 using 1
  · ext t
    unfold s6FinalG costAngleKernel
    field_simp
  · unfold s6FinalG1 costAngleKernel1
    field_simp

theorem s6_final_g1_deriv (a : ℝ) : HasDerivAt s6FinalG1 (s6FinalG2 a) a := by
  convert (costAngleKernel1_hasDerivAt a).div_const 2 using 1
  · ext t
    unfold s6FinalG1 costAngleKernel1
    field_simp
  · unfold s6FinalG2 costAngleKernel2
    field_simp

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

/-! ### Variance excess -/

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

theorem s6_final_interval {a : ℝ} (ha : 9/31 ≤ a) (ha1 : a ≤ 7/19) :
    0 < a ∧ 2/7 < a ∧ a^2 < 1/7 := by
  have hapos : 0 < a := by linarith only [ha]
  have hasq : a^2 ≤ (7/19:ℝ)^2 := by nlinarith only [hapos,ha1]
  exact ⟨hapos,by linarith only [ha],by norm_num at hasq ⊢; linarith only [hasq]⟩

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

/-! ### Shape coordinate and displacement derivatives -/

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

end SmoothedOctagon

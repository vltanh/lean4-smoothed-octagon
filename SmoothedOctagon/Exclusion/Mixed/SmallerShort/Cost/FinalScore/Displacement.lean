module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Pair

/-!
# S6 final score: the shear and anisotropy losses increase with displacement
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

noncomputable def s6FinalNu (R d e : ℝ) : ℝ :=
  (R^2-(costT R d e)^2)/(3+(costT R d e)^2)
noncomputable def s6FinalNuD (R d e : ℝ) : ℝ :=
  -2*costT R d e*(3+R^2)*s6FinalTD R d e/(3+(costT R d e)^2)^2

private theorem s6_final_nu_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalNu R d e) (s6FinalNuD R d e) d := by
  have hT := s6_final_t_displacement_deriv hR hR1 hd hd1 he he1
  have hn := (hT.pow 2).const_sub (R^2)
  have hd0 := (hT.pow 2).const_add 3
  have hh := hn.div hd0 (by
    change 3+(costT R d e)^2 ≠ 0
    positivity)
  refine hh.congr_deriv ?_
  unfold s6FinalNuD
  norm_num
  field_simp
  ring

private theorem s6_final_R_sub_T {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    (R-costT R d e)*s6FinalL R d e=(e-1)*(1-R^2)*d := by
  have hb := s6_final_box_denoms hR hR1 hd hd1 he he1
  have hLn : s6FinalL R d e ≠ 0 := hb.2.2.2.2.2.1.ne'
  change (R-(2*R+((e+1)*R-(e-1))*d)/s6FinalL R d e)*s6FinalL R d e=_
  rw [sub_mul,div_mul_cancel₀ _ hLn]
  unfold s6FinalL s6FinalGamma
  ring

private theorem s6_final_nu_pos {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 < d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalNu R d e ∧ 0 < s6FinalNuD R d e := by
  rcases s6_final_box_denoms hR hR1 hd.le hd1 he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hT := costT_correlated_bounds hR hR1 hd.le hd1 he he1
  have hTp : 0 < costT R d e := by linarith only [hT.1,hR]
  have hRs : 0 < 1-R^2 := by nlinarith only [hRp,hRm]
  have hdiff := s6_final_R_sub_T hR hR1 hd.le hd1 he he1
  have hright : 0 < (e-1)*(1-R^2)*d := by positivity
  have hstrict : costT R d e < R := by nlinarith only [hdiff,hright,hLp]
  have hnum : 0 < R^2-(costT R d e)^2 := by nlinarith only [hstrict,hTp,hRp]
  have hTD := s6_final_td_neg hR hR1 hd.le hd1 he he1
  constructor
  · unfold s6FinalNu
    exact div_pos hnum (by positivity)
  · unfold s6FinalNuD
    exact div_pos (mul_pos_of_neg_of_neg (by nlinarith only [hTp,sq_nonneg R]) hTD) (by positivity)

/-- Exact logarithmic derivative relation, from the original Möbius shape coordinate. -/
private theorem s6_final_nu_log_identity {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalNuD R d e*s6FinalL R d e*d*(3+(costT R d e)^2)*(R+costT R d e)=
      4*costT R d e*(3+R^2)*s6FinalNu R d e := by
  have hb := s6_final_box_denoms hR hR1 hd hd1 he he1
  have hLn := hb.2.2.2.2.2.1.ne'
  have hdiff := s6_final_R_sub_T hR hR1 hd hd1 he he1
  have hn : (e-1)*(1-R^2)*d=s6FinalL R d e*(R-costT R d e) := by
    linarith only [hdiff]
  have hid : s6FinalNuD R d e*s6FinalL R d e*d*(3+(costT R d e)^2)*(R+costT R d e)=
      4*costT R d e*(3+R^2)*((e-1)*(1-R^2)*d)*(R+costT R d e)/
        (s6FinalL R d e*(3+(costT R d e)^2)) := by
    unfold s6FinalNuD s6FinalTD
    field_simp [hLn]
    ring
  rw [hid,hn]
  unfold s6FinalNu
  field_simp [hLn]
  ring

/-- The anisotropy grows at least as fast as required by the lower shear envelope. -/
private theorem s6_final_nu_growth {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 < d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalNu R d e < 4*d*s6FinalNuD R d e := by
  have hb := s6_final_box_denoms hR hR1 hd.le hd1 he he1
  have hLp := hb.2.2.2.2.2.1
  have hLhi := hb.2.2.2.2.2.2.2
  have hT := costT_correlated_bounds hR hR1 hd.le hd1 he he1
  have hTq : 1/4 < costT R d e := by linarith only [hT.1,hR]
  have hTp : 0 < costT R d e := by linarith only [hTq]
  have hRpos : 0 < R := by linarith only [hR]
  have hThi : costT R d e ≤ 7/19 := hT.2.trans hR1
  have hTs : 3+(costT R d e)^2 < 4 := by nlinarith only [hThi,hTp]
  have hsum : R+costT R d e < 1 := by linarith only [hT.2,hR1]
  have hNu := s6_final_nu_pos hR hR1 hd hd1 he he1
  have hsumpos : 0 < R+costT R d e := by positivity
  have hprod : s6FinalL R d e*(3+(costT R d e)^2)*(R+costT R d e) < 3*4*1 := by
    gcongr
  norm_num only [Nat.cast_ofNat,mul_one] at hprod
  have hnum : 3 < 4*costT R d e*(3+R^2) := by nlinarith only [hTq,mul_nonneg hTp.le (sq_nonneg R)]
  have hmul := mul_lt_mul_of_pos_left hprod (mul_pos hNu.2 hd)
  have hmul2 := mul_lt_mul_of_pos_right hnum hNu.1
  have hid := s6_final_nu_log_identity hR hR1 hd.le hd1 he he1
  nlinarith only [hmul,hmul2,hid]

noncomputable def s6FinalZL0 (R : ℝ) : ℝ := 2*R^2*(1+R)/(3-R)
noncomputable def s6FinalZLD (R : ℝ) : ℝ := s6FinalZL0 R*(11/2)
noncomputable def s6FinalAnisotropyD (R d e : ℝ) : ℝ :=
  (161/54)/8*(2*s6FinalNu R d e*s6FinalNuD R d e*costZL R d-
    (s6FinalNu R d e)^2*s6FinalZLD R)/(costZL R d)^2

private theorem s6_final_zl_deriv (R d : ℝ) :
    HasDerivAt (costZL R) (s6FinalZLD R) d := by
  have hh := (((hasDerivAt_id' d).const_mul 11).div_const 2).const_add 1
  exact (hh.const_mul (s6FinalZL0 R)).congr_deriv (by unfold s6FinalZLD; ring)

private theorem s6_final_anisotropy_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalAnisotropyLoss R d e) (s6FinalAnisotropyD R d e) d := by
  have hN := s6_final_nu_deriv hR hR1 hd hd1 he he1
  have hZ := s6_final_zl_deriv R d
  have hpos := (cost_shear_envelopes_pos hR hR1 hd hd1).2
  have hh := (((hN.pow 2).div hZ hpos.ne').const_mul ((161/54)/8))
  convert hh using 1
  · funext v
    unfold s6FinalAnisotropyLoss s6FinalNu
    dsimp only [Pi.div_apply,Pi.pow_apply]
    ring
  · unfold s6FinalAnisotropyD
    norm_num
    ring

private theorem s6_final_anisotropyD_nonneg {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : 0 ≤ s6FinalAnisotropyD R d e := by
  by_cases hd0 : d=0
  · subst d
    simp [s6FinalAnisotropyD,s6FinalNu,costT_zero_displacement]
  have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hNu := s6_final_nu_pos hR hR1 hdp hd1 he he1
  have hZp := (cost_shear_envelopes_pos hR hR1 hd hd1).2
  have hZ0 : 0 < s6FinalZL0 R := by
    have hRp : 0 < R := by linarith only [hR]
    have hRm : 0 < 3-R := by linarith only [hR1]
    unfold s6FinalZL0
    positivity
  have hZlog : s6FinalZLD R ≤ (11/2)*costZL R d := by
    unfold s6FinalZLD costZL
    change s6FinalZL0 R*(11/2) ≤ (11/2)*(s6FinalZL0 R*(1+11*d/2))
    nlinarith only [mul_nonneg hZ0.le hd]
  have hgrowth := s6_final_nu_growth hR hR1 hdp hd1 he he1
  have hrate : (19/4)*s6FinalNu R d e < s6FinalNuD R d e := by
    have hupper := mul_le_mul_of_nonneg_right hd1 hNu.2.le
    nlinarith only [hgrowth,hupper]
  have hmult := mul_lt_mul_of_pos_right hrate hZp
  have hmult2 := mul_le_mul_of_nonneg_left hZlog hNu.1.le
  have hinner : 0 < 2*s6FinalNuD R d e*costZL R d-s6FinalNu R d e*s6FinalZLD R := by
    nlinarith only [hmult,hmult2,mul_pos hNu.1 hZp]
  unfold s6FinalAnisotropyD
  apply div_nonneg
  · have hm := mul_pos hNu.1 hinner
    convert (mul_nonneg (by norm_num : (0:ℝ) ≤ (161/54)/8) hm.le) using 1; ring
  · positivity

/-- The anisotropy loss is nondecreasing through the closed displacement interval. -/
theorem s6_final_anisotropy_monotone_displacement {R d v e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hdv : d ≤ v) (hv : v ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalAnisotropyLoss R d e ≤ s6FinalAnisotropyLoss R v e := by
  exact ss_le_of_deriv (f:=fun v => s6FinalAnisotropyLoss R v e)
    (f':=fun v => s6FinalAnisotropyD R v e) hdv
    (fun y hy => s6_final_anisotropy_deriv hR hR1 (hd.trans hy.1) (hy.2.trans hv) he he1)
    (fun y hy => s6_final_anisotropyD_nonneg hR hR1 (hd.trans hy.1.le) (hy.2.le.trans hv) he he1)


/-! The scalar E controls the displacement derivative of the shear loss. -/
noncomputable def s6FinalA (R : ℝ) : ℝ := (1+2*R)/(3*(1-R))
noncomputable def s6FinalA1 (R : ℝ) : ℝ := 1/(1-R)^2
noncomputable def s6FinalD (R : ℝ) : ℝ := 3*(1-R^2)/(2*R)
noncomputable def s6FinalD1 (R : ℝ) : ℝ := -(3/2)*(1+1/R^2)
noncomputable def s6FinalZ01 (R : ℝ) : ℝ := 4*R*(3+4*R-R^2)/(3-R)^2
noncomputable def s6FinalW (R : ℝ) : ℝ := (1-R)*(1+R)^2
noncomputable def s6FinalW1 (R : ℝ) : ℝ := (1+R)*(1-3*R)
noncomputable def s6FinalDZ01 (R : ℝ) : ℝ :=
  9*s6FinalW R/(3-R)^2+3*R/(3-R)*s6FinalW1 R
noncomputable def s6FinalDA1 (R : ℝ) : ℝ := (2-1/R^2)/2
noncomputable def s6FinalE (R d : ℝ) : ℝ :=
  (s6FinalA R-3*d)*(1+2*d)^2-s6FinalD R*(s6FinalZL0 R+2*s6FinalA R*d)
noncomputable def s6FinalED (R d : ℝ) : ℝ :=
  s6FinalA R*(4-2*s6FinalD R)-3+(8*s6FinalA R-24)*d-36*d^2
noncomputable def s6FinalER (R d : ℝ) : ℝ :=
  s6FinalA1 R*(1+2*d)^2-s6FinalDZ01 R-2*d*s6FinalDA1 R

private theorem s6_final_a_deriv {R : ℝ} (hR : R < 1) :
    HasDerivAt s6FinalA (s6FinalA1 R) R := by
  have hp : 1-R ≠ 0 := ne_of_gt (by linarith only [hR])
  have hh := (((hasDerivAt_id' R).const_mul 2).const_add 1).div
    (((hasDerivAt_id' R).const_sub 1).const_mul 3) (mul_ne_zero (by norm_num) hp)
  refine hh.congr_deriv ?_
  unfold s6FinalA1
  norm_num
  field_simp
  ring

private theorem s6_final_d_deriv {R : ℝ} (hR : 0 < R) :
    HasDerivAt s6FinalD (s6FinalD1 R) R := by
  have hh := (((hasDerivAt_pow 2 R).const_sub 1).const_mul 3).div
    ((hasDerivAt_id' R).const_mul 2) (mul_ne_zero (by norm_num) hR.ne')
  refine hh.congr_deriv ?_
  unfold s6FinalD1
  norm_num
  field_simp
  ring

private theorem s6_final_z0_deriv {R : ℝ} (hR : R < 3) :
    HasDerivAt s6FinalZL0 (s6FinalZ01 R) R := by
  have hh := ((((hasDerivAt_pow 2 R).const_mul 2).mul
    ((hasDerivAt_id' R).const_add 1)).div ((hasDerivAt_id' R).const_sub 3)
    (ne_of_gt (by linarith only [hR])))
  refine hh.congr_deriv ?_
  unfold s6FinalZ01
  norm_num
  field_simp
  ring

private theorem s6_final_e_deriv_d (R d : ℝ) :
    HasDerivAt (s6FinalE R) (s6FinalED R d) d := by
  have hleft := ((hasDerivAt_id' d).const_mul 3).const_sub (s6FinalA R)
  have hright := (((hasDerivAt_id' d).const_mul 2).const_add 1).pow 2
  have hh := (hleft.mul hright).sub
    ((((hasDerivAt_id' d).const_mul (2*s6FinalA R)).const_add (s6FinalZL0 R)).const_mul (s6FinalD R))
  refine hh.congr_deriv ?_
  unfold s6FinalED
  norm_num
  ring

private theorem s6_final_e_deriv_r {R d : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    HasDerivAt (fun R => s6FinalE R d) (s6FinalER R d) R := by
  have hA := s6_final_a_deriv hR1
  have hD := s6_final_d_deriv hR
  have hZ := s6_final_z0_deriv (show R < 3 by linarith only [hR1])
  have hh := ((hA.sub_const (3*d)).mul_const ((1+2*d)^2)).sub
    (hD.mul (hZ.add (hA.mul_const (2*d))))
  convert hh using 1
  · funext r
    unfold s6FinalE
    dsimp only [Pi.add_apply,Pi.mul_apply,Pi.sub_apply]
    ring
  · unfold s6FinalER s6FinalA1 s6FinalDZ01 s6FinalDA1 s6FinalW s6FinalW1
    unfold s6FinalD1 s6FinalD s6FinalZ01 s6FinalZL0 s6FinalA
    dsimp only [Pi.add_apply]
    field_simp [hR.ne',ne_of_gt (show 0 < 1-R by linarith only [hR1]),
      ne_of_gt (show 0 < 3-R by linarith only [hR1])]
    ring

private theorem s6_final_ad_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalA R ∧ s6FinalA R < 1 ∧ 3 < s6FinalD R := by
  have hRp : 0 < R := by linarith only [hR]
  have hRm : 0 < 1-R := by linarith only [hR1]
  refine ⟨by unfold s6FinalA; positivity,?_,?_⟩
  · unfold s6FinalA
    rw [div_lt_one (by positivity)]
    linarith only [hR1]
  · unfold s6FinalD
    rw [lt_div_iff₀ (by positivity)]
    have hs : R^2 ≤ (7/19:ℝ)^2 := by nlinarith only [hRp,hR1]
    nlinarith only [hs,hR1]

private theorem s6_final_ed_neg {R d : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) : s6FinalED R d < 0 := by
  rcases s6_final_ad_bounds hR hR1 with ⟨hA,hA1,hD⟩
  have h1 : s6FinalA R*(4-2*s6FinalD R) < 0 :=
    mul_neg_of_pos_of_neg hA (by linarith only [hD])
  have h2 : (8*s6FinalA R-24)*d ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hA1]) hd
  unfold s6FinalED
  nlinarith only [h1,h2,sq_nonneg d]

private theorem s6_final_er_pos {R d : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) : 0 < s6FinalER R d := by
  have hRp : 0 < R := by linarith only [hR]
  have hRm : 0 < 1-R := by linarith only [hR1]
  have h3 : 5/2 < 3-R := by linarith only [hR1]
  have hA1 : (9/4:ℝ) ≤ s6FinalA1 R := by
    unfold s6FinalA1
    rw [le_div_iff₀ (sq_pos_of_pos hRm)]
    have hs : (1-R)^2 ≤ (2/3:ℝ)^2 := by nlinarith only [hR,hRm]
    nlinarith only [hs]
  have hDA1 : s6FinalDA1 R < 0 := by
    unfold s6FinalDA1
    have hh : (2:ℝ) < 1/R^2 := by
      rw [lt_div_iff₀ (sq_pos_of_pos hRp)]
      have hs : R^2 ≤ (7/19:ℝ)^2 := by nlinarith only [hRp,hR1]
      nlinarith only [hs]
    linarith only [hh]
  have hW1 : s6FinalW1 R ≤ 0 := by
    unfold s6FinalW1
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith only [hR])
  have hW0 : 0 < s6FinalW R := by unfold s6FinalW; positivity
  have hW : s6FinalW R < 4/3 := by
    have hprod : 0 ≤ (3*R-1)^2*(3*R+5) := by positivity
    unfold s6FinalW
    nlinarith only [hprod]
  have hD1 : 9*s6FinalW R/(3-R)^2 < 2 := by
    rw [div_lt_iff₀ (sq_pos_of_pos (show 0 < 3-R by linarith only [h3]))]
    nlinarith only [hW,h3]
  have hD2 : 3*R/(3-R)*s6FinalW1 R ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hW1
  have hDZ : s6FinalDZ01 R < 2 := by unfold s6FinalDZ01; linarith only [hD1,hD2]
  have hterm : 0 ≤ -2*d*s6FinalDA1 R := by
    exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hd]) hDA1.le
  have hsq : 1 ≤ (1+2*d)^2 := by nlinarith only [hd,sq_nonneg d]
  have hApr : 0 ≤ s6FinalA1 R := by linarith only [hA1]
  have hmul := mul_le_mul_of_nonneg_left hsq hApr
  unfold s6FinalER
  nlinarith only [hA1,hmul,hDZ,hterm]

/-- The shear-budget E is positive on the entire closed rectangle by two monotonicities. -/
theorem s6_final_e_pos {R d : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) : 0 < s6FinalE R d := by
  have hmd := ss_le_of_deriv (f:=fun d => -s6FinalE R d)
    (f':=fun d => -s6FinalED R d) hd1
    (fun y hy => (s6_final_e_deriv_d R y).neg)
    (fun y hy => by
      have hs := s6_final_ed_neg hR hR1 (hd.trans hy.1.le)
      linarith only [hs])
  have hmr := ss_le_of_deriv (f:=fun R => s6FinalE R (1/19))
    (f':=fun R => s6FinalER R (1/19)) hR
    (fun y hy => s6_final_e_deriv_r (by linarith only [hy.1]) (by linarith only [hy.2,hR1]))
    (fun y hy => (s6_final_er_pos hy.1.le (hy.2.le.trans hR1) (by norm_num)).le)
  have hcorner : 0 < s6FinalE (1/3) (1/19) := by
    norm_num [s6FinalE,s6FinalA,s6FinalD,s6FinalZL0]
  linarith only [hmd,hmr,hcorner]


/-! The anisotropy's natural rational denominator and its nonnegative deficit. -/
noncomputable def s6FinalNuScale (R e : ℝ) : ℝ := (e-1)*R*(1-R^2)/(3+R^2)
noncomputable def s6FinalNuA (R e : ℝ) : ℝ := (e+1)/2-(e-1)*(R+1/R)/4
noncomputable def s6FinalNuB (R e : ℝ) : ℝ := s6FinalGamma R e-s6FinalNuScale R e
noncomputable def s6FinalNuJ (R e : ℝ) : ℝ :=
  (3*(s6FinalGamma R e)^2+((e+1)*R-(e-1))^2)/(4*(3+R^2))
noncomputable def s6FinalNuDen (R d e : ℝ) : ℝ :=
  1+s6FinalNuB R e*d+s6FinalNuJ R e*d^2
noncomputable def s6FinalNuModel (R d e : ℝ) : ℝ :=
  s6FinalNuScale R e*d*(1+s6FinalNuA R e*d)/s6FinalNuDen R d e
noncomputable def s6FinalNuModelD (R d e : ℝ) : ℝ :=
  s6FinalNuScale R e*((1+s6FinalNuA R e*d)^2-
    (s6FinalNuJ R e-s6FinalNuA R e*(s6FinalNuB R e-s6FinalNuA R e))*d^2)/
      (s6FinalNuDen R d e)^2

private theorem s6_final_nu_coefficient_bounds {R e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalNuScale R e ∧ s6FinalNuScale R e < 1/4 ∧
    1/3 ≤ s6FinalNuA R e ∧ s6FinalNuA R e ≤ 7/12 ∧
    11/4 < s6FinalNuB R e ∧ s6FinalNuB R e ≤ 10/3 ∧ 27/16 < s6FinalNuJ R e := by
  rcases s6_final_box_denoms hR hR1 (d:=0) (by norm_num) (by norm_num) he he1 with
    ⟨hRp,hRm,hep,hGlo,hGhi,hLp,hMp,hLhi⟩
  have hRs : R^2 < 1/7 := (s6_final_interval (by linarith only [hR]) hR1).2.2
  have hRs0 : 0 < 1-R^2 := by linarith only [hRs]
  have hScale : 0 < s6FinalNuScale R e := by unfold s6FinalNuScale; positivity
  have hScale1 : s6FinalNuScale R e < 1/4 := by
    unfold s6FinalNuScale
    rw [div_lt_iff₀ (by positivity : 0 < 3+R^2)]
    have hmul : (e-1)*R*(1-R^2) < 2*(3/8)*1 := by
      have hRs1 : 0 < 1-R^2 := by linarith only [hRs]
      have hRs2 : 1-R^2 < 1 := by nlinarith only [hRp]
      have he2 : e-1 ≤ 2 := by linarith only [he1]
      have hR3 : R < 3/8 := by linarith only [hR1]
      have hweak := mul_le_mul_of_nonneg_right he2 (mul_nonneg hRp.le hRs1.le)
      have hstrict : 2*R*(1-R^2) < 2*(3/8)*1 := by gcongr
      nlinarith only [hweak,hstrict]
    nlinarith only [hmul,sq_nonneg R]
  have hAI : s6FinalNuA R e=1-(e-1)*(1-R)^2/(4*R) := by
    unfold s6FinalNuA
    field_simp [hRp.ne']
    ring
  have hsqHi : (1-R)^2 ≤ (2/3:ℝ)^2 := by nlinarith only [hR,hRm]
  have hsqLo : (12/19:ℝ)^2 ≤ (1-R)^2 := by nlinarith only [hR1,hRm]
  have hmHi := mul_le_mul (show e-1 ≤ 2 by linarith only [he1]) hsqHi (sq_nonneg (1-R)) (by norm_num : (0:ℝ) ≤ 2)
  have hmLo := mul_le_mul (show (8/5:ℝ) ≤ e-1 by linarith only [he]) hsqLo (by norm_num) hep.le
  have hAlo : 1/3 ≤ s6FinalNuA R e := by
    rw [hAI]
    have hq : (e-1)*(1-R)^2/(4*R) ≤ 2/3 := by
      rw [div_le_iff₀ (by positivity : 0 < 4*R)]
      nlinarith only [hmHi,hR]
    linarith only [hq]
  have hAhi : s6FinalNuA R e ≤ 7/12 := by
    rw [hAI]
    have hq : (5/12:ℝ) ≤ (e-1)*(1-R)^2/(4*R) := by
      rw [le_div_iff₀ (by positivity : 0 < 4*R)]
      nlinarith only [hmLo,hR1]
    linarith only [hq]
  have hGhi2 : s6FinalGamma R e ≤ 10/3 := by
    have hm := mul_le_mul (show e-1 ≤ 2 by linarith only [he1])
      (show 1-R ≤ 2/3 by linarith only [hR]) hRm.le (by norm_num : (0:ℝ) ≤ 2)
    unfold s6FinalGamma
    nlinarith only [hm]
  have hBlo : 11/4 < s6FinalNuB R e := by unfold s6FinalNuB; linarith only [hGlo,hScale1]
  have hBhi : s6FinalNuB R e ≤ 10/3 := by unfold s6FinalNuB; linarith only [hGhi2,hScale]
  have hJ : 27/16 < s6FinalNuJ R e := by
    unfold s6FinalNuJ
    rw [lt_div_iff₀ (by positivity : 0 < 4*(3+R^2))]
    have hsG : (9:ℝ) < (s6FinalGamma R e)^2 := by nlinarith only [hGlo]
    nlinarith only [hsG,hRs,sq_nonneg ((e+1)*R-(e-1))]
  exact ⟨hScale,hScale1,hAlo,hAhi,hBlo,hBhi,hJ⟩

private theorem s6_final_nu_deficits {R e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 ≤ s6FinalNuA R e ∧ s6FinalNuA R e+2 ≤ s6FinalNuB R e ∧
    2*s6FinalNuA R e ≤ s6FinalNuJ R e ∧
    s6FinalNuA R e*(s6FinalNuB R e-s6FinalNuA R e) ≤ s6FinalNuJ R e := by
  rcases s6_final_nu_coefficient_bounds hR hR1 he he1 with
    ⟨hS,hS1,hA,hA1,hB,hB1,hJ⟩
  have hprod : s6FinalNuA R e*(s6FinalNuB R e-s6FinalNuA R e) ≤ 77/48 := by
    have hm := mul_le_mul_of_nonneg_left hB1 (show 0 ≤ s6FinalNuA R e by linarith only [hA])
    have hf : 0 ≤ (7/12-s6FinalNuA R e)*(10/3-s6FinalNuA R e-7/12) := by
      apply mul_nonneg (by linarith only [hA1]) (by linarith only [hA1])
    nlinarith only [hm,hf]
  exact ⟨by linarith only [hA],by linarith only [hA1,hB],by linarith only [hA1,hJ],
    by linarith only [hprod,hJ]⟩

/-- A generic positive-denominator comparison; no expanded numerator signs are needed. -/
private theorem s6_final_ratio_bounds {a b j s d : ℝ}
    (ha : 0 ≤ a) (hb : a+2 ≤ b) (hj : 2*a ≤ j) (hm : a*(b-a) ≤ j)
    (hs : 0 ≤ s) (hd : 0 ≤ d) :
    s*d*(1+a*d)/(1+b*d+j*d^2) ≤ s*d/(1+2*d) ∧
    s*((1+a*d)^2-(j-a*(b-a))*d^2)/(1+b*d+j*d^2)^2 ≤ s/(1+2*d)^2 := by
  have hD : 0 < 1+b*d+j*d^2 := by
    have hbp : 0 ≤ b := by linarith only [ha,hb]
    have hjp : 0 ≤ j := by linarith only [ha,hj]
    positivity
  have hq : 0 < 1+a*d := by positivity
  have hp : 0 < 1+2*d := by positivity
  have hdef : (1+a*d)*(1+2*d) ≤ 1+b*d+j*d^2 := by
    have h1 := mul_nonneg (sub_nonneg.2 hb) hd
    have h2 := mul_nonneg (sub_nonneg.2 hj) (sq_nonneg d)
    nlinarith only [h1,h2]
  constructor
  · rw [div_le_div_iff₀ hD hp]
    have hmul := mul_le_mul_of_nonneg_left hdef (mul_nonneg hs hd)
    nlinarith only [hmul]
  · have hnum : (1+a*d)^2-(j-a*(b-a))*d^2 ≤ (1+a*d)^2 := by
      have hh := mul_nonneg (sub_nonneg.2 hm) (sq_nonneg d)
      linarith only [hh]
    have hstep1 : s*((1+a*d)^2-(j-a*(b-a))*d^2)/(1+b*d+j*d^2)^2 ≤
        s*(1+a*d)^2/(1+b*d+j*d^2)^2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hs) (sq_nonneg _)
    have hstep2 : s*(1+a*d)^2/(1+b*d+j*d^2)^2 ≤ s/(1+2*d)^2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hp)]
      have hsq := sq_le_sq₀ (by positivity : 0 ≤ (1+a*d)*(1+2*d)) hD.le |>.2 hdef
      have hmul := mul_le_mul_of_nonneg_left hsq hs
      nlinarith only [hmul]
    exact hstep1.trans hstep2


private theorem s6_final_nu_model_eq_general {R d e : ℝ}
    (hR : 0 < R) (hLn : s6FinalL R d e ≠ 0) (hDn : s6FinalNuDen R d e ≠ 0) :
    s6FinalNu R d e=s6FinalNuModel R d e := by
  let N := 2*R+((e+1)*R-(e-1))*d
  have hden : 3*(s6FinalL R d e)^2+N^2=4*(3+R^2)*s6FinalNuDen R d e := by
    dsimp [N]
    unfold s6FinalNuDen s6FinalNuB s6FinalNuJ s6FinalNuScale s6FinalL s6FinalGamma
    field_simp
    ring
  have hnum : R^2*(s6FinalL R d e)^2-N^2=
      4*(3+R^2)*s6FinalNuScale R e*d*(1+s6FinalNuA R e*d) := by
    dsimp [N]
    unfold s6FinalNuScale s6FinalNuA s6FinalL s6FinalGamma
    field_simp [hR.ne']
    ring
  have hbase : s6FinalNu R d e=(R^2*(s6FinalL R d e)^2-N^2)/
      (3*(s6FinalL R d e)^2+N^2) := by
    change (R^2-(N/s6FinalL R d e)^2)/(3+(N/s6FinalL R d e)^2)=_
    field_simp [hLn]
  rw [hbase,hnum,hden]
  unfold s6FinalNuModel
  field_simp [hDn]

private theorem s6_final_nu_den_pos {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : 0 < s6FinalNuDen R d e := by
  have hb := s6_final_nu_coefficient_bounds hR hR1 he he1
  have hb0 : 0 < s6FinalNuB R e := by linarith only [hb.2.2.2.2.1]
  have hj0 : 0 < s6FinalNuJ R e := by linarith only [hb.2.2.2.2.2.2]
  unfold s6FinalNuDen
  positivity

private theorem s6_final_nu_model_deriv {R d e : ℝ} (hD : s6FinalNuDen R d e ≠ 0) :
    HasDerivAt (fun d => s6FinalNuModel R d e) (s6FinalNuModelD R d e) d := by
  have hn := ((hasDerivAt_id' d).const_mul (s6FinalNuScale R e)).mul
    (((hasDerivAt_id' d).const_mul (s6FinalNuA R e)).const_add 1)
  have hd0 := ((((hasDerivAt_id' d).const_mul (s6FinalNuB R e)).const_add 1).add
    ((hasDerivAt_pow 2 d).const_mul (s6FinalNuJ R e)))
  have hh := hn.div hd0 hD
  refine hh.congr_deriv ?_
  unfold s6FinalNuModelD s6FinalNuDen
  norm_num
  field_simp
  ring

/-- The model and the original anisotropy have the same displacement derivative. -/
private theorem s6_final_nuD_eq_modelD {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : s6FinalNuD R d e=s6FinalNuModelD R d e := by
  have hb := s6_final_box_denoms hR hR1 hd hd1 he he1
  have hRpos : 0 < R := by linarith only [hR]
  have hLp := hb.2.2.2.2.2.1
  have hDp := s6_final_nu_den_pos hR hR1 hd he he1
  have hLc : Continuous (fun d => s6FinalL R d e) := by unfold s6FinalL; fun_prop
  have hDc : Continuous (fun d => s6FinalNuDen R d e) := by unfold s6FinalNuDen; fun_prop
  have hLe : ∀ᶠ y in nhds d, s6FinalL R y e ≠ 0 := hLc.continuousAt.eventually_ne hLp.ne'
  have hDe : ∀ᶠ y in nhds d, s6FinalNuDen R y e ≠ 0 := hDc.continuousAt.eventually_ne hDp.ne'
  have heq : (fun y => s6FinalNu R y e) =ᶠ[nhds d] (fun y => s6FinalNuModel R y e) := by
    filter_upwards [hLe,hDe] with y hyL hyD
    exact s6_final_nu_model_eq_general hRpos hyL hyD
  exact (s6_final_nu_deriv hR hR1 hd hd1 he he1).unique
    ((s6_final_nu_model_deriv hDp.ne').congr_of_eventuallyEq heq)

/-- The two anisotropy bounds used in the shear-loss budget, directly from positive deficits. -/
private theorem s6_final_nu_upper_bounds {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalNu R d e ≤ s6FinalNuScale R e*d/(1+2*d) ∧
    s6FinalNuD R d e ≤ s6FinalNuScale R e/(1+2*d)^2 := by
  have hdef := s6_final_nu_deficits hR hR1 he he1
  have hScale := (s6_final_nu_coefficient_bounds hR hR1 he he1).1
  have hb := s6_final_ratio_bounds hdef.1 hdef.2.1 hdef.2.2.1 hdef.2.2.2 hScale.le hd
  have hLn := (s6_final_box_denoms hR hR1 hd hd1 he he1).2.2.2.2.2.1.ne'
  have hDn := (s6_final_nu_den_pos hR hR1 hd he he1).ne'
  rw [s6_final_nu_model_eq_general (by linarith only [hR]) hLn hDn,s6_final_nuD_eq_modelD hR hR1 hd hd1 he he1]
  exact hb


private theorem s6_final_v0_quadratic_upper {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6FinalV0 R ≤ R^2/3 := by
  have hRp : 0 < R := by linarith only [hR]
  have hf := ss_le_of_deriv (f:=fun r => -s6FinalFloorFactor r)
    (f':=fun r => (16*(3*r+2))/(3*(3*r+4)^3)) hR
    (fun r hr => by
      have hh := (s6_final_floor_factor_deriv (show 0 ≤ r by linarith only [hr.1])).neg
      convert hh using 1; ring)
    (fun r hr => by
      have hrp : 0 < r := by linarith only [hr.1]
      positivity)
  have hfb : s6FinalFloorFactor R ≤ 64/225 := by
    have hb : s6FinalFloorFactor (1/3)=64/225 := by norm_num [s6FinalFloorFactor]
    linarith only [hf,hb]
  have hRs : R^2 < 1/7 := (s6_final_interval (by linarith only [hR]) hR1).2.2
  have hq : 3*R^2/(80*(1+R)^3) < 1/400 := by
    rw [div_lt_iff₀ (by positivity : 0 < 80*(1+R)^3)]
    have hp : (4/3:ℝ)^3 ≤ (1+R)^3 := by gcongr; linarith only [hR]
    nlinarith only [hRs,hp]
  have hid : s6FinalV0 R=R^2*(s6FinalFloorFactor R+3*R^2/(80*(1+R)^3)) := by
    unfold s6FinalV0 s6FinalFloorFactor
    field_simp
    ring
  have hsum : s6FinalFloorFactor R+3*R^2/(80*(1+R)^3) ≤ 1/3 := by linarith only [hfb,hq]
  have hm := mul_le_mul_of_nonneg_left hsum (sq_nonneg R)
  rw [hid]
  nlinarith only [hm]

private theorem s6_final_v_quadratic_upper {R d : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) : s6FinalV R d ≤ R^2/3 := by
  have hRp : 0 < R := by linarith only [hR]
  have hV0p : 0 < s6FinalV0 R := by unfold s6FinalV0; positivity
  have hden : 0 < 2*R+(1+R)*d := by positivity
  have hratio : (2*R)/(2*R+(1+R)*d) ≤ 1 := by
    rw [div_le_one hden]
    have hh : 0 ≤ (1+R)*d := by positivity
    linarith only [hh]
  have hm := mul_le_of_le_one_right hV0p.le hratio
  rw [s6_final_v_eq hRp hd]
  simpa only [mul_div_assoc] using hm.trans (s6_final_v0_quadratic_upper hR hR1)

noncomputable def s6FinalB1 (R d : ℝ) : ℝ := 1-4*s6VarianceFloor R d/(3+R^2)
noncomputable def s6FinalB1D (R d e : ℝ) : ℝ :=
  -(s6FinalV R d*s6FinalChi R d e*s6FinalTD R d e)/(3+R^2)
noncomputable def s6FinalBLow (R : ℝ) : ℝ := 2*R^2/(3*(3+R^2))
noncomputable def s6FinalZUD (R d : ℝ) : ℝ := s6FinalA R-3*d
noncomputable def s6FinalShearD (R d e : ℝ) : ℝ :=
  (s6FinalZUD R d*(2*s6FinalB1 R d-(1-s6FinalB1 R d)*s6FinalNu R d e)+
    costZU R d*((2+s6FinalNu R d e)*s6FinalB1D R d e-(1-s6FinalB1 R d)*s6FinalNuD R d e))/8

private theorem s6_final_b1_eq (R d : ℝ) : s6FinalB1 R d=(R^2-s6FinalV R d)/(3+R^2) := by
  unfold s6FinalB1 s6FinalV
  field_simp
  ring

private theorem s6_final_b1_bounds {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalBLow R ∧ s6FinalBLow R ≤ s6FinalB1 R d ∧ s6FinalB1 R d < 1 ∧
    0 < s6FinalB1D R d e := by
  have hRp : 0 < R := by linarith only [hR]
  have hV := s6_final_v_bounds hR hR1 hd
  have hVq := s6_final_v_quadratic_upper hR hR1 hd
  have hC := s6_final_chi_bounds hR hR1 hd hd1 he he1
  have hT := s6_final_td_neg hR hR1 hd hd1 he he1
  have hVp := hV.1
  have hCp := hC.1
  refine ⟨by unfold s6FinalBLow; positivity,?_,?_,?_⟩
  · rw [s6_final_b1_eq]
    unfold s6FinalBLow
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_right hVq (show 0 ≤ 3+R^2 by positivity)
    nlinarith only [hh]
  · rw [s6_final_b1_eq]
    rw [div_lt_one (by positivity)]
    linarith only [hVp]
  · unfold s6FinalB1D
    exact div_pos (neg_pos.2 (mul_neg_of_pos_of_neg (mul_pos hVp hCp) hT)) (by positivity)

private theorem s6_final_b1_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (s6FinalB1 R) (s6FinalB1D R d e) d := by
  have hh := ((s6_final_v_displacement_deriv hR hR1 hd hd1 he he1).const_sub (R^2)).div_const (3+R^2)
  have hfun : s6FinalB1 R=(fun d => (R^2-s6FinalV R d)/(3+R^2)) := funext (s6_final_b1_eq R)
  rw [hfun]
  exact hh.congr_deriv (by unfold s6FinalB1D; ring)

private theorem s6_final_zU_deriv (R d : ℝ) :
    HasDerivAt (costZU R) (s6FinalZUD R d) d := by
  have hh := (((hasDerivAt_id' d).const_mul (s6FinalA R)).const_add (s6FinalZL0 R)).sub
    ((hasDerivAt_pow 2 d).const_mul (3/2))
  refine hh.congr_deriv ?_
  unfold s6FinalZUD
  norm_num
  ring

private theorem s6_final_b_sum_eq (R d e : ℝ) :
    (1-4*s6VarianceFloor R d/(3+R^2))+(1-4*s6VarianceFloor R d/(3+(costT R d e)^2))=
    2*s6FinalB1 R d-(1-s6FinalB1 R d)*s6FinalNu R d e := by
  unfold s6FinalB1 s6FinalNu
  field_simp
  ring

private theorem s6_final_shear_deriv {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    HasDerivAt (fun d => s6FinalShearLoss R d e) (s6FinalShearD R d e) d := by
  have hB := s6_final_b1_deriv hR hR1 hd hd1 he he1
  have hN := s6_final_nu_deriv hR hR1 hd hd1 he he1
  have hZ := s6_final_zU_deriv R d
  have hsum := (hB.const_mul 2).sub ((hB.const_sub 1).mul hN)
  have hh := (hZ.mul hsum).div_const 8
  convert hh using 1
  · funext v
    unfold s6FinalShearLoss
    rw [s6_final_b_sum_eq]
    dsimp only [Pi.mul_apply,Pi.sub_apply]
  · unfold s6FinalShearD
    dsimp only [Pi.mul_apply,Pi.sub_apply]
    ring

private theorem s6_final_nu_closed_signs {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : 0 ≤ s6FinalNu R d e ∧ 0 < s6FinalNuD R d e := by
  have hT := costT_correlated_bounds hR hR1 hd hd1 he he1
  have hRp : 0 < R := by linarith only [hR]
  have hTp : 0 < costT R d e := by linarith only [hT.1,hR]
  have hTD := s6_final_td_neg hR hR1 hd hd1 he he1
  refine ⟨?_,?_⟩
  · unfold s6FinalNu
    exact div_nonneg (by nlinarith only [hT.2,hTp,hRp]) (by positivity)
  · unfold s6FinalNuD
    exact div_pos (mul_pos_of_neg_of_neg (by nlinarith only [hTp,sq_nonneg R]) hTD) (by positivity)

private theorem s6_final_ZU_d_pos {R d : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (_hd : 0 ≤ d) (hd1 : d ≤ 1/19) : 0 < s6FinalZUD R d := by
  have hRp : 0 < R := by linarith only [hR]
  have hRm : 0 < 1-R := by linarith only [hR1]
  have hA : (1/3:ℝ) < s6FinalA R := by
    unfold s6FinalA
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hRp]
  unfold s6FinalZUD
  linarith only [hA,hd1]

/-- The product Z_U nu has the paper's rational derivative ceiling. -/
private theorem s6_final_ZU_nu_derivative_bound {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalZUD R d*s6FinalNu R d e+costZU R d*s6FinalNuD R d e ≤
      s6FinalNuScale R e*(s6FinalZL0 R+2*s6FinalA R*d)/(1+2*d)^2 := by
  have hZ := (cost_shear_envelopes_pos hR hR1 hd hd1).1
  have hZd := s6_final_ZU_d_pos hR hR1 hd hd1
  have hN := s6_final_nu_upper_bounds hR hR1 hd hd1 he he1
  have hS := (s6_final_nu_coefficient_bounds hR hR1 he he1).1
  have hA := (s6_final_ad_bounds hR hR1).2.1
  have hm1 := mul_le_mul_of_nonneg_left hN.1 hZd.le
  have hm2 := mul_le_mul_of_nonneg_left hN.2 hZ.le
  have hfactor : s6FinalZUD R d*(s6FinalNuScale R e*d/(1+2*d))+
      costZU R d*(s6FinalNuScale R e/(1+2*d)^2)=
      s6FinalNuScale R e*(s6FinalZL0 R+2*s6FinalA R*d+
        (2*s6FinalA R-9/2)*d^2-6*d^3)/(1+2*d)^2 := by
    unfold s6FinalZUD costZU s6FinalA s6FinalZL0
    field_simp
    ring
  have hrest : (2*s6FinalA R-9/2)*d^2-6*d^3 ≤ 0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg (show 2*s6FinalA R-9/2 ≤ 0 by linarith only [hA]) (sq_nonneg d)
    have h3 : 0 ≤ d^3 := by positivity
    linarith only [h1,h3]
  have hnum : s6FinalNuScale R e*(s6FinalZL0 R+2*s6FinalA R*d+
      (2*s6FinalA R-9/2)*d^2-6*d^3) ≤ s6FinalNuScale R e*(s6FinalZL0 R+2*s6FinalA R*d) := by
    exact mul_le_mul_of_nonneg_left (by linarith only [hrest]) hS.le
  have hdiv := div_le_div_of_nonneg_right hnum (sq_nonneg (1+2*d))
  have hsum := add_le_add hm1 hm2
  rw [hfactor] at hsum
  exact hsum.trans hdiv


private theorem s6_final_nu_scale_budget {R e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (_he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalNuScale R e ≤ 2*s6FinalBLow R*s6FinalD R := by
  have hRp : 0 < R := by linarith only [hR]
  have hRs : 0 < 1-R^2 := by
    have hs := (s6_final_interval (show 9/31 ≤ R by linarith only [hR]) hR1).2.2
    linarith only [hs]
  have hid : 2*s6FinalBLow R*s6FinalD R=2*R*(1-R^2)/(3+R^2) := by
    unfold s6FinalBLow s6FinalD
    field_simp [hRp.ne']
  rw [hid]
  unfold s6FinalNuScale
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hm := mul_le_mul_of_nonneg_right (show e-1 ≤ 2 by linarith only [he1]) (mul_nonneg hRp.le hRs.le)
  nlinarith only [hm]

/-- E pays for the full derivative of Z_U nu, using the original norm deficit. -/
private theorem s6_final_ZU_nu_paid {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6FinalZUD R d*s6FinalNu R d e+costZU R d*s6FinalNuD R d e <
      2*s6FinalZUD R d*s6FinalBLow R := by
  have hbound := s6_final_ZU_nu_derivative_bound hR hR1 hd hd1 he he1
  have hscale := s6_final_nu_scale_budget hR hR1 he he1
  have hE := s6_final_e_pos hR hR1 hd hd1
  have hRp : 0 < R := by linarith only [hR]
  have h3 : 0 < 3-R := by linarith only [hR1]
  have hZ0 : 0 < s6FinalZL0 R := by unfold s6FinalZL0; positivity
  have hA := (s6_final_ad_bounds hR hR1).1
  have hB : 0 < s6FinalBLow R := by unfold s6FinalBLow; positivity
  have hC : 0 < s6FinalZL0 R+2*s6FinalA R*d := by positivity
  have hden : 0 < (1+2*d)^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hscale hC.le
  have hEclear : s6FinalD R*(s6FinalZL0 R+2*s6FinalA R*d) < s6FinalZUD R d*(1+2*d)^2 := by
    unfold s6FinalE at hE
    unfold s6FinalZUD
    linarith only [hE]
  have hstrict := mul_lt_mul_of_pos_left hEclear (show 0 < 2*s6FinalBLow R by positivity)
  have hdiv : s6FinalNuScale R e*(s6FinalZL0 R+2*s6FinalA R*d)/(1+2*d)^2 <
      2*s6FinalZUD R d*s6FinalBLow R := by
    rw [div_lt_iff₀ hden]
    nlinarith only [hmul,hstrict]
  exact hbound.trans_lt hdiv

private theorem s6_final_shearD_pos {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : 0 < s6FinalShearD R d e := by
  have hB := s6_final_b1_bounds hR hR1 hd hd1 he he1
  have hZp := (cost_shear_envelopes_pos hR hR1 hd hd1).1
  have hZd := s6_final_ZU_d_pos hR hR1 hd hd1
  have hN := s6_final_nu_closed_signs hR hR1 hd hd1 he he1
  have hpaid := s6_final_ZU_nu_paid hR hR1 hd hd1 he he1
  have hBp : 0 < s6FinalB1 R d := hB.1.trans_le hB.2.1
  have hBd := hB.2.2.2
  have hNp := hN.1
  have hNdp := hN.2
  have hP : 0 < s6FinalZUD R d*s6FinalNu R d e+costZU R d*s6FinalNuD R d e := by positivity
  have hm1 := mul_le_mul_of_nonneg_left hB.2.1 (show 0 ≤ 2*s6FinalZUD R d by positivity)
  have hm2 : 0 ≤ costZU R d*s6FinalB1D R d e*(2+s6FinalNu R d e) := by positivity
  have hm3 := mul_le_mul_of_nonneg_right (show 1-s6FinalB1 R d ≤ 1 by linarith only [hBp]) hP.le
  have hid : 8*s6FinalShearD R d e=
      2*s6FinalZUD R d*s6FinalB1 R d+costZU R d*s6FinalB1D R d e*(2+s6FinalNu R d e)-
      (1-s6FinalB1 R d)*(s6FinalZUD R d*s6FinalNu R d e+costZU R d*s6FinalNuD R d e) := by
    unfold s6FinalShearD
    ring
  linarith only [hid,hm1,hm2,hm3,hpaid]

/-- The shear loss increases on the closed displacement interval. -/
theorem s6_final_shear_monotone_displacement {R d v e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hdv : d ≤ v) (hv : v ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : s6FinalShearLoss R d e ≤ s6FinalShearLoss R v e := by
  exact ss_le_of_deriv (f:=fun v => s6FinalShearLoss R v e)
    (f':=fun v => s6FinalShearD R v e) hdv
    (fun y hy => s6_final_shear_deriv hR hR1 (hd.trans hy.1) (hy.2.trans hv) he he1)
    (fun y hy => (s6_final_shearD_pos hR hR1 (hd.trans hy.1.le) (hy.2.le.trans hv) he he1).le)

/-- The final exact score decreases with displacement, with no endpoint assumptions. -/
theorem s6_final_score_antitone_displacement {R d v e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hdv : d ≤ v) (hv : v ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : s6FinalScore R v e ≤ s6FinalScore R d e := by
  have hPair := s6_final_pair_antitone_displacement hR hR1 hd hdv hv he he1
  have hShear := s6_final_shear_monotone_displacement hR hR1 hd hdv hv he he1
  have hAnis := s6_final_anisotropy_monotone_displacement hR hR1 hd hdv hv he he1
  rw [s6_final_score_decomposition,s6_final_score_decomposition]
  linarith only [hPair,hShear,hAnis]

end SmoothedOctagon

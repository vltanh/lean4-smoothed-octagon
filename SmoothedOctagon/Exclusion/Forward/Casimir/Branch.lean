module

public import SmoothedOctagon.Exclusion.Forward.Casimir.Curvature

/-!
# The first scalar branch of the forward Casimir comparison

The exact derivative identities and a twice-integrated curvature bound place
the curve above its midpoint quadratic lower bound.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set Filter

noncomputable def fcBranchM' (U : ℝ) : ℝ := fcBranchM0' U-fcBranchLog' U
noncomputable def fcBranchM'' (U : ℝ) : ℝ := fcBranchM0'' U-fcBranchLog'' U
noncomputable def fcBranchCurve (U : ℝ) : ℝ := fcScale U*(75/32-(fcBranchM U)^2)
noncomputable def fcBranchSlope (U : ℝ) : ℝ :=
  fcScale' U*(75/32-(fcBranchM U)^2)-2*fcScale U*fcBranchM U*fcBranchM' U
noncomputable def fcCorrectionTail (U : ℝ) : ℝ :=
  2*fcScale U*fcBranchM0'' U*fcBranchLog U+
  4*fcScale' U*fcBranchM0' U*fcBranchLog U+
  fcScale'' U*(2*fcBranchM0 U*fcBranchLog U-(fcBranchLog U)^2)
noncomputable def fcCorrectionSecond (U : ℝ) : ℝ :=
  2*fcScale U*fcBranchM U*fcBranchLog'' U-2*fcScale U*(fcBranchLog' U)^2+
  4*(fcScale U*fcBranchM0' U+fcScale' U*fcBranchM U)*fcBranchLog' U+fcCorrectionTail U
noncomputable def fcBranchSecond (U : ℝ) : ℝ := fcBaseCurvature U+fcCorrectionSecond U

theorem fc_branchM_hasDerivAt {U : ℝ} (hU : 11/5 ≤ U) :
    HasDerivAt fcBranchM (fcBranchM' U) U := by
  exact (fc_branchM0_hasDerivAt (by linarith only [hU])).sub (fc_branchLog_hasDerivAt hU)

theorem fc_branchM'_hasDerivAt {U : ℝ} (hU : 11/5 ≤ U) :
    HasDerivAt fcBranchM' (fcBranchM'' U) U := by
  exact (fc_branchM0'_hasDerivAt (by linarith only [hU])).sub (fc_branchLog'_hasDerivAt hU)

theorem fc_branchCurve_hasDerivAt {U : ℝ} (hU : 11/5 ≤ U) :
    HasDerivAt fcBranchCurve (fcBranchSlope U) U := by
  have h := (fc_scale_hasDerivAt (by linarith only [hU])).mul
    (((fc_branchM_hasDerivAt hU).pow 2).const_sub (75/32:ℝ))
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply]
    unfold fcBranchSlope
    ring

theorem fc_branchSlope_hasDerivAt {U : ℝ} (hU : 11/5 ≤ U) :
    HasDerivAt fcBranchSlope (fcBranchSecond U) U := by
  have hU0 : 0 < U := by linarith only [hU]
  have hB := fc_scale_hasDerivAt hU0
  have hBp := fc_scale'_hasDerivAt hU0
  have hM := fc_branchM_hasDerivAt hU
  have hMp := fc_branchM'_hasDerivAt hU
  have h := (hBp.mul ((hM.pow 2).const_sub (75/32:ℝ))).sub
    ((((hB.const_mul 2).mul hM).mul hMp))
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply,Pi.mul_apply]
    unfold fcBranchSecond fcCorrectionSecond fcCorrectionTail
    rw [fc_baseCurvature_eq_raw hU0]
    unfold fcBranchM' fcBranchM'' fcBranchM
    ring

theorem fc_correctionTail_nonneg {U : ℝ} (hU : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    0 ≤ fcCorrectionTail U := by
  rcases fc_branch_uniform_bounds hU hhi with ⟨hBlo,hBhi,hBp0,hBp1,hMp0,hMp1,hMlo,hMhi⟩
  have hU0 : 0 < U := by linarith only [hU]
  have hL := fc_branchLog_nonneg hU
  have hB0 : 0 ≤ fcScale U := by unfold fcScale; positivity
  have hMpp0 : 0 ≤ fcBranchM0'' U := by unfold fcBranchM0''; positivity
  have hBpp0 : 0 ≤ fcScale'' U := by unfold fcScale''; positivity
  have hM0 : 0 ≤ fcBranchM0 U := by unfold fcBranchM at hMlo; linarith only [hMlo,hL]
  have hM : 0 ≤ fcBranchM U := by linarith only [hMlo]
  have hp1 : 0 ≤ 2*fcScale U*fcBranchM0'' U*fcBranchLog U := by positivity
  have hprod : 0 ≤ fcScale' U*fcBranchM0' U :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith only [hBp0]) (by linarith only [hMp0])
  have hp2 : 0 ≤ 4*fcScale' U*fcBranchM0' U*fcBranchLog U := by nlinarith only [mul_nonneg hprod hL]
  have hpair := mul_nonneg hL (add_nonneg hM0 hM)
  unfold fcBranchM at hpair
  have hinner : 0 ≤ 2*fcBranchM0 U*fcBranchLog U-(fcBranchLog U)^2 := by nlinarith only [hpair]
  have hp3 := mul_nonneg hBpp0 hinner
  unfold fcCorrectionTail
  linarith only [hp1,hp2,hp3]

theorem fc_correctionSecond_nonneg {U : ℝ} (hU : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    0 ≤ fcCorrectionSecond U := by
  rcases fc_branch_uniform_bounds hU hhi with ⟨hBlo,hBhi,hBp0,hBp1,hMp0,hMp1,hMlo,hMhi⟩
  have hLp := fc_branchLog'_bounds hU hhi
  have hc := fc_correction_core_nonneg (B := fcScale U) (Bp := fcScale' U)
    (M := fcBranchM U) (M0p := fcBranchM0' U) (Lp := fcBranchLog' U)
    (Lpp := fcBranchLog'' U) (d := U-11/5) hBlo.le hBhi.le
    (by linarith only [hBp1]) (by linarith only [hMp1]) hMlo.le hMhi.le
    hLp.1 hLp.2.le (fc_branchLog''_nonneg hU) (by linarith only [hhi] : U-11/5 ≤ 2/5)
    (fc_branchLog'_le_mul hU hhi)
  have ht := fc_correctionTail_nonneg hU hhi
  unfold fcCorrectionSecond
  linarith only [hc,ht]

theorem fc_branchSecond_pos {U : ℝ} (hU : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    0 < fcBranchSecond U := by
  have hb := fc_baseCurvature_pos hU hhi
  have hc := fc_correctionSecond_nonneg hU hhi
  unfold fcBranchSecond
  linarith only [hb,hc]

theorem fc_branchSecond_near {U : ℝ} (hU : 5/2 ≤ U) (hhi : U ≤ 13/5) :
    (1/192:ℝ) < fcBranchSecond U := by
  have hUlo : 11/5 ≤ U := by linarith only [hU]
  rcases fc_branch_uniform_bounds hUlo hhi with ⟨hBlo,hBhi,hBp0,hBp1,hMp0,hMp1,hMlo,hMhi⟩
  rcases fc_branch_near_minimum_bounds hU hhi with ⟨hBhi',hBp1',hMp1',hLpp⟩
  have hLp := fc_branchLog'_bounds hUlo hhi
  have hc := fc_correction_quantitative (B := fcScale U) (Bp := fcScale' U)
    (M := fcBranchM U) (M0p := fcBranchM0' U) (Lp := fcBranchLog' U)
    (Lpp := fcBranchLog'' U) (Base := fcBaseCurvature U) (Pos := fcCorrectionTail U) hBlo.le hBhi'.le
    (by linarith only [hBp1']) (by linarith only [hMp1']) hMlo.le hMhi.le
    hLp.1 hLp.2.le hLpp.le (fc_baseCurvature_near hU hhi).le (fc_correctionTail_nonneg hUlo hhi)
  unfold fcBranchSecond fcCorrectionSecond
  convert hc using 1; ring

theorem fc_branchSlope_monotone : MonotoneOn fcBranchSlope (Icc (11/5) (13/5)) := by
  apply ff_monotoneOn_Icc (f' := fcBranchSecond)
  · intro U hU; exact fc_branchSlope_hasDerivAt hU.1
  · intro U hU; exact (fc_branchSecond_pos hU.1 hU.2).le

theorem fc_branch_midpoint_slope_neg : fcBranchSlope (5/2) < 0 := by
  norm_num [fcBranchSlope,fcScale',fcBranchM,fcBranchM0,ff_e0,fcBranchLog,fcBranchX,
    fcLogCorrection,fcScale,fcBranchM',fcBranchM0',fcBranchLog',fcLogCorrection']

theorem fc_branch_midpoint_margin :
    (9193/50000:ℝ) < fcBranchCurve (5/2)-96*(fcBranchSlope (5/2))^2 := by
  norm_num [fcBranchCurve,fcBranchSlope,fcScale',fcBranchM,fcBranchM0,ff_e0,fcBranchLog,fcBranchX,
    fcLogCorrection,fcScale,fcBranchM',fcBranchM0',fcBranchLog',fcLogCorrection']

/-- The entire first branch, controlled by convexity and the natural
midpoint `5/2`. -/
theorem fc_branch_curve_gt {U : ℝ} (hU : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    (9193/50000:ℝ) < fcBranchCurve U := by
  have hm := fc_branch_midpoint_margin
  rcases le_total U (5/2) with hleft | hright
  · have hf : AntitoneOn fcBranchCurve (Icc U (5/2)) := by
      apply fc_antitoneOn_Icc (f' := fcBranchSlope)
      · intro t ht; exact fc_branchCurve_hasDerivAt (hU.trans ht.1)
      · intro t ht
        have hs := fc_branchSlope_monotone ⟨hU.trans ht.1,by linarith only [ht.2]⟩
          (show (5/2:ℝ) ∈ Icc (11/5) (13/5) by norm_num) ht.2
        exact (hs.trans_lt fc_branch_midpoint_slope_neg).le
    have hval := hf ⟨le_rfl,hleft⟩ ⟨hleft,le_rfl⟩ hleft
    nlinarith only [hm,hval,sq_nonneg (fcBranchSlope (5/2))]
  · have hquad := fc_second_order_lower (f := fcBranchCurve) (f1 := fcBranchSlope)
      (f2 := fcBranchSecond) (k := (1/192:ℝ)) hright
      (fun t ht => fc_branchCurve_hasDerivAt (by linarith only [ht.1]))
      (fun t ht => fc_branchSlope_hasDerivAt (by linarith only [ht.1]))
      (fun t ht => (fc_branchSecond_near ht.1 (ht.2.trans hhi)).le)
    have hsquare := fc_midpoint_square (fcBranchCurve (5/2)) (fcBranchSlope (5/2)) (U-5/2)
    nlinarith only [hm,hquad,hsquare]

end SmoothedOctagon

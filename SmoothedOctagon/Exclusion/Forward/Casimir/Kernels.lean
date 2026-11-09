module

public import SmoothedOctagon.Exclusion.Forward.Casimir.Shape

/-!
# Reciprocal kernels on the first Casimir branch

Monotonicity of the original logarithmic correction and scale functions gives
the bounds used in the scalar curvature comparison.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

theorem fc_logCorrection'_hasDerivAt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt fcLogCorrection' (fcLogCorrection'' x) x := by
  have hx1 : 1+x ≠ 0 := by linarith only [hx]
  have hx2 : 2+x ≠ 0 := by linarith only [hx]
  have h1 := (((hasDerivAt_id x).const_add 1).pow 2).inv (pow_ne_zero 2 hx1)
  have h2 := (((hasDerivAt_id x).const_add 2).pow 2).inv (pow_ne_zero 2 hx2)
  have h := ((h1.const_add 1).sub (h2.const_mul 8)).const_mul (2/3:ℝ)
  convert h using 1
  · ext y; simp [fcLogCorrection',div_eq_mul_inv]
  · simp only [id_eq,Pi.pow_apply]
    unfold fcLogCorrection''
    field_simp
    ring

theorem fc_logCorrection''_hasDerivAt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt fcLogCorrection'' (fcLogCorrection''' x) x := by
  have hx1 : 1+x ≠ 0 := by linarith only [hx]
  have hx2 : 2+x ≠ 0 := by linarith only [hx]
  have h1 := (((hasDerivAt_id x).const_add 1).pow 3).inv (pow_ne_zero 3 hx1)
  have h2 := (((hasDerivAt_id x).const_add 2).pow 3).inv (pow_ne_zero 3 hx2)
  have h := ((h2.const_mul 8).sub h1).const_mul (4/3:ℝ)
  convert h using 1
  · ext y; simp [fcLogCorrection'',div_eq_mul_inv]
  · simp only [id_eq,Pi.pow_apply]
    unfold fcLogCorrection'''
    field_simp
    ring

theorem fc_logCorrection''_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fcLogCorrection'' x := by
  have hx1 : 0 < 1+x := by linarith only [hx]
  have hx2 : 0 < 2+x := by linarith only [hx]
  have hp : (2+x)^3 ≤ (2*(1+x))^3 := pow_le_pow_left₀ hx2.le (by linarith only [hx]) 3
  rw [mul_pow] at hp
  have hdiv : 1/(1+x)^3 ≤ 8/(2+x)^3 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hp]
  unfold fcLogCorrection''
  linarith only [hdiv]

theorem fc_logCorrection'''_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/6) :
    0 < fcLogCorrection''' x := by
  have h1 : 0 < 1+x := by linarith only [hx0]
  have h2 : 0 < 2+x := by linarith only [hx0]
  have hp : ((13/7:ℝ)*(1+x))^4 ≤ (2+x)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hx1]) 4
  rw [mul_pow] at hp
  have hp1 : 0 < (1+x)^4 := by positivity
  have hstrict : 8*(1+x)^4 < (2+x)^4 := by nlinarith only [hp,hp1]
  have hdiv : 8/(2+x)^4 < 1/(1+x)^4 := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hstrict]
  unfold fcLogCorrection'''
  linarith only [hdiv]

theorem fc_logCorrection'_mono : MonotoneOn fcLogCorrection' (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx; exact (fc_logCorrection'_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx; exact (fc_logCorrection'_hasDerivAt (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 ≤ x := interior_subset hx
    rw [(fc_logCorrection'_hasDerivAt hx').deriv]
    exact fc_logCorrection''_nonneg hx'

theorem fc_logCorrection'_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fcLogCorrection' x := by
  have h := fc_logCorrection'_mono (show (0:ℝ) ∈ Ici 0 by norm_num) hx hx
  have hz : fcLogCorrection' 0=0 := by norm_num [fcLogCorrection']
  rw [hz] at h
  exact h

theorem fc_logCorrection''_mono : MonotoneOn fcLogCorrection'' (Icc 0 (1/6)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro x hx; exact (fc_logCorrection''_hasDerivAt hx.1).continuousAt.continuousWithinAt
  · intro x hx; exact (fc_logCorrection''_hasDerivAt (interior_subset hx).1).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(fc_logCorrection''_hasDerivAt hx'.1).deriv]
    exact (fc_logCorrection'''_pos hx'.1 hx'.2).le

/-- The increasing second reciprocal kernel controls its accumulated first
kernel from the exact zero initial derivative. -/
theorem fc_logCorrection'_le_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/6) :
    fcLogCorrection' x ≤ x*fcLogCorrection'' x := by
  have h := ff_le_of_deriv hx0
    (f := fun t => t*fcLogCorrection'' x-fcLogCorrection' t)
    (f' := fun t => fcLogCorrection'' x-fcLogCorrection'' t)
    (fun t ht => by
      have hd := ((hasDerivAt_id t).mul_const (fcLogCorrection'' x)).sub
        (fc_logCorrection'_hasDerivAt ht.1)
      convert hd using 1
      · rfl
      · ring)
    (fun t ht => by
      have hm := fc_logCorrection''_mono ⟨ht.1,ht.2.trans hx1⟩ ⟨hx0,hx1⟩ ht.2
      linarith only [hm])
  have hz : fcLogCorrection' 0=0 := by norm_num [fcLogCorrection']
  simp only [zero_mul,hz,sub_zero] at h
  linarith only [h]

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set
noncomputable def fcBranchX (U : ℝ) : ℝ := (5*U-11)/12
noncomputable def fcBranchLog (U : ℝ) : ℝ := fcLogCorrection (fcBranchX U)
noncomputable def fcBranchLog' (U : ℝ) : ℝ := (5/12)*fcLogCorrection' (fcBranchX U)
noncomputable def fcBranchLog'' (U : ℝ) : ℝ := (25/144)*fcLogCorrection'' (fcBranchX U)
noncomputable def fcBranchM0 (U : ℝ) : ℝ := ff_e0 U+(5*U+1)/192
noncomputable def fcBranchM0' (U : ℝ) : ℝ := -19/192-1/(1+U)^2
noncomputable def fcBranchM0'' (U : ℝ) : ℝ := 2/(1+U)^3
noncomputable def fcBranchM (U : ℝ) : ℝ := fcBranchM0 U-fcBranchLog U
noncomputable def fcScale' (U : ℝ) : ℝ := -(1+U)/(8*U^3)
noncomputable def fcScale'' (U : ℝ) : ℝ := (2*U+3)/(8*U^4)

theorem fc_branchX_mem {U : ℝ} (hlo : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    fcBranchX U ∈ Icc (0:ℝ) (1/6) := by
  unfold fcBranchX; constructor <;> linarith only [hlo,hhi]

theorem fc_branchLog_hasDerivAt {U : ℝ} (hU : 11/5 ≤ U) :
    HasDerivAt fcBranchLog (fcBranchLog' U) U := by
  have hx : 0 ≤ fcBranchX U := by unfold fcBranchX; linarith only [hU]
  have h := (fc_logCorrection_hasDerivAt hx).comp U
    ((((hasDerivAt_id U).const_mul 5).sub_const 11).div_const 12)
  convert h using 1
  · rfl
  · unfold fcBranchLog'; ring

theorem fc_branchLog'_hasDerivAt {U : ℝ} (hU : 11/5 ≤ U) :
    HasDerivAt fcBranchLog' (fcBranchLog'' U) U := by
  have hx : 0 ≤ fcBranchX U := by unfold fcBranchX; linarith only [hU]
  have h := ((fc_logCorrection'_hasDerivAt hx).comp U
    ((((hasDerivAt_id U).const_mul 5).sub_const 11).div_const 12)).const_mul (5/12:ℝ)
  convert h using 1
  · rfl
  · unfold fcBranchLog''; ring

theorem fc_branchLog_nonneg {U : ℝ} (hU : 11/5 ≤ U) : 0 ≤ fcBranchLog U := by
  have hx : 0 ≤ fcBranchX U := by unfold fcBranchX; linarith only [hU]
  unfold fcBranchLog fcLogCorrection
  positivity

theorem fc_branchLog'_bounds {U : ℝ} (hlo : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    0 ≤ fcBranchLog' U ∧ fcBranchLog' U < 1/100 := by
  have hx := fc_branchX_mem hlo hhi
  have hn := fc_logCorrection'_nonneg hx.1
  have hm := fc_logCorrection'_mono hx.1 (show (1/6:ℝ) ∈ Ici 0 by norm_num) hx.2
  have hend : (5/12:ℝ)*fcLogCorrection' (1/6) < 1/100 := by norm_num [fcLogCorrection']
  unfold fcBranchLog'
  constructor
  · positivity
  · linarith only [hm,hend]

theorem fc_branchLog''_nonneg {U : ℝ} (hU : 11/5 ≤ U) : 0 ≤ fcBranchLog'' U := by
  have hx : 0 ≤ fcBranchX U := by unfold fcBranchX; linarith only [hU]
  have h := fc_logCorrection''_nonneg hx
  unfold fcBranchLog''
  positivity

theorem fc_branchLog'_le_mul {U : ℝ} (hlo : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    fcBranchLog' U ≤ (U-11/5)*fcBranchLog'' U := by
  have hx := fc_branchX_mem hlo hhi
  have hm := mul_le_mul_of_nonneg_left (fc_logCorrection'_le_mul hx.1 hx.2)
    (by norm_num : (0:ℝ) ≤ 5/12)
  unfold fcBranchLog' fcBranchLog''
  convert hm using 1
  unfold fcBranchX
  ring

theorem fc_branchLog''_lower {U : ℝ} (hlo : 5/2 ≤ U) (hhi : U ≤ 13/5) :
    (3/100:ℝ) < fcBranchLog'' U := by
  have hx := fc_branchX_mem (by linarith only [hlo]) hhi
  have hxm : (1/8:ℝ) ≤ fcBranchX U := by unfold fcBranchX; linarith only [hlo]
  have hm := fc_logCorrection''_mono (show (1/8:ℝ) ∈ Icc 0 (1/6) by norm_num) hx hxm
  have hend : (3/100:ℝ) < (25/144)*fcLogCorrection'' (1/8) := by norm_num [fcLogCorrection'']
  unfold fcBranchLog''
  linarith only [hm,hend]

theorem fc_scale_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcScale (fcScale' U) U := by
  have h := (((hasDerivAt_id U).const_add 1).pow 2).div
    ((hasDerivAt_pow 2 U).const_mul 16) (by positivity)
  convert h using 1
  · rfl
  · simp only [id_eq,Pi.pow_apply]
    unfold fcScale'
    field_simp
    ring

theorem fc_scale'_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcScale' (fcScale'' U) U := by
  have h := (((hasDerivAt_id U).const_add 1).neg).div
    ((hasDerivAt_pow 3 U).const_mul 8) (by positivity)
  convert h using 1
  · rfl
  · simp only [id_eq,Pi.neg_apply]
    unfold fcScale''
    field_simp
    ring

theorem fc_branchM0_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcBranchM0 (fcBranchM0' U) U := by
  have hK : 1+U ≠ 0 := by linarith only [hU]
  have h := (((((hasDerivAt_id U).const_add 1).div_const 8).const_sub 1).add
    ((((hasDerivAt_id U).const_add 1).inv hK).const_mul 1)).add
      ((((hasDerivAt_id U).const_mul 5).add_const 1).div_const 192)
  convert h using 1
  · rfl
  · simp only [id_eq]
    unfold fcBranchM0'
    ring

theorem fc_branchM0'_hasDerivAt {U : ℝ} (hU : 0 < U) :
    HasDerivAt fcBranchM0' (fcBranchM0'' U) U := by
  have hK : 1+U ≠ 0 := by linarith only [hU]
  have h := ((((hasDerivAt_id U).const_add 1).pow 2).inv (pow_ne_zero 2 hK)).const_sub (-19/192:ℝ)
  convert h using 1
  · ext x; simp [fcBranchM0',one_div]
  · simp only [id_eq,Pi.pow_apply]
    unfold fcBranchM0''
    field_simp
    ring

theorem fc_antitoneOn_Icc {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc a b, f' x ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx; rw [(hd x (interior_subset hx)).deriv]; exact hn x (interior_subset hx)

theorem fc_scale_antitone : AntitoneOn fcScale (Icc (11/5) (13/5)) := by
  apply fc_antitoneOn_Icc (f' := fcScale')
  · intro x hx; exact fc_scale_hasDerivAt (by linarith only [hx.1])
  · intro x hx
    have hx0 : 0 < x := by linarith only [hx.1]
    unfold fcScale'
    exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hx0]) (by positivity)

theorem fc_scale'_monotone : MonotoneOn fcScale' (Icc (11/5) (13/5)) := by
  apply ff_monotoneOn_Icc (f' := fcScale'')
  · intro x hx; exact fc_scale'_hasDerivAt (by linarith only [hx.1])
  · intro x hx
    have hx0 : 0 < x := by linarith only [hx.1]
    unfold fcScale''; positivity

theorem fc_branchM0_antitone : AntitoneOn fcBranchM0 (Icc (11/5) (13/5)) := by
  apply fc_antitoneOn_Icc (f' := fcBranchM0')
  · intro x hx; exact fc_branchM0_hasDerivAt (by linarith only [hx.1])
  · intro x hx
    unfold fcBranchM0'
    have hrec : 0 ≤ 1/(1+x)^2 := by positivity
    linarith only [hrec]

theorem fc_branchM0'_monotone : MonotoneOn fcBranchM0' (Icc (11/5) (13/5)) := by
  apply ff_monotoneOn_Icc (f' := fcBranchM0'')
  · intro x hx; exact fc_branchM0'_hasDerivAt (by linarith only [hx.1])
  · intro x hx
    have hx0 : 0 < x := by linarith only [hx.1]
    unfold fcBranchM0''; positivity

theorem fc_branchLog_monotone : MonotoneOn fcBranchLog (Icc (11/5) (13/5)) := by
  apply ff_monotoneOn_Icc (f' := fcBranchLog')
  · intro x hx; exact fc_branchLog_hasDerivAt hx.1
  · intro x hx; exact (fc_branchLog'_bounds hx.1 hx.2).1

theorem fc_branchM_antitone : AntitoneOn fcBranchM (Icc (11/5) (13/5)) := by
  intro x hx y hy hxy
  have hM0 := fc_branchM0_antitone hx hy hxy
  have hL := fc_branchLog_monotone hx hy hxy
  unfold fcBranchM
  linarith only [hM0,hL]

/-- Every bound is obtained by monotonicity of an intrinsic kernel and
substitution at the branch endpoints. -/
theorem fc_branch_uniform_bounds {U : ℝ} (hlo : 11/5 ≤ U) (hhi : U ≤ 13/5) :
    7/60 < fcScale U ∧ fcScale U < 2/15 ∧
    0 < -fcScale' U ∧ -fcScale' U < 1/24 ∧
    0 < -fcBranchM0' U ∧ -fcBranchM0' U < 1/5 ∧
    8/9 < fcBranchM U ∧ fcBranchM U < 1 := by
  have hmem : U ∈ Icc (11/5:ℝ) (13/5) := ⟨hlo,hhi⟩
  have hlow : (11/5:ℝ) ∈ Icc (11/5) (13/5) := by norm_num
  have hhigh : (13/5:ℝ) ∈ Icc (11/5) (13/5) := by norm_num
  have hBlo := fc_scale_antitone hmem hhigh hhi
  have hBhi := fc_scale_antitone hlow hmem hlo
  have hBp := fc_scale'_monotone hlow hmem hlo
  have hM0p := fc_branchM0'_monotone hlow hmem hlo
  have hMlo := fc_branchM_antitone hmem hhigh hhi
  have hMhi := fc_branchM_antitone hlow hmem hlo
  have heBlo : (7/60:ℝ) < fcScale (13/5) := by norm_num [fcScale]
  have heBhi : fcScale (11/5) < (2/15:ℝ) := by norm_num [fcScale]
  have heBp : -fcScale' (11/5) < (1/24:ℝ) := by norm_num [fcScale']
  have heM0p : -fcBranchM0' (11/5) < (1/5:ℝ) := by norm_num [fcBranchM0']
  have heMlo : (8/9:ℝ) < fcBranchM (13/5) := by
    norm_num [fcBranchM,fcBranchM0,fcBranchLog,fcBranchX,fcLogCorrection,ff_e0]
  have heMhi : fcBranchM (11/5) < (1:ℝ) := by
    norm_num [fcBranchM,fcBranchM0,fcBranchLog,fcBranchX,fcLogCorrection,ff_e0]
  have hU0 : 0 < U := by linarith only [hlo]
  have hBp0 : 0 < -fcScale' U := by
    unfold fcScale'
    have hd : 0 < (1+U)/(8*U^3) := by positivity
    simpa only [neg_div,neg_neg] using hd
  have hM0p0 : 0 < -fcBranchM0' U := by
    unfold fcBranchM0'
    have hrec : 0 ≤ 1/(1+U)^2 := by positivity
    linarith only [hrec]
  exact ⟨heBlo.trans_le hBlo,hBhi.trans_lt heBhi,hBp0,by linarith only [hBp,heBp],
    hM0p0,by linarith only [hM0p,heM0p],heMlo.trans_le hMlo,hMhi.trans_lt heMhi⟩

theorem fc_branch_near_minimum_bounds {U : ℝ} (hlo : 5/2 ≤ U) (hhi : U ≤ 13/5) :
    fcScale U < 1/8 ∧ -fcScale' U < 1/32 ∧ -fcBranchM0' U < 3/16 ∧
      3/100 < fcBranchLog'' U := by
  have hmem : U ∈ Icc (11/5:ℝ) (13/5) := ⟨by linarith only [hlo],hhi⟩
  have hmid : (5/2:ℝ) ∈ Icc (11/5) (13/5) := by norm_num
  have hB := fc_scale_antitone hmid hmem hlo
  have hBp := fc_scale'_monotone hmid hmem hlo
  have hM0p := fc_branchM0'_monotone hmid hmem hlo
  have heB : fcScale (5/2) < (1/8:ℝ) := by norm_num [fcScale]
  have heBp : -fcScale' (5/2) < (1/32:ℝ) := by norm_num [fcScale']
  have heM0p : -fcBranchM0' (5/2) < (3/16:ℝ) := by norm_num [fcBranchM0']
  exact ⟨hB.trans_lt heB,by linarith only [hBp,heBp],by linarith only [hM0p,heM0p],
    fc_branchLog''_lower hlo hhi⟩

end SmoothedOctagon

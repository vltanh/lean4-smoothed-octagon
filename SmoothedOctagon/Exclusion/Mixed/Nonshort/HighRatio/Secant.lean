module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.CentreGap
public import Mathlib.Analysis.Convex.Deriv

/-!
# The physical secant path and its variance ceiling

First-contact comparison preserves the right switching floor as the middle
margin rises. Reciprocal variance and Taylor remainders give a strict ceiling.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

noncomputable def mhtSecC (C D : ℝ) : ℝ :=
  (m2g C 1-m2Sec 1 C D+D*(m2Sec 1 C D-m2g C D))/(C*(D-1))

/-- The homogeneous derivative of the actual incident secant. -/
theorem mhtSec_hasDerivAt_C {C D : ℝ} (hC : 0 < C) (hD : 1 < D) :
    HasDerivAt (fun x => m2Sec 1 x D) (mhtSecC C D) C := by
  have hcp : 0 < 1+C := by linarith only [hC]
  have hdp : 0 < D+C := by linarith only [hD,hC]
  have hDm : D-1 ≠ 0 := by linarith only [hD]
  have hrat : 0 < (D+C)/(1+C) := div_pos hdp hcp
  have hid := hasDerivAt_id' C
  have h1 := hid.const_add 1
  have hd := hid.const_add D
  have h := ((hasDerivAt_const C (1:ℝ)).add
    ((hid.pow 2).div (h1.mul hd) (mul_ne_zero hcp.ne' hdp.ne'))).sub
    ((hid.div_const (D-1)).mul ((hd.div h1 hcp.ne').log hrat.ne'))
  convert h using 1
  · ext x
    rw [m2Sec_of_ne (ne_of_lt hD)]
    rfl
  · unfold mhtSecC
    rw [m2Sec_of_ne (ne_of_lt hD)]
    unfold m2g
    norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    field_simp
    ring

theorem mhtg_hasDerivAt_C {C D : ℝ} (hCD : 0 < C+D) :
    HasDerivAt (fun x => m2g x D) (D*(C-D)/(C+D)^3) C := by
  have hid := hasDerivAt_id' C
  have h := (((hid.pow 2).add (hid.mul_const D)).add_const (D^2)).div
    ((hid.add_const D).pow 2) (pow_ne_zero 2 hCD.ne')
  change HasDerivAt (fun x => (x^2+x*D+D^2)/(x+D)^2) _ C
  refine h.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
  field_simp
  ring

theorem mhtS_le_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z)
    (hn : ∀ z ∈ Ioo x y, 0 ≤ f' z) : f x ≤ f y := by
  have hm : MonotoneOn f (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hd z (interior_subset hz)).deriv]
      exact hn z (by simpa only [interior_Icc] using hz)
  exact hm (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

theorem mhtg_ge_floor {C s : ℝ} (h : C+s ≠ 0) : (3/4:ℝ) ≤ m2g C s := by
  have hid : m2g C s-3/4 = (C-s)^2/(4*(C+s)^2) := by
    unfold m2g
    field_simp
    ring
  have hp : 0 ≤ (C-s)^2/(4*(C+s)^2) := div_nonneg (sq_nonneg _) (by positivity)
  linarith only [hid,hp]

theorem mhtSec_ge_floor {C D : ℝ} (hC : 0 < C) (hD : 1 < D) :
    (3/4:ℝ) ≤ m2Sec 1 C D := by
  have hm := mhtS_le_of_deriv hD.le
    (f := fun s => nsrG C s-(3/4)*s) (f' := fun s => m2g C s-3/4)
    (fun s hs => by
      have hd := (nsr_hasDerivAt_G (by linarith only [hs.1,hC] : 0<C+s)).sub
        ((hasDerivAt_id' s).const_mul (3/4))
      convert hd using 1; ring)
    (fun s hs => sub_nonneg.mpr (mhtg_ge_floor (by linarith only [hs.1,hC])))
  rw [nsr_sec_eq_G (by norm_num) hC (by linarith only [hD]) (ne_of_lt hD)]
  rw [le_div_iff₀ (by linarith only [hD])]
  linarith only [hm]

/-- The actual secant stays below its left switching ceiling underD<C². -/
theorem mhtSec_lt_left {C D : ℝ} (hC : 1 < C) (hD : 1 < D) (hshape : D < C^2) :
    m2Sec 1 C D < m2g C 1 := by
  have hc : 0 < C := by linarith only [hC]
  have hd : 0 < D := by linarith only [hD]
  have hch := nsr_sec_lt_chord (a := 1) (c := C) (d := D)
    (by norm_num) hc hD (by simpa only [one_mul] using hshape)
  have hid := nsr_m2g_sub (B := C) (s1 := 1) (s2 := D)
    (by linarith only [hC]) (by linarith only [hC,hD])
  have hp : 0 < C*(D-1)*(C^2-1*D)/((C+1)^2*(C+D)^2) := by
    apply div_pos
    · exact mul_pos (mul_pos hc (sub_pos.mpr hD)) (by simpa only [one_mul] using sub_pos.mpr hshape)
    · positivity
  have hends : m2g C D < m2g C 1 := by linarith only [hid,hp]
  linarith only [hch,hends]

/-- ForC≥D the right endpoint is below the average, independently of contact propagation. -/
theorem mhtSec_gt_right {C D : ℝ} (hD : 1 < D) (hDC : D ≤ C) :
    m2g C D < m2Sec 1 C D := by
  have hc : 0 < C := by linarith only [hD,hDC]
  have hg := nsr_G_sub_gt (B := C) (z := 1) (P := D) (c := m2g C D)
    (by linarith only [hc]) hD (fun s hs0 hs1 => by
      have hid := nsr_m2g_sub (B := C) (s1 := s) (s2 := D)
        (by linarith only [hc,hs0]) (by linarith only [hc,hD])
      have hsq : D^2 ≤ C^2 := by nlinarith only [hD,hDC,sq_nonneg (C-D)]
      have hprod : s*D < D^2 := by nlinarith only [hs1,hD]
      have hp : 0 < C*(D-s)*(C^2-s*D)/((C+s)^2*(C+D)^2) := by
        apply div_pos
        · exact mul_pos (mul_pos hc (sub_pos.mpr hs1)) (by linarith only [hsq,hprod])
        · have : 0 < s := by linarith only [hs0]
          positivity
      linarith only [hid,hp])
  rw [nsr_sec_eq_G (by norm_num) hc (by linarith only [hD]) (ne_of_lt hD),
    lt_div_iff₀ (by linarith only [hD])]
  exact hg

/-- The incoming right-endpoint floor is retained whileC≤D. -/
theorem mhtSec_gap_preserved {C0 C D : ℝ} (hC0 : 1 < C0) (hC0C : C0 ≤ C)
    (hD : 1 < D) (hCD : C ≤ D) (hshape : D < C0^2)
    (hinit : m2g C0 D ≤ m2Sec 1 C0 D) : m2g C D ≤ m2Sec 1 C D := by
  let f : ℝ → ℝ := fun x => -(m2Sec 1 x D-m2g x D)
  let fp : ℝ → ℝ := fun x => -(mhtSecC x D-D*(x-D)/(x+D)^3)
  have hd : ∀ x ∈ Icc C0 C, HasDerivAt f (fp x) x := by
    intro x hx
    have hx0 : 0 < x := by linarith only [hC0,hx.1]
    exact ((mhtSec_hasDerivAt_C hx0 hD).sub
      (mhtg_hasDerivAt_C (by linarith only [hx0,hD]))).neg
  have hstart : f C0 ≤ 0 := by dsimp [f]; linarith only [hinit]
  have hbound : ∀ x ∈ Ico C0 C, f x = 0 → fp x < 0 := by
    intro x hx hf
    have hxC : 1 < x := by linarith only [hC0,hx.1]
    have hxD : x ≤ D := le_trans hx.2.le hCD
    have hxx : C0^2 ≤ x^2 := by nlinarith only [hx.1,hC0,sq_nonneg (x-C0)]
    have hleft := mhtSec_lt_left hxC hD (lt_of_lt_of_le hshape hxx)
    have heq : m2Sec 1 x D=m2g x D := by dsimp [f] at hf; linarith only [hf]
    rw [heq] at hleft
    have hvc : 0 < mhtSecC x D := by
      unfold mhtSecC
      rw [heq]
      apply div_pos
      · linarith only [hleft]
      · exact mul_pos (by linarith only [hxC]) (by linarith only [hD])
    have hgc : D*(x-D)/(x+D)^3 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hD]) (by linarith only [hxD])
      · have : 0 < x+D := by linarith only [hxC,hD]
        positivity
    dsimp [fp]
    linarith only [hvc,hgc]
  have hf := image_le_of_deriv_right_lt_deriv_boundary
    (f := f) (f' := fp) (a := C0) (b := C) (B := fun _ => 0) (B' := fun _ => 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    hstart (fun x => hasDerivAt_const x 0) hbound (right_mem_Icc.mpr hC0C)
  dsimp [f] at hf
  linarith only [hf]

/-- Actual secant monotonicity on the entire path toC=3/2, with no assumed derivative sign. -/
theorem mhtSecC_pos_on_path {C0 C D : ℝ} (hC0 : 1 < C0) (hC0C : C0 ≤ C)
    (hD : 1 < D) (hshape : D < C0^2)
    (hinit : m2g C0 D ≤ m2Sec 1 C0 D) : 0 < mhtSecC C D := by
  have hC : 1 < C := lt_of_lt_of_le hC0 hC0C
  have hsq : C0^2 ≤ C^2 := by nlinarith only [hC0C,hC0,sq_nonneg (C-C0)]
  have hleft := mhtSec_lt_left hC hD (lt_of_lt_of_le hshape hsq)
  have hright : m2g C D ≤ m2Sec 1 C D := by
    rcases le_total C D with h | h
    · exact mhtSec_gap_preserved hC0 hC0C hD h hshape hinit
    · exact (mhtSec_gt_right hD h).le
  unfold mhtSecC
  apply div_pos
  · have hp := mul_nonneg (by linarith only [hD] : 0≤D) (sub_nonneg.mpr hright)
    linarith only [hleft,hp]
  · exact mul_pos (by linarith only [hC]) (by linarith only [hD])


noncomputable def mhtg1 (C s : ℝ) : ℝ := C*(s-C)/(C+s)^3
noncomputable def mhtg2 (C s : ℝ) : ℝ := 2*C*(2*C-s)/(C+s)^4
noncomputable def mhtg3 (C s : ℝ) : ℝ := 6*C*(s-3*C)/(C+s)^5

theorem mhtg_hasDerivAt_s {C s : ℝ} (h : 0 < C+s) :
    HasDerivAt (m2g C) (mhtg1 C s) s := by
  have hi := hasDerivAt_id' s
  have hn := (((hasDerivAt_const s (C^2)).add (hi.const_mul C)).add (hi.pow 2))
  have hd := (hi.const_add C).pow 2
  have hg := hn.div hd (pow_ne_zero 2 h.ne')
  change HasDerivAt (fun x => (C^2+C*x+x^2)/(C+x)^2) _ s
  refine hg.congr_deriv ?_
  unfold mhtg1
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,id_eq]
  field_simp
  ring
theorem mhtg1_hasDerivAt {C s : ℝ} (h : 0 < C+s) :
    HasDerivAt (mhtg1 C) (mhtg2 C s) s := by
  have hi := hasDerivAt_id' s
  have hg := ((hi.sub_const C).const_mul C).div ((hi.const_add C).pow 3) (pow_ne_zero 3 h.ne')
  refine hg.congr_deriv ?_
  unfold mhtg2
  norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
  field_simp
  ring
private theorem mhtg2_hasDerivAt {C s : ℝ} (h : 0 < C+s) :
    HasDerivAt (mhtg2 C) (mhtg3 C s) s := by
  have hi := hasDerivAt_id' s
  have hg := ((hi.const_sub (2*C)).const_mul (2*C)).div
    ((hi.const_add C).pow 4) (pow_ne_zero 4 h.ne')
  refine hg.congr_deriv ?_
  unfold mhtg3
  norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
  field_simp
  ring

noncomputable def mhtSecD1 (C D : ℝ) : ℝ := (m2g C D-m2Sec 1 C D)/(D-1)
noncomputable def mhtSecD2 (C D : ℝ) : ℝ :=
  (mhtg1 C D*(D-1)-2*(m2g C D-m2Sec 1 C D))/(D-1)^2
noncomputable def mhtSecD3 (C D : ℝ) : ℝ :=
  (mhtg2 C D*(D-1)^2-3*mhtg1 C D*(D-1)+6*(m2g C D-m2Sec 1 C D))/(D-1)^3

/-- The actual secant, differentiated in its upper endpoint. -/
theorem mhtSec_hasDerivAt_D {C D : ℝ} (hC : 0 < C) (hD : 1 < D) :
    HasDerivAt (fun x => m2Sec 1 C x) (mhtSecD1 C D) D := by
  have hCp : 0 < 1+C := by linarith only [hC]
  have hDp : 0 < D+C := by linarith only [hD,hC]
  have hDm : D-1 ≠ 0 := by linarith only [hD]
  have hratio : 0 < (D+C)/(1+C) := div_pos hDp hCp
  let f : ℝ → ℝ := fun x => 1+C^2/((1+C)*(x+C))-C/(x-1)*Real.log ((x+C)/(1+C))
  have hi := hasDerivAt_id' D
  have hg := ((hasDerivAt_const D (1:ℝ)).add
    ((hasDerivAt_const D (C^2)).div ((hi.add_const C).const_mul (1+C))
      (mul_ne_zero hCp.ne' hDp.ne'))).sub
    (((hasDerivAt_const D C).div (hi.sub_const 1) hDm).mul
      (((hi.add_const C).div_const (1+C)).log hratio.ne'))
  have hd : HasDerivAt f (mhtSecD1 C D) D := by
    refine hg.congr_deriv ?_
    unfold mhtSecD1
    rw [m2Sec_of_ne (ne_of_lt hD)]
    unfold m2g
    norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    field_simp
    ring
  have heq : (fun x => m2Sec 1 C x) =ᶠ[nhds D] f := by
    filter_upwards [eventually_gt_nhds hD] with x hx
    exact m2Sec_of_ne (ne_of_lt hx)
  exact hd.congr_of_eventuallyEq heq

theorem mhtSecD1_hasDerivAt {C D : ℝ} (hC : 0 < C) (hD : 1 < D) :
    HasDerivAt (mhtSecD1 C) (mhtSecD2 C D) D := by
  have hCD : 0 < C+D := by linarith only [hC,hD]
  have hDm : D-1 ≠ 0 := by linarith only [hD]
  have hg := ((mhtg_hasDerivAt_s hCD).sub (mhtSec_hasDerivAt_D hC hD)).div
    ((hasDerivAt_id' D).sub_const 1) hDm
  refine hg.congr_deriv ?_
  unfold mhtSecD2 mhtSecD1
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
  field_simp
  ring

theorem mhtSecD2_hasDerivAt {C D : ℝ} (hC : 0 < C) (hD : 1 < D) :
    HasDerivAt (mhtSecD2 C) (mhtSecD3 C D) D := by
  have hCD : 0 < C+D := by linarith only [hC,hD]
  have hDm : D-1 ≠ 0 := by linarith only [hD]
  have hi := (hasDerivAt_id' D).sub_const 1
  have hg := (((mhtg1_hasDerivAt hCD).mul hi).sub
    (((mhtg_hasDerivAt_s hCD).sub (mhtSec_hasDerivAt_D hC hD)).const_mul 2)).div
    (hi.pow 2) (pow_ne_zero 2 hDm)
  refine hg.congr_deriv ?_
  unfold mhtSecD3 mhtSecD1
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
  field_simp
  ring

private theorem mhtg2_strictAnti {C D : ℝ} (hC : 0 < C) (_hD : 1 < D) (hDC : D < 3*C) :
    StrictAntiOn (mhtg2 C) (Icc (1:ℝ) D) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 1 D)
  · exact fun s hs => (mhtg2_hasDerivAt (by linarith only [hC,hs.1])).continuousAt.continuousWithinAt
  · intro s hs
    obtain ⟨hs0,hs1⟩ := interior_subset hs
    rw [(mhtg2_hasDerivAt (by linarith only [hC,hs0])).deriv]
    unfold mhtg3
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg (by linarith only [hC]) (by linarith only [hs1,hDC])
    · have : 0 < C+s := by linarith only [hC,hs0]
      positivity

noncomputable def mhtgRemainder (C D s : ℝ) : ℝ :=
  m2g C s-m2g C D-mhtg1 C D*(s-D)-mhtg2 C D*(s-D)^2/2
noncomputable def mhtgRemainder1 (C D s : ℝ) : ℝ :=
  mhtg1 C s-mhtg1 C D-mhtg2 C D*(s-D)
noncomputable def mhtgRemainder2 (C D s : ℝ) : ℝ := mhtg2 C s-mhtg2 C D
private theorem mhtgRemainder_hasDerivAt {C D s : ℝ} (h : 0 < C+s) :
    HasDerivAt (mhtgRemainder C D) (mhtgRemainder1 C D s) s := by
  have hi := (hasDerivAt_id' s).sub_const D
  have hd := (((mhtg_hasDerivAt_s h).sub_const (m2g C D)).sub
    (hi.const_mul (mhtg1 C D))).sub (((hi.pow 2).const_mul (mhtg2 C D)).div_const 2)
  refine hd.congr_deriv ?_
  unfold mhtgRemainder1
  norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
  ring
private theorem mhtgRemainder1_hasDerivAt {C D s : ℝ} (h : 0 < C+s) :
    HasDerivAt (mhtgRemainder1 C D) (mhtgRemainder2 C D s) s := by
  have hd := ((mhtg1_hasDerivAt h).sub_const (mhtg1 C D)).sub
    (((hasDerivAt_id' s).sub_const D).const_mul (mhtg2 C D))
  exact hd.congr_deriv (by unfold mhtgRemainder2; ring)

/-- The positive backward Taylor remainder integrates the negative third derivative. -/
theorem mhtgRemainder_pos {C D s : ℝ} (hC : 0 < C) (hD : 1 < D) (hDC : D < 3*C)
    (hs : s ∈ Ico (1:ℝ) D) : 0 < mhtgRemainder C D s := by
  have hpos : ∀ x ∈ Ioo (1:ℝ) D, 0 < mhtgRemainder2 C D x := by
    intro x hx
    unfold mhtgRemainder2
    exact sub_pos.mpr ((mhtg2_strictAnti hC hD hDC) ⟨hx.1.le,hx.2.le⟩ (right_mem_Icc.mpr hD.le) hx.2)
  have hmono : StrictMonoOn (mhtgRemainder1 C D) (Ioo (1:ℝ) D) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 1 D)
    · exact fun x hx => (mhtgRemainder1_hasDerivAt
        (by linarith only [hC,hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(mhtgRemainder1_hasDerivAt (by linarith only [hC,hx'.1])).deriv]
      exact hpos x hx'
  have hc : StrictConvexOn ℝ (Icc (1:ℝ) D) (mhtgRemainder C D) := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 1 D)
    · exact fun x hx => (mhtgRemainder_hasDerivAt
        (by linarith only [hC,hx.1])).continuousAt.continuousWithinAt
    · intro x hx y hy hxy
      rw [interior_Icc] at hx hy
      rw [(mhtgRemainder_hasDerivAt (by linarith only [hC,hx.1])).deriv,
        (mhtgRemainder_hasDerivAt (by linarith only [hC,hy.1])).deriv]
      exact hmono hx hy hxy
  have hd : HasDerivAt (mhtgRemainder C D) 0 D := by
    convert mhtgRemainder_hasDerivAt (by linarith only [hC,hD] : 0<C+D) using 1
    unfold mhtgRemainder1
    ring
  have hsup := hc.slope_lt_of_hasDerivAt (Ico_subset_Icc_self hs) (right_mem_Icc.mpr hD.le) hs.2 hd
  rw [slope_def_field] at hsup
  have hm := (div_lt_iff₀ (sub_pos.mpr hs.2)).mp hsup
  have hz : mhtgRemainder C D D=0 := by unfold mhtgRemainder; ring
  rw [hz] at hm
  linarith only [hm]

/-- The actual secant has negative third upper-endpoint derivative. -/
theorem mhtSecD3_neg {C D : ℝ} (hC : 0 < C) (hD : 1 < D) (hDC : D < 3*C) :
    mhtSecD3 C D < 0 := by
  let F : ℝ → ℝ := fun s => nsrG C s-m2g C D*s-
    mhtg1 C D*(s-D)^2/2-mhtg2 C D*(s-D)^3/6
  have hd : ∀ s ∈ Icc (1:ℝ) D, HasDerivAt F (mhtgRemainder C D s) s := by
    intro s hs
    have hi := (hasDerivAt_id' s).sub_const D
    have h := (((nsr_hasDerivAt_G (B := C) (s := s) (by linarith only [hC,hs.1])).sub
      ((hasDerivAt_id' s).const_mul (m2g C D))).sub
      (((hi.pow 2).const_mul (mhtg1 C D)).div_const 2)).sub
      (((hi.pow 3).const_mul (mhtg2 C D)).div_const 6)
    refine h.congr_deriv ?_
    unfold mhtgRemainder
    norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
    ring
  have hm : StrictMonoOn F (Icc (1:ℝ) D) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 D)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact mhtgRemainder_pos hC hD hDC
        ⟨(interior_subset hs).1,(show s<D from by have := hs; rw [interior_Icc] at this; exact this.2)⟩
  have hh := hm (left_mem_Icc.mpr hD.le) (right_mem_Icc.mpr hD.le) hD
  have heq := nsr_sec_eq_G (by norm_num : (0:ℝ)≤1) hC (by linarith only [hD]) (ne_of_lt hD)
  have heq' : (D-1)*m2Sec 1 C D = nsrG C D-nsrG C 1 := by
    rw [heq]
    field_simp
  dsimp [F] at hh
  unfold mhtSecD3
  have hDm : 0 < D-1 := by linarith only [hD]
  apply div_neg_of_neg_of_pos
  · have hmult : 0 < (D-1)*(-(mhtg2 C D*(D-1)^2-
        3*mhtg1 C D*(D-1)+6*(m2g C D-m2Sec 1 C D))) := by
      nlinarith only [hh,heq']
    have hnum := pos_of_mul_pos_right hmult hDm.le
    linarith only [hnum]
  · positivity

/-- The variance of the actual reciprocal secant, bounded by its left denominator. -/
theorem mhtSec_unit_variance_lt {C : ℝ} (hC : 1 < C) :
    m2Sec 1 C C-3/4 < (C-1)^2/(12*(C+1)^2) := by
  have hc : 0 < C := by linarith only [hC]
  have hCp : 0 < C+1 := by linarith only [hC]
  let F : ℝ → ℝ := fun s => nsrG C s-(3/4)*s+(C-s)^3/(12*(C+1)^2)
  let fp : ℝ → ℝ := fun s => m2g C s-3/4-(C-s)^2/(4*(C+1)^2)
  have hd : ∀ s ∈ Icc (1:ℝ) C, HasDerivAt F (fp s) s := by
    intro s hs
    have hi := (hasDerivAt_id' s).const_sub C
    have h := ((nsr_hasDerivAt_G (B := C) (s := s) (by linarith only [hC,hs.1])).sub
      ((hasDerivAt_id' s).const_mul (3/4))).add ((hi.pow 3).div_const (12*(C+1)^2))
    refine h.congr_deriv ?_
    dsimp [fp]
    norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
    field_simp
    ring
  have hn : ∀ s ∈ Ioo (1:ℝ) C, fp s < 0 := by
    intro s hs
    have hsp : 0 < C+s := by linarith only [hC,hs.1]
    have hid : m2g C s-3/4=(C-s)^2/(4*(C+s)^2) := by
      unfold m2g
      field_simp
      ring
    have hnum : 0 < (C-s)^2 := sq_pos_of_pos (sub_pos.mpr hs.2)
    have hden : 0 < 4*(C+1)^2 := by positivity
    have hdenlt : 4*(C+1)^2 < 4*(C+s)^2 := by
      have hh := mul_pos (sub_pos.mpr hs.1) (by linarith only [hC,hs.1] : 0<2*C+s+1)
      nlinarith only [hh]
    have hf := div_lt_div_of_pos_left hnum hden hdenlt
    dsimp [fp]
    rw [hid]
    exact sub_neg.mpr hf
  have ha : StrictAntiOn F (Icc (1:ℝ) C) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 C)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact hn s (by simpa only [interior_Icc] using hs)
  have hh := ha (left_mem_Icc.mpr hC.le) (right_mem_Icc.mpr hC.le) hC
  have hid : F 1-F C = (C-1)*((C-1)^2/(12*(C+1)^2)-(m2Sec 1 C C-3/4)) := by
    rw [nsr_sec_eq_G (by norm_num : (0:ℝ)≤1) hc hc.le (ne_of_lt hC)]
    dsimp [F]
    have hDm : C-1 ≠ 0 := by linarith only [hC]
    field_simp
    ring
  have hp : 0 < (C-1)*((C-1)^2/(12*(C+1)^2)-(m2Sec 1 C C-3/4)) := by
    rw [← hid]
    exact sub_pos.mpr hh
  have hf := pos_of_mul_pos_right hp (sub_nonneg.mpr hC.le)
  exact sub_pos.mp hf

noncomputable def mhtSecTaylor (D : ℝ) : ℝ :=
  m2Sec 1 (3/2) D-m2Sec 1 (3/2) (3/2)-
    mhtSecD1 (3/2) (3/2)*(D-3/2)-mhtSecD2 (3/2) (3/2)*(D-3/2)^2/2
noncomputable def mhtSecTaylor1 (D : ℝ) : ℝ :=
  mhtSecD1 (3/2) D-mhtSecD1 (3/2) (3/2)-mhtSecD2 (3/2) (3/2)*(D-3/2)
noncomputable def mhtSecTaylor2 (D : ℝ) : ℝ := mhtSecD2 (3/2) D-mhtSecD2 (3/2) (3/2)
private theorem mhtSecTaylor_hasDerivAt {D : ℝ} (hD : 1 < D) :
    HasDerivAt mhtSecTaylor (mhtSecTaylor1 D) D := by
  have hi := (hasDerivAt_id' D).sub_const (3/2)
  have hd := (((mhtSec_hasDerivAt_D (by norm_num : (0:ℝ)<3/2) hD).sub_const
    (m2Sec 1 (3/2) (3/2))).sub (hi.const_mul (mhtSecD1 (3/2) (3/2)))).sub
    (((hi.pow 2).const_mul (mhtSecD2 (3/2) (3/2))).div_const 2)
  refine hd.congr_deriv ?_
  unfold mhtSecTaylor1
  norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
  ring
private theorem mhtSecTaylor1_hasDerivAt {D : ℝ} (hD : 1 < D) :
    HasDerivAt mhtSecTaylor1 (mhtSecTaylor2 D) D := by
  have hd := ((mhtSecD1_hasDerivAt (by norm_num : (0:ℝ)<3/2) hD).sub_const
    (mhtSecD1 (3/2) (3/2))).sub
    (((hasDerivAt_id' D).sub_const (3/2)).const_mul (mhtSecD2 (3/2) (3/2)))
  exact hd.congr_deriv (by unfold mhtSecTaylor2; ring)

private theorem mhtSecTaylor2_nonpos {D : ℝ} (hD : D ∈ Icc (3/2:ℝ) (11/6)) :
    mhtSecTaylor2 D ≤ 0 := by
  have hh := mhtS_le_of_deriv (f := fun x => -mhtSecD2 (3/2) x)
    (f' := fun x => -mhtSecD3 (3/2) x) hD.1
    (fun x hx => (mhtSecD2_hasDerivAt (by norm_num : (0:ℝ)<3/2)
      (by linarith only [hx.1])).neg)
    (fun x hx => neg_nonneg.mpr (mhtSecD3_neg (by norm_num : (0:ℝ)<3/2)
      (by linarith only [hx.1]) (by linarith only [hx.2,hD.2])).le)
  unfold mhtSecTaylor2
  linarith only [hh]

/-- Taylor's bound for the actual secant uses its negative third derivative. -/
theorem mhtSec_taylor_bound {D : ℝ} (hD : D ∈ Icc (3/2:ℝ) (11/6)) :
    m2Sec 1 (3/2) D ≤ 3/4+(m2Sec 1 (3/2) (3/2)-3/4)*
      (1-2*(D-3/2)+4*(D-3/2)^2) := by
  have hc : ConcaveOn ℝ (Icc (3/2:ℝ) (11/6)) mhtSecTaylor := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (3/2) (11/6))
      (f' := mhtSecTaylor1) (f'' := mhtSecTaylor2)
    · exact fun x hx => (mhtSecTaylor_hasDerivAt (by linarith only [hx.1])).continuousAt.continuousWithinAt
    · exact fun x hx => (mhtSecTaylor_hasDerivAt
        (by have := (interior_subset hx).1; linarith only [this])).hasDerivWithinAt
    · exact fun x hx => (mhtSecTaylor1_hasDerivAt
        (by have := (interior_subset hx).1; linarith only [this])).hasDerivWithinAt
    · exact fun x hx => mhtSecTaylor2_nonpos (interior_subset hx)
  have hd0 : HasDerivAt mhtSecTaylor 0 (3/2) := by
    convert mhtSecTaylor_hasDerivAt (by norm_num : (1:ℝ)<3/2) using 1
    unfold mhtSecTaylor1
    ring
  have h0 : mhtSecTaylor (3/2)=0 := by unfold mhtSecTaylor; ring
  have hbound : mhtSecTaylor D ≤ 0 := by
    rcases eq_or_lt_of_le hD.1 with he | he
    · rw [← he,h0]
    have hs := hc.slope_le_of_hasDerivAt (left_mem_Icc.mpr (by norm_num)) hD he hd0
    rw [slope_def_field,h0] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr he)).mp hs
    linarith only [hh]
  have hf1 : mhtSecD1 (3/2) (3/2) = -2*(m2Sec 1 (3/2) (3/2)-3/4) := by
    unfold mhtSecD1
    norm_num [m2g]
    ring
  have hf2 : mhtSecD2 (3/2) (3/2) = 8*(m2Sec 1 (3/2) (3/2)-3/4) := by
    unfold mhtSecD2 mhtg1
    norm_num [m2g]
    ring
  unfold mhtSecTaylor at hbound
  rw [hf1,hf2] at hbound
  nlinarith only [hbound]

/-- The natural variance ceiling, with the original secant and closed endpoints. -/
theorem mhtSec_variance_ceiling {D : ℝ} (hD : D ∈ Icc (3/2:ℝ) (11/6)) :
    m2Sec 1 (3/2) D < 3/4+((2*D-3)^2-(2*D-3)+1)/300 := by
  have ht := mhtSec_taylor_bound hD
  have he := mhtSec_unit_variance_lt (by norm_num : (1:ℝ)<3/2)
  norm_num only [show (3/2-1:ℝ)^2/(12*(3/2+1)^2)=1/300 by norm_num] at he
  have hp : 0 < 1-2*(D-3/2)+4*(D-3/2)^2 := by nlinarith only [sq_nonneg (2*(D-3/2)-1/2)]
  have hm := mul_lt_mul_of_pos_right he hp
  have hid : (1/300:ℝ)*(1-2*(D-3/2)+4*(D-3/2)^2)=((2*D-3)^2-(2*D-3)+1)/300 := by ring
  rw [hid] at hm
  linarith only [ht,hm]

end SmoothedOctagon

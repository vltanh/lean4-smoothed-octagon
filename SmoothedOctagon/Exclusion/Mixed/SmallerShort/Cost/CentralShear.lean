module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# S6: exact central shear and its analytic envelopes
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

noncomputable def s6CentralT (R d e : ℝ) : ℝ :=
  (2*R+((e+1)*R-(e-1))*d)/(2+(e+1-(e-1)*R)*d)
noncomputable def s6CentralW (R e : ℝ) : ℝ := (e-1)*(1-R^2)
noncomputable def s6CentralGamma (R e : ℝ) : ℝ := e+1-(e-1)*R
noncomputable def s6CentralL (R d e : ℝ) : ℝ := 2+s6CentralGamma R e*d
noncomputable def s6CentralF (t : ℝ) : ℝ := t/(3+t^2)
noncomputable def s6CentralF1 (t : ℝ) : ℝ := (3-t^2)/(3+t^2)^2
noncomputable def s6CentralF2 (t : ℝ) : ℝ := 2*t*(t^2-9)/(3+t^2)^3
noncomputable def s6CentralF3 (t : ℝ) : ℝ := -6*(t^4-18*t^2+9)/(3+t^2)^4
noncomputable def s6CentralZ0 (R : ℝ) : ℝ := 2*R^2*(1+R)/(3-R)
noncomputable def s6CentralA (R : ℝ) : ℝ := (1+2*R)/(3*(1-R))
noncomputable def s6CentralB (R e : ℝ) : ℝ := (3+R^2)*((1-e)+(e+3)*R)/(2*(3-R))
noncomputable def s6CentralC (R e : ℝ) : ℝ := e*(3+R^2)*(1-R)/(2*(3-R))
noncomputable def s6CentralZ (R d e : ℝ) : ℝ :=
  s6CentralZ0 R+s6CentralB R e*d-s6CentralC R e*d^2-
    (3+R^2)*(s6CentralF (s6CentralT R d e)-s6CentralF R)
noncomputable def s6CentralZU (R d : ℝ) : ℝ := s6CentralZ0 R+s6CentralA R*d-3*d^2/2
noncomputable def s6CentralZL (R d : ℝ) : ℝ := s6CentralZ0 R*(1+11*d/2)

local syntax "central_deriv" : tactic
macro_rules
| `(tactic| central_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> central_deriv
  | apply HasDerivAt.sub <;> central_deriv
  | apply HasDerivAt.pow <;> central_deriv
  | apply HasDerivAt.mul <;> central_deriv
  | apply HasDerivAt.div <;> first | central_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> central_deriv)

theorem s6CentralF_hasDerivAt (t : ℝ) : HasDerivAt s6CentralF (s6CentralF1 t) t := by
  have hp : 0 < 3+t^2 := by positivity
  apply HasDerivAt.congr_deriv
  · unfold s6CentralF
    central_deriv
  · unfold s6CentralF1
    norm_num [npowRec]
    field_simp
    ring

theorem s6CentralF1_hasDerivAt (t : ℝ) : HasDerivAt s6CentralF1 (s6CentralF2 t) t := by
  have hp : 0 < 3+t^2 := by positivity
  apply HasDerivAt.congr_deriv
  · unfold s6CentralF1
    central_deriv
  · unfold s6CentralF2
    norm_num [npowRec]
    field_simp
    ring

theorem s6CentralF2_hasDerivAt (t : ℝ) : HasDerivAt s6CentralF2 (s6CentralF3 t) t := by
  have hp : 0 < 3+t^2 := by positivity
  apply HasDerivAt.congr_deriv
  · unfold s6CentralF2
    central_deriv
  · unfold s6CentralF3
    norm_num [npowRec]
    field_simp
    ring

private theorem s6_f2_neg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 7/19) : s6CentralF2 t < 0 := by
  have hs : t^2 < 9 := by nlinarith only [ht,ht1]
  unfold s6CentralF2
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith only [hs])) (by positivity)
private theorem s6_f3_neg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 7/19) : s6CentralF3 t < 0 := by
  have hs : t^2 ≤ (7/19:ℝ)^2 := by nlinarith only [ht,ht1]
  have hp : 0 < t^4-18*t^2+9 := by nlinarith only [hs,pow_nonneg ht 4]
  unfold s6CentralF3
  exact div_neg_of_neg_of_pos (by linarith only [hp]) (by positivity)

/-- Endpoint bounds for the original rational curvature kernel. -/
theorem s6CentralF_bounds {t : ℝ} (ht : 9/31 ≤ t) (ht1 : t ≤ 7/19) :
    35/121 < s6CentralF1 t ∧ s6CentralF1 t < 23/75 ∧
      7/40 < -s6CentralF2 t ∧ -s6CentralF2 t < 1/4 := by
  have hl1 := ss_le_of_deriv (f := fun v => -s6CentralF1 v) (f' := fun v => -s6CentralF2 v) ht
    (fun v _ => (s6CentralF1_hasDerivAt v).neg)
    (fun v hv => (neg_pos.mpr (s6_f2_neg (by linarith only [hv.1]) (le_trans hv.2.le ht1))).le)
  have hu1 := ss_le_of_deriv (f := fun v => -s6CentralF1 v) (f' := fun v => -s6CentralF2 v) ht1
    (fun v _ => (s6CentralF1_hasDerivAt v).neg)
    (fun v hv => (neg_pos.mpr (s6_f2_neg (by linarith only [hv.1,ht]) hv.2.le)).le)
  have hl2 := ss_le_of_deriv (f := fun v => -s6CentralF2 v) (f' := fun v => -s6CentralF3 v) ht
    (fun v _ => (s6CentralF2_hasDerivAt v).neg)
    (fun v hv => (neg_pos.mpr (s6_f3_neg (by linarith only [hv.1]) (le_trans hv.2.le ht1))).le)
  have hu2 := ss_le_of_deriv (f := fun v => -s6CentralF2 v) (f' := fun v => -s6CentralF3 v) ht1
    (fun v _ => (s6CentralF2_hasDerivAt v).neg)
    (fun v hv => (neg_pos.mpr (s6_f3_neg (by linarith only [hv.1,ht]) hv.2.le)).le)
  have h1 : (35/121:ℝ) < s6CentralF1 (7/19) := by norm_num [s6CentralF1]
  have h2 : s6CentralF1 (9/31) < (23/75:ℝ) := by norm_num [s6CentralF1]
  have h3 : (7/40:ℝ) < -s6CentralF2 (9/31) := by norm_num [s6CentralF2]
  have h4 : -s6CentralF2 (7/19) < (1/4:ℝ) := by norm_num [s6CentralF2]
  exact ⟨by linarith only [hu1,h1],by linarith only [hl1,h2],
    lt_of_lt_of_le h3 hl2,lt_of_le_of_lt hu2 h4⟩

theorem s6CentralL_pos {R d e : ℝ} (hR : R < 1) (hd : 0 ≤ d) (he : 1 ≤ e) :
    0 < s6CentralL R d e := by
  have hg : s6CentralGamma R e=2+(e-1)*(1-R) := by unfold s6CentralGamma; ring
  unfold s6CentralL
  rw [hg]
  positivity

/-- Natural shape bounds for w and gamma, before any curvature estimate. -/
theorem s6Central_shape_bounds {R e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    48/35 < s6CentralW R e ∧ s6CentralW R e ≤ 16/9 ∧
      3 < s6CentralGamma R e ∧ s6CentralGamma R e ≤ 10/3 := by
  have hsqlo : (1/3:ℝ)^2 ≤ R^2 := by nlinarith only [hR]
  have hsqhi : R^2 ≤ (7/19:ℝ)^2 := by nlinarith only [hR,hR1]
  have hwlo := mul_le_mul (show (8/5:ℝ) ≤ e-1 by linarith only [he])
    (show 1-(7/19:ℝ)^2 ≤ 1-R^2 by linarith only [hsqhi]) (by norm_num) (by linarith only [he] : 0 ≤ e-1)
  have hwhi := mul_le_mul (show e-1 ≤ (2:ℝ) by linarith only [he1])
    (show 1-R^2 ≤ 1-(1/3:ℝ)^2 by linarith only [hsqlo])
    (by nlinarith only [hsqhi] : 0 ≤ 1-R^2) (by norm_num)
  have hglo := mul_le_mul (show (8/5:ℝ) ≤ e-1 by linarith only [he])
    (show (12/19:ℝ) ≤ 1-R by linarith only [hR1]) (by norm_num) (by linarith only [he] : 0 ≤ e-1)
  have hghi := mul_le_mul (show e-1 ≤ (2:ℝ) by linarith only [he1])
    (show 1-R ≤ (2/3:ℝ) by linarith only [hR]) (by linarith only [hR1] : 0 ≤ 1-R) (by norm_num)
  unfold s6CentralW s6CentralGamma
  exact ⟨by nlinarith only [hwlo],by nlinarith only [hwhi],by nlinarith only [hglo],by nlinarith only [hghi]⟩

/-- Exact positive-product ratio comparisons, including d=0. -/
theorem s6CentralT_bounds {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    9/31 ≤ s6CentralT R d e ∧ s6CentralT R d e ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRlt : R < 1 := by linarith only [hR1]
  have he0 : 1 ≤ e := by linarith only [he]
  have hL := s6CentralL_pos hRlt hd he0
  have hN : (2*R+((e+1)*R-(e-1))*d)=R*s6CentralL R d e-s6CentralW R e*d := by
    unfold s6CentralL s6CentralGamma s6CentralW; ring
  have hW0 : 0 ≤ s6CentralW R e := by
    have hq : 0 ≤ 1-R^2 := by nlinarith only [hR0,hRlt]
    unfold s6CentralW; positivity
  have hTR : s6CentralT R d e ≤ R := by
    unfold s6CentralT
    change _/s6CentralL R d e ≤ R
    rw [div_le_iff₀ hL,hN]
    nlinarith only [mul_nonneg hW0 hd]
  have heL := s6CentralL_pos (R := R) (d := 1/19) (e := 3) hRlt (by norm_num) (by norm_num)
  have hprod : 0 ≤ 2*d*(1-R^2)*(1+d)*(3-e) := by
    have hq : 0 ≤ 1-R^2 := by nlinarith only [hR0,hRlt]
    positivity
  have hshape : s6CentralT R d 3 ≤ s6CentralT R d e := by
    have hL3 := s6CentralL_pos (R := R) (e := 3) hRlt hd (by norm_num)
    unfold s6CentralT
    change _/s6CentralL R d 3 ≤ _/s6CentralL R d e
    rw [div_le_div_iff₀ hL3 hL]
    dsimp [s6CentralL,s6CentralGamma]
    nlinarith only [hprod]
  have hprod2 : 0 ≤ 4*(1-R^2)*(1/19-d) := by
    have hq : 0 ≤ 1-R^2 := by nlinarith only [hR0,hRlt]
    positivity
  have hdisp : s6CentralT R (1/19) 3 ≤ s6CentralT R d 3 := by
    have hL3 := s6CentralL_pos (R := R) (e := 3) hRlt hd (by norm_num)
    unfold s6CentralT
    change _/s6CentralL R (1/19) 3 ≤ _/s6CentralL R d 3
    rw [div_le_div_iff₀ heL hL3]
    dsimp [s6CentralL,s6CentralGamma]
    nlinarith only [hprod2]
  have hcorner : 9/31 ≤ s6CentralT R (1/19) 3 := by
    unfold s6CentralT
    change _ ≤ _/s6CentralL R (1/19) 3
    rw [le_div_iff₀ heL]
    dsimp [s6CentralL,s6CentralGamma]
    linarith only [hR]
  exact ⟨hcorner.trans (hdisp.trans hshape),hTR⟩

theorem s6CentralT_hasDerivAt {R d e : ℝ} (hL : s6CentralL R d e ≠ 0) :
    HasDerivAt (fun v => s6CentralT R v e) (-2*s6CentralW R e/(s6CentralL R d e)^2) d := by
  have hn := ((hasDerivAt_id d).const_mul ((e+1)*R-(e-1))).const_add (2*R)
  have hdd := ((hasDerivAt_id d).const_mul (s6CentralGamma R e)).const_add 2
  have hh := hn.div hdd hL
  refine hh.congr_deriv ?_
  simp only [id_eq]
  unfold s6CentralW s6CentralL s6CentralGamma
  field_simp
  ring

theorem s6CentralT1_hasDerivAt {R d e : ℝ} (hL : s6CentralL R d e ≠ 0) :
    HasDerivAt (fun v => -2*s6CentralW R e/(s6CentralL R v e)^2)
      (4*s6CentralW R e*s6CentralGamma R e/(s6CentralL R d e)^3) d := by
  have hdd : HasDerivAt (fun v => s6CentralL R v e) (s6CentralGamma R e) d := by
    simpa only [s6CentralL,id_eq,mul_one] using
      ((hasDerivAt_id d).const_mul (s6CentralGamma R e)).const_add 2
  have hh := (hasDerivAt_const d (-2*s6CentralW R e)).div (hdd.pow 2) (pow_ne_zero 2 hL)
  refine hh.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring


private theorem s6_gamma_kernel_lower {d g : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (hg : 3 ≤ g) (hg1 : g ≤ 10/3) :
    3*(19/41)^3 ≤ g/(2+g*d)^3 := by
  have hm := ss_le_of_deriv (f := fun v => v/(2+v*d)^3)
    (f' := fun v => (2-2*v*d)/(2+v*d)^4) hg (fun v hv => ?_) (fun v hv => ?_)
  · have hD : 0 < 2+3*d := by positivity
    have hpow : (2+3*d)^3 ≤ (41/19:ℝ)^3 := by gcongr; linarith only [hd1]
    have hlower : 3*(19/41)^3 ≤ 3/(2+3*d)^3 := by
      apply (le_div_iff₀ (pow_pos hD 3)).mpr
      nlinarith only [hpow]
    exact hlower.trans hm
  · have hv0 : 0 < v := by linarith only [hv.1]
    have hD : 0 < 2+v*d := by positivity
    apply HasDerivAt.congr_deriv
    · central_deriv
    · norm_num [npowRec]
      field_simp
      ring
  · have hv0 : 0 ≤ v := by linarith only [hv.1]
    have hmul := mul_le_mul (le_trans hv.2.le hg1) hd1 hd (by norm_num : (0:ℝ) ≤ 10/3)
    apply div_nonneg
    · nlinarith only [hmul]
    · positivity

private theorem s6_upper_kernel_le_at_two {w g L : ℝ}
    (_hw : 0 ≤ w) (hw1 : w ≤ 16/9) (hg : 3 ≤ g) (hL : 2 ≤ L) :
    23*g/(75*L^3)-7*w/(40*L^4) ≤ 23*g/(75*2^3)-7*w/(40*2^4) := by
  have hm := ss_le_of_deriv
    (f := fun v => -(23*g/(75*v^3)-7*w/(40*v^4)))
    (f' := fun v => -(7*w/10-23*g*v/25)/v^5) hL (fun v hv => ?_) (fun v hv => ?_)
  · exact neg_le_neg_iff.mp hm
  · have hv0 : 0 < v := by linarith only [hv.1]
    apply HasDerivAt.congr_deriv
    · central_deriv
    · norm_num [npowRec]
      field_simp
      ring
  · have hprod := mul_le_mul hg (show (2:ℝ) ≤ v by exact hv.1.le)
      (by norm_num : (0:ℝ) ≤ 2) (by linarith only [hg] : 0 ≤ g)
    have hv0 : 0 < v := by linarith only [hv.1]
    apply div_nonneg
    · nlinarith only [hprod,hw1]
    · positivity

noncomputable def s6CentralQ (R d e : ℝ) : ℝ :=
  s6CentralF2 (s6CentralT R d e)*(-2*s6CentralW R e/(s6CentralL R d e)^2)^2+
    s6CentralF1 (s6CentralT R d e)*(4*s6CentralW R e*s6CentralGamma R e/(s6CentralL R d e)^3)

/-- The natural rational shear-curvature kernel is bounded by the paper's two
simple constants, using monotonic reciprocal kernels only. -/
theorem s6CentralQ_bounds {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    7/20 < s6CentralQ R d e ∧ s6CentralQ R d e ≤ 104/135 := by
  obtain ⟨hwlo,hwhi,hglo,hghi⟩ := s6Central_shape_bounds hR hR1 he he1
  obtain ⟨htlo,hthi⟩ := s6CentralT_bounds hR hR1 hd hd1 he he1
  obtain ⟨hflo,hfhi,hfflo,hffhi⟩ := s6CentralF_bounds htlo (hthi.trans hR1)
  let w := s6CentralW R e
  let g := s6CentralGamma R e
  let L := s6CentralL R d e
  have hw : 0 < w := by dsimp [w]; linarith only [hwlo]
  have hg : 0 < g := by dsimp [g]; linarith only [hglo]
  have hL2 : 2 ≤ L := by dsimp [L,s6CentralL]; nlinarith only [hd,hg.le]
  have hL : 0 < L := by linarith only [hL2]
  have hkern := s6_gamma_kernel_lower hd hd1 hglo.le hghi
  change 3*(19/41)^3 ≤ g/L^3 at hkern
  have hratio : w/(g*L) ≤ 8/27 := by
    apply (div_le_iff₀ (mul_pos hg hL)).mpr
    have hm := mul_le_mul (show (3:ℝ) ≤ g by exact hglo.le) hL2 (by norm_num : (0:ℝ) ≤ 2) hg.le
    nlinarith only [hwhi,hm]
  have hratio0 : 0 ≤ w/(g*L) := by positivity
  have hf2weak : -1/4 ≤ s6CentralF2 (s6CentralT R d e) := by linarith only [hffhi]
  have hprod := mul_le_mul_of_nonneg_left hf2weak hratio0
  have hbracket : 35/121-2/27 < s6CentralF1 (s6CentralT R d e)+
      (w/(g*L))*s6CentralF2 (s6CentralT R d e) := by
    nlinarith only [hflo,hprod,hratio]
  have hid : s6CentralQ R d e = 4*w*(g/L^3)*
      (s6CentralF1 (s6CentralT R d e)+(w/(g*L))*s6CentralF2 (s6CentralT R d e)) := by
    unfold s6CentralQ
    change s6CentralF2 (s6CentralT R d e)*(-2*w/L^2)^2+
      s6CentralF1 (s6CentralT R d e)*(4*w*g/L^3)=_
    field_simp
    ring
  have hkg : 0 < g/L^3 := by positivity
  have hlead1 := mul_le_mul_of_nonneg_left hkern (show 0 ≤ 4*w by positivity)
  have hlead2 := mul_lt_mul_of_pos_right hwlo (by norm_num : (0:ℝ) < 4*(3*(19/41)^3))
  have hlead : 4*(48/35)*(3*(19/41)^3) < 4*w*(g/L^3) := by
    nlinarith only [hlead1,hlead2]
  have hlower : (7/20:ℝ) < s6CentralQ R d e := by
    have hm := mul_lt_mul hlead hbracket.le (by norm_num : (0:ℝ) < 35/121-2/27)
      (show 0 ≤ 4*w*(g/L^3) by positivity)
    have hconst : (7/20:ℝ) < 4*(48/35)*(3*(19/41)^3)*(35/121-2/27) := by norm_num
    rw [hid]
    exact hconst.trans hm
  have hco1 : 0 < 4*w*g/L^3 := by positivity
  have hco2 : 0 < (-2*w/L^2)^2 := by
    exact sq_pos_of_ne_zero (ne_of_lt (div_neg_of_neg_of_pos (by linarith only [hw]) (by positivity)))
  have hfp := mul_lt_mul_of_pos_right hfhi hco1
  have hfpp := mul_lt_mul_of_pos_right (show s6CentralF2 (s6CentralT R d e) < -7/40 by linarith only [hfflo]) hco2
  have hupper0 : s6CentralQ R d e < 4*w*(23*g/(75*L^3)-7*w/(40*L^4)) := by
    have heq : (23/75:ℝ)*(4*w*g/L^3)+(-7/40)*(-2*w/L^2)^2 =
        4*w*(23*g/(75*L^3)-7*w/(40*L^4)) := by field_simp; ring
    unfold s6CentralQ
    change s6CentralF2 (s6CentralT R d e)*(-2*w/L^2)^2+
      s6CentralF1 (s6CentralT R d e)*(4*w*g/L^3)<_
    linarith only [hfp,hfpp,heq]
  have hupper1 := mul_le_mul_of_nonneg_left (s6_upper_kernel_le_at_two hw.le hwhi hglo.le hL2)
    (show 0 ≤ 4*w by positivity)
  have hupper2 : 4*w*(23*g/(75*2^3)-7*w/(40*2^4)) ≤ 104/135 := by
    have hfirst := mul_nonneg hw.le (show 0 ≤ (10/3:ℝ)-g by linarith only [hghi])
    have hsecond := mul_nonneg (show 0 ≤ (16/9:ℝ)-w by linarith only [hwhi])
      (show 0 ≤ 23/45-(7/160)*((16/9:ℝ)+w) by linarith only [hwhi])
    nlinarith only [hfirst,hsecond]
  exact ⟨hlower,(hupper0.trans_le (hupper1.trans hupper2)).le⟩


noncomputable def s6CentralCBase (R : ℝ) : ℝ := (3+R^2)*(1-R)/(2*(3-R))
noncomputable def s6CentralCBase1 (R : ℝ) : ℝ := (R^3-5*R^2+3*R-3)/(3-R)^2

theorem s6CentralCBase_hasDerivAt {R : ℝ} (hR : R ≠ 3) :
    HasDerivAt s6CentralCBase (s6CentralCBase1 R) R := by
  have hp : 3-R ≠ 0 := sub_ne_zero.mpr (Ne.symm hR)
  apply HasDerivAt.congr_deriv
  · unfold s6CentralCBase
    central_deriv
  · unfold s6CentralCBase1
    norm_num [npowRec]
    field_simp
    ring

private theorem s6_CBase1_neg {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6CentralCBase1 R < 0 := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hc : R^3 ≤ (7/19:ℝ)^3 := by gcongr
  have hnum : R^3-5*R^2+3*R-3 < 0 := by nlinarith only [hc,hR1,sq_nonneg R]
  unfold s6CentralCBase1
  exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos (by linarith only [hR1] : 0 < 3-R))

theorem s6CentralC_bounds {R e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    39/40 < s6CentralC R e ∧ s6CentralC R e ≤ 7/6 := by
  have hlo := ss_le_of_deriv (f := fun v => -s6CentralCBase v) (f' := fun v => -s6CentralCBase1 v)
    hR (fun v hv => (s6CentralCBase_hasDerivAt (by linarith only [hv.2,hR1])).neg)
    (fun v hv => (neg_pos.mpr (s6_CBase1_neg hv.1.le (le_trans hv.2.le hR1))).le)
  have hhi := ss_le_of_deriv (f := fun v => -s6CentralCBase v) (f' := fun v => -s6CentralCBase1 v)
    hR1 (fun v hv => (s6CentralCBase_hasDerivAt (by linarith only [hv.2])).neg)
    (fun v hv => (neg_pos.mpr (s6_CBase1_neg (le_trans hR hv.1.le) hv.2.le)).le)
  have hleft : s6CentralCBase (1/3) = (7/18:ℝ) := by norm_num [s6CentralCBase]
  have hright : (3/8:ℝ) < s6CentralCBase (7/19) := by norm_num [s6CentralCBase]
  have hbase : (3/8:ℝ) < s6CentralCBase R := by linarith only [hhi,hright]
  have hbase1 : s6CentralCBase R ≤ (7/18:ℝ) := by linarith only [hlo,hleft]
  have he0 : 0 ≤ e := by linarith only [he]
  have hc0 : 0 ≤ s6CentralCBase R := by linarith only [hbase]
  have hl := mul_lt_mul_of_pos_left hbase (show 0 < e by linarith only [he])
  have hr := mul_le_mul he1 hbase1 hc0 (by norm_num : (0:ℝ) ≤ 3)
  have hid : s6CentralC R e=e*s6CentralCBase R := by
    unfold s6CentralC s6CentralCBase
    ring
  rw [hid]
  exact ⟨by nlinarith only [hl,he],by nlinarith only [hr]⟩

noncomputable def s6CentralZ1 (R d e : ℝ) : ℝ :=
  s6CentralB R e-2*s6CentralC R e*d-
    (3+R^2)*s6CentralF1 (s6CentralT R d e)*(-2*s6CentralW R e/(s6CentralL R d e)^2)
noncomputable def s6CentralZ2 (R d e : ℝ) : ℝ := -2*s6CentralC R e-(3+R^2)*s6CentralQ R d e

theorem s6CentralZ_hasDerivAt {R d e : ℝ} (hL : s6CentralL R d e ≠ 0) :
    HasDerivAt (fun v => s6CentralZ R v e) (s6CentralZ1 R d e) d := by
  have hf := (s6CentralF_hasDerivAt (s6CentralT R d e)).comp d (s6CentralT_hasDerivAt hL)
  have hh := (((hasDerivAt_const d (s6CentralZ0 R)).add
    ((hasDerivAt_id d).const_mul (s6CentralB R e))).sub
    ((hasDerivAt_pow 2 d).const_mul (s6CentralC R e))).sub
    ((hf.sub_const (s6CentralF R)).const_mul (3+R^2))
  change HasDerivAt (fun v => s6CentralZ R v e) _ d at hh
  exact hh.congr_deriv (by unfold s6CentralZ1; norm_num; ring)

theorem s6CentralZ1_hasDerivAt {R d e : ℝ} (hL : s6CentralL R d e ≠ 0) :
    HasDerivAt (fun v => s6CentralZ1 R v e) (s6CentralZ2 R d e) d := by
  have hT := s6CentralT_hasDerivAt hL
  have hf := (s6CentralF1_hasDerivAt (s6CentralT R d e)).comp d hT
  have hp := (hf.const_mul (3+R^2)).mul (s6CentralT1_hasDerivAt hL)
  have hh := ((hasDerivAt_const d (s6CentralB R e)).sub
    ((hasDerivAt_id d).const_mul (2*s6CentralC R e))).sub hp
  change HasDerivAt (fun v => s6CentralZ1 R v e) _ d at hh
  exact hh.congr_deriv (by unfold s6CentralZ2 s6CentralQ; dsimp only [Function.comp_apply,id_eq]; norm_num; ring)

/-- The exact central shear has curvature between -19/4 and -3. -/
theorem s6CentralZ2_bounds {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    -19/4 < s6CentralZ2 R d e ∧ s6CentralZ2 R d e < -3 := by
  obtain ⟨hQ,hQ1⟩ := s6CentralQ_bounds hR hR1 hd hd1 he he1
  obtain ⟨hC,hC1⟩ := s6CentralC_bounds hR hR1 he he1
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hDlo : (3:ℝ) ≤ 3+R^2 := by nlinarith only [sq_nonneg R]
  have hDhi : 3+R^2 ≤ (1132/361:ℝ) := by nlinarith only [hR,hR1]
  have hlo := mul_lt_mul_of_pos_left hQ (show 0 < 3+R^2 by positivity)
  have hhi := mul_le_mul hDhi hQ1 (by linarith only [hQ] : 0 ≤ s6CentralQ R d e)
    (by norm_num : (0:ℝ) ≤ 1132/361)
  unfold s6CentralZ2
  constructor <;> nlinarith only [hC,hC1,hDlo,hlo,hhi]


noncomputable def s6CentralG (R : ℝ) : ℝ := R^2-7+24/(3+R^2)
noncomputable def s6CentralG1 (R : ℝ) : ℝ := 2*R*(1-24/(3+R^2)^2)
noncomputable def s6CentralB1 (R e : ℝ) : ℝ :=
  R*((1-e)+(e+3)*R)/(3-R)+(3+R^2)*(e+5)/(3-R)^2
noncomputable def s6CentralSlope (R e : ℝ) : ℝ := s6CentralB R e+(e-1)*s6CentralG R/2
noncomputable def s6CentralSlopeR (R e : ℝ) : ℝ := s6CentralB1 R e+(e-1)*s6CentralG1 R/2
noncomputable def s6CentralP (R : ℝ) : ℝ := 8*(3+R^2)/(3-R)^2-1/(1-R)^2
noncomputable def s6CentralP1 (R : ℝ) : ℝ :=
  16*R/(3-R)^2+16*(3+R^2)/(3-R)^3-2/(1-R)^3
noncomputable def s6CentralZ01 (R : ℝ) : ℝ := 4*R*(3+4*R-R^2)/(3-R)^2

theorem s6CentralG_hasDerivAt (R : ℝ) : HasDerivAt s6CentralG (s6CentralG1 R) R := by
  have hp : 0 < 3+R^2 := by positivity
  apply HasDerivAt.congr_deriv
  · unfold s6CentralG
    central_deriv
  · unfold s6CentralG1
    norm_num [npowRec]
    field_simp
    ring

theorem s6CentralB_hasDerivAt {R e : ℝ} (hR : R ≠ 3) :
    HasDerivAt (fun v => s6CentralB v e) (s6CentralB1 R e) R := by
  have hp : 3-R ≠ 0 := sub_ne_zero.mpr (Ne.symm hR)
  apply HasDerivAt.congr_deriv
  · unfold s6CentralB
    central_deriv
  · unfold s6CentralB1
    norm_num [npowRec]
    field_simp
    ring

theorem s6CentralSlope_hasDerivAt {R e : ℝ} (hR : R ≠ 3) :
    HasDerivAt (fun v => s6CentralSlope v e) (s6CentralSlopeR R e) R := by
  have hh := (s6CentralB_hasDerivAt (e := e) hR).add
    (((s6CentralG_hasDerivAt R).const_mul (e-1)).div_const 2)
  change HasDerivAt (fun v => s6CentralSlope v e) (s6CentralSlopeR R e) R at hh
  exact hh

theorem s6CentralA_hasDerivAt {R : ℝ} (hR : R ≠ 1) :
    HasDerivAt s6CentralA (1/(1-R)^2) R := by
  have hp : 1-R ≠ 0 := sub_ne_zero.mpr (Ne.symm hR)
  apply HasDerivAt.congr_deriv
  · unfold s6CentralA
    central_deriv
  · norm_num [npowRec]
    field_simp
    ring

theorem s6CentralP_hasDerivAt {R : ℝ} (hR : R ≠ 3) (hR1 : R ≠ 1) :
    HasDerivAt s6CentralP (s6CentralP1 R) R := by
  have hp : 3-R ≠ 0 := sub_ne_zero.mpr (Ne.symm hR)
  have hq : 1-R ≠ 0 := sub_ne_zero.mpr (Ne.symm hR1)
  apply HasDerivAt.congr_deriv
  · unfold s6CentralP
    central_deriv
  · unfold s6CentralP1
    norm_num [npowRec]
    field_simp
    ring

theorem s6CentralZ0_hasDerivAt {R : ℝ} (hR : R ≠ 3) :
    HasDerivAt s6CentralZ0 (s6CentralZ01 R) R := by
  have hp : 3-R ≠ 0 := sub_ne_zero.mpr (Ne.symm hR)
  apply HasDerivAt.congr_deriv
  · unfold s6CentralZ0
    central_deriv
  · unfold s6CentralZ01
    norm_num [npowRec]
    field_simp
    ring

private theorem s6_G1_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    -11/10 < s6CentralG1 R ∧ s6CentralG1 R < 0 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hD : 0 < 3+R^2 := by positivity
  have hlo : (28/9:ℝ) ≤ 3+R^2 := by nlinarith only [hR]
  have hhi : 3+R^2 < (22/7:ℝ) := by nlinarith only [hR,hR1]
  have hlo2 : (28/9:ℝ)^2 ≤ (3+R^2)^2 := by nlinarith only [hlo]
  have hhi2 : (3+R^2)^2 < (22/7:ℝ)^2 := by nlinarith only [hD,hhi]
  have hv : 24/(3+R^2)^2 ≤ (243/98:ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos hD)]
    nlinarith only [hlo2]
  have hv1 : (1:ℝ) < 24/(3+R^2)^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hD)]
    nlinarith only [hhi2]
  have hp := mul_le_mul_of_nonneg_left (show (-145/98:ℝ) ≤ 1-24/(3+R^2)^2 by linarith only [hv])
    (show 0 ≤ 2*R by positivity)
  unfold s6CentralG1
  exact ⟨by nlinarith only [hp,hR1],mul_neg_of_pos_of_neg (by positivity) (by linarith only [hv1])⟩

private theorem s6_P1_neg {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6CentralP1 R < 0 := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hp : (5/2:ℝ) < 3-R := by linarith only [hR1]
  have hq : 0 < 1-R := by linarith only [hR1]
  have hsq : (5/2:ℝ)^2 < (3-R)^2 := by nlinarith only [hp]
  have hcub : (5/2:ℝ)^3 < (3-R)^3 := by nlinarith only [hp,sq_nonneg (3-R-5/2)]
  have hD : 3+R^2 < (22/7:ℝ) := by nlinarith only [hR,hR1]
  have ht1 : 16*R/(3-R)^2 < (1:ℝ) := by
    rw [div_lt_one (sq_pos_of_pos (by linarith only [hp] : 0 < 3-R))]
    nlinarith only [hsq,hR1]
  have ht2 : 16*(3+R^2)/(3-R)^3 < (13/4:ℝ) := by
    rw [div_lt_iff₀ (pow_pos (by linarith only [hp] : 0 < 3-R) 3)]
    nlinarith only [hcub,hD]
  have hsmall : (1-R)^3 ≤ (2/3:ℝ)^3 := by gcongr; linarith only [hR]
  have ht3 : (27/4:ℝ) ≤ 2/(1-R)^3 := by
    rw [le_div_iff₀ (pow_pos hq 3)]
    nlinarith only [hsmall]
  unfold s6CentralP1
  linarith only [ht1,ht2,ht3]

private theorem s6_P_gt {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    11/10 < s6CentralP R := by
  have hm := ss_le_of_deriv (f := fun v => -s6CentralP v) (f' := fun v => -s6CentralP1 v) hR1
    (fun v hv => (s6CentralP_hasDerivAt (by linarith only [hv.2]) (by linarith only [hv.2])).neg)
    (fun v hv => (neg_pos.mpr (s6_P1_neg (le_trans hR hv.1.le) hv.2.le)).le)
  have he : (11/10:ℝ) < s6CentralP (7/19) := by norm_num [s6CentralP]
  linarith only [hm,he]

/-- The initial slope increases with the shape slope e. -/
theorem s6CentralSlope_mono_shape {R e f : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hef : e ≤ f) :
    s6CentralSlope R e ≤ s6CentralSlope R f := by
  have hD : 0 < 3+R^2 := by positivity
  have hp : 0 < 3-R := by linarith only [hR1]
  have hq : 0 < 1-R := by linarith only [hR1]
  have hR0 : 0 < R := by linarith only [hR]
  have hbr : 0 < 3-6*R-R^2 := by nlinarith only [hR,hR1]
  have hid : s6CentralSlope R f-s6CentralSlope R e =
      (f-e)*R*(1-R)*(3-6*R-R^2)/((3-R)*(3+R^2)) := by
    unfold s6CentralSlope s6CentralB s6CentralG
    field_simp
    ring
  have hnon : 0 ≤ (f-e)*R*(1-R)*(3-6*R-R^2)/((3-R)*(3+R^2)) := by positivity
  linarith only [hid,hnon]

private theorem s6_upper_slope_derivative_pos {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6CentralSlopeR R 3-1/(1-R)^2 := by
  have hp : 0 < 3-R := by linarith only [hR1]
  have hq : 0 < 1-R := by linarith only [hR1]
  have hD : 0 < 3+R^2 := by positivity
  have hid : s6CentralSlopeR R 3-1/(1-R)^2 =
      2*R*(3*R-1)/(3-R)+s6CentralP R+s6CentralG1 R := by
    unfold s6CentralSlopeR s6CentralB1 s6CentralP
    field_simp
    ring
  have hnon : 0 ≤ 2*R*(3*R-1)/(3-R) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hR] : 0 ≤ 2*R) (by linarith only [hR])
    · exact hp.le
  have hg := (s6_G1_bounds hR hR1).1
  have hpp := s6_P_gt hR hR1
  linarith only [hid,hnon,hg,hpp]

theorem s6CentralSlope_lt_A {R e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he1 : e ≤ 3) :
    s6CentralSlope R e < s6CentralA R := by
  have hm := ss_le_of_deriv (f := fun v => s6CentralSlope v 3-s6CentralA v)
    (f' := fun v => s6CentralSlopeR v 3-1/(1-v)^2) hR1
    (fun v hv => (s6CentralSlope_hasDerivAt (by linarith only [hv.2])).sub
      (s6CentralA_hasDerivAt (by linarith only [hv.2])))
    (fun v hv => (s6_upper_slope_derivative_pos (le_trans hR hv.1.le) hv.2.le).le)
  have he : s6CentralSlope (7/19) 3-s6CentralA (7/19) < 0 := by
    norm_num [s6CentralSlope,s6CentralB,s6CentralG,s6CentralA]
  have hs := s6CentralSlope_mono_shape hR hR1 he1
  linarith only [hm,he,hs]


private theorem s6_N_bounds {R e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 ≤ (1-e)+(e+3)*R ∧ (1-e)+(e+3)*R < 1/2 := by
  have hq : 0 ≤ 1-R := by linarith only [hR1]
  have hlo := mul_nonneg (show 0 ≤ 3-e by linarith only [he1]) hq
  have hhi := mul_nonneg (show 0 ≤ e-13/5 by linarith only [he]) hq
  constructor <;> nlinarith only [hlo,hhi,hR,hR1]

private theorem s6_B1_lt {R e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : s6CentralB1 R e < 17/4 := by
  obtain ⟨hN,hN1⟩ := s6_N_bounds hR hR1 he he1
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hp : (5/2:ℝ) < 3-R := by linarith only [hR1]
  have hD0 : 0 ≤ 3+R^2 := by positivity
  have hD : 3+R^2 ≤ (22/7:ℝ) := by nlinarith only [hR,hR1]
  have hnum1 := mul_le_mul (show R ≤ (3/8:ℝ) by linarith only [hR1]) hN1.le hN (by norm_num : (0:ℝ) ≤ 3/8)
  have hnum2 := mul_le_mul hD (show e+5 ≤ (8:ℝ) by linarith only [he1])
    (by linarith only [he] : 0 ≤ e+5) (by norm_num : (0:ℝ) ≤ 22/7)
  have ht1 : R*((1-e)+(e+3)*R)/(3-R) < (3/40:ℝ) := by
    rw [div_lt_iff₀ (by linarith only [hp] : 0 < 3-R)]
    nlinarith only [hnum1,hp]
  have hsq : (5/2:ℝ)^2 < (3-R)^2 := by nlinarith only [hp]
  have ht2 : (3+R^2)*(e+5)/(3-R)^2 < (704/175:ℝ) := by
    rw [div_lt_iff₀ (sq_pos_of_pos (by linarith only [hp] : 0 < 3-R))]
    nlinarith only [hnum2,hsq]
  unfold s6CentralB1
  linarith only [ht1,ht2]

private theorem s6_Z01_ge {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    19/24 ≤ s6CentralZ01 R := by
  have hp : 0 < 3-R := by linarith only [hR1]
  have hsq : R^2 ≤ (7/19:ℝ)^2 := by nlinarith only [hR,hR1]
  have hbr : 0 ≤ -32*R^2+111*R+171 := by nlinarith only [hsq,hR]
  have hid : s6CentralZ01 R-19/24 =
      (3*R-1)*(-32*R^2+111*R+171)/(24*(3-R)^2) := by
    unfold s6CentralZ01
    field_simp
    ring
  have hnon : 0 ≤ (3*R-1)*(-32*R^2+111*R+171)/(24*(3-R)^2) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [hR]) hbr
    · positivity
  linarith only [hid,hnon]

private theorem s6_lower_slope_derivative_neg {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6CentralSlopeR R (13/5)-(11/2)*s6CentralZ01 R < 0 := by
  have hB := s6_B1_lt hR hR1 (le_refl (13/5:ℝ)) (by norm_num)
  have hG := (s6_G1_bounds hR hR1).2
  have hZ := s6_Z01_ge hR hR1
  unfold s6CentralSlopeR
  linarith only [hB,hG,hZ]

/-- The initial slope exceeds the natural lower-envelope slope by 1/8. -/
theorem s6CentralSlope_gt_lower {R e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (he : 13/5 ≤ e) :
    (11/2)*s6CentralZ0 R+1/8 < s6CentralSlope R e := by
  have hm := ss_le_of_deriv (f := fun v => -(s6CentralSlope v (13/5)-(11/2)*s6CentralZ0 v))
    (f' := fun v => -(s6CentralSlopeR v (13/5)-(11/2)*s6CentralZ01 v)) hR1
    (fun v hv => ((s6CentralSlope_hasDerivAt (by linarith only [hv.2])).sub
      ((s6CentralZ0_hasDerivAt (by linarith only [hv.2])).const_mul (11/2))).neg)
    (fun v hv => (neg_pos.mpr (s6_lower_slope_derivative_neg (le_trans hR hv.1.le) hv.2.le)).le)
  have heval : (1/8:ℝ) < s6CentralSlope (7/19) (13/5)-(11/2)*s6CentralZ0 (7/19) := by
    norm_num [s6CentralSlope,s6CentralB,s6CentralG,s6CentralZ0]
  have hs := s6CentralSlope_mono_shape hR hR1 he
  linarith only [hm,heval,hs]

theorem s6Central_initial_values (R e : ℝ) :
    s6CentralZ R 0 e=s6CentralZ0 R ∧ s6CentralZ1 R 0 e=s6CentralSlope R e := by
  have hD : 0 < 3+R^2 := by positivity
  constructor
  · norm_num [s6CentralZ,s6CentralT]
  · unfold s6CentralZ1 s6CentralSlope s6CentralT s6CentralW s6CentralL s6CentralGamma
      s6CentralF1 s6CentralG
    norm_num
    field_simp
    ring

/-- Twice integrating the genuine curvature bounds. The zero-displacement
case is included without dividing by the displacement. -/
theorem s6Central_quadratic_bounds {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    s6CentralZ0 R+s6CentralSlope R e*d-19*d^2/8 ≤ s6CentralZ R d e ∧
      s6CentralZ R d e ≤ s6CentralZ0 R+s6CentralSlope R e*d-3*d^2/2 := by
  have hRlt : R < 1 := by linarith only [hR1]
  have he0 : 1 ≤ e := by linarith only [he]
  have hinit := s6Central_initial_values R e
  have hfirstUpper (v : ℝ) (hv : v ∈ Icc 0 d) :
      s6CentralZ1 R v e ≤ s6CentralSlope R e-3*v := by
    have hm := ss_le_of_deriv (f := fun t => -s6CentralZ1 R t e-3*t)
      (f' := fun t => -s6CentralZ2 R t e-3) hv.1 (fun t ht => ?_) (fun t ht => ?_)
    · rw [hinit.2] at hm
      nlinarith only [hm]
    · have hL := (s6CentralL_pos hRlt ht.1 he0).ne'
      exact ((s6CentralZ1_hasDerivAt hL).neg).sub ((hasDerivAt_id t).const_mul 3) |>.congr_deriv (by ring)
    · have hh := (s6CentralZ2_bounds hR hR1 ht.1.le (le_trans ht.2.le (hv.2.trans hd1)) he he1).2
      linarith only [hh]
  have hfirstLower (v : ℝ) (hv : v ∈ Icc 0 d) :
      s6CentralSlope R e-19*v/4 ≤ s6CentralZ1 R v e := by
    have hm := ss_le_of_deriv (f := fun t => s6CentralZ1 R t e+19*t/4)
      (f' := fun t => s6CentralZ2 R t e+19/4) hv.1 (fun t ht => ?_) (fun t ht => ?_)
    · rw [hinit.2] at hm
      nlinarith only [hm]
    · have hL := (s6CentralL_pos hRlt ht.1 he0).ne'
      exact (s6CentralZ1_hasDerivAt hL).add (((hasDerivAt_id t).const_mul 19).div_const 4) |>.congr_deriv (by ring)
    · have hh := (s6CentralZ2_bounds hR hR1 ht.1.le (le_trans ht.2.le (hv.2.trans hd1)) he he1).1
      linarith only [hh]
  have hupper := ss_le_of_deriv
    (f := fun v => -s6CentralZ R v e+s6CentralSlope R e*v-3*v^2/2)
    (f' := fun v => -s6CentralZ1 R v e+s6CentralSlope R e-3*v) hd
    (fun v hv => ?_) (fun v hv => by have hh := hfirstUpper v (Ioo_subset_Icc_self hv); linarith only [hh])
  · have hlower := ss_le_of_deriv
      (f := fun v => s6CentralZ R v e-s6CentralSlope R e*v+19*v^2/8)
      (f' := fun v => s6CentralZ1 R v e-s6CentralSlope R e+19*v/4) hd
      (fun v hv => ?_) (fun v hv => by have hh := hfirstLower v (Ioo_subset_Icc_self hv); linarith only [hh])
    · rw [hinit.1] at hlower hupper
      exact ⟨by nlinarith only [hlower],by nlinarith only [hupper]⟩
    · have hL := (s6CentralL_pos hRlt hv.1 he0).ne'
      have hh := ((s6CentralZ_hasDerivAt hL).sub
        ((hasDerivAt_id v).const_mul (s6CentralSlope R e))).add ((hasDerivAt_pow 2 v).const_mul (19/8))
      convert hh using 1
      · funext y
        dsimp only [Pi.add_apply,Pi.sub_apply,id_eq]
        ring
      · norm_num
        ring
  · have hL := (s6CentralL_pos hRlt hv.1 he0).ne'
    have hh := (((s6CentralZ_hasDerivAt hL).neg).add
      ((hasDerivAt_id v).const_mul (s6CentralSlope R e))).sub ((hasDerivAt_pow 2 v).const_mul (3/2))
    convert hh using 1
    · funext y
      dsimp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]
      ring
    · norm_num
      ring

/-- Analytic central shear envelopes, including d=0. -/
theorem s6Central_envelopes {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6CentralZL R d ∧ s6CentralZL R d ≤ s6CentralZ R d e ∧
      s6CentralZ R d e ≤ s6CentralZU R d := by
  obtain ⟨hlower,hupper⟩ := s6Central_quadratic_bounds hR hR1 hd hd1 he he1
  have hslo := s6CentralSlope_gt_lower hR hR1 he
  have hshi := s6CentralSlope_lt_A hR hR1 he1
  have hmlo := mul_le_mul_of_nonneg_right hslo.le hd
  have hmhi := mul_le_mul_of_nonneg_right hshi.le hd
  have hgain : 0 ≤ d*(1-19*d)/8 := div_nonneg (mul_nonneg hd (by linarith only [hd1])) (by norm_num)
  have hR0 : 0 < R := by linarith only [hR]
  have hZ0 : 0 < s6CentralZ0 R := by
    unfold s6CentralZ0
    exact div_pos (by positivity) (by linarith only [hR1])
  have hL : 0 < s6CentralZL R d := by unfold s6CentralZL; positivity
  refine ⟨hL,?_,?_⟩
  · unfold s6CentralZL
    nlinarith only [hlower,hmlo,hgain]
  · unfold s6CentralZU
    nlinarith only [hupper,hmhi]


/-- Exact anisotropy identity in the original angle coordinates. -/
theorem s6Central_anisotropy {x al be : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    ssAn x be al=(ssRr x^2-ssTs al be^2)/(3+ssTs al be^2) := by
  have hS : 0 < x+1 := by positivity
  have hsum : 0 < be+al := by positivity
  have hKA : 0 < al^2+al*be+be^2 := by positivity
  have hnum : 0 < 3*(be+al)^2+(be-al)^2 := by positivity
  unfold ssAn ssRr ssTs
  rw [div_eq_div_iff (by positivity) (by field_simp; positivity)]
  field_simp
  ring

/-- The f(T) representation is exactly the original physical central shear. -/
theorem s6CentralZ_physical {x d e : ℝ} (hx : 1 < x) (hd : 0 ≤ d) (he : 0 ≤ e) :
    s6CentralZ (ssRr x) d e =
      2*m2U (1/(1+x))*(2*(x*(1+d))*x-x-(1+e*d)*(x*(1+d)))/(x*(x+2))-
        ssRr x-(1+ssAn x (x*(1+d)) (1+e*d))*ssTs (1+e*d) (x*(1+d)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < 1+x := by positivity
  have hSp : 0 < x+1 := by positivity
  have hX2 : 0 < x+2 := by positivity
  have hal : 0 < 1+e*d := by positivity
  have hbe : 0 < x*(1+d) := by positivity
  have hsum : 0 < x*(1+d)+(1+e*d) := by positivity
  have hT : s6CentralT (ssRr x) d e=ssTs (1+e*d) (x*(1+d)) := by
    have hn : 2*ssRr x+((e+1)*ssRr x-(e-1))*d =
        2*(x*(1+d)-(1+e*d))/(x+1) := by unfold ssRr; field_simp; ring
    have hden : 2+(e+1-(e-1)*ssRr x)*d =
        2*(x*(1+d)+(1+e*d))/(x+1) := by unfold ssRr; field_simp; ring
    unfold s6CentralT ssTs
    rw [hn,hden]
    field_simp
  have hrow : s6CentralZ0 (ssRr x)+s6CentralB (ssRr x) e*d-s6CentralC (ssRr x) e*d^2 =
      2*m2U (1/(1+x))*(2*(x*(1+d))*x-x-(1+e*d)*(x*(1+d)))/(x*(x+2))-2*ssRr x := by
    have h3 : 3-ssRr x = 2*(x+2)/(x+1) := by unfold ssRr; field_simp; ring
    unfold s6CentralZ0 s6CentralB s6CentralC
    rw [h3]
    unfold ssRr m2U
    field_simp
    ring
  have hprod : (3+ssRr x^2)*s6CentralF (ssRr x)=ssRr x := by
    unfold s6CentralF
    field_simp
  have hAn := s6Central_anisotropy hx0 hal hbe
  have hterm : (1+ssAn x (x*(1+d)) (1+e*d))*ssTs (1+e*d) (x*(1+d)) =
      (3+ssRr x^2)*s6CentralF (ssTs (1+e*d) (x*(1+d))) := by
    rw [hAn]
    unfold s6CentralF
    field_simp
    ring
  unfold s6CentralZ
  rw [hrow,hT,hterm]
  nlinarith only [hprod]

/-- Initial slopes and curvature bound the physical central shear between both envelopes. -/
theorem cost_shear_core_analytic {x d e : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6CentralZL (ssRr x) d ∧
      s6CentralZL (ssRr x) d ≤
        2*m2U (1/(1+x))*(2*(x*(1+d))*x-x-(1+e*d)*(x*(1+d)))/(x*(x+2))-
          ssRr x-(1+ssAn x (x*(1+d)) (1+e*d))*ssTs (1+e*d) (x*(1+d)) ∧
      2*m2U (1/(1+x))*(2*(x*(1+d))*x-x-(1+e*d)*(x*(1+d)))/(x*(x+2))-
          ssRr x-(1+ssAn x (x*(1+d)) (1+e*d))*ssTs (1+e*d) (x*(1+d)) ≤
        s6CentralZU (ssRr x) d := by
  have hx0 : 0 < x+1 := by linarith only [hx]
  have hR : (1/3:ℝ) ≤ ssRr x := by unfold ssRr; rw [le_div_iff₀ hx0]; linarith only [hx]
  have hR1 : ssRr x ≤ (7/19:ℝ) := by unfold ssRr; rw [div_le_iff₀ hx0]; linarith only [hx1]
  have hh := s6Central_envelopes hR hR1 hd hd1 he he1
  rw [s6CentralZ_physical (by linarith only [hx]) hd (by linarith only [he])] at hh
  exact hh

/-- The central-shear envelopes in the original coordinates. -/
theorem cost_shear_core {x d e : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    2*ssRr x^2*(1+ssRr x)/(3-ssRr x)*(1+11*d/2) ≤
      2*m2U (1/(1+x))*(2*(x*(1+d))*x-x-(1+e*d)*(x*(1+d)))/(x*(x+2))-
        ssRr x-(1+ssAn x (x*(1+d)) (1+e*d))*ssTs (1+e*d) (x*(1+d)) ∧
    2*m2U (1/(1+x))*(2*(x*(1+d))*x-x-(1+e*d)*(x*(1+d)))/(x*(x+2))-
        ssRr x-(1+ssAn x (x*(1+d)) (1+e*d))*ssTs (1+e*d) (x*(1+d)) ≤
      2*ssRr x^2*(1+ssRr x)/(3-ssRr x)+(1+2*ssRr x)/(3*(1-ssRr x))*d-3/2*d^2 := by
  have hh := (cost_shear_core_analytic hx hx1 hd hd1 he he1).2
  unfold s6CentralZL s6CentralZU s6CentralZ0 s6CentralA at hh
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1; ring

end SmoothedOctagon

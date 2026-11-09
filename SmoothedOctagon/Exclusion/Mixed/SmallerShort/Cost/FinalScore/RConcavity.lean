module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Pair
public import Mathlib.Analysis.Convex.Deriv

/-!
# S6 final score: natural-kernel concavity at maximal displacement
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRP (e : ℝ) : ℝ := (e-1)/(39+e)
noncomputable def s6FinalRT (p R : ℝ) : ℝ := (R-p)/(1-p*R)
noncomputable def s6FinalRT1 (p R : ℝ) : ℝ := (1-p^2)/(1-p*R)^2
noncomputable def s6FinalRT2 (p R : ℝ) : ℝ := 2*p*(1-p^2)/(1-p*R)^3

private theorem s6_final_rp_bounds {e : ℝ} (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalRP e ∧ s6FinalRP e ≤ 1/21 := by
  have hp : 0 < 39+e := by linarith
  unfold s6FinalRP
  constructor
  · exact div_pos (by linarith) hp
  · rw [div_le_iff₀ hp]; linarith

private theorem s6_final_rt_eq {R e : ℝ} (he : 13/5 ≤ e) :
    costT R (1/19) e=s6FinalRT (s6FinalRP e) R := by
  have hp : 39+e ≠ 0 := by linarith
  unfold costT s6FinalRT s6FinalRP
  field_simp
  ; ring

private theorem s6_final_rt_deriv {p R : ℝ} (hden : 1-p*R ≠ 0) :
    HasDerivAt (s6FinalRT p) (s6FinalRT1 p R) R := by
  have hh := ((hasDerivAt_id R).sub_const p).div
    (((hasDerivAt_id R).const_mul p).const_sub 1) hden
  convert hh using 1
  · ext x; simp only [s6FinalRT, id, Pi.div_apply]
  · simp only [s6FinalRT1, id]
    field_simp
    ring

private theorem s6_final_rt1_deriv {p R : ℝ} (hden : 1-p*R ≠ 0) :
    HasDerivAt (s6FinalRT1 p) (s6FinalRT2 p R) R := by
  have hh := (hasDerivAt_const R (1-p^2)).div
    ((((hasDerivAt_id R).const_mul p).const_sub 1).pow 2) (pow_ne_zero 2 hden)
  convert hh using 1
  · ext x; simp only [s6FinalRT1, id, Pi.div_apply, Pi.pow_apply]
  · simp only [s6FinalRT2, id, Pi.pow_apply]
    field_simp
    ring

private theorem s6_final_rt_bounds {p R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1/21)
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    9/31 ≤ s6FinalRT p R ∧ s6FinalRT p R ≤ R ∧
    1 < s6FinalRT1 p R ∧ s6FinalRT1 p R < 21/20 ∧
    0 < s6FinalRT2 p R ∧ s6FinalRT2 p R < 1/9 := by
  have hR0 : 0 < R := by linarith
  have hRs : R^2 < 1/7 := by nlinarith only [hR0,hR1]
  have hpr : 0 < p*R := mul_pos hp hR0
  have hpr1 : p*R < 1/56 := by nlinarith only [mul_le_mul hp1 hR1 hR0.le (by norm_num : (0:ℝ)≤1/21)]
  have hd : 0 < 1-p*R := by linarith
  have hps : p^2 < 1 := by nlinarith only [hp,hp1]
  have hn : 0 < 1-p^2 := by linarith
  have hds : (55/56:ℝ)^2 < (1-p*R)^2 := by nlinarith only [hd,hpr1]
  have hdc : (55/56:ℝ)^3 < (1-p*R)^3 := by
    exact pow_lt_pow_left₀ (by linarith only [hpr1]) (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · unfold s6FinalRT
    rw [le_div_iff₀ hd]
    have hm : p*(1-(9/31)*R) ≤ (1/21)*(1-(9/31)*R) :=
      mul_le_mul_of_nonneg_right hp1 (by nlinarith only [hR1])
    linarith only [hm,hR]
  · unfold s6FinalRT
    rw [div_le_iff₀ hd]
    nlinarith only [mul_nonneg hp.le (show 0 ≤ 1-R^2 by linarith only [hRs])]
  · unfold s6FinalRT1
    rw [lt_div_iff₀ (sq_pos_of_pos hd)]
    have hh : 0 < p*(2*R-p*(1+R^2)) := by
      apply mul_pos hp
      have hm : p*(1+R^2) ≤ (1/21)*(1+1/7) :=
        mul_le_mul hp1 (by linarith only [hRs]) (by positivity) (by norm_num)
      linarith only [hm,hR]
    nlinarith only [hh]
  · unfold s6FinalRT1
    rw [div_lt_iff₀ (sq_pos_of_pos hd)]
    nlinarith only [hds,sq_nonneg p]
  · unfold s6FinalRT2
    positivity
  · unfold s6FinalRT2
    rw [div_lt_iff₀ (pow_pos hd 3)]
    have hm : p*(1-p^2) ≤ 1/21 := by
      calc
        p*(1-p^2) ≤ p*1 := mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg p]) hp.le
        _ ≤ 1/21 := by simpa using hp1
    nlinarith only [hm,hdc]

/-- The two positive kernels in the maximal-displacement norm floor. -/
noncomputable def s6FinalRQ1 (R : ℝ) : ℝ := 16*(1+R)/(3*(4+3*R)^2)
noncomputable def s6FinalRQ11 (R : ℝ) : ℝ := -16*(3*R+2)/(3*(3*R+4)^3)
noncomputable def s6FinalRQ12 (R : ℝ) : ℝ := 32*(3*R+1)/(3*R+4)^4
noncomputable def s6FinalRQ2 (R : ℝ) : ℝ := 3*R^2/(80*(1+R)^3)
noncomputable def s6FinalRQ21 (R : ℝ) : ℝ := 3*R*(2-R)/(80*(1+R)^4)
noncomputable def s6FinalRQ22 (R : ℝ) : ℝ := 3*(R^2-4*R+1)/(40*(1+R)^5)
noncomputable def s6FinalRH (R : ℝ) : ℝ := 38*R^3/(39*R+1)
noncomputable def s6FinalRH1 (R : ℝ) : ℝ := 114*R^2*(26*R+1)/(39*R+1)^2
noncomputable def s6FinalRH2 (R : ℝ) : ℝ := (76/39)*(1-(39*R+1)⁻¹^3)
noncomputable def s6FinalRV1 (R : ℝ) : ℝ :=
  (s6FinalRQ11 R+s6FinalRQ21 R)*s6FinalRH R+
    (s6FinalRQ1 R+s6FinalRQ2 R)*s6FinalRH1 R
noncomputable def s6FinalRV2 (R : ℝ) : ℝ :=
  (s6FinalRQ12 R+s6FinalRQ22 R)*s6FinalRH R+
    2*(s6FinalRQ11 R+s6FinalRQ21 R)*s6FinalRH1 R+
    (s6FinalRQ1 R+s6FinalRQ2 R)*s6FinalRH2 R

private theorem s6_final_rq_derivatives {R : ℝ} (hR : 0 ≤ R) :
    HasDerivAt s6FinalRQ1 (s6FinalRQ11 R) R ∧
    HasDerivAt s6FinalRQ11 (s6FinalRQ12 R) R ∧
    HasDerivAt s6FinalRQ2 (s6FinalRQ21 R) R ∧
    HasDerivAt s6FinalRQ21 (s6FinalRQ22 R) R ∧
    HasDerivAt s6FinalRH (s6FinalRH1 R) R ∧
    HasDerivAt s6FinalRH1 (s6FinalRH2 R) R := by
  have ha : 4+3*R ≠ 0 := ne_of_gt (by positivity)
  have ha' : 3*R+4 ≠ 0 := ne_of_gt (by positivity)
  have hb : 1+R ≠ 0 := ne_of_gt (by positivity)
  have hc : 39*R+1 ≠ 0 := ne_of_gt (by positivity)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hh := (((hasDerivAt_id R).const_add 1).const_mul 16).div
      (((((hasDerivAt_id R).const_mul 3).const_add 4).pow 2).const_mul 3) (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha))
    convert hh using 1
    · ext x; simp only [s6FinalRQ1, id, Pi.div_apply, Pi.pow_apply]
    · simp only [s6FinalRQ11, id, Pi.pow_apply]
      field_simp
      ring
  · have hh := ((((hasDerivAt_id R).const_mul 3).const_add 2).const_mul (-16)).div
      (((((hasDerivAt_id R).const_mul 3).const_add 4).pow 3).const_mul 3) (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha))
    convert hh using 1
    · ext x; simp only [s6FinalRQ11, id, Pi.div_apply, Pi.pow_apply] ; ring
    · simp only [s6FinalRQ12, id, Pi.pow_apply]
      field_simp
      ring
  · have hh := ((hasDerivAt_pow 2 R).const_mul 3).div
      ((((hasDerivAt_id R).const_add 1).pow 3).const_mul 80) (mul_ne_zero (by norm_num) (pow_ne_zero 3 hb))
    convert hh using 1
    · ext x; simp only [s6FinalRQ2, id, Pi.div_apply, Pi.pow_apply]
    · simp only [s6FinalRQ21, id, Pi.pow_apply]
      field_simp
      ring
  · have hh := (((hasDerivAt_id R).mul ((hasDerivAt_id R).const_sub 2)).const_mul 3).div
      ((((hasDerivAt_id R).const_add 1).pow 4).const_mul 80) (mul_ne_zero (by norm_num) (pow_ne_zero 4 hb))
    convert hh using 1
    · ext x; simp only [s6FinalRQ21, id, Pi.div_apply, Pi.mul_apply, Pi.pow_apply] ; ring
    · simp only [s6FinalRQ22, id, Pi.mul_apply, Pi.pow_apply]
      field_simp
      ring
  · have hh := ((hasDerivAt_pow 3 R).const_mul 38).div
      (((hasDerivAt_id R).const_mul 39).const_add 1) (by simpa only [id,add_comm] using hc)
    convert hh using 1
    · ext x; simp only [s6FinalRH, id, Pi.div_apply] ; ring
    · simp only [s6FinalRH1, id]
      field_simp
      ring
  · have hh := (((hasDerivAt_pow 2 R).mul (((hasDerivAt_id R).const_mul 26).const_add 1)).const_mul 114).div
      ((((hasDerivAt_id R).const_mul 39).const_add 1).pow 2) (pow_ne_zero 2 (show 1+39*id R ≠ 0 by simpa only [id,add_comm] using hc))
    convert hh using 1
    · ext x; simp only [s6FinalRH1, id, Pi.div_apply, Pi.mul_apply, Pi.pow_apply] ; ring
    · simp only [s6FinalRH2, id, Pi.mul_apply, Pi.pow_apply]
      field_simp
      ring

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

private theorem s6_final_rq_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalRQ1 R ∧ 0 < s6FinalRQ2 R ∧
    s6FinalRQ1 R+s6FinalRQ2 R < 23/80 ∧
    s6FinalRQ11 R+s6FinalRQ21 R < 0 ∧
    s6FinalRQ12 R < 1/9 ∧ s6FinalRQ22 R < 0 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hR8 : R ≤ 3/8 := by linarith only [hR1]
  have hq11 : s6FinalRQ11 R < -1/10 := by
    have hb : (16*3/(3*(41/8)^3):ℝ) ≤ 16*(3*R+2)/(3*(3*R+4)^3) := by
      gcongr <;> linarith only [hR,hR8]
    unfold s6FinalRQ11
    have hh : (-16*(3*R+2)/(3*(3*R+4)^3)) = -(16*(3*R+2)/(3*(3*R+4)^3)) := by ring
    rw [hh]
    linarith only [hb]
  have htwo : 0 < 2-R := by linarith only [hR1]
  have hq21 : 0 < s6FinalRQ21 R ∧ s6FinalRQ21 R < 1/100 := by
    unfold s6FinalRQ21
    constructor
    · positivity
    · have hb : 3*R*(2-R)/(80*(1+R)^4) ≤ (3*(3/8)*(5/3)/(80*(4/3)^4):ℝ) := by
        gcongr <;> linarith only [hR,hR8]
      linarith only [hb]
  have hq1 : s6FinalRQ1 R ≤ 64/225 := by
    have hh := ss_le_of_deriv (f := fun R => -s6FinalRQ1 R)
      (f' := fun R => -s6FinalRQ11 R) hR
      (fun z hz => (s6_final_rq_derivatives (show 0 ≤ z by linarith only [hz.1])).1.neg)
      (fun z hz => by
        unfold s6FinalRQ11
        have hz0 : 0 ≤ z := by linarith only [hz.1]
        have hp : 0 < 3*(3*z+4)^3 := by positivity
        have hn : 0 ≤ 16*(3*z+2) := by positivity
        have hh := div_nonneg hn hp.le
        convert hh using 1 ; ring)
    norm_num [s6FinalRQ1] at hh
    change s6FinalRQ1 R ≤ 64/225 at hh
    exact hh
  have hq2 : s6FinalRQ2 R < 1/400 := by
    have hb : 3*R^2/(80*(1+R)^3) ≤ (3*(3/8)^2/(80*(4/3)^3):ℝ) := by
      gcongr ; linarith only [hR,hR8]
    change 3*R^2/(80*(1+R)^3)<1/400
    linarith only [hb]
  have hq12 : s6FinalRQ12 R < 1/9 := by
    have hb : 32*(3*R+1)/(3*R+4)^4 ≤ (32*(17/8)/5^4:ℝ) := by
      gcongr <;> linarith only [hR,hR8]
    change 32*(3*R+1)/(3*R+4)^4<1/9
    linarith only [hb]
  have hq22 : s6FinalRQ22 R < 0 := by
    unfold s6FinalRQ22
    apply div_neg_of_neg_of_pos
    · have hrs : R^2 ≤ (3/8:ℝ)^2 := by nlinarith only [hR0,hR8]
      nlinarith only [hrs,hR]
    · positivity
  refine ⟨by unfold s6FinalRQ1; positivity,by unfold s6FinalRQ2; positivity,
    ?_,by linarith only [hq11,hq21.2],hq12,hq22⟩
  linarith only [hq1,hq2]

private theorem s6_final_rh_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalRH R ∧ s6FinalRH R < 1/7 ∧
    0 < s6FinalRH1 R ∧ s6FinalRH1 R ≤ s6FinalRH1 (7/19) ∧
    0 < s6FinalRH2 R ∧ s6FinalRH2 R < 2 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hden : 0 < 39*R+1 := by positivity
  have hHlt : s6FinalRH R < R^2 := by
    unfold s6FinalRH
    rw [div_lt_iff₀ hden]
    nlinarith only [sq_pos_of_pos hR0,mul_pos (sq_pos_of_pos hR0) (show 0 < R+1 by positivity)]
  have hH2 (z : ℝ) (hz : 0 < z) : 0 < s6FinalRH2 z ∧ s6FinalRH2 z < 2 := by
    have hd : 1 < 39*z+1 := by linarith only [hz]
    have hi : 0 < (39*z+1)⁻¹ ∧ (39*z+1)⁻¹ < 1 := by
      constructor
      · positivity
      · exact (inv_lt_one₀ (by linarith only [hd])).2 hd
    have hip : (39*z+1)⁻¹^3 < 1 := by nlinarith only [hi.1,hi.2,sq_nonneg ((39*z+1)⁻¹-1)]
    unfold s6FinalRH2
    constructor
    · nlinarith only [hip]
    · have hip0 : 0 < (39*z+1)⁻¹^3 := by positivity
      nlinarith only [hip0]
  have hm := ss_le_of_deriv hR1
    (fun z hz => (s6_final_rq_derivatives (show 0 ≤ z by linarith only [hz.1,hR])).2.2.2.2.2)
    (fun z hz => (hH2 z (by linarith only [hz.1,hR])).1.le)
  refine ⟨by unfold s6FinalRH; positivity,?_,by unfold s6FinalRH1; positivity,hm,
    (hH2 R hR0).1,(hH2 R hR0).2⟩
  have hrs : R^2 < 1/7 := by nlinarith only [hR0,hR1]
  linarith only [hHlt,hrs]

private theorem s6_final_rv_derivatives {R : ℝ} (hR : 0 < R) :
    HasDerivAt (fun R => s6FinalV R (1/19)) (s6FinalRV1 R) R ∧
    HasDerivAt s6FinalRV1 (s6FinalRV2 R) R := by
  have hd := s6_final_rq_derivatives hR.le
  have hp : 1+R ≠ 0 := by positivity
  have hq : 4+3*R ≠ 0 := by positivity
  have hm : 39*R+1 ≠ 0 := by positivity
  have hprod := hd.2.2.2.2.1.mul (hd.1.add hd.2.2.1)
  have heq : (fun R => s6FinalV R (1/19)) =ᶠ[nhds R]
      (fun R => s6FinalRH R*(s6FinalRQ1 R+s6FinalRQ2 R)) := by
    filter_upwards [eventually_gt_nhds hR] with z hz
    have hpz : 1+z ≠ 0 := by positivity
    have hqz : 4+3*z ≠ 0 := by positivity
    have hmz : 39*z+1 ≠ 0 := by positivity
    unfold s6FinalV s6VarianceFloor s6FinalRH s6FinalRQ1 s6FinalRQ2
    field_simp
    ring
  constructor
  · apply HasDerivAt.congr_of_eventuallyEq _ heq
    apply hprod.congr_deriv
    simp only [s6FinalRV1, Pi.add_apply]
    ring
  · have hh := ((hd.2.1.add hd.2.2.2.1).mul hd.2.2.2.2.1).add
      ((hd.1.add hd.2.2.1).mul hd.2.2.2.2.2)
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRV2, Pi.add_apply]
      ring

private theorem s6_final_rv_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalRV1 R ∧ s6FinalRV1 R < 1/5 ∧ s6FinalRV2 R < 3/5 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hq := s6_final_rq_bounds hR hR1
  have hh := s6_final_rh_bounds hR hR1
  have hp : 1+R ≠ 0 := by positivity
  have ha : 4+3*R ≠ 0 := by positivity
  have hb : 39*R+1 ≠ 0 := by positivity
  have hlog1 : 0 < 3/R+1/(1+R)-39/(39*R+1)-6/(4+3*R) := by
    have hb1 : 39/(39*R+1)<1/R := by rw [div_lt_div_iff₀ (by positivity) hR0]; linarith
    have hb2 : 6/(4+3*R)<2/R := by rw [div_lt_div_iff₀ (by positivity) hR0]; linarith
    have hb3 : 0 < 1/(1+R) := by positivity
    simp only [div_eq_mul_inv] at hb1 hb2 hb3 ⊢
    linarith only [hb1,hb2,hb3]
  have hlog2 : 0 < 5/R-39/(39*R+1)-3/(1+R) := by
    have hb1 : 39/(39*R+1)<1/R := by rw [div_lt_div_iff₀ (by positivity) hR0]; linarith
    have hb2 : 3/(1+R)<3/R := by rw [div_lt_div_iff₀ (by positivity) hR0]; linarith
    have hb3 : 0 < 1/R := by positivity
    simp only [div_eq_mul_inv] at hb1 hb2 hb3 ⊢
    linarith only [hb1,hb2,hb3]
  have hi1 : s6FinalRQ11 R*s6FinalRH R+s6FinalRQ1 R*s6FinalRH1 R=
      (s6FinalRH R*s6FinalRQ1 R)*(3/R+1/(1+R)-39/(39*R+1)-6/(4+3*R)) := by
    unfold s6FinalRH s6FinalRH1 s6FinalRQ1 s6FinalRQ11
    field_simp
    ring
  have hi2 : s6FinalRQ21 R*s6FinalRH R+s6FinalRQ2 R*s6FinalRH1 R=
      (s6FinalRH R*s6FinalRQ2 R)*(5/R-39/(39*R+1)-3/(1+R)) := by
    unfold s6FinalRH s6FinalRH1 s6FinalRQ2 s6FinalRQ21
    field_simp
    ring
  have hv1p : 0 < s6FinalRV1 R := by
    have hh1 := mul_pos (mul_pos hh.1 hq.1) hlog1
    have hh2 := mul_pos (mul_pos hh.1 hq.2.1) hlog2
    unfold s6FinalRV1
    linarith only [hh1,hh2,hi1,hi2]
  have hv1 : s6FinalRV1 R < 1/5 := by
    have hc := mul_neg_of_neg_of_pos hq.2.2.2.1 hh.1
    have hu := mul_lt_mul_of_pos_right hq.2.2.1 hh.2.2.1
    have hlast : (23/80:ℝ)*s6FinalRH1 R < 1/5 := by
      have hm := hh.2.2.2.1
      norm_num [s6FinalRH1] at hm
      change s6FinalRH1 R ≤ _ at hm
      linarith only [hm]
    unfold s6FinalRV1
    linarith only [hc,hu,hlast]
  have hv2 : s6FinalRV2 R < 3/5 := by
    have hc := mul_neg_of_neg_of_pos hq.2.2.2.1 hh.2.2.1
    have hnn := mul_neg_of_neg_of_pos hq.2.2.2.2.2 hh.1
    have ha1 := mul_lt_mul_of_pos_right hq.2.2.2.2.1 hh.1
    have ha2 := mul_lt_mul_of_pos_left hh.2.1 (by norm_num : (0:ℝ)<1/9)
    have hb1 := mul_lt_mul_of_pos_right hq.2.2.1 hh.2.2.2.2.1
    have hb2 := mul_lt_mul_of_pos_left hh.2.2.2.2.2 (by norm_num : (0:ℝ)<23/80)
    unfold s6FinalRV2
    nlinarith only [hc,hnn,ha1,ha2,hb1,hb2]
  exact ⟨hv1p,hv1,hv2⟩

end SmoothedOctagon

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

private theorem s6_final_rpair_derivatives {e R : ℝ}
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

private theorem s6_final_rpair_second_upper {e R : ℝ}
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

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

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

private theorem s6_final_rshear_derivatives {e R : ℝ}
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

private theorem s6_final_rshear_second_lower {e R : ℝ}
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

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRWA (R : ℝ) : ℝ := 1-R^2
noncomputable def s6FinalRWB (p R : ℝ) : ℝ := 2-p*(R+1/R)
noncomputable def s6FinalRWB1 (p R : ℝ) : ℝ := p*(1/R^2-1)
noncomputable def s6FinalRWB2 (p R : ℝ) : ℝ := -2*p/R^3
noncomputable def s6FinalRWD (p R : ℝ) : ℝ := 3*(1-p*R)^2+(R-p)^2
noncomputable def s6FinalRWD1 (p R : ℝ) : ℝ := -6*p*(1-p*R)+2*(R-p)
noncomputable def s6FinalRWD2 (p : ℝ) : ℝ := 6*p^2+2
noncomputable def s6FinalRWC (p R : ℝ) : ℝ := 1/s6FinalRWD p R
noncomputable def s6FinalRWC1 (p R : ℝ) : ℝ := -s6FinalRWD1 p R/(s6FinalRWD p R)^2
noncomputable def s6FinalRWC2 (p R : ℝ) : ℝ :=
  2*(s6FinalRWD1 p R)^2/(s6FinalRWD p R)^3-s6FinalRWD2 p/(s6FinalRWD p R)^2
noncomputable def s6FinalRW (p R : ℝ) : ℝ := p*s6FinalRWA R*s6FinalRWB p R*s6FinalRWC p R
noncomputable def s6FinalRW1 (p R : ℝ) : ℝ :=
  p*((-2*R*s6FinalRWB p R+s6FinalRWA R*s6FinalRWB1 p R)*s6FinalRWC p R+
    s6FinalRWA R*s6FinalRWB p R*s6FinalRWC1 p R)
noncomputable def s6FinalRW2 (p R : ℝ) : ℝ :=
  p*((-2*s6FinalRWB p R-4*R*s6FinalRWB1 p R+s6FinalRWA R*s6FinalRWB2 p R)*s6FinalRWC p R+
    2*(-2*R*s6FinalRWB p R+s6FinalRWA R*s6FinalRWB1 p R)*s6FinalRWC1 p R+
    s6FinalRWA R*s6FinalRWB p R*s6FinalRWC2 p R)

private theorem s6_final_rw_kernel_bounds {p R : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1/21) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalRWA R ∧ s6FinalRWA R ≤ 8/9 ∧
    7/4 < s6FinalRWB p R ∧ s6FinalRWB p R < 2 ∧
    0 < s6FinalRWB1 p R ∧ s6FinalRWB1 p R ≤ 3/7 ∧
    8/3 < s6FinalRWD p R ∧ 0 < s6FinalRWD1 p R ∧ s6FinalRWD1 p R < 4/5 ∧
    s6FinalRWD2 p < 21/10 ∧ 0 < s6FinalRWC p R ∧ s6FinalRWC p R < 3/8 ∧
    s6FinalRWC1 p R < 0 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hR8 : R ≤ 3/8 := by linarith only [hR1]
  have hRs : R^2 < 1/7 := by nlinarith only [hR0,hR1]
  have hpr : 0 < p*R := mul_pos hp hR0
  have hpr1 : p*R < 1/56 := by nlinarith only [mul_le_mul hp1 hR1 hR0.le (by norm_num : (0:ℝ)≤1/21)]
  have hir : 1/R ≤ 3 := by rw [div_le_iff₀ hR0]; linarith only [hR]
  have hi : 0 < 1/R := by positivity
  have hA : 0 < s6FinalRWA R ∧ s6FinalRWA R ≤ 8/9 := by
    unfold s6FinalRWA
    constructor <;> nlinarith only [hRs,hR,hR0]
  have hB : 7/4 < s6FinalRWB p R ∧ s6FinalRWB p R < 2 := by
    have hu : p*(R+1/R) ≤ (1/21)*(3/8+3) :=
      mul_le_mul hp1 (by linarith only [hR8,hir]) (by positivity) (by norm_num)
    have hl : 0 < p*(R+1/R) := by positivity
    unfold s6FinalRWB
    constructor <;> linarith only [hu,hl]
  have hB1 : 0 < s6FinalRWB1 p R ∧ s6FinalRWB1 p R ≤ 3/7 := by
    have hmin : 1 < 1/R^2 := by rw [lt_div_iff₀ (sq_pos_of_pos hR0)]; linarith only [hRs]
    have hmax : 1/R^2 ≤ 9 := by rw [div_le_iff₀ (sq_pos_of_pos hR0)]; nlinarith only [hR,hR0]
    have hh := mul_le_mul hp1 hmax (by positivity : 0 ≤ 1/R^2) (by norm_num : (0:ℝ)≤1/21)
    unfold s6FinalRWB1
    constructor
    · exact mul_pos hp (by linarith only [hmin])
    · nlinarith only [hh,hp]
  have hD : 8/3 < s6FinalRWD p R := by
    have hs : (55/56:ℝ)^2 < (1-p*R)^2 := by nlinarith only [hpr1]
    unfold s6FinalRWD
    nlinarith only [hs,sq_nonneg (R-p)]
  have hD1 : 0 < s6FinalRWD1 p R ∧ s6FinalRWD1 p R < 4/5 := by
    have hsmall : 0 ≤ 6*p^2*R := by positivity
    have hupper := mul_lt_mul_of_pos_left (show 6*(p*R)<8 by linarith only [hpr1]) hp
    unfold s6FinalRWD1
    constructor <;> nlinarith only [hsmall,hupper,hp1,hR,hR1]
  have hD2 : s6FinalRWD2 p < 21/10 := by
    unfold s6FinalRWD2
    nlinarith only [hp,hp1]
  have hD0 : 0 < s6FinalRWD p R := by linarith only [hD]
  have hC : 0 < s6FinalRWC p R ∧ s6FinalRWC p R < 3/8 := by
    unfold s6FinalRWC
    constructor
    · positivity
    · rw [div_lt_iff₀ hD0]; linarith only [hD]
  have hC1 : s6FinalRWC1 p R < 0 := by
    unfold s6FinalRWC1
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hD1.1) (sq_pos_of_pos hD0)
  exact ⟨hA.1,hA.2,hB.1,hB.2,hB1.1,hB1.2,hD,hD1.1,hD1.2,hD2,hC.1,hC.2,hC1⟩

private theorem s6_final_rw_derivatives {p R : ℝ} (hR : R ≠ 0) (hD : s6FinalRWD p R ≠ 0) :
    HasDerivAt (s6FinalRW p) (s6FinalRW1 p R) R ∧
    HasDerivAt (s6FinalRW1 p) (s6FinalRW2 p R) R := by
  have hid := hasDerivAt_id R
  have hA : HasDerivAt s6FinalRWA (-2*R) R := by
    convert (hasDerivAt_pow 2 R).const_sub 1 using 1
    · ext x; rfl
    · ring
  have hA1 := hid.const_mul (-2)
  have hB : HasDerivAt (s6FinalRWB p) (s6FinalRWB1 p R) R := by
    have hh := ((hid.add ((hasDerivAt_const R (1:ℝ)).div hid hR)).const_mul p).const_sub 2
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRWB1,id]
      field_simp
      ring
  have hB1 : HasDerivAt (s6FinalRWB1 p) (s6FinalRWB2 p R) R := by
    have hh := (((hasDerivAt_const R (1:ℝ)).div (hasDerivAt_pow 2 R) (pow_ne_zero 2 hR)).sub_const 1).const_mul p
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRWB2]
      field_simp
      ring
  have hD1 : HasDerivAt (s6FinalRWD p) (s6FinalRWD1 p R) R := by
    have hh := ((((hid.const_mul p).const_sub 1).pow 2).const_mul 3).add ((hid.sub_const p).pow 2)
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRWD1,id]
      ring
  have hD2 : HasDerivAt (s6FinalRWD1 p) (s6FinalRWD2 p) R := by
    have hh := ((((hid.const_mul p).const_sub 1).const_mul (-6*p)).add ((hid.sub_const p).const_mul 2))
    convert hh using 1
    · ext x; simp only [s6FinalRWD1,id,Pi.add_apply]
    · simp only [s6FinalRWD2]
      ring
  have hC : HasDerivAt (s6FinalRWC p) (s6FinalRWC1 p R) R := by
    have hh := (hasDerivAt_const R (1:ℝ)).div hD1 hD
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRWC1]
      ring
  have hC1 : HasDerivAt (s6FinalRWC1 p) (s6FinalRWC2 p R) R := by
    have hh := hD2.neg.div (hD1.pow 2) (pow_ne_zero 2 hD)
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRWC2,Pi.pow_apply,Pi.neg_apply]
      field_simp
      ring
  constructor
  · have hh := ((hA.mul hB).mul hC).const_mul p
    convert hh using 1
    · ext x; simp only [s6FinalRW,Pi.mul_apply]; ring
    · simp only [s6FinalRW1,Pi.mul_apply]
  · have hfirst := ((hA1.mul hB).add (hA.mul hB1)).mul hC
    have hh := ((hfirst.add ((hA.mul hB).mul hC1)).const_mul p)
    convert hh using 1
    · ext x; simp only [s6FinalRW1,Pi.mul_apply,Pi.add_apply,id]
    · simp only [s6FinalRW2,Pi.mul_apply,Pi.add_apply,id]
      ring

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

private theorem s6_final_rw_bounds {p R : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1/21) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalRW p R ∧ s6FinalRW p R < 1/30 ∧
    s6FinalRW1 p R < 0 ∧ -(1/5:ℝ) < s6FinalRW2 p R := by
  have hR0 : 0 < R := by linarith only [hR]
  have hR8 : R ≤ 3/8 := by linarith only [hR1]
  rcases s6_final_rw_kernel_bounds hp hp1 hR hR1 with
    ⟨hA,hAu,hB,hBu,hB1,hB1u,hD,hD1,hD1u,hD2,hC,hCu,hC1⟩
  have hD0 : 0 < s6FinalRWD p R := by linarith only [hD]
  have hB0 : 0 < s6FinalRWB p R := by linarith only [hB]
  have hWp : 0 < s6FinalRW p R := by unfold s6FinalRW; positivity
  have hWu : s6FinalRW p R < 1/30 := by
    have hh : p*s6FinalRWA R*s6FinalRWB p R*s6FinalRWC p R ≤
        (1/21)*(8/9)*2*(3/8) := by gcongr
    unfold s6FinalRW
    linarith only [hh]
  have hW1 : s6FinalRW1 p R < 0 := by
    have hn1 : -2*R*s6FinalRWB p R < -(7/6:ℝ) := by
      have hh : (1/3)*(7/4)<R*s6FinalRWB p R := by
        calc
          _ < (1/3)*s6FinalRWB p R := mul_lt_mul_of_pos_left hB (by norm_num)
          _ ≤ _ := mul_le_mul_of_nonneg_right hR hB0.le
      linarith only [hh]
    have hn2 : s6FinalRWA R*s6FinalRWB1 p R ≤ 3/7 := by
      have hh : s6FinalRWA R*s6FinalRWB1 p R ≤ (8/9)*(3/7) := by gcongr
      linarith only [hh]
    have hn : -2*R*s6FinalRWB p R+s6FinalRWA R*s6FinalRWB1 p R < 0 := by
      linarith only [hn1,hn2]
    have hh1 := mul_neg_of_neg_of_pos hn hC
    have hh2 := mul_neg_of_pos_of_neg (mul_pos hA hB0) hC1
    unfold s6FinalRW1
    exact mul_neg_of_pos_of_neg hp (by linarith only [hh1,hh2])
  let B := 2*s6FinalRWB p R*s6FinalRWC p R+
    2*p*s6FinalRWA R*s6FinalRWC p R/R^3+
    s6FinalRWA R*s6FinalRWB p R*s6FinalRWD2 p*(s6FinalRWC p R)^2+
    4*R*s6FinalRWB1 p R*s6FinalRWC p R+
    2*s6FinalRWA R*s6FinalRWB1 p R*s6FinalRWD1 p R*(s6FinalRWC p R)^2
  have hterm1 : 2*s6FinalRWB p R*s6FinalRWC p R < 3/2 := by
    calc
      _ < 2*2*(3/8:ℝ) := by gcongr
      _ = 3/2 := by norm_num
  have hterm2 : 2*p*s6FinalRWA R*s6FinalRWC p R/R^3 < 1 := by
    have hh : 2*p*s6FinalRWA R*s6FinalRWC p R/R^3 ≤
      (2*(1/21)*(8/9)*(3/8)/(1/3)^3:ℝ) := by gcongr
    linarith only [hh]
  have hterm3 : s6FinalRWA R*s6FinalRWB p R*s6FinalRWD2 p*(s6FinalRWC p R)^2 < 3/5 := by
    have hD2p : 0 < s6FinalRWD2 p := by unfold s6FinalRWD2; positivity
    have hh : s6FinalRWA R*s6FinalRWB p R*s6FinalRWD2 p*(s6FinalRWC p R)^2 ≤
      (8/9)*2*(21/10)*(3/8:ℝ)^2 := by gcongr
    linarith only [hh]
  have hterm4 : 4*R*s6FinalRWB1 p R*s6FinalRWC p R < 1/4 := by
    have hh : 4*R*s6FinalRWB1 p R*s6FinalRWC p R ≤ (4*(3/8)*(3/7)*(3/8):ℝ) := by gcongr
    linarith only [hh]
  have hterm5 : 2*s6FinalRWA R*s6FinalRWB1 p R*s6FinalRWD1 p R*(s6FinalRWC p R)^2 < 1/10 := by
    have hh : 2*s6FinalRWA R*s6FinalRWB1 p R*s6FinalRWD1 p R*(s6FinalRWC p R)^2 ≤
      (2*(8/9)*(3/7)*(4/5)*(3/8)^2:ℝ) := by gcongr
    linarith only [hh]
  have hBcap : B < 69/20 := by
    dsimp only [B]
    linarith only [hterm1,hterm2,hterm3,hterm4,hterm5]
  have hpB : p*B < 1/5 := by
    have h1 := mul_lt_mul_of_pos_left hBcap hp
    have h2 := mul_le_mul_of_nonneg_right hp1 (show (0:ℝ)≤69/20 by norm_num)
    linarith only [h1,h2]
  have hrem : s6FinalRW2 p R+p*B=
      p*(4*R*s6FinalRWB p R*s6FinalRWD1 p R*(s6FinalRWC p R)^2+
        2*s6FinalRWA R*s6FinalRWB p R*(s6FinalRWD1 p R)^2*(s6FinalRWC p R)^3) := by
    dsimp only [B]
    unfold s6FinalRW2 s6FinalRWB2 s6FinalRWC1 s6FinalRWC2 s6FinalRWC
    field_simp
    ring
  have hremp : 0 ≤ s6FinalRW2 p R+p*B := by rw [hrem]; positivity
  exact ⟨hWp,hWu,hW1,by linarith only [hremp,hpB]⟩

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRF (R : ℝ) : ℝ := (38/49)*(3-R)/(2*(1+R))
noncomputable def s6FinalRF1 (R : ℝ) : ℝ := -76/(49*(1+R)^2)
noncomputable def s6FinalRF2 (R : ℝ) : ℝ := 152/(49*(1+R)^3)
noncomputable def s6FinalRAniso1 (e R : ℝ) : ℝ :=
  let p := s6FinalRP e
  (161/54)/8*(2*s6FinalRW p R*s6FinalRW1 p R*s6FinalRF R+
    (s6FinalRW p R)^2*s6FinalRF1 R)
noncomputable def s6FinalRAniso2 (e R : ℝ) : ℝ :=
  let p := s6FinalRP e
  (161/54)/8*(2*((s6FinalRW1 p R)^2+s6FinalRW p R*s6FinalRW2 p R)*s6FinalRF R+
    4*s6FinalRW p R*s6FinalRW1 p R*s6FinalRF1 R+
    (s6FinalRW p R)^2*s6FinalRF2 R)

private theorem s6_final_rf_derivatives {R : ℝ} (hR : 0 ≤ R) :
    HasDerivAt s6FinalRF (s6FinalRF1 R) R ∧ HasDerivAt s6FinalRF1 (s6FinalRF2 R) R := by
  have hp : 1+R ≠ 0 := ne_of_gt (by positivity)
  have hid := hasDerivAt_id R
  constructor
  · have hh := ((hid.const_sub 3).const_mul (38/49)).div
      ((hid.const_add 1).const_mul 2) (by simpa using mul_ne_zero (show (2:ℝ)≠0 by norm_num) hp)
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRF1,id]
      field_simp
      ring
  · have hh := (hasDerivAt_const R (-76:ℝ)).div
      (((hid.const_add 1).pow 2).const_mul 49) (by simpa using mul_ne_zero (show (49:ℝ)≠0 by norm_num) (pow_ne_zero 2 hp))
    convert hh using 1
    · ext x; rfl
    · simp only [s6FinalRF2,id,Pi.pow_apply]
      field_simp
      ring

private theorem s6_final_rf_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    0 < s6FinalRF R ∧ s6FinalRF R ≤ 38/49 ∧ s6FinalRF1 R < 0 ∧ 0 < s6FinalRF2 R := by
  have hRp : 0 < R := by linarith only [hR]
  have hR3 : 0 < 3-R := by linarith only [hR1]
  refine ⟨by unfold s6FinalRF; positivity,?_,?_,by unfold s6FinalRF2; positivity⟩
  · unfold s6FinalRF
    rw [div_le_iff₀ (by positivity)]
    linarith only [hR]
  · unfold s6FinalRF1
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

private theorem s6_final_raniso_eq {R e : ℝ} (he : 13/5 ≤ e) (he1 : e ≤ 3)
    (hR : 0 < R) (hR1 : R < 1) :
    s6FinalAnisotropyLoss R (1/19) e=(161/54)/8*(s6FinalRW (s6FinalRP e) R)^2*s6FinalRF R := by
  have hp := s6_final_rp_bounds he he1
  have hpr : s6FinalRP e*R < 1 := by nlinarith only [hp.2,hp.1,hR1,hR]
  have hden : 1-s6FinalRP e*R ≠ 0 := by linarith only [hpr]
  have hD : 0 < s6FinalRWD (s6FinalRP e) R := by
    unfold s6FinalRWD
    have hh : 0 < (1-s6FinalRP e*R)^2 := sq_pos_of_ne_zero hden
    positivity
  have hpR : 3-R ≠ 0 := by linarith only [hR1]
  have hpR1 : 1+R ≠ 0 := by positivity
  have hden' : (1-s6FinalRP e*R)^2 ≠ 0 := pow_ne_zero 2 hden
  let p := s6FinalRP e
  have hdenp : 1-p*R ≠ 0 := hden
  have hTnum : R^2-(s6FinalRT p R)^2=
      (R^2*(1-p*R)^2-(R-p)^2)/(1-p*R)^2 := by
    unfold s6FinalRT
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hdenp)).2
    rw [sub_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hdenp)]
  have hTden : 3+(s6FinalRT p R)^2=s6FinalRWD p R/(1-p*R)^2 := by
    unfold s6FinalRT s6FinalRWD
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hdenp)).2
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hdenp)]
  have hfactor : R^2*(1-p*R)^2-(R-p)^2=p*R*s6FinalRWA R*s6FinalRWB p R := by
    unfold s6FinalRWA s6FinalRWB
    field_simp
    ring
  have hnu : (R^2-(s6FinalRT p R)^2)/(3+(s6FinalRT p R)^2)=R*s6FinalRW p R := by
    rw [hTnum,hTden,div_div_div_cancel_right₀ hden',hfactor]
    unfold s6FinalRW s6FinalRWC
    ring
  rw [s6FinalAnisotropyLoss,s6_final_rt_eq he,hnu]
  unfold s6FinalRF costZL
  field_simp
  ring

private theorem s6_final_raniso_derivatives {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    HasDerivAt (fun R => s6FinalAnisotropyLoss R (1/19) e) (s6FinalRAniso1 e R) R ∧
    HasDerivAt (s6FinalRAniso1 e) (s6FinalRAniso2 e R) R := by
  have hp := s6_final_rp_bounds he he1
  have hR0 : 0 < R := by linarith only [hR]
  have hRi : R < 1 := by linarith only [hR1]
  have hD := (s6_final_rw_kernel_bounds hp.1 hp.2 hR hR1).2.2.2.2.2.2.1
  have hw := s6_final_rw_derivatives hR0.ne' (ne_of_gt (by linarith only [hD]))
  have hf := s6_final_rf_derivatives hR0.le
  have heq : (fun R => s6FinalAnisotropyLoss R (1/19) e) =ᶠ[nhds R]
      (fun R => (161/54)/8*(s6FinalRW (s6FinalRP e) R)^2*s6FinalRF R) := by
    filter_upwards [eventually_gt_nhds hR0,eventually_lt_nhds hRi] with z hz hz1
    exact s6_final_raniso_eq he he1 hz hz1
  constructor
  · apply HasDerivAt.congr_of_eventuallyEq _ heq
    have hh := ((hw.1.pow 2).const_mul ((161/54)/8)).mul hf.1
    convert hh using 1
    simp only [s6FinalRAniso1,Pi.pow_apply]
    ring
  · have hh := ((((hw.1.mul hw.2).const_mul 2).mul hf.1).add ((hw.1.pow 2).mul hf.2)).const_mul ((161/54)/8)
    convert hh using 1
    · ext x; simp only [s6FinalRAniso1,Pi.mul_apply,Pi.add_apply,Pi.pow_apply]; ring
    · simp only [s6FinalRAniso2, Pi.mul_apply, Pi.pow_apply]
      ring

private theorem s6_final_raniso_second_lower {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    -(19/4900:ℝ) < s6FinalRAniso2 e R := by
  let p := s6FinalRP e
  have hp := s6_final_rp_bounds he he1
  have hw := s6_final_rw_bounds hp.1 hp.2 hR hR1
  have hf := s6_final_rf_bounds hR hR1
  have hmain1 := mul_lt_mul_of_pos_left hw.2.2.2 hw.1
  have hmain2 := mul_lt_mul_of_neg_left hw.2.1 (by norm_num : (-(1/5:ℝ))<0)
  have hmain : -(1/150:ℝ) < s6FinalRW p R*s6FinalRW2 p R := by
    linarith only [hmain1,hmain2]
  have hmainf := mul_lt_mul_of_pos_right hmain hf.1
  have hmainfu := mul_le_mul_of_nonpos_left hf.2.1 (by norm_num : (-(1/150:ℝ))≤0)
  have hfp := hf.1
  have hf2p := hf.2.2.2
  have hnonneg1 : 0 ≤ 2*(s6FinalRW1 p R)^2*s6FinalRF R := by positivity
  have hnonneg2 : 0 ≤ 4*s6FinalRW p R*s6FinalRW1 p R*s6FinalRF1 R := by
    have hh := mul_nonneg_of_nonpos_of_nonpos hw.2.2.1.le hf.2.2.1.le
    nlinarith only [mul_nonneg hw.1.le hh]
  have hnonneg3 : 0 ≤ (s6FinalRW p R)^2*s6FinalRF2 R := by positivity
  change -(19/4900:ℝ) < (161/54)/8*
    (2*((s6FinalRW1 p R)^2+s6FinalRW p R*s6FinalRW2 p R)*s6FinalRF R+
      4*s6FinalRW p R*s6FinalRW1 p R*s6FinalRF1 R+(s6FinalRW p R)^2*s6FinalRF2 R)
  nlinarith only [hmainf,hmainfu,hnonneg1,hnonneg2,hnonneg3]

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRScore1 (e R : ℝ) : ℝ :=
  s6FinalRPair1 e R-s6FinalRShear1 e R-s6FinalRAniso1 e R
noncomputable def s6FinalRScore2 (e R : ℝ) : ℝ :=
  s6FinalRPair2 e R-s6FinalRShear2 e R-s6FinalRAniso2 e R

private theorem s6_final_rscore_derivatives {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    HasDerivAt (fun R => s6FinalScore R (1/19) e) (s6FinalRScore1 e R) R ∧
    HasDerivAt (s6FinalRScore1 e) (s6FinalRScore2 e R) R := by
  have hp := s6_final_rpair_derivatives he he1 hR hR1
  have hs := s6_final_rshear_derivatives he he1 hR hR1
  have ha := s6_final_raniso_derivatives he he1 hR hR1
  constructor
  · convert (hp.1.sub hs.1).sub ha.1 using 1
    · ext x
      simp only [Pi.sub_apply]
      exact s6_final_score_decomposition x (1/19) e
    · rfl
  · convert (hp.2.sub hs.2).sub ha.2 using 1 <;> rfl

/-- The paper's maximal-displacement score curvature, with the genuine norm floor. -/
theorem s6_final_score_R_curvature {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6FinalRScore2 e R < -(1/1764:ℝ) := by
  have hp := s6_final_rpair_second_upper he he1 hR hR1
  have hs := s6_final_rshear_second_lower he he1 hR hR1
  have ha := s6_final_raniso_second_lower he he1 hR hR1
  unfold s6FinalRScore2
  linarith only [hp,hs,ha]

/-- Concavity in R at delta=1/19. -/
theorem s6_final_score_concave_R {e : ℝ} (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    ConcaveOn ℝ (Icc (1/3) (7/19)) (fun R => s6FinalScore R (1/19) e) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := s6FinalRScore1 e) (f'' := s6FinalRScore2 e) ?_ ?_ ?_ ?_
  · intro R hR
    exact (s6_final_rscore_derivatives he he1 hR.1 hR.2).1.continuousAt.continuousWithinAt
  · intro R hR
    have hRc : R ∈ Icc (1/3:ℝ) (7/19) := interior_subset hR
    exact (s6_final_rscore_derivatives he he1 hRc.1 hRc.2).1.hasDerivWithinAt
  · intro R hR
    have hRc : R ∈ Icc (1/3:ℝ) (7/19) := interior_subset hR
    exact (s6_final_rscore_derivatives he he1 hRc.1 hRc.2).2.hasDerivWithinAt
  · intro R hR
    have hRc : R ∈ Icc (1/3:ℝ) (7/19) := interior_subset hR
    have hc := s6_final_score_R_curvature he he1 hRc.1 hRc.2
    linarith only [hc]

end SmoothedOctagon

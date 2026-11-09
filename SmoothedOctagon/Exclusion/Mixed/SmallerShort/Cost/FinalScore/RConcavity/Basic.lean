module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Basic

/-!
# S6 maximal displacement: shape coordinate and variance

At displacement `1/19`, the shape coordinate is a Möbius transform. The norm
floor is a product of positive kernels. Their derivative bounds are shared by
the three curvature estimates.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRP (e : ℝ) : ℝ := (e-1)/(39+e)
noncomputable def s6FinalRT (p R : ℝ) : ℝ := (R-p)/(1-p*R)
noncomputable def s6FinalRT1 (p R : ℝ) : ℝ := (1-p^2)/(1-p*R)^2
noncomputable def s6FinalRT2 (p R : ℝ) : ℝ := 2*p*(1-p^2)/(1-p*R)^3

theorem s6_final_rp_bounds {e : ℝ} (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    0 < s6FinalRP e ∧ s6FinalRP e ≤ 1/21 := by
  have hp : 0 < 39+e := by linarith
  unfold s6FinalRP
  constructor
  · exact div_pos (by linarith) hp
  · rw [div_le_iff₀ hp]; linarith

theorem s6_final_rt_eq {R e : ℝ} (he : 13/5 ≤ e) :
    costT R (1/19) e=s6FinalRT (s6FinalRP e) R := by
  have hp : 39+e ≠ 0 := by linarith
  unfold costT s6FinalRT s6FinalRP
  field_simp
  ; ring

theorem s6_final_rt_deriv {p R : ℝ} (hden : 1-p*R ≠ 0) :
    HasDerivAt (s6FinalRT p) (s6FinalRT1 p R) R := by
  have hh := ((hasDerivAt_id R).sub_const p).div
    (((hasDerivAt_id R).const_mul p).const_sub 1) hden
  convert hh using 1
  · ext x; simp only [s6FinalRT, id, Pi.div_apply]
  · simp only [s6FinalRT1, id]
    field_simp
    ring

theorem s6_final_rt1_deriv {p R : ℝ} (hden : 1-p*R ≠ 0) :
    HasDerivAt (s6FinalRT1 p) (s6FinalRT2 p R) R := by
  have hh := (hasDerivAt_const R (1-p^2)).div
    ((((hasDerivAt_id R).const_mul p).const_sub 1).pow 2) (pow_ne_zero 2 hden)
  convert hh using 1
  · ext x; simp only [s6FinalRT1, id, Pi.div_apply, Pi.pow_apply]
  · simp only [s6FinalRT2, id, Pi.pow_apply]
    field_simp
    ring

theorem s6_final_rt_bounds {p R : ℝ} (hp : 0 < p) (hp1 : p ≤ 1/21)
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

theorem s6_final_rv_derivatives {R : ℝ} (hR : 0 < R) :
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

theorem s6_final_rv_bounds {R : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
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

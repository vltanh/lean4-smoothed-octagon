module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Basic

/-!
# S6 maximal displacement: anisotropy-loss curvature

Factoring the anisotropy as `p A B C` isolates a positive reciprocal
denominator. Bounds on these factors and the lower shear envelope give the
curvature floor `-19/4900`.
-/

@[expose] public section

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

theorem s6_final_raniso_derivatives {e R : ℝ}
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

theorem s6_final_raniso_second_lower {e R : ℝ}
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

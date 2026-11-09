module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.Defs

/-!
# The maximum-duration endpoint: residues and face slopes
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private noncomputable def jE (x : ℝ) : ℝ := ssE0 x (19/25)
private noncomputable def jV (x : ℝ) : ℝ := x*(x+2)
private noncomputable def jC0 (x be : ℝ) : ℝ := 1+2*x-2*be*x
private noncomputable def jP (x be : ℝ) : ℝ := ((6/25)*be^2+x-1+jE x*jC0 x be)/be
private noncomputable def jQ (x be : ℝ) : ℝ := jP x be+be*(19/25-jE x)
private noncomputable def jQ0 (x be : ℝ) : ℝ := (38/25)*jC0 x be-jE x-2*(x+1)+1
private noncomputable def jD4 (x be : ℝ) : ℝ :=
  (x+1)^2-(x+1)+1+jC0 x be*((19/25)*jC0 x be-jE x-2*(x+1)+1)
private noncomputable def jPoly (x be z : ℝ) : ℝ :=
  (6/25)*z^4+be*(1-2*(19/25)+jE x)*z^3+
    (be^2+x-1+jE x*jC0 x be)*z^2+be*jQ0 x be*z+jD4 x be
private noncomputable def jA (x be : ℝ) : ℝ := jD4 x be/(be*jV x)
private noncomputable def jB (x be : ℝ) : ℝ := -jPoly x be (-be)/(be*(be^2+jV x))
private noncomputable def jL (x be : ℝ) : ℝ := be*(jE x-19/25)-jA x be-jB x be
private noncomputable def jM (x be : ℝ) : ℝ :=
  be^2+x-1+jE x*jC0 x be-(6/25)*jV x-be*(jA x be+jL x be)
private noncomputable def jC1 (x be : ℝ) : ℝ := -jP x be+(15/16)*jA x be
private noncomputable def jC2 (x be : ℝ) : ℝ := jQ x be+(15/16)*jB x be
private noncomputable def jLittleL (x be : ℝ) : ℝ := (15/16)*jL x be
private noncomputable def jLittleM (x be : ℝ) : ℝ := (15/16)*jM x be

private theorem j_raw {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    ssS5J x be al = -(6/25)-jP x be/al+jQ x be/(al+be)+
      (15/16)*jPoly x be al/(al*(al+be)*(al^2+jV x)) := by
  simp only [ssS5J,ssRA,ssA1,ssA2,ssA3,ssDg,ssQc,jP,jQ,jPoly,jQ0,jD4,jC0,jE,jV,ssE0]
  field_simp (disch := positivity)
  ring

private theorem j_poly_division {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    jPoly x be al/(al*(al+be)*(al^2+jV x)) =
      6/25+jA x be/al+jB x be/(al+be)+(jL x be*al+jM x be)/(al^2+jV x) := by
  simp only [jPoly,jA,jB,jL,jM,jQ0,jD4,jC0,jE,jV,ssE0]
  field_simp (disch := positivity)
  ring

private theorem j_resolvents {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    ssS5J x be al = (15/16-1)*(6/25)+jC1 x be/al+jC2 x be/(al+be)+
      (jLittleL x be*al+jLittleM x be)/(al^2+jV x) := by
  rw [j_raw hx hb ha]
  have h := j_poly_division hx hb ha
  have he : (15/16)*jPoly x be al/(al*(al+be)*(al^2+jV x)) =
      (15/16)*(jPoly x be al/(al*(al+be)*(al^2+jV x))) := by ring
  rw [he,h]
  unfold jC1 jC2 jLittleL jLittleM
  ring

local syntax "jderiv" : tactic
macro_rules
| `(tactic| jderiv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> jderiv
  | apply HasDerivAt.sub <;> jderiv
  | apply HasDerivAt.pow <;> jderiv
  | apply HasDerivAt.mul <;> jderiv
  | apply HasDerivAt.div <;> first | jderiv | positivity | assumption
  | apply HasDerivAt.neg <;> jderiv)

private theorem j_resolvent_deriv {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    HasDerivAt (fun al => ssS5J x be al)
      (-jC1 x be/al^2-jC2 x be/(al+be)^2+
        jLittleL x be*(jV x-al^2)/(al^2+jV x)^2-
        2*al*jLittleM x be/(al^2+jV x)^2) al := by
  let f := fun al : ℝ => (15/16-1)*(6/25)+jC1 x be/al+jC2 x be/(al+be)+
    (jLittleL x be*al+jLittleM x be)/(al^2+jV x)
  have hd : HasDerivAt f
      (-jC1 x be/al^2-jC2 x be/(al+be)^2+
        jLittleL x be*(jV x-al^2)/(al^2+jV x)^2-
        2*al*jLittleM x be/(al^2+jV x)^2) al := by
    dsimp [f]
    apply HasDerivAt.congr_deriv
    · unfold jV; jderiv
    · norm_num [npowRec]
      unfold jV
      field_simp (disch := positivity)
      ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with z hz
  exact j_resolvents hx hb hz

private noncomputable def jLoC1 (x : ℝ) : ℝ :=
  -12*x^2/25+261*x/100-319/50+201/(16*(x+2))-3/(16*(x+1))+51/(400*x)
private noncomputable def jLoC2 (x : ℝ) : ℝ :=
  153*x^2/400-221*x/100+761/200-143/(40*(x+1))-51/(400*x)
private noncomputable def jLoL (x : ℝ) : ℝ :=
  9*x^2/80-27*x/80+201/80-201/(16*(x+2))+153/(40*(x+1))
private noncomputable def jLoM (x : ℝ) : ℝ :=
  27*x^3/80-9*x^2/5+141*x/40-63/16+153/(40*(x+1))
private theorem j_lower_models {x : ℝ} (hx : 0 < x) :
    jC1 x x=jLoC1 x ∧ jC2 x x=jLoC2 x ∧ jLittleL x x=jLoL x ∧ jLittleM x x=jLoM x := by
  simp only [jC1,jC2,jLittleL,jLittleM,jP,jQ,jA,jB,jL,jM,jPoly,jQ0,jD4,jC0,jE,jV,ssE0,
    jLoC1,jLoC2,jLoL,jLoM]
  constructor
  · field_simp (disch := positivity); ring
  constructor
  · field_simp (disch := positivity); ring
  constructor <;> field_simp (disch := positivity) <;> ring

private noncomputable def jLoC1D (x : ℝ) : ℝ :=
  -24*x/25+261/100-201/(16*(x+2)^2)+3/(16*(x+1)^2)-51/(400*x^2)
private noncomputable def jLoC2D (x : ℝ) : ℝ :=
  153*x/200-221/100+143/(40*(x+1)^2)+51/(400*x^2)
private noncomputable def jLoLD (x : ℝ) : ℝ :=
  9*x/40-27/80+201/(16*(x+2)^2)-153/(40*(x+1)^2)
private noncomputable def jLoMD (x : ℝ) : ℝ :=
  81*x^2/80-18*x/5+141/40-153/(40*(x+1)^2)
private noncomputable def jLoMDD (x : ℝ) : ℝ :=
  81*x/40-18/5+153/(20*(x+1)^3)

private theorem j_lower_derivatives {x : ℝ} (hx : 0 < x) :
    HasDerivAt jLoC1 (jLoC1D x) x ∧ HasDerivAt jLoC2 (jLoC2D x) x ∧
    HasDerivAt jLoL (jLoLD x) x ∧ HasDerivAt jLoM (jLoMD x) x ∧
    HasDerivAt jLoMD (jLoMDD x) x := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    (dsimp only [jLoC1,jLoC1D,jLoC2,jLoC2D,jLoL,jLoLD,jLoM,jLoMD,jLoMDD];
     apply HasDerivAt.congr_deriv
     · jderiv
     · norm_num [npowRec]; field_simp (disch := positivity); ring)

private theorem j_motion_upper {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hbound : ∀ z ∈ Icc a b, f' z ≤ C) : f b ≤ f a+C*(b-a) := by
  have h := ss_le_of_deriv (f := fun z => C*z-f z) (f' := fun z => C-f' z) hab
    (fun z hz => by
      convert ((hasDerivAt_id' z).const_mul C).sub (hd z hz) using 1; ring)
    (fun z hz => by linarith only [hbound z ⟨hz.1.le,hz.2.le⟩])
  linarith only [h]

private theorem j_motion_lower {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hbound : ∀ z ∈ Icc a b, C ≤ f' z) : f a+C*(b-a) ≤ f b := by
  have h := j_motion_upper (f := fun z => -f z) (f' := fun z => -f' z) (C := -C) hab
    (fun z hz => (hd z hz).neg) (fun z hz => by linarith only [hbound z hz])
  linarith only [h]

private theorem j_lower_derivative_bounds {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    jLoC1D x < 0 ∧ -(3/10) < jLoC2D x ∧ jLoLD x < 3/5 ∧ 0 < jLoMDD x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hU : 0 < x+2 := by positivity
  have hslo : (3:ℝ)^2 ≤ (x+1)^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 2
  have hshi : (x+1)^2 ≤ (19/6:ℝ)^2 := pow_le_pow_left₀ (by positivity) (by linarith only [hx1]) 2
  have hulo : (4:ℝ)^2 ≤ (x+2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 2
  have huhi : (x+2)^2 ≤ (25/6:ℝ)^2 := pow_le_pow_left₀ (by positivity) (by linarith only [hx1]) 2
  have hxhi : x^2 ≤ (13/6:ℝ)^2 := pow_le_pow_left₀ hx0.le hx1 2
  have h201lo : 1809/2500 ≤ 201/(16*(x+2)^2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith only [huhi]
  have h201hi : 201/(16*(x+2)^2) ≤ 201/256 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith only [hulo]
  have h3hi : 3/(16*(x+1)^2) ≤ 1/48 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith only [hslo]
  have h143lo : 1287/3610 ≤ 143/(40*(x+1)^2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith only [hshi]
  have h51lo : 459/16900 ≤ 51/(400*x^2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith only [hxhi]
  have h153lo : 1377/3610 ≤ 153/(40*(x+1)^2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith only [hshi]
  have h51pos : 0 ≤ 51/(400*x^2) := by positivity
  have h153pos : 0 ≤ 153/(20*(x+1)^3) := by positivity
  refine ⟨?_,?_,?_,?_⟩
  · unfold jLoC1D; nlinarith only [h201lo,h3hi,h51pos,hx]
  · unfold jLoC2D; nlinarith only [h143lo,h51lo,hx]
  · unfold jLoLD; nlinarith only [h201hi,h153lo,hx1]
  · unfold jLoMDD; nlinarith only [h153pos,hx]

private theorem j_lower_coefficients {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    1/28 < jC1 x x ∧ -(2/5) < jC2 x x ∧ jLittleL x x < 8/15 ∧ -(1/8) < jLittleM x x := by
  have hx0 : 0 < x := by linarith only [hx]
  obtain ⟨e1,e2,e3,e4⟩ := j_lower_models hx0
  have hC1 := ss_le_of_deriv (f := fun z => -jLoC1 z) (f' := fun z => -jLoC1D z) hx1
    (fun z hz => (j_lower_derivatives (by linarith only [hx,hz.1])).1.neg)
    (fun z hz => by
      have h := (j_lower_derivative_bounds (by linarith only [hx,hz.1]) hz.2.le).1
      linarith only [h])
  have hC2 := j_motion_lower (f := jLoC2) (f' := jLoC2D) (C := -(3/10)) hx
    (fun z hz => (j_lower_derivatives (by linarith only [hz.1])).2.1)
    (fun z hz => (j_lower_derivative_bounds hz.1 (hz.2.trans hx1)).2.1.le)
  have hL := j_motion_upper (f := jLoL) (f' := jLoLD) (C := 3/5) hx
    (fun z hz => (j_lower_derivatives (by linarith only [hz.1])).2.2.1)
    (fun z hz => (j_lower_derivative_bounds hz.1 (hz.2.trans hx1)).2.2.1.le)
  have hM := j_motion_lower (f := jLoM) (f' := jLoMD) (C := -(1/20)) hx
    (fun z hz => (j_lower_derivatives (by linarith only [hz.1])).2.2.2.1)
    (fun z hz => by
      have hm := ss_le_of_deriv (f := jLoMD) (f' := jLoMDD) hz.1
        (fun w hw => (j_lower_derivatives (by linarith only [hw.1])).2.2.2.2)
        (fun w hw => (j_lower_derivative_bounds hw.1.le (hw.2.le.trans (hz.2.trans hx1))).2.2.2.le)
      rw [show jLoMD 2 = -(1/20) by norm_num [jLoMD]] at hm
      exact hm)
  rw [show jLoC1 (13/6) = 269/7410 by norm_num [jLoC1]] at hC1
  rw [show jLoC2 2 = -(817/2400) by norm_num [jLoC2]] at hC2
  rw [show jLoL 2 = 27/64 by norm_num [jLoL]] at hL
  rw [show jLoM 2 = -(9/80) by norm_num [jLoM]] at hM
  rw [e1,e2,e3,e4]
  exact ⟨by linarith only [hC1],by linarith only [hC2,hx1],by linarith only [hL,hx1],by linarith only [hM,hx1]⟩

private theorem j_alpha_kernels {x be al : ℝ} (hx : 2 ≤ x) (hb : x ≤ be)
    (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    36/49 ≤ 1/al^2 ∧ 1/(al+be)^2 ≤ 1/9 ∧
    0 ≤ (jV x-al^2)/(al^2+jV x)^2 ∧ (jV x-al^2)/(al^2+jV x)^2 ≤ 7/81 ∧
    0 ≤ al/(al^2+jV x)^2 ∧ al/(al^2+jV x)^2 ≤ 7/486 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hb0 : 0 < be := by linarith only [hx,hb]
  have ha0 : 0 < al := by linarith only [ha]
  have hV : 8 ≤ jV x := by unfold jV; nlinarith only [hx]
  have hasq : 1 ≤ al^2 := by nlinarith only [ha]
  have hasq1 : al^2 ≤ (7/6:ℝ)^2 := pow_le_pow_left₀ ha0.le ha1 2
  have hN : 9 ≤ al^2+jV x := by linarith only [hasq,hV]
  have hN0 : 0 < al^2+jV x := by linarith only [hN]
  have hN2 : (9:ℝ)^2 ≤ (al^2+jV x)^2 := pow_le_pow_left₀ (by norm_num) hN 2
  have hsum : 0 < al+be := by positivity
  have hsumsq : (3:ℝ)^2 ≤ (al+be)^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [ha,hx,hb]) 2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith only [hasq1]
  · rw [div_le_iff₀ (by positivity)]; nlinarith only [hsumsq]
  · exact div_nonneg (by nlinarith only [hV,hasq1]) (sq_nonneg _)
  · rw [div_le_iff₀ (by positivity)]
    have h1 := mul_nonneg (show 0 ≤ jV x-8 by linarith only [hV])
      (show 0 ≤ 7*(jV x+al^2+9)-81 by linarith only [hN])
    have h2 := mul_nonneg (show 0 ≤ al^2-1 by linarith only [hasq])
      (show 0 ≤ 7*(jV x+al^2+9)+81 by linarith only [hN])
    nlinarith only [h1,h2]
  · positivity
  · rw [div_le_iff₀ (by positivity)]; nlinarith only [hN2,ha1]

private theorem j_alpha_bound_of_coefficients {x be al C1 C2 Lu Mu : ℝ}
    (hx : 2 ≤ x) (hb : x ≤ be) (ha : 1 ≤ al) (ha1 : al ≤ 7/6)
    (hC1 : C1 < jC1 x be) (hC10 : 0 ≤ C1)
    (hC2 : -C2 < jC2 x be) (hC20 : 0 ≤ C2)
    (hL : jLittleL x be < Lu) (hL0 : 0 ≤ Lu)
    (hM : -Mu < jLittleM x be) (hM0 : 0 ≤ Mu) :
    -jC1 x be/al^2-jC2 x be/(al+be)^2+
        jLittleL x be*(jV x-al^2)/(al^2+jV x)^2-
        2*al*jLittleM x be/(al^2+jV x)^2 <
      -C1*(36/49)+C2/9+Lu*(7/81)+2*Mu*(7/486) := by
  have ha0 : 0 < al := by linarith only [ha]
  have hb0 : 0 < be := by linarith only [hx,hb]
  have hx0 : 0 < x := by linarith only [hx]
  have hV0 : 0 < jV x := by unfold jV; positivity
  obtain ⟨hk1,hk2,hk30,hk3,hk40,hk4⟩ := j_alpha_kernels hx hb ha ha1
  have hterm1 : -jC1 x be/al^2 < -C1*(36/49) := by
    have hh := (div_lt_div_iff_of_pos_right (sq_pos_of_pos ha0)).2 (neg_lt_neg hC1)
    have hm := mul_le_mul_of_nonneg_left hk1 hC10
    have he : C1*(1/al^2) = C1/al^2 := by ring
    rw [he] at hm
    simp only [neg_div] at hh ⊢
    linarith only [hh,hm]
  have hterm2 : -jC2 x be/(al+be)^2 < C2/9 := by
    have hh := (div_lt_div_iff_of_pos_right (sq_pos_of_pos (show 0 < al+be by positivity))).2
      (show -jC2 x be < C2 by linarith only [hC2])
    have hm := mul_le_mul_of_nonneg_left hk2 hC20
    have he : C2*(1/(al+be)^2) = C2/(al+be)^2 := by ring
    rw [he] at hm
    linarith only [hh,hm]
  have hterm3 : jLittleL x be*(jV x-al^2)/(al^2+jV x)^2 ≤ Lu*(7/81) := by
    have hm := mul_le_mul_of_nonneg_right hL.le hk30
    have hm2 := mul_le_mul_of_nonneg_left hk3 hL0
    have he : jLittleL x be*((jV x-al^2)/(al^2+jV x)^2) = jLittleL x be*(jV x-al^2)/(al^2+jV x)^2 := by ring
    rw [he] at hm
    exact hm.trans hm2
  have hterm4 : -(2*al*jLittleM x be/(al^2+jV x)^2) ≤ 2*Mu*(7/486) := by
    have hm := mul_le_mul_of_nonneg_right (show -jLittleM x be ≤ Mu by linarith only [hM]) hk40
    have hm2 := mul_le_mul_of_nonneg_left hk4 hM0
    have he : (-jLittleM x be)*(al/(al^2+jV x)^2) = -(al*jLittleM x be/(al^2+jV x)^2) := by ring
    rw [he] at hm
    have he2 : 2*(al*jLittleM x be/(al^2+jV x)^2) = 2*al*jLittleM x be/(al^2+jV x)^2 := by ring
    nlinarith only [hm,hm2,he2]
  simp only [neg_div] at hterm1 hterm2 ⊢
  linarith only [hterm1,hterm2,hterm3,hterm4]

private theorem j_lower_alpha_slope {x al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    ∃ d : ℝ, HasDerivAt (fun al => ssS5J x x al) d al ∧ d < 3/40 := by
  refine ⟨_,j_resolvent_deriv (by linarith only [hx]) (by linarith only [hx]) (by linarith only [ha]),?_⟩
  obtain ⟨h1,h2,h3,h4⟩ := j_lower_coefficients hx hx1
  have hh := j_alpha_bound_of_coefficients hx le_rfl ha ha1
    (lt_trans (by norm_num : (1/36:ℝ) < 1/28) h1) (by norm_num)
    h2 (by norm_num) h3 (by norm_num) h4 (by norm_num)
  norm_num at hh ⊢
  linarith only [hh]

private noncomputable def jChi : ℝ := 20/19
private noncomputable def jDc : ℝ := 1+jChi^2
private noncomputable def jRho : ℝ := jChi+1/jChi
private noncomputable def jZeta : ℝ := jChi-1/jChi
private noncomputable def jTauA (r : ℝ) : ℝ := (3/80)*(3+184/r+140/r^2-24/r^3)
private noncomputable def jTauB (r : ℝ) : ℝ := 3*(r+2)*(3*r-4)*(3-r)/(40*r^3)
private noncomputable def jTau : ℝ := 153/20-(jRho-2)*jTauA jRho-jZeta*jTauB jRho
private noncomputable def jHiA2 : ℝ := (6/25)*(jChi+2)*(1+(1/16)*jChi^2)/jDc
private noncomputable def jHip : ℝ := (jChi+1)^2/(16*jChi)
private noncomputable def jHih : ℝ := 51/(400*jChi)
private noncomputable def jHiAL : ℝ := 9*jChi*(2*jChi-1)/(40*jDc)
private noncomputable def jHiB : ℝ := 3*(4*jChi+1)*(76*jChi-9)/(80*jChi)
private noncomputable def jHiBL : ℝ := -(3*jChi/80)*(44-76/jRho+12/jRho^2+
  jZeta*(7/jRho-12/jRho^2))
private noncomputable def jHiAM : ℝ := 9*jChi*(jChi+2)/(40*jDc)
private noncomputable def jHiBM : ℝ := -(3/40)*(19*jRho+19/2-50/jRho+6/jRho^2+
  jZeta*(19+1/(2*jRho)-6/jRho^2))
private noncomputable def jHiTauM : ℝ := 2*jChi*jTau/jDc

-- The affine terms are fixed by original row values; the exact identities below
-- prove the divisions. No inequality is inferred from these evaluations.
private noncomputable def jHiC2Base (x : ℝ) : ℝ :=
  jHiA2*x^2-jTau/(jDc*x+2)+jHip/(x+1)-jHih/x
private noncomputable def jHiC2Aff (x : ℝ) : ℝ :=
  (jC2 2 (2*jChi)-jHiC2Base 2-(jC2 1 jChi-jHiC2Base 1))*(x-1)+jC2 1 jChi-jHiC2Base 1
private noncomputable def jHiC2 (x : ℝ) : ℝ := jHiC2Base x+jHiC2Aff x
private noncomputable def jHiL (x : ℝ) : ℝ :=
  jHiAL*x^2+jHiBL*x+(jLittleL 1 jChi-jHiAL-jHiBL-jTau/(jDc+2)+jHiB/3)+
    jTau/(jDc*x+2)-jHiB/(x+2)
private noncomputable def jHiMBase (x : ℝ) : ℝ :=
  jHiAM*x^3+jHiBM*x^2+jHiTauM/(jDc*x+2)
private noncomputable def jHiMAff (x : ℝ) : ℝ :=
  (jLittleM 2 (2*jChi)-jHiMBase 2-(jLittleM 1 jChi-jHiMBase 1))*(x-1)+
    jLittleM 1 jChi-jHiMBase 1
private noncomputable def jHiM (x : ℝ) : ℝ := jHiMBase x+jHiMAff x

private theorem j_upper_models {x : ℝ} (hx : 0 < x) :
    jC2 x (jChi*x)=jHiC2 x ∧ jLittleL x (jChi*x)=jHiL x ∧ jLittleM x (jChi*x)=jHiM x := by
  norm_num [jHiC2,jHiC2Base,jHiC2Aff,jHiL,jHiM,jHiMBase,jHiMAff,
    jHiA2,jHip,jHih,jHiAL,jHiBL,jHiAM,jHiBM,jHiTauM,jHiB,
    jTau,jTauA,jTauB,jRho,jZeta,jDc,jChi,jC2,jLittleL,jLittleM,
    jP,jQ,jA,jB,jL,jM,jPoly,jQ0,jD4,jC0,jE,jV,ssE0]
  refine ⟨?_,?_,?_⟩ <;> field_simp (disch := positivity) <;> ring

private theorem j_upper_constants :
    2 < jDc ∧ jDc < 17/8 ∧ jDc < 9/4 ∧
    15/2 < jTau ∧ jTau < 8 ∧ 1/3 < jHiA2 ∧ 0 < jHip ∧ 0 < jHih ∧ jHih < 1/8 ∧
    0 < jHiAL ∧ jHiAL < 1/8 ∧ jHiBL < -(1/3) ∧ 13 < jHiB ∧ jHiB < 53/4 ∧
    1/3 < jHiAM ∧ -(2:ℝ) < jHiBM ∧ 0 < jHiTauM := by
  norm_num [jDc,jTau,jTauA,jTauB,jHiA2,jHip,jHih,jHiAL,jHiBL,jHiAM,jHiBM,jHiTauM,jHiB,jRho,jZeta,jChi]

private noncomputable def jHiC2D (x : ℝ) : ℝ :=
  2*jHiA2*x+(jC2 2 (2*jChi)-jHiC2Base 2-(jC2 1 jChi-jHiC2Base 1))+
    jTau*jDc/(jDc*x+2)^2-jHip/(x+1)^2+jHih/x^2
private noncomputable def jHiC2DD (x : ℝ) : ℝ :=
  2*jHiA2-2*jTau*jDc^2/(jDc*x+2)^3+2*jHip/(x+1)^3-2*jHih/x^3
private noncomputable def jHiLD (x : ℝ) : ℝ :=
  2*jHiAL*x+jHiBL-jTau*jDc/(jDc*x+2)^2+jHiB/(x+2)^2
private noncomputable def jHiMD (x : ℝ) : ℝ :=
  3*jHiAM*x^2+2*jHiBM*x+
    (jLittleM 2 (2*jChi)-jHiMBase 2-(jLittleM 1 jChi-jHiMBase 1))-
    jHiTauM*jDc/(jDc*x+2)^2
private noncomputable def jHiMDD (x : ℝ) : ℝ :=
  6*jHiAM*x+2*jHiBM+2*jHiTauM*jDc^2/(jDc*x+2)^3

private theorem j_upper_derivatives {x : ℝ} (hx : 0 < x) :
    HasDerivAt jHiC2 (jHiC2D x) x ∧ HasDerivAt jHiC2D (jHiC2DD x) x ∧
    HasDerivAt jHiL (jHiLD x) x ∧ HasDerivAt jHiM (jHiMD x) x ∧
    HasDerivAt jHiMD (jHiMDD x) x := by
  have hD : 0 < jDc := by norm_num [jDc,jChi]
  have hden : 0 < jDc*x+2 := by positivity
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    (dsimp only [jHiC2,jHiC2Base,jHiC2Aff,jHiC2D,jHiC2DD,jHiL,jHiLD,jHiM,jHiMBase,jHiMAff,jHiMD,jHiMDD];
     apply HasDerivAt.congr_deriv
     · jderiv
     · norm_num [npowRec]
       simp only [jHiC2Base,jHiMBase,mul_comm]
       field_simp (disch := positivity)
       ring)

private noncomputable def jHiG (x : ℝ) : ℝ := 2*jHiAL*x+jHiB/(x+2)^2
private noncomputable def jHiGD (x : ℝ) : ℝ := 2*jHiAL-2*jHiB/(x+2)^3
private theorem j_HiG_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt jHiG (jHiGD x) x := by
  unfold jHiG jHiGD
  apply HasDerivAt.congr_deriv
  · jderiv
  · norm_num [npowRec]; field_simp (disch := positivity); ring

private theorem j_upper_derivative_bounds {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    0 < jHiC2DD x ∧ jHiLD x < 2/3 ∧ 0 < jHiMDD x := by
  have hx0 : 0 < x := by linarith only [hx]
  rcases j_upper_constants with ⟨hD2,hD17,hD9,hTlo,hThi,hA2,hp,hh0,hh1,hAL0,hAL1,hBL,hBlo,hBhi,hAM,hBM,hTM⟩
  have hD0 : 0 < jDc := by linarith only [hD2]
  have hT0 : 0 < jTau := by linarith only [hTlo]
  have hden : 0 < jDc*x+2 := by positivity
  have hden6 : 6 ≤ jDc*x+2 := by
    have hm := mul_le_mul_of_nonneg_right hD2.le hx0.le
    nlinarith only [hm,hx]
  have hdenHi : jDc*x+2 < 20/3 := by
    have hm := mul_le_mul_of_nonneg_right hD17.le hx0.le
    nlinarith only [hm,hx1]
  have hden3 : (6:ℝ)^3 ≤ (jDc*x+2)^3 := pow_le_pow_left₀ (by norm_num) hden6 3
  have hx3 : (2:ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hx 3
  have hDsq := pow_le_pow_left₀ hD0.le hD9.le 2
  have hnum : 2*jTau*jDc^2 ≤ 81 := by
    have hm := mul_le_mul_of_nonneg_left hDsq hT0.le
    nlinarith only [hm,hThi]
  have hPole1 : 2*jTau*jDc^2/(jDc*x+2)^3 ≤ 3/8 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith only [hnum,hden3]
  have hPole2 : 2*jHih/x^3 ≤ 1/32 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith only [hh1,hx3]
  have hpole : 0 ≤ 2*jHip/(x+1)^3 := by positivity
  have hmpole : 0 < 2*jHiTauM*jDc^2/(jDc*x+2)^3 := by positivity
  have hAMx := mul_pos (show 0 < jHiAM-1/3 by linarith only [hAM]) hx0
  have hGanti : jHiG x ≤ jHiG 2 := by
    have hneg : ∀ z ∈ Icc 2 x, jHiGD z < 0 := by
      intro z hz
      have hz0 : 0 < z := by linarith only [hz.1]
      have hpow : (z+2)^3 ≤ (25/6:ℝ)^3 := pow_le_pow_left₀ (by positivity)
        (by linarith only [hz.2,hx1]) 3
      have hlo : 26/(25/6:ℝ)^3 < 2*jHiB/(z+2)^3 := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith only [hpow,hBlo]
      unfold jHiGD
      nlinarith only [hAL1,hlo]
    have hh := ss_le_of_deriv (f := fun z => -jHiG z) (f' := fun z => -jHiGD z) hx
      (fun z hz => (j_HiG_deriv (by linarith only [hz.1])).neg)
      (fun z hz => by linarith only [hneg z ⟨hz.1.le,hz.2.le⟩])
    linarith only [hh]
  have hG0 : jHiG 2 < 85/64 := by unfold jHiG; norm_num; linarith only [hAL1,hBhi]
  have hTauD : 15 < jTau*jDc := by
    have hm := mul_lt_mul_of_pos_right hTlo hD0
    nlinarith only [hm,hD2]
  have hden2 := pow_le_pow_left₀ hden.le hdenHi.le 2
  have hPoleLo : 27/80 < jTau*jDc/(jDc*x+2)^2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith only [hTauD,hden2]
  refine ⟨?_,?_,?_⟩
  · unfold jHiC2DD; linarith only [hA2,hPole1,hPole2,hpole]
  · have he : jHiLD x = jHiG x+jHiBL-jTau*jDc/(jDc*x+2)^2 := by
      unfold jHiLD jHiG; ring
    rw [he]
    linarith only [hGanti,hG0,hBL,hPoleLo]
  · unfold jHiMDD
    nlinarith only [hAMx,hx,hBM,hmpole]

private theorem j_upper_initial_coefficients :
    -(5/9) < jHiC2 2 ∧ -(2/5) < jHiC2D 2 ∧
    jHiL 2 < 5/9 ∧ -(1/3) < jHiM 2 ∧ -(3/8) < jHiMD 2 := by
  norm_num [jHiC2,jHiC2Base,jHiC2Aff,jHiC2D,jHiL,jHiM,jHiMBase,jHiMAff,jHiMD,
    jHiA2,jHip,jHih,jHiAL,jHiBL,jHiAM,jHiBM,jHiTauM,jHiB,
    jTau,jTauA,jTauB,jRho,jZeta,jDc,jChi,jC2,jLittleL,jLittleM,
    jP,jQ,jA,jB,jL,jM,jPoly,jQ0,jD4,jC0,jE,jV,ssE0]

private theorem j_upper_three_coefficients {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    -(5/8) < jC2 x (jChi*x) ∧ jLittleL x (jChi*x) < 2/3 ∧ -(2/5) < jLittleM x (jChi*x) := by
  have hx0 : 0 < x := by linarith only [hx]
  rcases j_upper_initial_coefficients with ⟨hC0,hCD0,hL0,hM0,hMD0⟩
  have hCD : ∀ z ∈ Icc 2 x, -(2/5) ≤ jHiC2D z := by
    intro z hz
    have hm := ss_le_of_deriv (f := jHiC2D) (f' := jHiC2DD) hz.1
      (fun w hw => (j_upper_derivatives (by linarith only [hw.1])).2.1)
      (fun w hw => (j_upper_derivative_bounds hw.1.le (hw.2.le.trans (hz.2.trans hx1))).1.le)
    linarith only [hm,hCD0]
  have hC := j_motion_lower hx
    (fun z hz => (j_upper_derivatives (by linarith only [hz.1])).1) hCD
  have hL := j_motion_upper (f := jHiL) (f' := jHiLD) (C := 2/3) hx
    (fun z hz => (j_upper_derivatives (by linarith only [hz.1])).2.2.1)
    (fun z hz => (j_upper_derivative_bounds hz.1 (hz.2.trans hx1)).2.1.le)
  have hMD : ∀ z ∈ Icc 2 x, -(3/8) ≤ jHiMD z := by
    intro z hz
    have hm := ss_le_of_deriv (f := jHiMD) (f' := jHiMDD) hz.1
      (fun w hw => (j_upper_derivatives (by linarith only [hw.1])).2.2.2.2)
      (fun w hw => (j_upper_derivative_bounds hw.1.le (hw.2.le.trans (hz.2.trans hx1))).2.2.le)
    linarith only [hm,hMD0]
  have hM := j_motion_lower hx
    (fun z hz => (j_upper_derivatives (by linarith only [hz.1])).2.2.2.1) hMD
  obtain ⟨e1,e2,e3⟩ := j_upper_models hx0
  rw [e1,e2,e3]
  exact ⟨by linarith only [hC,hC0,hx1],by linarith only [hL,hL0,hx1],by linarith only [hM,hM0,hx1]⟩

private noncomputable def jB00 (x : ℝ) : ℝ :=
  x*(x^2*(192*x^2-61)+16*x*(29*x^2-16)+102)/(400*(x+1))
private noncomputable def jR0 (x : ℝ) : ℝ :=
  213/100-939/(160*(x+2))-1/(16*(x+1))+409/(800*x)-51/(400*x^2)
private noncomputable def jR0D (x : ℝ) : ℝ :=
  939/(160*(x+2)^2)+1/(16*(x+1)^2)-409/(800*x^2)+102/(400*x^3)
private theorem j_C1_difference {x be : ℝ} (hx : 0 < x) (hb : 0 < be) :
    jC1 x be-jC1 x x = (be-x)*jR0 x+jB00 x*(be-x)^2/(be*x^2*jV x) := by
  simp only [jC1,jP,jA,jD4,jC0,jE,jV,ssE0,jB00,jR0]
  field_simp (disch := positivity)
  ring
private theorem j_R0_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt jR0 (jR0D x) x := by
  unfold jR0 jR0D
  apply HasDerivAt.congr_deriv
  · jderiv
  · norm_num [npowRec]; field_simp (disch := positivity); ring
private theorem j_R0D_pos {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : 0 < jR0D x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hpow : (x+2)^2 ≤ (25/6:ℝ)^2 := pow_le_pow_left₀ (by positivity)
    (by linarith only [hx1]) 2
  have hpow2 : (2:ℝ)^2 ≤ x^2 := pow_le_pow_left₀ (by norm_num) hx 2
  have h939 : 939/(160*(25/6:ℝ)^2) ≤ 939/(160*(x+2)^2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith only [hpow]
  have h409 : 409/(800*x^2) ≤ 409/3200 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith only [hpow2]
  have hp1 : 0 ≤ 1/(16*(x+1)^2) := by positivity
  have hp2 : 0 ≤ 102/(400*x^3) := by positivity
  unfold jR0D
  nlinarith only [h939,h409,hp1,hp2]
private theorem j_upper_C1 {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : 1/8 < jC1 x (jChi*x) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hchi : 0 < jChi := by norm_num [jChi]
  have hb0 : 0 < jChi*x := mul_pos hchi hx0
  have hpow : (2:ℝ)^2 ≤ x^2 := pow_le_pow_left₀ (by norm_num) hx 2
  have hBpos : 0 < jB00 x := by
    have hp1 : 0 ≤ x^2*(192*x^2-61) := mul_nonneg (sq_nonneg x) (by linarith only [hpow])
    have hp2 : 0 ≤ 16*x*(29*x^2-16) := mul_nonneg (by positivity) (by linarith only [hpow])
    unfold jB00
    exact div_pos (mul_pos hx0 (by linarith only [hp1,hp2])) (by positivity)
  have hRmono := ss_le_of_deriv (f := jR0) (f' := jR0D) hx
    (fun z hz => j_R0_deriv (by linarith only [hz.1]))
    (fun z hz => (j_R0D_pos hz.1.le (hz.2.le.trans hx1)).le)
  rw [show jR0 2 = 8311/9600 by norm_num [jR0]] at hRmono
  have hR : 6/7 < jR0 x := by linarith only [hRmono]
  have hdiff : 2/19 ≤ jChi*x-x := by norm_num [jChi]; linarith only [hx]
  have hmul := mul_le_mul hdiff hR.le (by norm_num : (0:ℝ) ≤ 6/7)
    (show 0 ≤ jChi*x-x by linarith only [hdiff])
  have hrest : 0 ≤ jB00 x*(jChi*x-x)^2/(jChi*x*x^2*jV x) := by
    unfold jV; positivity
  have he := j_C1_difference hx0 hb0
  have hC := (j_lower_coefficients hx hx1).1
  linarith only [he,hmul,hrest,hC]

private theorem j_upper_alpha_slope {x al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    ∃ d : ℝ, HasDerivAt (fun al => ssS5J x (jChi*x) al) d al ∧ d < 3/40 := by
  have hbe : x ≤ jChi*x := by norm_num [jChi]; linarith only [hx]
  refine ⟨_,j_resolvent_deriv (by linarith only [hx]) (by linarith only [hbe,hx]) (by linarith only [ha]),?_⟩
  obtain ⟨h2,h3,h4⟩ := j_upper_three_coefficients hx hx1
  have h1 := j_upper_C1 hx hx1
  have hh := j_alpha_bound_of_coefficients hx hbe ha ha1 h1 (by norm_num)
    h2 (by norm_num) h3 (by norm_num) h4 (by norm_num)
  norm_num at hh ⊢
  linarith only [hh]

private noncomputable def jInitBracket (x : ℝ) : ℝ :=
  (x-2)*(6*x^2-8*x+3)+(38*x^2-26*x-13)/16
private noncomputable def jInitBracketD (x : ℝ) : ℝ :=
  (6*x^2-8*x+3)+(x-2)*(12*x-8)+(76*x-26)/16
private noncomputable def jInitPref (x : ℝ) : ℝ := 2*x*(x-1)/(25*(x+1)^3)
private noncomputable def jInitPrefD (x : ℝ) : ℝ := 2*(3-(x-2)^2)/(25*(x+1)^4)
private noncomputable def jInitScaledPref (x : ℝ) : ℝ := 2*x*(x-1)/(25*(x+1)^2)
private noncomputable def jInitScaledPrefD (x : ℝ) : ℝ := 2*(3*x-1)/(25*(x+1)^3)
private noncomputable def jInitLow (x : ℝ) : ℝ := -jInitPref x*jInitBracket x
private noncomputable def jInitL (x : ℝ) : ℝ :=
  jE x*(2*x-1)-12*(x+1)/25+1+(15/16)/(x+1)^2*
    (-1+12*(x+1)/25+(38/25)*(2*x^2-3*x-1)*(2*x-1)+(2*x-1)*(2*x+1))
private noncomputable def jInitQ (x : ℝ) : ℝ :=
  -(6/25)+(15/16)/(x+1)^2*(6/25+(19/25)*(2*x-1)^2)
private noncomputable def jInitQD (x : ℝ) : ℝ :=
  2*(15/16)*(3*(19/25)*(2*x-1)-6/25)/(x+1)^3
private noncomputable def jInitLD (x : ℝ) : ℝ :=
  -(6/25)*(4*x+3)+3/(x+1)^2+(15/16)*(2+6*(2*x-1))/(x+1)^3+
    (15/16)*(38/25)*(4*x-3)*(2*x-1)/(x+1)^2+
    (15/16)*(-12*(x+1)/25+(76/25)*(2*x^2-3*x-1)*(2-x)+4*(2-x))/(x+1)^3
private noncomputable def jInitUpper (x : ℝ) : ℝ :=
  -jInitScaledPref x*jInitBracket x+(x/19)*jInitL x+(x/19)^2*jInitQ x+(1+jChi*x)/80

private theorem j_initial_identities {x : ℝ} (hx : 0 < x) :
    ssS5J x x 1=jInitLow x ∧
    (1+jChi*x)*(ssS5J x (jChi*x) 1+1/80)=jInitUpper x := by
  have hchi : 0 < jChi := by norm_num [jChi]
  have h1 := j_raw hx hx (by norm_num : (0:ℝ)<1)
  have h2 := j_raw hx (mul_pos hchi hx) (by norm_num : (0:ℝ)<1)
  rw [h1,h2]
  norm_num [jP,jQ,jPoly,jQ0,jD4,jC0,jE,jV,ssE0,jInitLow,jInitPref,jInitBracket,
    jInitUpper,jInitScaledPref,jInitL,jInitQ,jChi]
  constructor <;> field_simp (disch := positivity) <;> ring

private theorem j_initial_derivatives {x : ℝ} (hx : 0 < x) :
    HasDerivAt jInitBracket (jInitBracketD x) x ∧
    HasDerivAt jInitPref (jInitPrefD x) x ∧
    HasDerivAt jInitScaledPref (jInitScaledPrefD x) x ∧
    HasDerivAt jInitL (jInitLD x) x ∧ HasDerivAt jInitQ (jInitQD x) x := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    (dsimp only [jInitBracket,jInitBracketD,jInitPref,jInitPrefD,jInitScaledPref,jInitScaledPrefD,
      jInitL,jInitLD,jInitQ,jInitQD,jE,ssE0];
     apply HasDerivAt.congr_deriv
     · jderiv
     · norm_num [npowRec,jE,ssE0]; field_simp (disch := positivity); ring)

private theorem j_initial_positive_factors {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    151/8 ≤ jInitBracketD x ∧ 0 ≤ jInitPrefD x ∧ 0 ≤ jInitScaledPrefD x ∧
    87/16 ≤ jInitBracket x ∧ 4/675 ≤ jInitPref x ∧ 4/225 ≤ jInitScaledPref x := by
  have hx0 : 0 < x := by linarith only [hx]
  have h1 := mul_nonneg (show 0 ≤ x-2 by linarith only [hx]) (show 0 ≤ 6*x+4 by linarith only [hx])
  have h2 := mul_nonneg (show 0 ≤ x-2 by linarith only [hx]) (show 0 ≤ 12*x-8 by linarith only [hx])
  have hbr : 151/8 ≤ jInitBracketD x := by
    unfold jInitBracketD; nlinarith only [h1,h2,hx]
  have hpref : 0 ≤ jInitPrefD x := by
    unfold jInitPrefD
    apply div_nonneg _ (by positivity)
    have hs := pow_le_pow_left₀ (show 0 ≤ x-2 by linarith only [hx])
      (show x-2 ≤ (1/6:ℝ) by linarith only [hx1]) 2
    nlinarith only [hs]
  have hscaled : 0 ≤ jInitScaledPrefD x := by
    have : 0 ≤ 3*x-1 := by linarith only [hx]
    unfold jInitScaledPrefD; positivity
  have hB := ss_le_of_deriv (f := jInitBracket) (f' := jInitBracketD) hx
    (fun z hz => (j_initial_derivatives (by linarith only [hz.1])).1)
    (fun z hz => by
      have h1 := mul_nonneg (show 0 ≤ z-2 by linarith only [hz.1]) (show 0 ≤ 6*z+4 by linarith only [hz.1])
      have h2 := mul_nonneg (show 0 ≤ z-2 by linarith only [hz.1]) (show 0 ≤ 12*z-8 by linarith only [hz.1])
      unfold jInitBracketD; nlinarith only [h1,h2,hz.1])
  have hP := ss_le_of_deriv (f := jInitPref) (f' := jInitPrefD) hx
    (fun z hz => (j_initial_derivatives (by linarith only [hz.1])).2.1)
    (fun z hz => by
      unfold jInitPrefD
      apply div_nonneg _ (by positivity)
      have hs := pow_le_pow_left₀ (show 0 ≤ z-2 by linarith only [hz.1])
        (show z-2 ≤ (1/6:ℝ) by linarith only [hz.2,hx1]) 2
      nlinarith only [hs])
  have hSP := ss_le_of_deriv (f := jInitScaledPref) (f' := jInitScaledPrefD) hx
    (fun z hz => (j_initial_derivatives (by linarith only [hz.1])).2.2.1)
    (fun z hz => by
      have : 0 ≤ 3*z-1 := by linarith only [hz.1]
      have : 0 < z+1 := by linarith only [hz.1]
      unfold jInitScaledPrefD; positivity)
  rw [show jInitBracket 2 = 87/16 by norm_num [jInitBracket]] at hB
  rw [show jInitPref 2 = 4/675 by norm_num [jInitPref]] at hP
  rw [show jInitScaledPref 2 = 4/225 by norm_num [jInitScaledPref]] at hSP
  exact ⟨hbr,hpref,hscaled,hB,hP,hSP⟩

private theorem j_initial_LQ_bounds {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    jInitLD x < 2 ∧ jInitQ x < 1 ∧ jInitQD x < 1 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hS2 : (3:ℝ)^2 ≤ (x+1)^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 2
  have hS3 : (3:ℝ)^3 ≤ (x+1)^3 := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 3
  have h3 : 3/(x+1)^2 ≤ 1/3 := by rw [div_le_iff₀ (by positivity)]; nlinarith only [hS2]
  have hp := mul_nonneg (show 0 ≤ x-2 by linarith only [hx]) (show 0 ≤ 2*x+1 by linarith only [hx])
  have hH : 0 ≤ 2*x^2-3*x-1 := by nlinarith only [hp]
  have hHm := mul_nonpos_of_nonneg_of_nonpos hH (show 2-x ≤ 0 by linarith only [hx])
  have hneg : (15/16)*(-12*(x+1)/25+(76/25)*(2*x^2-3*x-1)*(2-x)+4*(2-x))/(x+1)^3 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith only [hHm,hx]
  have hfactor := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
    (show 0 ≤ 20*x^2+100*x-64 by nlinarith only [hx])
  have hrat : (15/16)*(2+6*(2*x-1))/(x+1)^3 ≤ 20/27 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hfactor,hx]
  have hprod := mul_nonneg (show 0 ≤ 6-(4*x-3) by linarith only [hx1])
    (show 0 ≤ 2*x-1 by linarith only [hx])
  have hpair : (15/16)*(38/25)*(4*x-3)*(2*x-1)/(x+1)^2 ≤ 16/5 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hprod,sq_nonneg (x-2),hS2]
  have hq : (15/16)/(x+1)^2 ≤ 5/48 := by rw [div_le_iff₀ (by positivity)]; nlinarith only [hS2]
  have hm0 : 0 ≤ 2*x-1 := by linarith only [hx]
  have hmhi : 2*x-1 ≤ 10/3 := by linarith only [hx1]
  have hm2 := pow_le_pow_left₀ hm0 hmhi 2
  have hN0 : 0 ≤ 6/25+(19/25)*(2*x-1)^2 := by positivity
  have hN : 6/25+(19/25)*(2*x-1)^2 ≤ 1/4+80/9 := by nlinarith only [hm2]
  have hmul1 := mul_le_mul_of_nonneg_right hq hN0
  have hmul2 := mul_le_mul_of_nonneg_left hN (by norm_num : (0:ℝ) ≤ 5/48)
  refine ⟨?_,?_,?_⟩
  · unfold jInitLD; nlinarith only [hx,h3,hrat,hpair,hneg]
  · unfold jInitQ
    linarith only [hmul1,hmul2]
  · unfold jInitQD
    rw [div_lt_iff₀ (by positivity)]
    nlinarith only [hmhi,hS3]

private theorem j_initial_L_lt {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : jInitL x < 1 := by
  have h := j_motion_upper (f := jInitL) (f' := jInitLD) (C := 2) hx
    (fun z hz => (j_initial_derivatives (by linarith only [hz.1])).2.2.2.1)
    (fun z hz => (j_initial_LQ_bounds hz.1 (hz.2.trans hx1)).1.le)
  rw [show jInitL 2 = 29/60 by norm_num [jInitL,jE,ssE0]] at h
  linarith only [h,hx1]

private theorem j_initial_lower_gap {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : ssS5J x x 1 < -(1/80) := by
  have hx0 : 0 < x := by linarith only [hx]
  obtain ⟨_,_,_,hB,hP,_⟩ := j_initial_positive_factors hx hx1
  have hmul := mul_le_mul hP hB (by norm_num : (0:ℝ) ≤ 87/16)
    (by linarith only [hP] : 0 ≤ jInitPref x)
  rw [(j_initial_identities hx0).1]
  unfold jInitLow
  nlinarith only [hmul]

private noncomputable def jInitUpperD (x : ℝ) : ℝ :=
  -(jInitScaledPrefD x*jInitBracket x+jInitScaledPref x*jInitBracketD x)+
    (jInitL x+x*jInitLD x)/19+(2*x*jInitQ x+x^2*jInitQD x)/19^2+jChi/80
private theorem j_initial_upper_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt jInitUpper (jInitUpperD x) x := by
  obtain ⟨hB,hP,hSP,hL,hQ⟩ := j_initial_derivatives hx
  have h := (((hSP.mul hB).neg.add (((hasDerivAt_id' x).div_const 19).mul hL)).add
    ((((hasDerivAt_id' x).div_const 19).pow 2).mul hQ)).add
      ((((hasDerivAt_id' x).const_mul jChi).const_add 1).div_const 80)
  convert h using 1
  · funext z
    simp only [jInitUpper,Pi.add_apply,Pi.neg_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  · norm_num [jInitUpperD,npowRec]
    ring

private theorem j_initial_upper_decreases {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    jInitUpperD x < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  obtain ⟨hBD,_,hSPD,hB,_,hSP⟩ := j_initial_positive_factors hx hx1
  have hprod1 := mul_nonneg hSPD (show 0 ≤ jInitBracket x by linarith only [hB])
  have hprod2 := mul_le_mul hSP hBD (by norm_num : (0:ℝ) ≤ 151/8)
    (show 0 ≤ jInitScaledPref x by linarith only [hSP])
  have hneg : -(jInitScaledPrefD x*jInitBracket x+jInitScaledPref x*jInitBracketD x) < -(1/3) := by
    nlinarith only [hprod1,hprod2]
  obtain ⟨hLD,hQ,hQD⟩ := j_initial_LQ_bounds hx hx1
  have hL := j_initial_L_lt hx hx1
  have hmulL := mul_lt_mul_of_pos_left hLD hx0
  have hterm1 : (jInitL x+x*jInitLD x)/19 < 2/7 := by
    rw [div_lt_iff₀ (by norm_num)]; nlinarith only [hL,hmulL,hx1]
  have hmulQ := mul_lt_mul_of_pos_left hQ (show 0 < 2*x by positivity)
  have hmulQD := mul_lt_mul_of_pos_left hQD (sq_pos_of_pos hx0)
  have hx2 := pow_le_pow_left₀ hx0.le hx1 2
  have hterm2 : (2*x*jInitQ x+x^2*jInitQD x)/19^2 < 1/36 := by
    rw [div_lt_iff₀ (by norm_num)]; nlinarith only [hmulQ,hmulQD,hx1,hx2]
  have hchi : jChi/80 < 1/72 := by norm_num [jChi]
  unfold jInitUpperD
  linarith only [hneg,hterm1,hterm2,hchi]

private theorem j_initial_upper_gap {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    ssS5J x (jChi*x) 1 < -(1/80) := by
  have hx0 : 0 < x := by linarith only [hx]
  have h := ss_le_of_deriv (f := fun z => -jInitUpper z) (f' := fun z => -jInitUpperD z) hx
    (fun z hz => (j_initial_upper_deriv (by linarith only [hz.1])).neg)
    (fun z hz => by linarith only [j_initial_upper_decreases hz.1.le (hz.2.le.trans hx1)])
  have h2 : jInitUpper 2 < 0 := by
    norm_num [jInitUpper,jInitScaledPref,jInitBracket,jInitL,jInitQ,jChi,jE,ssE0]
  have he := (j_initial_identities hx0).2
  have hp : 0 < 1+jChi*x := by
    have : 0 < jChi := by norm_num [jChi]
    positivity
  have hneg : (1+jChi*x)*(ssS5J x (jChi*x) 1+1/80) < 0 := by linarith only [h,h2,he]
  have hf : ssS5J x (jChi*x) 1+1/80 < 0 := (mul_neg_iff.mp hneg).resolve_right (by intro h; linarith only [hp,h.1]) |>.2
  linarith only [hf]

private noncomputable def jBetaQ (x al : ℝ) : ℝ := (15/16)*ssQc x al
private noncomputable def jBetaG (x be al : ℝ) : ℝ := ssDg x be al/al^2
private noncomputable def jBetaSlope (x al : ℝ) : ℝ := 2*(al-x)/al^2
private noncomputable def jBetaResidue (x al : ℝ) : ℝ :=
  al*(1-ssA1 x (-al) al (19/25)+jBetaQ x al*ssA2 x (-al) al (19/25))
private noncomputable def jBetaAffine (x al be : ℝ) : ℝ :=
  jE x+(19/25-1+jBetaQ x al)*(1+be/al)+1-jBetaQ x al-
    jBetaQ x al*ssA3 x be al (19/25)+al*jBetaSlope x al*
      (-jE x+jBetaQ x al*((19/25)*(jBetaG x be al+jBetaG x (-al) al)+
        (1-1/al^2)*jE x-(2*x+1)/al^2))

private theorem j_beta_decomposition {x al be : ℝ} (hx : 0 < x) (ha : 0 < al) (hb : 0 < be) :
    ssS5J x be al = jBetaAffine x al be+jBetaResidue x al/(al+be) := by
  simp only [ssS5J,jBetaAffine,jBetaResidue,jBetaQ,jBetaG,jBetaSlope,jE,ssE0,
    ssRA,ssA1,ssA2,ssA3,ssDg,ssQc]
  field_simp (disch := positivity)
  ring

private theorem j_beta_affine_chord {x al b l h : ℝ} (hx : 0 < x) (ha : 0 < al) :
    (h-l)*jBetaAffine x al b = (h-b)*jBetaAffine x al l+(b-l)*jBetaAffine x al h := by
  simp only [jBetaAffine,jBetaQ,jBetaG,jBetaSlope,jE,ssE0,ssA3,ssDg,ssQc]
  field_simp (disch := positivity)
  ring

private theorem j_beta_residue_pos {x al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (ha : 1 ≤ al) (ha1 : al ≤ 7/6) : 0 < jBetaResidue x al := by
  have hx0 : 0 < x := by linarith only [hx]
  have ha0 : 0 < al := by linarith only [ha]
  have hS : 0 < 1+x := by positivity
  have hInv : 1/(1+x) ≤ 1/3 := by
    rw [div_le_iff₀ hS]; linarith only [hx]
  have he : jE x ≤ -(1/3) := by
    unfold jE ssE0
    linarith only [hInv,hx]
  have hal2 := pow_le_pow_left₀ ha0.le ha1 2
  have hprod := mul_nonneg (show 0 ≤ al-1 by linarith only [ha])
    (show 0 ≤ 7/6-al by linarith only [ha1])
  have hstar : 0 < ssDg x (-al) al := by
    have hp := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2+2*al by positivity)
    unfold ssDg
    nlinarith only [hp,hal2,ha]
  have hidentity : al^2*(1-ssA1 x (-al) al (19/25)) =
      -al^2-x+1-ssDg x (-al) al*jE x := by
    simp only [ssA1,jE,ssE0]
    field_simp (disch := positivity)
    ring
  have hmult := mul_le_mul_of_nonneg_left he hstar.le
  have hshape := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
    (show 0 ≤ 2*al-1 by linarith only [ha])
  have hbase : (2-4*al*(al-1))/3 ≤ al^2*(1-ssA1 x (-al) al (19/25)) := by
    simp only [ssDg] at hidentity hmult
    nlinarith only [hidentity,hmult,hshape]
  have hpositive : 0 < 1-ssA1 x (-al) al (19/25) := by
    have : 0 < (2-4*al*(al-1))/3 := by nlinarith only [hal2,hprod,ha]
    nlinarith only [hbase,this,sq_nonneg al]
  have hA2 : 0 < ssA2 x (-al) al (19/25) :=
    ss_A2_pos hx (by linarith only [hx1]) ha (by norm_num) (by norm_num)
  have hq : 0 < jBetaQ x al := by unfold jBetaQ ssQc; positivity
  unfold jBetaResidue
  positivity

private theorem j_pole_chord {al b l h : ℝ} (ha : 0 < al) (hl : 0 < l) (hb : 0 < b) (hh : 0 < h) :
    (h-l)/(al+b) = (h-b)/(al+l)+(b-l)/(al+h)-
      (h-l)*(b-l)*(h-b)/((al+b)*(al+l)*(al+h)) := by
  field_simp (disch := positivity)
  ring

private theorem j_beta_chord {x al be lo hi : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (ha : 1 ≤ al) (ha1 : al ≤ 7/6) (hl : 0 < lo) (hlo : lo ≤ be) (hhi : be ≤ hi)
    (hwidth : lo < hi) :
    (hi-lo)*ssS5J x be al ≤ (hi-be)*ssS5J x lo al+(be-lo)*ssS5J x hi al := by
  have hx0 : 0 < x := by linarith only [hx]
  have ha0 : 0 < al := by linarith only [ha]
  have hb : 0 < be := hl.trans_le hlo
  have hh : 0 < hi := hb.trans_le hhi
  rw [j_beta_decomposition hx0 ha0 hb,j_beta_decomposition hx0 ha0 hl,
    j_beta_decomposition hx0 ha0 hh]
  have haf := j_beta_affine_chord (x := x) (al := al) (b := be) (l := lo) (h := hi) hx0 ha0
  have hrat := j_pole_chord ha0 hl hb hh
  have hrem : 0 ≤ jBetaResidue x al*((hi-lo)*(be-lo)*(hi-be)/((al+be)*(al+lo)*(al+hi))) := by
    apply mul_nonneg (j_beta_residue_pos hx hx1 ha ha1).le
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg (by linarith only [hwidth]) (by linarith only [hlo]))
      (by linarith only [hhi])
  have hdiff :
      (hi-be)*(jBetaAffine x al lo+jBetaResidue x al/(al+lo))+
        (be-lo)*(jBetaAffine x al hi+jBetaResidue x al/(al+hi))-
        (hi-lo)*(jBetaAffine x al be+jBetaResidue x al/(al+be)) =
      jBetaResidue x al*((hi-lo)*(be-lo)*(hi-be)/((al+be)*(al+lo)*(al+hi))) := by
    linear_combination -haf-jBetaResidue x al*hrat
  linarith only [hdiff,hrem]

private theorem j_face_negative {x be al : ℝ} (ha : 1 ≤ al) (ha1 : al ≤ 7/6)
    (hi : ssS5J x be 1 < -(1/80))
    (hslope : ∀ z ∈ Icc 1 al,
      ∃ d : ℝ, HasDerivAt (fun a => ssS5J x be a) d z ∧ d < 3/40) :
    ssS5J x be al < 0 := by
  have hd : ∀ z ∈ Icc 1 al,
      HasDerivAt (fun a => ssS5J x be a) (deriv (fun a => ssS5J x be a) z) z := by
    intro z hz
    obtain ⟨d,hd,_⟩ := hslope z hz
    simpa only [hd.deriv] using hd
  have hb : ∀ z ∈ Icc 1 al, deriv (fun a => ssS5J x be a) z ≤ 3/40 := by
    intro z hz
    obtain ⟨d,hd,hdlt⟩ := hslope z hz
    rw [hd.deriv]
    exact hdlt.le
  have hm := j_motion_upper (f := fun a => ssS5J x be a)
    (f' := fun a => deriv (fun a => ssS5J x be a) a) (C := 3/40) ha hd hb
  linarith only [hi,hm,ha1]

/-- The maximum-duration endpoint of the Gate S5 tangent is negative on the
paper's enlarged rectangular shape domain. -/
theorem ssS5J_neg {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (ha : 1 ≤ al) (ha1 : al ≤ 7/6) (hbe : x ≤ be) (hbe1 : be ≤ 20*x/19) :
    ssS5J x be al < 0 := by
  have hleft : ssS5J x x al < 0 := j_face_negative ha ha1 (j_initial_lower_gap hx hx1)
    (fun z hz => j_lower_alpha_slope hx hx1 hz.1 (hz.2.trans ha1))
  have hright : ssS5J x (jChi*x) al < 0 := j_face_negative ha ha1 (j_initial_upper_gap hx hx1)
    (fun z hz => j_upper_alpha_slope hx hx1 hz.1 (hz.2.trans ha1))
  have hbe1' : be ≤ jChi*x := by dsimp [jChi]; linarith only [hbe1]
  have hwidth : x < jChi*x := by dsimp [jChi]; linarith only [hx]
  have hc := j_beta_chord hx hx1 ha ha1 (by linarith only [hx]) hbe hbe1' hwidth
  have hsum : (jChi*x-be)*ssS5J x x al+(be-x)*ssS5J x (jChi*x) al < 0 := by
    rcases lt_or_eq_of_le hbe with hb | hb
    · have h1 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ jChi*x-be by linarith only [hbe1']) hleft.le
      have h2 := mul_neg_of_pos_of_neg (show 0 < be-x by linarith only [hb]) hright
      linarith only [h1,h2]
    · subst be
      have h1 := mul_neg_of_pos_of_neg (show 0 < jChi*x-x by linarith only [hwidth]) hleft
      simpa only [sub_self,zero_mul,add_zero] using h1
  have hp : 0 < jChi*x-x := by linarith only [hwidth]
  have hprod : (jChi*x-x)*ssS5J x be al < 0 := hc.trans_lt hsum
  exact (mul_neg_iff.mp hprod).resolve_right (by intro h; linarith only [hp,h.1]) |>.2

end SmoothedOctagon

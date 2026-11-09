module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.Defs
public import Mathlib.Analysis.Convex.Deriv

/-!
# Strict inner-shape concavity of the duration tangent
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

def s5V (x : ℝ) : ℝ := x*(x+2)
noncomputable def s5e (x : ℝ) : ℝ := (x+1)*(19/25-1)+1/(x+1)
def s5c (x be : ℝ) : ℝ := 1+2*x-2*be*x
noncomputable def s5D0 (x : ℝ) : ℝ := 19/25+s5e x
noncomputable def s5D1 (x be : ℝ) : ℝ := 2*be*(2*(19/25)+s5e x-1)
noncomputable def s5D2 (x be : ℝ) : ℝ :=
  be^2*(4*(19/25)-1)+2*(19/25)*s5c x be+s5e x*(s5c x be-1)-x-2
noncomputable def s5D3 (x be : ℝ) : ℝ := 2*be*(2*(19/25)*s5c x be-s5e x-2*x-1)
noncomputable def s5D4 (x be : ℝ) : ℝ := x^2+x+1+s5c x be*((19/25)*s5c x be-s5e x-2*x-1)
noncomputable def s5C4 (x : ℝ) : ℝ := -1-s5e x
noncomputable def s5C3 (be : ℝ) : ℝ := 4*be*(19/25)
noncomputable def s5C2u (x be u : ℝ) : ℝ :=
  -(1+2*u+3*((x+1)*(u-1)+1/(x+1)))*s5V x+2*be^2*(4*u-1)+
    2*u*s5c x be-((x+1)*(u-1)+1/(x+1))-(2*x+1)
noncomputable def s5C2 (x be : ℝ) : ℝ := s5C2u x be (19/25)
noncomputable def s5w (x be : ℝ) : ℝ :=
  -((1-19/25-s5e x)*s5V x+2*(19/25)*s5c x be-s5e x-(2*x+1))/s5V x
noncomputable def s5C1 (x be : ℝ) : ℝ := -4*be*s5V x*s5w x be
noncomputable def s5C0 (x be : ℝ) : ℝ :=
  (3+s5e x-2*s5c x be*(19/25+s5e x))*s5V x+2*s5D4 x be
noncomputable def s5L4 (x : ℝ) : ℝ := 15/16*s5C4 x-2*(15/16)*(1-15/16)*s5D0 x
noncomputable def s5L3 (x be : ℝ) : ℝ := 15/16*s5C3 be-2*(15/16)*(1-15/16)*s5D1 x be
noncomputable def s5L2 (x be : ℝ) : ℝ := 15/16*s5C2 x be-2*(15/16)*(1-15/16)*s5D2 x be
noncomputable def s5L1 (x be : ℝ) : ℝ := 15/16*s5C1 x be-2*(15/16)*(1-15/16)*s5D3 x be
noncomputable def s5L0 (x be : ℝ) : ℝ := 15/16*s5C0 x be-2*(15/16)*(1-15/16)*s5D4 x be
noncomputable def s5P (x be al : ℝ) : ℝ :=
 s5L4 x*al^4+s5L3 x be*al^3+s5L2 x be*al^2+s5L1 x be*al+s5L0 x be
noncomputable def s5Rep (x be al : ℝ) : ℝ :=
 s5e x+(19/25-1)+(19/25-1)*be/al+al/(al+be)+s5P x be al/(al^2+s5V x)^2

lemma s5_scale_coefficients {x be al : ℝ} (ha : al ≠ 0) :
    al^2*ssA1 x be al (19/25) = 2*(al^2-1)+(x+1)+ssDg x be al*s5e x ∧
    al^4*ssA2 x be al (19/25) = (al^2-1)^2+(al^2-1)*(x+1)+(x+1)^2+
      (19/25)*(ssDg x be al)^2+ssDg x be al*(al^2-1)*s5e x-ssDg x be al*(2*x+1) ∧
    al^2*ssA3 x be al (19/25) = 2*(19/25)*ssDg x be al+(al^2-1)*s5e x-(2*x+1) := by
  have he : ssE0 x (19/25) = s5e x := by unfold ssE0 s5e; congr 2 <;> ring
  rw [ssA1,ssA2,ssA3,he]
  constructor
  · field_simp [ha]
    ring
  constructor
  · field_simp [ha]
    ring
  · field_simp [ha]
    ring

noncomputable def s5Yn (x be al : ℝ) : ℝ :=
  4*al*(al+be)-2*(2*(al^2-1)+(x+1)+ssDg x be al*s5e x)-al^2-
    (2*(19/25)*ssDg x be al+(al^2-1)*s5e x-(2*x+1))
noncomputable def s5Zn (x be al : ℝ) : ℝ :=
  (al^2-1)^2+(al^2-1)*(x+1)+(x+1)^2+(19/25)*(ssDg x be al)^2+
    ssDg x be al*(al^2-1)*s5e x-ssDg x be al*(2*x+1)-al^2*(al+be)^2

lemma s5_z_numerator (x be al : ℝ) :
    s5Zn x be al = s5D0 x*al^4+s5D1 x be*al^3+s5D2 x be*al^2+s5D3 x be*al+s5D4 x be := by
  unfold s5Zn s5D0 s5D1 s5D2 s5D3 s5D4 ssDg s5c
  ring
lemma s5_c_numerator {x be al : ℝ} (hv : s5V x ≠ 0) :
    s5Yn x be al*(al^2+s5V x)+2*s5Zn x be al =
      s5C4 x*al^4+s5C3 be*al^3+s5C2 x be*al^2+s5C1 x be*al+s5C0 x be := by
  have hc : s5C2 x be = -(1+2*(19/25)+3*s5e x)*s5V x+2*be^2*(4*(19/25)-1)+
      2*(19/25)*s5c x be-s5e x-(2*x+1) := by rfl
  rw [hc]
  unfold s5C1 s5w
  field_simp [hv]
  unfold s5Yn s5Zn s5C4 s5C3 s5C0 s5D4 ssDg s5c s5V
  ring

lemma s5_T_scaled {x be al : ℝ} (ha : al ≠ 0) (hab : al+be ≠ 0) (hn : al^2+s5V x ≠ 0) :
    ssS5T x be al = s5e x+(19/25-1)+(19/25-1)*be/al+al/(al+be)+
      (15/16)*s5Yn x be al/(al^2+s5V x)+2*(15/16)^2*s5Zn x be al/(al^2+s5V x)^2 := by
  obtain ⟨h1,h2,h3⟩ := s5_scale_coefficients (x:=x) (be:=be) ha
  have he : ssE0 x (19/25) = s5e x := by unfold ssE0 s5e; congr 2 <;> ring
  unfold ssS5T
  rw [he]
  unfold ssRA ssQc s5Yn s5Zn
  change _ = _+ (15/16)*_/(al^2+x*(x+2))+2*(15/16)^2*_/(al^2+x*(x+2))^2
  have hn' : x*(x+2)+al^2 ≠ 0 := by dsimp [s5V] at hn; convert hn using 1; ring
  have hn'' : al^2+x*(x+2) ≠ 0 := hn
  have he1 : ssA1 x be al (19/25) = (2*(al^2-1)+(x+1)+ssDg x be al*s5e x)/al^2 := by
    rw [eq_div_iff (pow_ne_zero 2 ha)]; linarith only [h1]
  have he2 : ssA2 x be al (19/25) = ((al^2-1)^2+(al^2-1)*(x+1)+(x+1)^2+
      (19/25)*(ssDg x be al)^2+ssDg x be al*(al^2-1)*s5e x-ssDg x be al*(2*x+1))/al^4 := by
    rw [eq_div_iff (pow_ne_zero 4 ha)]; linarith only [h2]
  have he3 : ssA3 x be al (19/25) = (2*(19/25)*ssDg x be al+(al^2-1)*s5e x-(2*x+1))/al^2 := by
    rw [eq_div_iff (pow_ne_zero 2 ha)]; linarith only [h3]
  rw [he1,he2,he3]
  field_simp [ha,hab,hn',hn'']
  ring

theorem s5_rep_eq {x be al : ℝ} (hx : 0 < x) (ha : 0 < al) (hb : 0 < be) :
    ssS5T x be al = s5Rep x be al := by
  have hv : 0 < s5V x := by dsimp [s5V]; positivity
  have hn : al^2+s5V x ≠ 0 := ne_of_gt (by positivity)
  rw [s5_T_scaled ha.ne' (ne_of_gt (by positivity)) hn]
  unfold s5Rep
  have hz := s5_z_numerator x be al
  have hc := s5_c_numerator (be:=be) (al:=al) hv.ne'
  have hp : s5P x be al = (15/16)*(s5Yn x be al*(al^2+s5V x)+2*s5Zn x be al)-
      2*(15/16)*(1-15/16)*s5Zn x be al := by
    rw [hc,hz]
    unfold s5P s5L4 s5L3 s5L2 s5L1 s5L0
    ring
  rw [hp]
  field_simp [ha.ne',ne_of_gt (add_pos ha hb),hn]
  ring

lemma s5_base_bounds {x be : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    8 ≤ s5V x ∧ s5V x < 19/2 ∧ -1/2 < s5e x ∧ s5e x < -1/3 ∧
    -5 < s5c x be ∧ s5c x be ≤ -3 ∧ 1/4 < 19/25+s5e x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hSlo : 1/(x+1) ≥ 6/19 := by rw [ge_iff_le,le_div_iff₀ hS]; linarith only [hx1]
  have hShi : 1/(x+1) ≤ 1/3 := by rw [div_le_iff₀ hS]; linarith only [hx]
  have hx2 : x^2 ≤ (13/6)^2 := (sq_le_sq₀ hx0.le (by norm_num)).2 hx1
  have hxx : 4 ≤ x^2 := by nlinarith only [sq_nonneg (x-2),hx]
  have hbx : x^2 ≤ be*x := by nlinarith only [mul_nonneg (sub_nonneg.mpr hb) hx0.le]
  have hbx1 : be*x ≤ 20*x^2/19 := by nlinarith only [mul_le_mul_of_nonneg_right hb1 hx0.le]
  dsimp [s5V,s5e,s5c]
  constructor; · nlinarith only [hx,hxx]
  constructor; · nlinarith only [hx1,hx2]
  constructor; · linarith only [hSlo,hx1]
  constructor; · linarith only [hShi,hx]
  constructor; · nlinarith only [hbx1,hx2,hx]
  constructor; · nlinarith only [hbx,hxx,hx]
  linarith only [hSlo,hx1]


lemma s5_D_bounds {x be : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    0 < s5D0 x ∧ 0 < s5D1 x be ∧ 0 < s5D2 x be ∧ s5D2 x be < 3 ∧
    s5D3 x be < 0 ∧ 105/4 < s5D4 x be ∧ s5D4 x be < (s5V x)^2 := by
  obtain ⟨hv,hv1,he,he1,hc,hc1,he2⟩ := s5_base_bounds hx hx1 hb hb1
  have hx0 : 0 < x := by linarith only [hx]
  have hb0 : 0 < be := lt_of_lt_of_le hx0 hb
  have hs : 0 < x+1 := by positivity
  have hsi : 1/(x+1) ≤ 1/3 := by rw [div_le_iff₀ hs]; linarith only [hx]
  have hxq : x^2 < 5 := by nlinarith only [(sq_le_sq₀ hx0.le (by norm_num : (0:ℝ) ≤ 13/6)).2 hx1]
  have hxb : x < 9/4 := by linarith only [hx1]
  have hβ : be < 9*x/8 := by linarith only [hb1,hx0]
  have hd0 : 0 < s5D0 x := by dsimp [s5D0]; linarith only [he]
  have hd1 : 0 < s5D1 x be := by
    unfold s5D1
    exact mul_pos (by positivity) (by linarith only [he])
  have hinc : s5D2 x x ≤ s5D2 x be := by
    have hid : s5D2 x be-s5D2 x x = (be-x)*((4*(19/25)-1)*(be+x)-2*x*(2*(19/25)+s5e x)) := by
      unfold s5D2 s5c; ring
    have hk : 0 < (4*(19/25)-1)*(be+x)-2*x*(2*(19/25)+s5e x) := by
      have := mul_nonneg hx0.le (show 0 ≤ -1/3-s5e x by linarith only [he1])
      nlinarith only [this,hb,hx]
    nlinarith only [hid,mul_nonneg (sub_nonneg.mpr hb) hk.le]
  have hlow : 0 < s5D2 x x := by
    have hid : s5D2 x x = 86/75+(x-2)*((12*x^2-x-13)/25+4/(3*(x+1))) := by
      unfold s5D2 s5e s5c
      field_simp
      ring
    have hp : 0 < 12*x^2-x-13 := by nlinarith only [sq_nonneg (x-2),hx]
    have : 0 ≤ (x-2)*((12*x^2-x-13)/25+4/(3*(x+1))) := by positivity
    linarith only [hid,this]
  have hd2lo : 0 < s5D2 x be := lt_of_lt_of_le hlow hinc
  have hd2hi : s5D2 x be < 3 := by
    have hcneg : s5c x be < 0 := by linarith only [hc1]
    have hce : (2*(19/25)+s5e x)*s5c x be < s5c x be := by
      nlinarith only [mul_pos (show 0 < 2*(19/25)+s5e x-1 by linarith only [he]) (neg_pos.mpr hcneg)]
    have hstep : s5D2 x be < (19/9)*be^2-2*x*be+x-1/2 := by
      unfold s5D2
      have hbeq : 0 < be^2 := sq_pos_of_pos hb0
      dsimp [s5c] at hce ⊢
      nlinarith only [hce,he,hbeq]
    have hfac : (19/9)*be-2*x ≤ (2/9)*x := by linarith only [hb1]
    have hp := mul_le_mul_of_nonneg_right hfac hb0.le
    have hpb := mul_lt_mul_of_pos_left hβ hx0
    nlinarith only [hstep,hp,hpb,hxq,hxb]
  have hd3 : s5D3 x be < 0 := by
    unfold s5D3
    have hn : 2*(19/25)*s5c x be-s5e x-2*x-1 < 0 := by linarith only [hc1,he,hx]
    exact mul_neg_of_pos_of_neg (by positivity) hn
  have hcqlo : 9 ≤ (s5c x be)^2 := by nlinarith only [hc1]
  have hcqhi : (s5c x be)^2 < 25 := by nlinarith only [mul_pos (show 0 < 5+s5c x be by linarith only [hc]) (show 0 < 5-s5c x be by linarith only [hc1])]
  have hecpos : 0 < s5e x*s5c x be := mul_pos_of_neg_of_neg (by linarith only [he1]) (by linarith only [hc1])
  have hechi : s5e x*s5c x be < 5/2 := by
    have hp := mul_neg_of_pos_of_neg (show 0 < s5e x+1/2 by linarith only [he]) (show s5c x be < 0 by linarith only [hc1])
    nlinarith only [hp,hc]
  have hclo : -(2*x+1)*s5c x be ≥ 15 := by
    have hp := mul_nonneg (show 0 ≤ 2*x+1-5 by linarith only [hx]) (show 0 ≤ -s5c x be-3 by linarith only [hc1])
    nlinarith only [hp,hx,hc1]
  have hchi : -(2*x+1)*s5c x be < 30 := by
    have hp := mul_pos (show 0 < 2*x+1 by positivity) (show 0 < s5c x be+5 by linarith only [hc])
    nlinarith only [hp,hx1]
  have hd4lo : 105/4 < s5D4 x be := by
    unfold s5D4
    nlinarith only [hx,sq_nonneg (x-2),hcqlo,hechi,hclo]
  have hd4hi : s5D4 x be < (s5V x)^2 := by
    have hl : s5D4 x be < 60 := by
      unfold s5D4
      nlinarith only [hxq,hx1,hcqhi,hecpos,hchi]
    nlinarith only [hl,hv]
  exact ⟨hd0,hd1,hd2lo,hd2hi,hd3,hd4lo,hd4hi⟩

lemma s5_C2_bounds {x be : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) : |s5C2 x be| < s5V x/2 := by
  obtain ⟨hv,hv1,he,he1,hc,hc1,he2⟩ := s5_base_bounds hx hx1 hb hb1
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 0 < x+1 := by positivity
  have hb0 : 0 < be := lt_of_lt_of_le hx0 hb
  have hb9 : be ≤ 9*x/8 := by linarith only [hb1,hx0]
  have hsi : 1/(x+1) ≤ 1/3 := by rw [div_le_iff₀ hs]; linarith only [hx]
  have hxq : x^2 < 5 := by nlinarith only [(sq_le_sq₀ hx0.le (by norm_num : (0:ℝ) ≤ 13/6)).2 hx1]
  have hlo : -s5V x/2 < s5C2 x be := by
    have hinc : s5C2 x x ≤ s5C2 x be := by
      have hid : s5C2 x be-s5C2 x x = (be-x)*(2*(4*(19/25)-1)*(be+x)-4*(19/25)*x) := by
        unfold s5C2 s5C2u s5c; ring
      have hp := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ 2*(4*(19/25)-1)*(be+x)-4*(19/25)*x by linarith only [hb,hx])
      linarith only [hid,hp]
    have hid : s5C2 x x+s5V x/2 = 4/15+(x-2)*((36*x^2+131*x+46)/50-2/(3*(x+1))) := by
      unfold s5C2 s5C2u s5c s5V
      field_simp
      ring
    have hsmall : 2/(3*(x+1)) ≤ 2/9 := by rw [div_le_iff₀ (by positivity)]; linarith only [hx]
    have hp := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
      (show 0 ≤ (36*x^2+131*x+46)/50-2/(3*(x+1)) by nlinarith only [sq_nonneg x,hx,hsmall])
    linarith only [hinc,hid,hp]
  have hdu : 8*be^2-4*be*x-3*x^3-11*x^2-7*x+1 < 0 := by
    have hprod := mul_nonneg (show 0 ≤ 9*x/8-be by linarith only [hb9])
      (show 0 ≤ 8*(9*x/8+be)-4*x by linarith only [hb,hx])
    have hx3 : 0 ≤ x^3 := by positivity
    nlinarith only [hprod,hx3,sq_nonneg (x-2),hx]
  have hum : s5C2 x be ≤ s5C2u x be (3/4) := by
    have hid : s5C2u x be (3/4)-s5C2 x be =
        (3/4-19/25)*(8*be^2-4*be*x-3*x^3-11*x^2-7*x+1) := by
      unfold s5C2 s5C2u s5V s5c
      ring
    linarith only [hid,hdu]
  have hbm : s5C2u x be (3/4) ≤ s5C2u x (9*x/8) (3/4) := by
    have hid : s5C2u x (9*x/8) (3/4)-s5C2u x be (3/4) =
        (9*x/8-be)*(4*(9*x/8+be)-3*x) := by unfold s5C2u s5c; ring
    have hp := mul_nonneg (show 0 ≤ 9*x/8-be by linarith only [hb9])
      (show 0 ≤ 4*(9*x/8+be)-3*x by linarith only [hb,hx])
    linarith only [hid,hp]
  let e := -(x+1)/4+1/(x+1)
  have helo : -1/2 < e := by
    have hi : 6/19 ≤ 1/(x+1) := by rw [le_div_iff₀ hs]; linarith only [hx1]
    dsimp [e]; linarith only [hi,hx1]
  have hide : s5C2u x (9*x/8) (3/4) = -(5/2+3*e)*s5V x+27/16*x^2+x+1/2-e := by
    unfold s5C2u s5c s5V; dsimp [e]; ring
  have hlast : s5C2u x (9*x/8) (3/4) < -s5V x+27/16*x^2+x+1 := by
    have hp := mul_pos (show 0 < e+1/2 by linarith only [helo]) (show 0 < 3*s5V x+1 by linarith only [hv])
    nlinarith only [hide,hp]
  have hgap : -s5V x+27/16*x^2+x+1 < s5V x/2 := by
    dsimp [s5V]; nlinarith only [hxq,hx]
  exact abs_lt.mpr ⟨by linarith only [hlo],lt_of_le_of_lt hum (lt_of_le_of_lt hbm (hlast.trans hgap))⟩


lemma s5_other_C_bounds {x be : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    s5w x be < 5/8 ∧ (s5V x)^2 < s5C0 x be := by
  obtain ⟨hv,hv1,he,he1,hc,hc1,he2⟩ := s5_base_bounds hx hx1 hb hb1
  obtain ⟨_,_,_,_,_,hd4,_⟩ := s5_D_bounds hx hx1 hb hb1
  have hv0 : 0 < s5V x := by linarith only [hv]
  have hw : s5w x be < 5/8 := by
    have hinc : s5w x be ≤ s5w x (20*x/19) := by
      have hid : (s5w x (20*x/19)-s5w x be)*s5V x = 4*(19/25)*x*(20*x/19-be) := by
        unfold s5w s5c
        field_simp [hv0.ne']
        ring
      have hpos : 0 ≤ 4*(19/25)*x*(20*x/19-be) := by positivity
      nlinarith only [hid,hpos,hv0]
    have hid : s5w x (20*x/19) = 3/5+(x-2)*(-6*x^2+29*x-3)/(25*s5V x) := by
      unfold s5w s5e s5c s5V
      field_simp
      ring
    have hp : -6*x^2+29*x-3 ≤ 32 := by
      have h := mul_nonneg (show 0 ≤ 7-3*x by linarith only [hx1])
        (show 0 ≤ 5-2*x by linarith only [hx1])
      nlinarith only [h]
    have hfac := mul_le_mul_of_nonneg_left hp (show 0 ≤ x-2 by linarith only [hx])
    have hvx : 4*x ≤ s5V x := by dsimp [s5V]; nlinarith only [mul_nonneg (show 0 ≤ x by linarith only [hx]) (show 0 ≤ x-2 by linarith only [hx])]
    have hxx : x-2 ≤ x/13 := by linarith only [hx1]
    have hquot : (x-2)*(-6*x^2+29*x-3)/(25*s5V x) ≤ 8/325 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hfac,hvx,hxx]
    linarith only [hinc,hid,hquot]
  have hp : 0 < (-s5c x be-3)*(19/25+s5e x)+3*(19/25+s5e x-1/4) := by
    have hfirst := mul_nonneg (show 0 ≤ -s5c x be-3 by linarith only [hc1])
      (show 0 ≤ 19/25+s5e x by linarith only [he2])
    linarith only [hfirst,he2]
  have hcoef : 4 < 3+s5e x-2*s5c x be*(19/25+s5e x) := by nlinarith only [hp,he]
  have hC : 4*s5V x+105/2 < s5C0 x be := by
    unfold s5C0
    nlinarith only [mul_pos (sub_pos.mpr hcoef) hv0,hd4]
  have hvprod := mul_pos (show 0 < 19/2-s5V x by linarith only [hv1])
    (show 0 < s5V x+11/2 by linarith only [hv])
  exact ⟨hw,by nlinarith only [hC,hvprod]⟩

lemma s5_L_bounds {x be : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    s5L4 x < -(15/16)/2 ∧ s5L3 x be < 3*be ∧
    15/16*s5C1 x be < s5L1 x be ∧ |s5L2 x be| < 4*s5V x/7 ∧
    7*(s5V x)^2/9 < s5L0 x be := by
  obtain ⟨hv,hv1,he,he1,hc,hc1,he2⟩ := s5_base_bounds hx hx1 hb hb1
  obtain ⟨hd0,hd1,hd2,hd2hi,hd3,hd4,hd4hi⟩ := s5_D_bounds hx hx1 hb hb1
  have hC2 := s5_C2_bounds hx hx1 hb hb1
  obtain ⟨hw,hC0⟩ := s5_other_C_bounds hx hx1 hb hb1
  have hb0 : 0 < be := by linarith only [hx,hb]
  constructor
  · unfold s5L4 s5C4; linarith only [he,hd0]
  constructor
  · unfold s5L3 s5C3; linarith only [hd1,hb0]
  constructor
  · unfold s5L1; linarith only [hd3]
  constructor
  · obtain ⟨hl,hu⟩ := abs_lt.mp hC2
    apply abs_lt.mpr
    unfold s5L2
    constructor <;> linarith only [hl,hu,hd2,hd2hi,hv]
  · unfold s5L0
    nlinarith only [hC0,hd4hi,hv]

noncomputable def s5Phi1 (t : ℝ) := t^2*(3-8*t+t^2)/(1+t)^4
noncomputable def s5Phi2 (t : ℝ) := t^2*(1-t)/(1+t)^4
noncomputable def s5Psi (t : ℝ) := t*|1-8*t+3*t^2|/(1+t)^4
noncomputable def s5Chi (t : ℝ) := t*(1-5*t)/(1+t)^4
noncomputable def s5F (t : ℝ) := 3*s5Phi1 t+(27/2)*s5Phi2 t+s5Psi t/3-(2/3)*s5Chi t

lemma s5_kernel_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 3/17) :
    0 < s5Phi1 t ∧ 0 < s5Phi2 t ∧ 0 ≤ s5Psi t ∧ 0 < s5Chi t ∧ s5F t < 3*t/2 := by
  have hs : 0 < 1+t := by positivity
  have hn : 0 < 3-8*t+t^2 := by nlinarith only [ht1,sq_nonneg t]
  have hphi1 : 0 < s5Phi1 t := by unfold s5Phi1; positivity
  have hphi2 : 0 < s5Phi2 t := by unfold s5Phi2; exact div_pos (mul_pos (sq_pos_of_pos ht) (by linarith only [ht1])) (by positivity)
  have hpsi : 0 ≤ s5Psi t := by unfold s5Psi; positivity
  have hchi : 0 < s5Chi t := by unfold s5Chi; exact div_pos (mul_pos ht (by linarith only [ht1])) (by positivity)
  refine ⟨hphi1,hphi2,hpsi,hchi,?_⟩
  by_cases hsmall : t ≤ 1/7
  · have habs : |1-8*t+3*t^2| ≤ 1-5*t := by
      rw [abs_le]
      constructor
      · nlinarith only [mul_nonneg (show 0 ≤ t by linarith only [ht]) (show 0 ≤ 1/7-t by linarith only [hsmall])]
      · nlinarith only [mul_nonneg ht.le (show 0 ≤ 1-t by linarith only [hsmall])]
    have hpc : s5Psi t ≤ s5Chi t := by
      unfold s5Psi s5Chi
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habs ht.le) (by positivity)
    have hid : 3*t/2-(3*s5Phi1 t+(27/2)*s5Phi2 t) =
        (3/2)*t*((1-11*t/2)^2+3*t^2/4+2*t^3+t^4)/(1+t)^4 := by
      unfold s5Phi1 s5Phi2
      field_simp
      ring
    have hpos : 0 < (3/2)*t*((1-11*t/2)^2+3*t^2/4+2*t^3+t^4)/(1+t)^4 := by positivity
    unfold s5F
    linarith only [hid,hpos,hpc,hchi]
  · have htlo : 1/7 ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have hsgn : 1-8*t+3*t^2 < 0 := by
      have hp := mul_nonneg (show 0 ≤ t-1/7 by linarith only [htlo]) (show 0 ≤ 3/17-t by linarith only [ht1])
      nlinarith only [hp,htlo,ht1]
    have hid : 3*t/2-s5F t =
        t*(5*((1-4*t)*(1-5*t)-t^2)+6*t^3+3*t^4)/(2*(1+t)^4) := by
      unfold s5F s5Phi1 s5Phi2 s5Psi s5Chi
      rw [abs_of_neg hsgn]
      field_simp
      ring
    have hp := mul_nonneg (show 0 ≤ (1-4*t)-5/17 by linarith only [ht1])
      (show 0 ≤ (1-5*t)-2/17 by linarith only [ht1])
    have htq : t^2 ≤ (3/17)^2 := (sq_le_sq₀ ht.le (by norm_num)).2 ht1
    have hpos1 : 0 < (1-4*t)*(1-5*t)-t^2 := by nlinarith only [hp,ht1,htq]
    have hpos : 0 < t*(5*((1-4*t)*(1-5*t)-t^2)+6*t^3+3*t^4)/(2*(1+t)^4) := by positivity
    linarith only [hid,hpos]


lemma s5_ratio_and_t {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    3/7 < al/be ∧ al/be ≤ 7/12 ∧ 0 < al^2/s5V x ∧ al^2/s5V x < 3/17 ∧
    al^2/s5V x/5 < (ssRA al be)^3 := by
  obtain ⟨hv,hv1,_,_,_,_,_⟩ := s5_base_bounds hx hx1 hb hb1
  have hx0 : 0 < x := by linarith only [hx]
  have hb0 : 0 < be := by linarith only [hb,hx]
  have ha0 : 0 < al := by linarith only [ha]
  have hv0 : 0 < s5V x := by linarith only [hv]
  have haloq : 1 ≤ al^2 := by nlinarith only [ha]
  have hahiq : al^2 ≤ (7/6)^2 := (sq_le_sq₀ ha0.le (by norm_num)).2 ha1
  have hratio1 : 3/7 < al/be := by rw [lt_div_iff₀ hb0]; linarith only [hb1,hx1,ha]
  have hratio2 : al/be ≤ 7/12 := by rw [div_le_iff₀ hb0]; linarith only [hb,hx,ha1]
  have ht : 0 < al^2/s5V x := div_pos (sq_pos_of_pos ha0) hv0
  have ht1 : al^2/s5V x < 3/17 := by rw [div_lt_iff₀ hv0]; linarith only [hahiq,hv]
  refine ⟨hratio1,hratio2,ht,ht1,?_⟩
  let v := sqrt (s5V x)
  have hvp : 0 < v := sqrt_pos.2 hv0
  have hvq : v^2 = s5V x := sq_sqrt hv0.le
  let y := al/v
  let b := be/v
  have hylo : 3/10 < y := by
    dsimp [y]; rw [lt_div_iff₀ hvp]
    nlinarith only [hvq,hv1,haloq,ha,hvp]
  have hyhi : y < 1/2 := by
    dsimp [y]; rw [div_lt_iff₀ hvp]
    nlinarith only [hvq,hv,hahiq,ha0,hvp]
  have hbhi : b < 4/5 := by
    have hbeq : be^2 ≤ (20*x/19)^2 := (sq_le_sq₀ hb0.le (by positivity)).2 hb1
    have hfac : 0 < 32/25-((400/361)-(16/25))*x := by linarith only [hx1]
    have hsq : be^2 < (16/25)*s5V x := by
      have hp := mul_pos hx0 hfac
      dsimp [s5V] at hp ⊢
      nlinarith only [hbeq,hp]
    dsimp [b]; rw [div_lt_iff₀ hvp]
    nlinarith only [hsq,hvq,hb0,hvp]
  have hy0 : 0 < y := lt_trans (by norm_num) hylo
  have hbpos : 0 < b := div_pos hb0 hvp
  have hcubic : 0 < 5*y-(y+4/5)^3 := by
    have he1 : 0 < 5*(3/10:ℝ)-(3/10+4/5)^3 := by norm_num
    have he2 : 0 < 5*(1/2:ℝ)-(1/2+4/5)^3 := by norm_num
    have hrem := mul_nonneg (mul_nonneg (show 0 ≤ y-3/10 by linarith only [hylo])
      (show 0 ≤ 1/2-y by linarith only [hyhi])) (show 0 ≤ y+3/10+1/2+12/5 by positivity)
    have hid : 5*y-(y+4/5)^3 =
        ((5*(3/10:ℝ)-(3/10+4/5)^3)*(1/2-y)+
        (5*(1/2:ℝ)-(1/2+4/5)^3)*(y-3/10))/(1/2-3/10)+
        (y-3/10)*(1/2-y)*(y+3/10+1/2+12/5) := by ring
    have hline : 0 < ((5*(3/10:ℝ)-(3/10+4/5)^3)*(1/2-y)+
        (5*(1/2:ℝ)-(1/2+4/5)^3)*(y-3/10))/(1/2-3/10) := by positivity
    linarith only [hid,hline,hrem]
  have hcube : (y+b)^3 < (y+4/5)^3 := by
    exact pow_lt_pow_left₀ (by linarith only [hbhi]) (by positivity) (by norm_num)
  have hmain : (y+b)^3 < 5*y := by linarith only [hcubic,hcube]
  have hrescale : (ssRA al be)^3/(al^2/s5V x) = y/(y+b)^3 := by
    dsimp [ssRA,y,b]
    field_simp [ha0.ne',hvp.ne',ne_of_gt (add_pos ha0 hb0),hv0.ne']
    nlinarith only [hvq]
  have hdiv : 1/5 < y/(y+b)^3 := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hmain]
  rw [← hrescale] at hdiv
  rw [lt_div_iff₀ ht] at hdiv
  linarith only [hdiv]


noncomputable def s5P1 (x be al : ℝ) : ℝ :=
  4*s5L4 x*al^3+3*s5L3 x be*al^2+2*s5L2 x be*al+s5L1 x be
noncomputable def s5P2 (x be al : ℝ) : ℝ :=
  12*s5L4 x*al^2+6*s5L3 x be*al+2*s5L2 x be
noncomputable def s5First (x be al : ℝ) : ℝ :=
  (6/25)*be/al^2+be/(al+be)^2+
    (s5P1 x be al*(al^2+s5V x)-4*al*s5P x be al)/(al^2+s5V x)^3
noncomputable def s5Second (x be al : ℝ) : ℝ :=
  -(12/25)*be/al^3-2*be/(al+be)^3+
    (s5L4 x*(12*s5V x*al^2*(s5V x-al^2))+
     s5L3 x be*(2*al*(3*(s5V x)^2-8*s5V x*al^2+al^4))+
     s5L2 x be*(2*((s5V x)^2-8*s5V x*al^2+3*al^4))+
     s5L1 x be*(12*al*(al^2-s5V x))+
     s5L0 x be*(4*(5*al^2-s5V x)))/(al^2+s5V x)^4

lemma s5_P_deriv (x be al : ℝ) : HasDerivAt (s5P x be) (s5P1 x be al) al := by
  have h := (((((hasDerivAt_pow 4 al).const_mul (s5L4 x)).add
    ((hasDerivAt_pow 3 al).const_mul (s5L3 x be))).add
    ((hasDerivAt_pow 2 al).const_mul (s5L2 x be))).add
    ((hasDerivAt_id al).const_mul (s5L1 x be))).add_const (s5L0 x be)
  convert h using 1
  · rfl
  · dsimp [s5P1]; ring
lemma s5_P1_deriv (x be al : ℝ) : HasDerivAt (s5P1 x be) (s5P2 x be al) al := by
  have h := ((((hasDerivAt_pow 3 al).const_mul (4*s5L4 x)).add
    ((hasDerivAt_pow 2 al).const_mul (3*s5L3 x be))).add
    ((hasDerivAt_id al).const_mul (2*s5L2 x be))).add_const (s5L1 x be)
  convert h using 1
  · rfl
  · dsimp [s5P2]; ring

lemma s5_rep_hasDerivAt {x be al : ℝ} (ha : al ≠ 0) (hab : al+be ≠ 0)
    (hn : al^2+s5V x ≠ 0) : HasDerivAt (s5Rep x be) (s5First x be al) al := by
  have hN := (hasDerivAt_pow 2 al).add_const (s5V x)
  have hX := (((hasDerivAt_const al (s5e x+(19/25-1))).add
    ((hasDerivAt_const al ((19/25-1)*be)).div (hasDerivAt_id al) ha)).add
    ((hasDerivAt_id al).div ((hasDerivAt_id al).add_const be) hab))
  have h := hX.add ((s5_P_deriv x be al).div (hN.pow 2) (pow_ne_zero 2 hn))
  convert h using 1
  · rfl
  · unfold s5First
    dsimp only [Pi.pow_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,pow_one,zero_mul,zero_add,mul_one,one_mul]
    field_simp [ha,hab,hn]
    ring

lemma s5_first_hasDerivAt {x be al : ℝ} (ha : al ≠ 0) (hab : al+be ≠ 0)
    (hn : al^2+s5V x ≠ 0) : HasDerivAt (s5First x be) (s5Second x be al) al := by
  have hN := (hasDerivAt_pow 2 al).add_const (s5V x)
  have hA := (((s5_P1_deriv x be al).mul hN).sub
    ((((hasDerivAt_id al).const_mul 4)).mul (s5_P_deriv x be al)))
  have h1 := (hasDerivAt_const al ((6/25)*be)).div (hasDerivAt_pow 2 al) (pow_ne_zero 2 ha)
  have h2 := (hasDerivAt_const al be).div (((hasDerivAt_id al).add_const be).pow 2) (pow_ne_zero 2 hab)
  have h := (h1.add h2).add (hA.div (hN.pow 3) (pow_ne_zero 3 hn))
  convert h using 1
  · rfl
  · unfold s5Second s5P s5P1 s5P2
    dsimp only [Pi.pow_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,pow_one,zero_mul,zero_add,mul_one,one_mul]
    field_simp [ha,hab,hn]
    ring


noncomputable def s5K2 (t : ℝ) := t*(1-8*t+3*t^2)/(1+t)^4

lemma s5_second_normalized {x be al : ℝ} (ha : 0 < al) (hb : 0 < be) (hv : 0 < s5V x) :
    al^3/(2*be)*s5Second x be al = -6/25-(ssRA al be)^3+
      (s5L3 x be/be)*s5Phi1 (al^2/s5V x)+
      (6*s5L4 x*(al/be)-6*s5L1 x be/(be*s5V x))*s5Phi2 (al^2/s5V x)+
      (s5L2 x be/s5V x)*(al/be)*s5K2 (al^2/s5V x)-
      2*(s5L0 x be/(s5V x)^2)*(al/be)*s5Chi (al^2/s5V x) := by
  have hn : al^2+s5V x ≠ 0 := ne_of_gt (by positivity)
  have hsum : 1+al^2/s5V x = (al^2+s5V x)/s5V x := by field_simp; ring
  unfold s5Second ssRA s5Phi1 s5Phi2 s5K2 s5Chi
  rw [hsum]
  field_simp [ha.ne',hb.ne',hv.ne',hn,ne_of_gt (add_pos ha hb)]
  ring

lemma s5_second_neg {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    s5Second x be al < 0 := by
  obtain ⟨hv,hv1,_,_,_,_,_⟩ := s5_base_bounds hx hx1 hb hb1
  have hv0 : 0 < s5V x := by linarith only [hv]
  have hb0 : 0 < be := by linarith only [hx,hb]
  have ha0 : 0 < al := by linarith only [ha]
  obtain ⟨hL4,hL3,hL1,hL2,hL0⟩ := s5_L_bounds hx hx1 hb hb1
  obtain ⟨hw,_⟩ := s5_other_C_bounds hx hx1 hb hb1
  obtain ⟨hrlo,hrhi,ht,ht1,hcorr⟩ := s5_ratio_and_t hx hx1 hb hb1 ha ha1
  obtain ⟨hp1,hp2,hpsi,hchi,hF⟩ := s5_kernel_bounds ht ht1.le
  have hr0 : 0 < al/be := div_pos ha0 hb0
  have h3 : s5L3 x be/be < 3 := by rw [div_lt_iff₀ hb0]; linarith only [hL3]
  have h3p := mul_lt_mul_of_pos_right h3 hp1
  have h4r : 6*s5L4 x*(al/be) < -135/112 := by
    have h := mul_lt_mul_of_neg_left hrlo (show 6*s5L4 x < 0 by linarith only [hL4])
    nlinarith only [h,hL4]
  have h1 : -6*s5L1 x be/(be*s5V x) < 225/16 := by
    have hwb := mul_lt_mul_of_pos_left hw (show 0 < 4*be*s5V x by positivity)
    unfold s5C1 at hL1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith only [hL1,hwb]
  have h1' : -(6*s5L1 x be/(be*s5V x)) < 225/16 := by
    convert h1 using 1; ring
  have h24 : 6*s5L4 x*(al/be)-6*s5L1 x be/(be*s5V x) < 27/2 := by
    linarith only [h4r,h1']
  have h24p := mul_lt_mul_of_pos_right h24 hp2
  have h2abs : |s5L2 x be/s5V x| ≤ 4/7 := by
    rw [abs_div,abs_of_pos hv0,div_le_iff₀ hv0]
    linarith only [hL2]
  have hrabs : |al/be| ≤ 7/12 := by rw [abs_of_pos hr0]; exact hrhi
  have hkabs : |s5K2 (al^2/s5V x)| = s5Psi (al^2/s5V x) := by
    unfold s5K2 s5Psi
    rw [abs_div,abs_mul,abs_of_pos ht,abs_of_pos (by positivity : 0 < (1+al^2/s5V x)^4)]
  have h2 : (s5L2 x be/s5V x)*(al/be)*s5K2 (al^2/s5V x) ≤ s5Psi (al^2/s5V x)/3 := by
    calc
      _ ≤ |(s5L2 x be/s5V x)*(al/be)*s5K2 (al^2/s5V x)| := le_abs_self _
      _ = |s5L2 x be/s5V x| * |al/be| * s5Psi (al^2/s5V x) := by rw [abs_mul,abs_mul,hkabs]
      _ ≤ (4/7)*(7/12)*s5Psi (al^2/s5V x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h2abs hrabs (abs_nonneg _) (by norm_num)) hpsi
      _ = _ := by ring
  have h0 : 7/9 < s5L0 x be/(s5V x)^2 := by
    rw [lt_div_iff₀ (by positivity)]; linarith only [hL0]
  have h0prod : 1/3 < (s5L0 x be/(s5V x)^2)*(al/be) := by
    have h := mul_pos (show 0 < s5L0 x be/(s5V x)^2-7/9 by linarith only [h0]) hr0
    nlinarith only [h,hrlo]
  have h0p := mul_lt_mul_of_pos_right h0prod hchi
  have hnorm := s5_second_normalized ha0 hb0 hv0
  have hnormneg : al^3/(2*be)*s5Second x be al < 0 := by
    unfold s5F at hF
    nlinarith only [hnorm,h3p,h24p,h2,h0p,hF,hcorr,ht1]
  by_contra hnot
  exact (not_le_of_gt hnormneg) (mul_nonneg (by positivity : 0 ≤ al^3/(2*be)) (le_of_not_gt hnot))


lemma s5_T_hasDerivAt {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    HasDerivAt (ssS5T x be) (s5First x be al) al := by
  have hv : 0 < s5V x := by unfold s5V; positivity
  have heq : ssS5T x be =ᶠ[nhds al] s5Rep x be := by
    filter_upwards [eventually_gt_nhds ha] with z hz
    exact s5_rep_eq hx hz hb
  exact (s5_rep_hasDerivAt ha.ne' (ne_of_gt (add_pos ha hb))
    (ne_of_gt (by positivity : 0 < al^2+s5V x))).congr_of_eventuallyEq heq

lemma s5_rep_deriv2 {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    (deriv^[2] (s5Rep x be)) al = s5Second x be al := by
  have hv : 0 < s5V x := by unfold s5V; positivity
  have heq : deriv (s5Rep x be) =ᶠ[nhds al] s5First x be := by
    filter_upwards [eventually_gt_nhds ha] with z hz
    exact (s5_rep_hasDerivAt hz.ne' (ne_of_gt (add_pos hz hb))
      (ne_of_gt (by positivity : 0 < z^2+s5V x))).deriv
  change deriv (deriv (s5Rep x be)) al = _
  exact ((s5_first_hasDerivAt ha.ne' (ne_of_gt (add_pos ha hb))
    (ne_of_gt (by positivity : 0 < al^2+s5V x))).congr_of_eventuallyEq heq).deriv

/-- The exact fixed-norm duration tangent is strictly concave in alpha on the
    full enlarged rectangle. No equal-secant relation is needed. -/
theorem ssS5T_strictConcaveOn {x be : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    StrictConcaveOn ℝ (Icc 1 (7/6)) (ssS5T x be) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hb0 : 0 < be := by linarith only [hb,hx]
  have hv : 0 < s5V x := by unfold s5V; positivity
  have hf : ContinuousOn (s5Rep x be) (Icc 1 (7/6)) := by
    intro al ha
    have ha0 : 0 < al := by linarith only [ha.1]
    exact (s5_rep_hasDerivAt ha0.ne' (ne_of_gt (add_pos ha0 hb0))
      (ne_of_gt (by positivity : 0 < al^2+s5V x))).continuousAt.continuousWithinAt
  have hconc : StrictConcaveOn ℝ (Icc 1 (7/6)) (s5Rep x be) := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Icc 1 (7/6)) hf
    intro al ha
    rw [s5_rep_deriv2 hx0 hb0 (by linarith only [ha.1])]
    exact s5_second_neg hx hx1 hb hb1 ha.1 ha.2
  apply hconc.congr
  intro al ha
  exact (s5_rep_eq hx0 (by linarith only [ha.1]) hb0).symm

/-- The alpha=1 tangent controls the entire enlarged alpha interval. -/
theorem ssS5T_le_tangent {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    ssS5T x be al ≤ ssS5T x be 1+(al-1)*s5First x be 1 := by
  rcases ha.eq_or_lt with rfl | hal
  · simp
  have hc := (ssS5T_strictConcaveOn hx hx1 hb hb1).concaveOn
  have hd := s5_T_hasDerivAt (by linarith only [hx] : 0 < x)
    (by linarith only [hx,hb] : 0 < be) (by norm_num : (0:ℝ) < 1)
  have h := hc.slope_le_of_hasDerivAt (by norm_num) ⟨ha,ha1⟩ hal hd
  rw [slope_def_field,div_le_iff₀ (by linarith only [hal])] at h
  nlinarith only [h]

end SmoothedOctagon

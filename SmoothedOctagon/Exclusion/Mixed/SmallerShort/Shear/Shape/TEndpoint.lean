module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.Defs

/-!
# The two geometric faces of the inner-shape tangent
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

local syntax "tederiv" : tactic
macro_rules
| `(tactic| tederiv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> tederiv
  | apply HasDerivAt.sub <;> tederiv
  | apply HasDerivAt.pow <;> tederiv
  | apply HasDerivAt.mul <;> tederiv
  | apply HasDerivAt.div <;> first | tederiv | positivity | assumption
  | apply HasDerivAt.neg <;> tederiv)

noncomputable def teE (x : ℝ) : ℝ := -6*(x+1)/25+1/(x+1)
noncomputable def teQ (x : ℝ) : ℝ := (15/16)/(x+1)^2
private noncomputable def teG (x k : ℝ) : ℝ := x+1-k*x*(x-1)
private noncomputable def teA (x k : ℝ) : ℝ :=
  15*k/8+1-15*(3*k+1)/(8*(x+1))+15*k/(4*(x+1)^2)
private noncomputable def teAp (x k : ℝ) : ℝ :=
  15*(3*k+1)/(8*(x+1)^2)-15*k/(2*(x+1)^3)
private noncomputable def teB (x k : ℝ) : ℝ :=
  6*(x+1)/25-57*k/40+(171*k-58)/(40*(x+1))-3*(76*k-25)/(80*(x+1)^2)
private noncomputable def teBp (x k : ℝ) : ℝ :=
  6/25-(171*k-58)/(40*(x+1)^2)+3*(76*k-25)/(40*(x+1)^3)
private noncomputable def teBpp (x k : ℝ) : ℝ :=
  (171*k-58)/(20*(x+1)^3)-9*(76*k-25)/(40*(x+1)^4)
private noncomputable def teC (x k : ℝ) : ℝ :=
  -6/25-1/((x+1)*(1+k*x))+4*teQ x-2*(teQ x)^2*(x+1+(1+k*x))

private theorem te_a_natural {x k : ℝ} (hs : x+1 ≠ 0) :
    teA x k = 1-2*teQ x*teG x k := by
  unfold teA teQ teG
  field_simp
  ring
private theorem te_b_natural {x k : ℝ} (hs : x+1 ≠ 0) :
    teB x k = -teE x-teQ x*(2*x+1-2*(19/25)*teG x k) := by
  unfold teB teE teQ teG
  field_simp
  ring

private noncomputable def teGg (x be al : ℝ) : ℝ := ssDg x be al/al^2
private noncomputable def teQg (x al : ℝ) : ℝ := (15/16)*ssQc x al
private noncomputable def teAg (x be al : ℝ) : ℝ := 1-teQg x al*teGg x be al
private noncomputable def teBg (x be al : ℝ) : ℝ :=
  -teE x-teQg x al*((2*x+1)/al^2-(19/25)*teGg x be al)
private noncomputable def teD0 (x be al : ℝ) : ℝ :=
  (19/25-1)/ssRA al be+ssRA al be-teE x
private noncomputable def teD1 (x be al : ℝ) : ℝ :=
  4*be/al-1+(5-4*(x+1))/al^2-(1-1/al^2)*teE x
private noncomputable def teD2 (x be al : ℝ) : ℝ :=
  (1-1/al^2)^2+(1-1/al^2)*(x+1)/al^2+(x+1)^2/al^4+
    teGg x be al*(1-1/al^2)*teE x-1/(ssRA al be)^2
private noncomputable def teFactor (x be al : ℝ) : ℝ :=
  -2*teAg x be al*teBg x be al+teD0 x be al+
    teQg x al*teD1 x be al+2*(teQg x al)^2*teD2 x be al

private theorem te_original_factor {x be al : ℝ} (hx : 0 < x) (hb : 0 < be) (ha : 0 < al) :
    ssS5T x be al = teFactor x be al := by
  unfold ssS5T teFactor teAg teBg teD0 teD1 teD2 teQg teGg teE
    ssRA ssQc ssA1 ssA2 ssA3 ssDg ssE0
  field_simp (disch := positivity)
  ring

noncomputable def teC1g (x be : ℝ) : ℝ :=
  2*teQ x*(1+be-2*(x+1-be*(x-1))/(x+1)^2)
noncomputable def teE1g (x be : ℝ) : ℝ :=
  2*teQ x*((19/25)*(1+be)+(2*x+1-2*(19/25)*(x+1-be*(x-1)))/(x+1)^2)
noncomputable def teDalpha (x be : ℝ) : ℝ :=
  6*be/25+be/(1+be)^2+
    2*teQ x*(1-1/(x+1)^2)*(4*(be-x))+
    teQ x*(-4*be+8*(x+1)-10-2*teE x)+
    8*(teQ x)^2*(1-1/(x+1)^2)*((x+1)^2-(1+be)^2)+
    2*(teQ x)^2*(2*(x+1)-4*(x+1)^2+
      4*(x+1-be*(x-1))*teE x+2*(1+be)*be)
noncomputable def ssS5Ta (x be : ℝ) : ℝ :=
  2*teC1g x be*(-teE x-teQ x*(2*x+1-2*(19/25)*(x+1-be*(x-1))))-
    2*(1-2*teQ x*(x+1-be*(x-1)))*teE1g x be+teDalpha x be

theorem te_original_alpha_deriv {x be : ℝ} (hx : 0 < x) (hb : 0 < be) :
    HasDerivAt (fun al => ssS5T x be al) (ssS5Ta x be) 1 := by
  have hs : 0 < x+1 := by positivity
  have hN : 0 < 1+x*(x+2) := by positivity
  have hB : 0 < 1+be := by positivity
  have hd : HasDerivAt (fun al => teFactor x be al) (ssS5Ta x be) 1 := by
    unfold teFactor teAg teBg teD0 teD1 teD2 teQg teGg teE ssRA ssQc ssDg
    apply HasDerivAt.congr_deriv
    · tederiv
    · norm_num [npowRec]
      unfold ssS5Ta teC1g teE1g teDalpha teQ teE
      field_simp (disch := positivity)
      ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ)<1)] with al ha
  exact te_original_factor hx hb ha

private theorem te_endpoint_factor {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    ssS5T x (k*x) 1 = -2*teA x k*teB x k+(k-1)*x*teC x k := by
  rw [te_original_factor hx (by positivity) (by norm_num)]
  unfold teFactor teAg teBg teD0 teD1 teD2 teQg teGg teC teQ teE ssRA ssQc ssDg
  rw [te_a_natural (by positivity),te_b_natural (by positivity)]
  unfold teQ teG teE
  field_simp (disch := positivity)
  ring

private theorem te_a_deriv {x k : ℝ} (hs : 0 < x+1) :
    HasDerivAt (fun x => teA x k) (teAp x k) x := by
  unfold teA teAp
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring
private theorem te_b_deriv {x k : ℝ} (hs : 0 < x+1) :
    HasDerivAt (fun x => teB x k) (teBp x k) x := by
  unfold teB teBp
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring
private theorem te_bp_deriv {x k : ℝ} (hs : 0 < x+1) :
    HasDerivAt (fun x => teBp x k) (teBpp x k) x := by
  unfold teBp teBpp
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring

private theorem te_bpp_pos {x k : ℝ} (hx : 2 ≤ x) (hk : 1 ≤ k) : 0 < teBpp x k := by
  have hs : 0 < x+1 := by linarith
  have he : teBpp x k = 2*((153/80)*(2*x-1)-(x+1)+(171/40)*(k-1)*(x-1))/(x+1)^4 := by
    unfold teBpp
    field_simp
    ring
  rw [he]
  apply div_pos _ (by positivity)
  have hm : 0 ≤ (k-1)*(x-1) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [hx,hm]

private theorem te_ap_half {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) (hk : 1 ≤ k) :
    1/2 < teAp x k := by
  have hs : 0 < x+1 := by linarith
  have hlow : 0 < 15*x-(x+1)^3 := by
    have hm := ss_le_of_deriv (f := fun z : ℝ => -(15*z-(z+1)^3))
      (f' := fun z => 3*(z+1)^2-15) hx1
      (fun z hz => by
        apply HasDerivAt.congr_deriv
        · tederiv
        · ring)
      (fun z hz => by
        have hz0 : 2 ≤ z := hx.trans hz.1.le
        nlinarith [sq_nonneg (z-2)])
    norm_num at hm
    linarith only [hm]
  have he : teAp x k = (15/8)*((x+1)+k*(3*x-1))/(x+1)^3 := by
    unfold teAp
    field_simp
    ring
  rw [he,lt_div_iff₀ (by positivity)]
  have hm := mul_nonneg (show 0 ≤ k-1 by linarith) (show 0 ≤ 3*x-1 by linarith)
  nlinarith only [hlow,hm]

private theorem te_bp_mono {x y k : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hk : 1 ≤ k) :
    teBp x k ≤ teBp y k := by
  exact ss_le_of_deriv hxy
    (fun z hz => te_bp_deriv (by linarith [hz.1]))
    (fun z hz => (te_bpp_pos (hx.trans hz.1.le) hk).le)

private theorem te_bp_k_antitone {x k l : ℝ} (hx : 2 ≤ x) (hkl : k ≤ l) :
    teBp x l ≤ teBp x k := by
  have hs : 0 < x+1 := by linarith
  have hgap : 0 ≤ l-k := by linarith
  have hnum : 0 < 3*(x+1)-4 := by linarith
  have he : teBp x k-teBp x l = (57/40)*(l-k)*(3*(x+1)-4)/(x+1)^3 := by
    unfold teBp
    field_simp
    ring
  have hn : 0 ≤ (57/40)*(l-k)*(3*(x+1)-4)/(x+1)^3 := by positivity
  linarith only [he,hn]

private theorem te_bp_bounds {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : 4/75 < teBp x k ∧ teBp x k < 1/12 := by
  have hlo := te_bp_mono (x := 2) (by norm_num) hx hk
  have hi : 97/1800 ≤ teBp 2 k := by norm_num [teBp]; linarith only [hk1]
  have hhi := te_bp_mono hx hx1 hk
  have hi1 : teBp (13/6) k ≤ teBp (13/6) 1 := te_bp_k_antitone (by norm_num) hk
  have hi2 : teBp (13/6) 1 < 1/12 := by norm_num [teBp]
  constructor <;> linarith only [hlo,hi,hhi,hi1,hi2]

private theorem te_b_lower {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : 3/400 ≤ teB x k := by
  have hm := ss_le_of_deriv (f := fun z => teB z k) (f' := fun z => teBp z k) hx
    (fun z hz => te_b_deriv (by linarith [hz.1]))
    (fun z hz => (le_trans (by norm_num : (0:ℝ) ≤ 4/75)
      (te_bp_bounds hz.1.le (hz.2.le.trans hx1) hk hk1).1.le))
  have hi : 3/400 ≤ teB 2 k := by norm_num [teB]; linarith only [hk1]
  exact hi.trans hm

private theorem te_g_bounds {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : 1/2 < teG x k ∧ teG x k ≤ 1 := by
  have he : teG x k-teG (13/6) (20/19) =
      (13/6-x)*((20/19)*(13/6+x-1)-1)+(20/19-k)*x*(x-1) := by unfold teG; ring
  have hm1 : 0 ≤ (13/6-x)*((20/19)*(13/6+x-1)-1) :=
    mul_nonneg (by linarith) (by linarith)
  have hx0 : 0 ≤ x := by linarith
  have hxm : 0 ≤ x-1 := by linarith
  have hkm : 0 ≤ 20/19-k := by linarith
  have hk0 : 0 ≤ k-1 := by linarith
  have hx2 : 0 ≤ x-2 := by linarith
  have hm2 : 0 ≤ (20/19-k)*x*(x-1) := by positivity
  have hlo : 1/2 < teG (13/6) (20/19) := by norm_num [teG]
  have he1 : 1-teG x k = (k-1)*x*(x-1)+x*(x-2) := by unfold teG; ring
  have hm3 : 0 ≤ (k-1)*x*(x-1) := by positivity
  have hm4 : 0 ≤ x*(x-2) := by positivity
  constructor <;> linarith only [he,hm1,hm2,hlo,he1,hm3,hm4]

private theorem te_a_bounds {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : 19/24 ≤ teA x k ∧ teA x k < 11/12 := by
  have hs : 0 < x+1 := by linarith
  have hm := ss_le_of_deriv (f := fun z => teA z k) (f' := fun z => teAp z k) hx
    (fun z hz => te_a_deriv (by linarith [hz.1]))
    (fun z hz => le_trans (by norm_num : (0:ℝ) ≤ 1/2)
      (te_ap_half hz.1.le (hz.2.le.trans hx1) hk).le)
  have hi : 19/24 ≤ teA 2 k := by norm_num [teA]; linarith only [hk]
  have hg := (te_g_bounds hx hx1 hk hk1).1
  have hs2 : (x+1)^2 < 11 := by nlinarith [sq_nonneg (x-2)]
  have hd : (1/12:ℝ) < (15/8)*teG x k/(x+1)^2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith only [hg,hs2]
  constructor
  · exact hi.trans hm
  · rw [te_a_natural hs.ne']
    unfold teQ
    have he : 2*(15/16/(x+1)^2)*teG x k = (15/8)*teG x k/(x+1)^2 := by ring
    rw [he]
    linarith only [hd]

private noncomputable def teC1 (x k : ℝ) : ℝ :=
  (15/8)*(k/(x+1)+(k+1)/(x+1)^2-2*(3*k+1)/(x+1)^3+4*k/(x+1)^4)
private noncomputable def teE1 (x k : ℝ) : ℝ :=
  (15/8)*((19/25)*k/(x+1)+(19/25)*(k+1)/(x+1)^2-
    2*(3*k*(19/25)+(19/25)-1)/(x+1)^3+(4*k*(19/25)-1)/(x+1)^4)
private noncomputable def teH (x k : ℝ) : ℝ :=
  k*(x+1)^3+2*(k+1)*(x+1)^2-6*(3*k+1)*(x+1)+16*k
private noncomputable def teH1 (x k : ℝ) : ℝ :=
  (19/25)*k*(x+1)^3+3*(19/25)*(k+1)*(x+1)^2-
    12*(3*k*(19/25)+(19/25)-1)*(x+1)+10*(4*k*(19/25)-1)
private noncomputable def teC1p (x k : ℝ) : ℝ := -(15/8)*teH x k/(x+1)^5
private noncomputable def teE1p (x k : ℝ) : ℝ :=
  (15/8)*(-(19/25)*k/(x+1)^2-2*(19/25)*(k+1)/(x+1)^3+
    6*(3*k*(19/25)+(19/25)-1)/(x+1)^4-4*(4*k*(19/25)-1)/(x+1)^5)
private noncomputable def teE1pp (x k : ℝ) : ℝ := (15/4)*teH1 x k/(x+1)^6

private theorem te_c1_deriv {x k : ℝ} (hs : 0 < x+1) :
    HasDerivAt (fun x => teC1 x k) (teC1p x k) x := by
  unfold teC1 teC1p teH
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring
private theorem te_e1_deriv {x k : ℝ} (hs : 0 < x+1) :
    HasDerivAt (fun x => teE1 x k) (teE1p x k) x := by
  unfold teE1 teE1p
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring
private theorem te_e1p_deriv {x k : ℝ} (hs : 0 < x+1) :
    HasDerivAt (fun x => teE1p x k) (teE1pp x k) x := by
  unfold teE1p teE1pp teH1
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring

private theorem te_h_pos {x k : ℝ} (hx : 2 ≤ x) (hk : 1 ≤ k) : 0 < teH x k := by
  have hd : 0 ≤ x-2 := by linarith
  have he : teH x k = 7*k+(21*k+6)*(x-2)+(11*k+2)*(x-2)^2+k*(x-2)^3 := by
    unfold teH; ring
  rw [he]
  positivity
private theorem te_h1_pos {x k : ℝ} (hx : 2 ≤ x) (hk : 1 ≤ k) (hk1 : k ≤ 20/19) :
    0 < teH1 x k := by
  have hd : 0 ≤ x-2 := by linarith
  have he : teH1 x k = 26-(19/25)*(14*k+9)+
      (9*k*(19/25)+6*(19/25)+12)*(x-2)+
      (12*k*(19/25)+3*(19/25))*(x-2)^2+(19/25)*k*(x-2)^3 := by
    unfold teH1; ring
  have hi : 0 < 26-(19/25)*(14*k+9) := by linarith only [hk1]
  rw [he]
  positivity

private theorem te_c1p_neg {x k : ℝ} (hx : 2 ≤ x) (hk : 1 ≤ k) : teC1p x k < 0 := by
  have hs : 0 < x+1 := by linarith
  have hh := te_h_pos hx hk
  unfold teC1p
  exact div_neg_of_neg_of_pos (by nlinarith only [hh]) (by positivity)

private theorem te_e1p_lower {x k : ℝ} (hx : 2 ≤ x) (hk : 1 ≤ k) (hk1 : k ≤ 20/19) :
    -(1/6) < teE1p x k := by
  have hm := ss_le_of_deriv (f := fun z => teE1p z k) (f' := fun z => teE1pp z k) hx
    (fun z hz => te_e1p_deriv (by linarith [hz.1]))
    (fun z hz => by
      have hh := te_h1_pos hz.1.le hk hk1
      unfold teE1pp
      positivity)
  have hi : -(49/324) ≤ teE1p 2 k := by norm_num [teE1p]; linarith only [hk1]
  linarith only [hi,hm]

private theorem te_c1e1_bounds {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) :
    0 < teC1 x k ∧ teC1 x k < 2/3 ∧ 1/2 < teE1 x k := by
  have hs : 0 < x+1 := by linarith
  have hg := te_g_bounds hx hx1 hk hk1
  have hec : teC1 x k = 2*teQ x*(1+k*x-2*teG x k/(x+1)^2) := by
    unfold teC1 teQ teG
    field_simp
    ring
  have hcpos : 0 < teC1 x k := by
    rw [hec]
    apply mul_pos (by unfold teQ; positivity)
    rw [sub_pos,div_lt_iff₀ (by positivity)]
    have hm := mul_nonneg (show 0 ≤ k-1 by linarith) (show 0 ≤ x by linarith)
    have hs2 : 9 ≤ (x+1)^2 := by nlinarith [sq_nonneg (x-2)]
    nlinarith only [hm,hx,hg.2,hs2,mul_nonneg (show 0 ≤ k*x by positivity) (sq_nonneg (x+1))]
  have hcmono := ss_le_of_deriv (f := fun z => -teC1 z k) (f' := fun z => -teC1p z k) hx
    (fun z hz => (te_c1_deriv (by linarith [hz.1])).neg)
    (fun z hz => neg_nonneg.mpr (te_c1p_neg hz.1.le hk).le)
  have hcinit : teC1 2 k < 2/3 := by norm_num [teC1]; linarith only [hk1]
  have hemono := ss_le_of_deriv (f := fun z => teE1 z k+z/6)
    (f' := fun z => teE1p z k+1/6) hx
    (fun z hz => by convert (te_e1_deriv (by linarith [hz.1])).add ((hasDerivAt_id' z).div_const 6) using 1)
    (fun z hz => by have he := te_e1p_lower hz.1.le hk hk1; linarith only [he])
  have heinit : 5/9 ≤ teE1 2 k := by norm_num [teE1]; linarith only [hk]
  refine ⟨hcpos,?_,?_⟩ <;> linarith only [hcmono,hcinit,hemono,heinit,hx1]

private noncomputable def teCorr (x k : ℝ) : ℝ := (k-1)*x*teC x k
private noncomputable def teAbsorb (x k : ℝ) : ℝ :=
  (2*x-1)*(x+1)+(k-1)*x*(x-1)
private noncomputable def teCorrp (x k : ℝ) : ℝ := (k-1)*
  (-6/25+(k*x^2-1)/((x+1)^2*(1+k*x)^2)-
    (15/4)*(x-1)/(x+1)^3+(225/64)*teAbsorb x k/(x+1)^5)
private noncomputable def teFace (x k : ℝ) : ℝ := -2*teA x k*teB x k+teCorr x k
private noncomputable def teFacep (x k : ℝ) : ℝ :=
  -2*(teAp x k*teB x k+teA x k*teBp x k)+teCorrp x k

private theorem te_corr_deriv {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    HasDerivAt (fun x => teCorr x k) (teCorrp x k) x := by
  have hs : 0 < x+1 := by positivity
  have hb : 0 < 1+k*x := by positivity
  unfold teCorr teC teQ teCorrp teAbsorb
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]; field_simp; ring

private theorem te_face_deriv {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    HasDerivAt (fun x => teFace x k) (teFacep x k) x := by
  have h := (((te_a_deriv (k := k) (by positivity)).const_mul (-2)).mul
    (te_b_deriv (k := k) (by positivity))).add (te_corr_deriv hx hk)
  convert h using 1
  · funext y; rfl
  · dsimp [teFacep]; ring

private theorem te_corrp_upper {x : ℝ} (hx : 2 ≤ x) : teCorrp x (20/19) < -(1/160) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < x+1 := by linarith
  have hxm : 0 < x-1 := by linarith
  have hb : 0 < 1+(20/19)*x := by positivity
  have ha : (15/16)*teAbsorb x (20/19) < (x-1)*(x+1)^2 := by
    have he : (20/19)*(x-1)*(x+1)^2-teAbsorb x (20/19) =
        (20/19-1)*(x^3-1)+x*(x-2)*(x+1) := by unfold teAbsorb; ring
    have hm1 : 0 ≤ (20/19-1)*(x^3-1) := by
      have hx3 : 1 ≤ x^3 := by nlinarith [mul_nonneg (show 0 ≤ x-2 by linarith) (sq_nonneg x)]
      positivity
    have hm2 : 0 ≤ x*(x-2)*(x+1) := by
      have hx2 : 0 ≤ x-2 := by linarith
      positivity
    have hm3 : 0 < (x-1)*(x+1)^2 := by positivity
    nlinarith only [he,hm1,hm2,hm3]
  have hn : -(15/4)*(x-1)/(x+1)^3+(225/64)*teAbsorb x (20/19)/(x+1)^5 < 0 := by
    have he : -(15/4)*(x-1)/(x+1)^3+(225/64)*teAbsorb x (20/19)/(x+1)^5 =
        (15/4)*((15/16)*teAbsorb x (20/19)-(x-1)*(x+1)^2)/(x+1)^5 := by
      field_simp; ring
    rw [he]
    exact div_neg_of_neg_of_pos (by linarith only [ha]) (by positivity)
  have hr : ((20/19)*x^2-1)/((x+1)^2*(1+(20/19)*x)^2) < 1/9 := by
    rw [div_lt_iff₀ (by positivity)]
    have hs2 : 9 ≤ (x+1)^2 := by nlinarith [sq_nonneg (x-2)]
    have hm := mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg (1+(20/19)*x))
    nlinarith only [hm,sq_nonneg x,hx]
  have he : teCorrp x (20/19) = (1/19)*(-6/25+
      ((20/19)*x^2-1)/((x+1)^2*(1+(20/19)*x)^2)+
      (-(15/4)*(x-1)/(x+1)^3+(225/64)*teAbsorb x (20/19)/(x+1)^5)) := by
    unfold teCorrp
    ring
  rw [he]
  linarith only [hr,hn]

private theorem te_a_initial {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) (hk : 1 ≤ k) :
    teA 2 k ≤ teA x k := by
  exact ss_le_of_deriv (f := fun z => teA z k) (f' := fun z => teAp z k) hx
    (fun z hz => te_a_deriv (by linarith [hz.1]))
    (fun z hz => le_trans (by norm_num : (0:ℝ) ≤ 1/2)
      (te_ap_half hz.1.le (hz.2.le.trans hx1) hk).le)

private theorem te_facep_neg {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : k = 1 ∨ k = 20/19) : teFacep x k < -(1/10) := by
  rcases hk with rfl | rfl
  · have hab := te_a_bounds hx hx1 (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤20/19)
    have hbp := te_bp_mono (x := 2) (by norm_num) hx (by norm_num : (1:ℝ)≤1)
    have hb := te_b_lower hx hx1 (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤20/19)
    have hap := te_ap_half hx hx1 (by norm_num : (1:ℝ)≤1)
    have hinit : teBp 2 1 = 61/900 := by norm_num [teBp]
    rw [hinit] at hbp
    have hbp0 : 0 < teBp x 1 := by linarith only [hbp]
    have hm := mul_nonneg (sub_nonneg.mpr hab.1) hbp0.le
    have hm1 := mul_nonneg (by linarith only [hap] : 0 ≤ teAp x 1)
      (by linarith only [hb] : 0 ≤ teB x 1)
    unfold teFacep teCorrp
    norm_num
    nlinarith only [hm,hm1,hbp]
  · have ha := te_a_initial hx hx1 (by norm_num : (1:ℝ)≤20/19)
    have hb := te_b_lower hx hx1 (by norm_num : (1:ℝ)≤20/19) (by norm_num : (20/19:ℝ)≤20/19)
    have hbp := (te_bp_bounds hx hx1 (by norm_num : (1:ℝ)≤20/19)
      (by norm_num : (20/19:ℝ)≤20/19)).1
    have hap := te_ap_half hx hx1 (by norm_num : (1:ℝ)≤20/19)
    have hc := te_corrp_upper hx
    have hinit : teA 2 (20/19) = 371/456 := by norm_num [teA]
    rw [hinit] at ha
    have ha1 : 13/16 < teA x (20/19) := by linarith only [ha]
    have hm := mul_nonneg (sub_nonneg.mpr hap.le)
      (by linarith only [hb] : 0 ≤ teB x (20/19))
    have hm1 := mul_nonneg (sub_nonneg.mpr ha1.le) (by linarith only [hbp] : 0 ≤ teBp x (20/19))
    unfold teFacep
    nlinarith only [hm,hm1,hb,hbp,hc]

private noncomputable def teP (x k : ℝ) : ℝ := 2*teC1 x k*teB x k-2*teA x k*teE1 x k
private noncomputable def tePp (x k : ℝ) : ℝ :=
  2*(teC1p x k*teB x k+teC1 x k*teBp x k-teAp x k*teE1 x k-teA x k*teE1p x k)
private theorem te_p_deriv {x k : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun x => teP x k) (tePp x k) x := by
  have hs : 0 < x+1 := by linarith
  have hd := (((te_c1_deriv (k := k) hs).const_mul 2).mul (te_b_deriv (k := k) hs)).sub
    (((te_a_deriv (k := k) hs).const_mul 2).mul (te_e1_deriv (k := k) hs))
  convert hd using 1
  · funext y; rfl
  · dsimp [tePp]; ring
private theorem te_pp_upper {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : tePp x k < -(1/12) := by
  obtain ⟨hc0,hc1,he1⟩ := te_c1e1_bounds hx hx1 hk hk1
  obtain ⟨hbp0,hbp1⟩ := te_bp_bounds hx hx1 hk hk1
  obtain ⟨ha0,ha1⟩ := te_a_bounds hx hx1 hk hk1
  have hb := te_b_lower hx hx1 hk hk1
  have hap := te_ap_half hx hx1 hk
  have hcp := te_c1p_neg hx hk
  have hep := te_e1p_lower hx hk hk1
  have hm0 : teC1p x k*teB x k < 0 := mul_neg_of_neg_of_pos hcp (by linarith only [hb])
  have hm1 := mul_pos (sub_pos.mpr hc1) (by linarith only [hbp0] : 0 < teBp x k)
  have hm2 := mul_pos (sub_pos.mpr hap) (by linarith only [he1] : 0 < teE1 x k)
  have hm3 := mul_pos (by linarith only [ha0] : 0 < teA x k)
    (show 0 < teE1p x k+1/6 by linarith only [hep])
  unfold tePp
  nlinarith only [hm0,hm1,hm2,hm3,hbp1,he1,ha1]

private noncomputable def teL (x : ℝ) : ℝ := -2*(x+1)+4/(x+1)-1-2*teE x*(x-1)
private noncomputable def teLp (x : ℝ) : ℝ := 24*x/25-2-8/(x+1)^2
private noncomputable def teF (x : ℝ) : ℝ := x*teQ x*(4-8/(x+1)^2)
private noncomputable def teFp (x : ℝ) : ℝ := (15/4)*(-x^3-x^2+7*x-1)/(x+1)^5
private noncomputable def teQr (x : ℝ) : ℝ := 4*x*(teQ x)^2*teL x
private noncomputable def teQrp (x : ℝ) : ℝ :=
  (225/64)*((1-3*x)*teL x+x*(x+1)*teLp x)/(x+1)^5
private noncomputable def teR (x : ℝ) : ℝ := -4*x^2*(teQ x)^2*(1-2/(x+1)^2)
private noncomputable def teRp (x : ℝ) : ℝ :=
  (225/32)*x*(x-1)/(x+1)^5-(225/16)*x*(2*x-1)/(x+1)^7
private noncomputable def teBracket (x k : ℝ) : ℝ := k*x/(1+k*x)^2-x/(x+1)^2
private noncomputable def teBracketp (x k : ℝ) : ℝ :=
  k*(1-k*x)/(1+k*x)^3-(1-x)/(x+1)^3
private noncomputable def teJ (x : ℝ) : ℝ := 6/(25*(x+1))-1/(x+1)^3
private noncomputable def teJp (x : ℝ) : ℝ := -6/(25*(x+1)^2)+3/(x+1)^4
private noncomputable def teA0 (x : ℝ) : ℝ := 2*teA x 1-1
private noncomputable def teK (x : ℝ) : ℝ := (15/8)*teJ x*teA0 x
private noncomputable def teKp (x : ℝ) : ℝ :=
  (15/8)*(teJp x*teA0 x+teJ x*(2*teAp x 1))
private noncomputable def teQt (x : ℝ) : ℝ := teQ x*(4*x-2-4*(15/16))
private noncomputable def teQtp (x : ℝ) : ℝ := (15/16)*(8+8*(15/16)-4*x)/(x+1)^3
private noncomputable def teDelta (x k : ℝ) : ℝ :=
  6*x/25+x/(x+1)^2+teQt x+teK x+(6/25)*(k-1)*x+teBracket x k+
    (k-1)*teF x+(k-1)*teQr x+(k-1)^2*teR x
private noncomputable def teDeltap (x k : ℝ) : ℝ :=
  6/25+(1-x)/(x+1)^3+teQtp x+teKp x+(6/25)*(k-1)+teBracketp x k+
    (k-1)*teFp x+(k-1)*teQrp x+(k-1)^2*teRp x

private theorem te_alpha_face_rep {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    ssS5Ta x (k*x) = teP x k+teDelta x k := by
  unfold ssS5Ta teP teDelta teA teB teC1 teE1 teC1g teE1g teDalpha
    teQt teK teJ teA0 teA teBracket teF teQr teR teL teQ teE
  field_simp (disch := positivity)
  ring

private theorem te_delta_deriv {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    HasDerivAt (fun x => teDelta x k) (teDeltap x k) x := by
  have hs : 0 < x+1 := by positivity
  have hb : 0 < 1+k*x := by positivity
  unfold teDelta teQt teK teJ teA0 teA teBracket teF teQr teR teL teQ teE
  apply HasDerivAt.congr_deriv
  · tederiv
  · norm_num [npowRec]
    unfold teDeltap teQtp teKp teJp teA0 teA teJ teAp teBracketp teFp teQrp teRp teLp teL teE
    field_simp (disch := positivity)
    ring

private theorem te_powers {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    9 ≤ (x+1)^2 ∧ (x+1)^2 < 11 ∧ 27 ≤ (x+1)^3 ∧ 81 ≤ (x+1)^4 ∧ 243 ≤ (x+1)^5 := by
  have hs : (3:ℝ) ≤ x+1 := by linarith
  have hs1 : x+1 ≤ 19/6 := by linarith
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hs 2
  have hu := pow_le_pow_left₀ (by linarith : 0 ≤ x+1) hs1 2
  have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hs 3
  have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hs 4
  have h5 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hs 5
  norm_num at h2 hu h3 h4 h5
  exact ⟨h2,by linarith only [hu],h3,h4,h5⟩

private theorem te_fprime_upper {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : teFp x < 1/50 := by
  have hs : 0 < x+1 := by linarith
  have hp := (te_powers hx hx1).2.2.2.2
  have hn : -x^3-x^2+7*x-1 ≤ 1 := by
    have hm := mul_nonneg (show 0 ≤ x-2 by linarith)
      (show 0 ≤ x^2+3*x-1 by nlinarith only [hx,sq_nonneg x])
    nlinarith only [hm]
  unfold teFp
  rw [div_lt_iff₀ (by positivity)]
  nlinarith only [hn,hp]

private theorem te_l_bounds {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    teL x < 0 ∧ teLp x < 0 ∧ -teL x < 61/12 := by
  have hs : 0 < x+1 := by linarith
  have hp := te_powers hx hx1
  have hxx := pow_le_pow_left₀ (by linarith : 0 ≤ x) hx1 2
  have he : teL x = 12*x^2/25-2*x-87/25+(6-2*x)/(x+1) := by
    unfold teL teE
    field_simp
    ring
  have hr : (6-2*x)/(x+1) ≤ 2/3 := by rw [div_le_iff₀ hs]; linarith only [hx]
  have hr1 : 12/25 < (6-2*x)/(x+1) := by rw [lt_div_iff₀ hs]; linarith only [hx1]
  have hrec : 8/11 < 8/(x+1)^2 := by rw [lt_div_iff₀ (by positivity)]; linarith only [hp.2.1]
  have hsq : 2*x-12*x^2/25 ≤ 25/12 := by nlinarith [sq_nonneg (x-25/12)]
  refine ⟨?_,?_,?_⟩
  · rw [he]; norm_num at hxx; linarith only [hxx,hx,hr]
  · unfold teLp; linarith only [hx1,hrec]
  · rw [he]; linarith only [hsq,hr1]

private theorem te_ratio1 {x : ℝ} (hx : 2 ≤ x) : (3*x-1)/(x+1)^5 ≤ 5/243 := by
  have hm := ss_le_of_deriv (f := fun z : ℝ => -(3*z-1)/(z+1)^5)
    (f' := fun z => (12*z-8)/(z+1)^6) hx
    (fun z hz => by
      have hs : 0 < z+1 := by linarith [hz.1]
      apply HasDerivAt.congr_deriv
      · tederiv
      · norm_num [npowRec]; field_simp; ring)
    (fun z hz => div_nonneg (by linarith [hz.1]) (by positivity))
  norm_num at hm
  rw [show (1-3*x)/(x+1)^5 = -((3*x-1)/(x+1)^5) by ring] at hm
  linarith only [hm]

private theorem te_ratio2 {x : ℝ} (hx : 2 ≤ x) : x*(x-1)/(x+1)^5 ≤ 2/243 := by
  have hm := ss_le_of_deriv (f := fun z : ℝ => -z*(z-1)/(z+1)^5)
    (f' := fun z => (3*(z-1)^2-2)/(z+1)^6) hx
    (fun z hz => by
      have hs : 0 < z+1 := by linarith [hz.1]
      apply HasDerivAt.congr_deriv
      · tederiv
      · norm_num [npowRec]; field_simp; ring)
    (fun z hz => by
      have hz0 : 2 ≤ z := hz.1.le
      apply div_nonneg _ (by positivity)
      nlinarith [sq_nonneg (z-2)])
  norm_num at hm
  rw [neg_div] at hm
  linarith only [hm]

private theorem te_ratio3 {x : ℝ} (hx : 2 ≤ x) : x/(x+1)^3 ≤ 2/27 := by
  have hm := ss_le_of_deriv (f := fun z : ℝ => -z/(z+1)^3)
    (f' := fun z => (2*z-1)/(z+1)^4) hx
    (fun z hz => by
      have hs : 0 < z+1 := by linarith [hz.1]
      apply HasDerivAt.congr_deriv
      · tederiv
      · norm_num [npowRec]; field_simp; ring)
    (fun z hz => div_nonneg (by linarith [hz.1]) (by positivity))
  norm_num at hm
  rw [neg_div] at hm
  linarith only [hm]

private theorem te_ratio4 {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : 1/28 < (x-1)/(x+1)^3 := by
  have hm := ss_le_of_deriv (f := fun z : ℝ => -(z-1)/(z+1)^3)
    (f' := fun z => (2*z-4)/(z+1)^4) hx1
    (fun z hz => by
      have hs : 0 < z+1 := by linarith [hz.1,hx]
      apply HasDerivAt.congr_deriv
      · tederiv
      · norm_num [npowRec]; field_simp; ring)
    (fun z hz => div_nonneg (by linarith [hz.1,hx]) (by positivity))
  norm_num at hm
  rw [show (1-x)/(x+1)^3 = -((x-1)/(x+1)^3) by ring] at hm
  linarith only [hm]

private theorem te_qrprime_upper {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : teQrp x < 3/8 := by
  have hs : 0 < x+1 := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hL,hLp,hLm⟩ := te_l_bounds hx hx1
  have hr := te_ratio1 hx
  have hr0 : 0 < (3*x-1)/(x+1)^5 := div_pos (by linarith) (by positivity)
  have hm := mul_lt_mul_of_pos_left hLm hr0
  have hm1 := mul_le_mul_of_nonneg_right hr (by norm_num : (0:ℝ) ≤ 61/12)
  have hn : x*teLp x/(x+1)^4 < 0 := div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hx0 hLp) (by positivity)
  have he : teQrp x = (225/64)*((3*x-1)/(x+1)^5*(-teL x)+x*teLp x/(x+1)^4) := by
    unfold teQrp
    field_simp
    ring
  rw [he]
  nlinarith only [hm,hm1,hn]

private theorem te_rprime_upper {x : ℝ} (hx : 2 ≤ x) : teRp x < 1/16 := by
  have hs : 0 < x+1 := by linarith
  have hx0 : 0 < x := by linarith
  have hr := te_ratio2 hx
  have hn : 0 < (225/16)*x*(2*x-1)/(x+1)^7 := by
    have hh : 0 < 2*x-1 := by linarith
    positivity
  have he : teRp x = (225/32)*(x*(x-1)/(x+1)^5)-(225/16)*x*(2*x-1)/(x+1)^7 := by
    unfold teRp; ring
  rw [he]
  linarith only [hr,hn]

private theorem te_qtprime_upper {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : teQtp x < 4/15 := by
  have hs : 0 < x+1 := by linarith
  have hp := (te_powers hx hx1).2.2.1
  unfold teQtp
  rw [div_lt_iff₀ (by positivity)]
  nlinarith only [hx,hp]

private theorem te_kprime_upper {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) : teKp x < 1/8 := by
  have hs : 0 < x+1 := by linarith
  have hp := te_powers hx hx1
  have hj0 : 0 < teJ x := by
    have he : teJ x = ((6/25)*(x+1)^2-1)/(x+1)^3 := by unfold teJ; field_simp
    rw [he]
    exact div_pos (by linarith only [hp.1]) (by positivity)
  have hj1 : teJ x < 1/20 := by
    have he : teJ x = (6/25-1/(x+1)^2)/(x+1) := by unfold teJ; field_simp
    have hr : 1/11 < 1/(x+1)^2 := by rw [lt_div_iff₀ (by positivity)]; linarith only [hp.2.1]
    have hfirst : teJ x < (6/25-1/11)/(x+1) := by rw [he]; exact div_lt_div_of_pos_right (by linarith only [hr]) hs
    have hlast : (6/25-1/11)/(x+1) ≤ (6/25-1/11)/3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith only [hx]
    linarith only [hfirst,hlast]
  have hjp : 0 < teJp x ∧ teJp x < 1/90 := by
    have he : teJp x = (3-(6/25)*(x+1)^2)/(x+1)^4 := by unfold teJp; field_simp; ring
    rw [he]
    constructor
    · exact div_pos (by linarith only [hp.2.1]) (by positivity)
    · rw [div_lt_iff₀ (by positivity)]
      linarith only [hp.1,hp.2.2.2.1]
  obtain ⟨ha0,ha1⟩ := te_a_bounds hx hx1 (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤20/19)
  have hA0 : 0 < teA0 x ∧ teA0 x < 1 := by unfold teA0; constructor <;> linarith only [ha0,ha1]
  have hAp0 : 0 < 2*teAp x 1 := by have h := te_ap_half hx hx1 (by norm_num : (1:ℝ)≤1); linarith only [h]
  have hAp1 : 2*teAp x 1 ≤ 10/9 := by
    have hr := te_ratio3 hx
    have he : 2*teAp x 1 = 15*(x/(x+1)^3) := by unfold teAp; field_simp; ring
    rw [he]; linarith only [hr]
  have hm := mul_pos hjp.1 (sub_pos.mpr hA0.2)
  have hm1 := mul_nonneg hj0.le (sub_nonneg.mpr hAp1)
  unfold teKp
  nlinarith only [hm,hm1,hjp.2,hj1]

private noncomputable def teBracketKernel (y : ℝ) : ℝ := y*(1-y)/(1+y)^3
private theorem te_bracketp_nonpos {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : teBracketp x k ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := by linarith
  have hxx : x ≤ k*x := by nlinarith only [mul_nonneg (sub_nonneg.mpr hk) hx0.le]
  have hhi : k*x < 5/2 := by
    have hm := mul_le_mul_of_nonneg_right hk1 hx0.le
    have hm1 := mul_le_mul_of_nonneg_left hx1 (by norm_num : (0:ℝ) ≤ 20/19)
    linarith only [hm,hm1]
  have hm := ss_le_of_deriv (f := fun y => -teBracketKernel y)
    (f' := fun y => (3-(y-2)^2)/(1+y)^4) hxx
    (fun y hy => by
      have hs : 0 < 1+y := by linarith [hy.1,hx]
      unfold teBracketKernel
      apply HasDerivAt.congr_deriv
      · tederiv
      · norm_num [npowRec]; field_simp; ring)
    (fun y hy => by
      have hy0 : 0 ≤ y-2 := by linarith [hy.1,hx]
      have hy1 : y-2 ≤ 1/2 := by linarith [hy.2,hhi]
      have hs := pow_le_pow_left₀ hy0 hy1 2
      apply div_nonneg _ (by positivity)
      norm_num at hs
      linarith only [hs])
  have he : teBracketp x k = (teBracketKernel (k*x)-teBracketKernel x)/x := by
    unfold teBracketp teBracketKernel
    field_simp (disch := positivity)
    ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hm]) hx0.le

private theorem te_deltap_upper {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : 1 ≤ k) (hk1 : k ≤ 20/19) : teDeltap x k < 2/3 := by
  have hF := te_fprime_upper hx hx1
  have hQ := te_qrprime_upper hx hx1
  have hR := te_rprime_upper hx
  have hBr := te_bracketp_nonpos hx hx1 hk hk1
  have hQt := te_qtprime_upper hx hx1
  have hK := te_kprime_upper hx hx1
  have hratio := te_ratio4 hx hx1
  have hd : 0 ≤ k-1 := by linarith only [hk]
  have hd1 : k-1 ≤ 1/19 := by linarith only [hk1]
  have hd2 := pow_le_pow_left₀ hd hd1 2
  norm_num at hd2
  have hmF := mul_le_mul_of_nonneg_left hF.le hd
  have hmQ := mul_le_mul_of_nonneg_left hQ.le hd
  have hmR := mul_le_mul_of_nonneg_left hR.le (sq_nonneg (k-1))
  have hdisp : (6/25)*(k-1)+(k-1)*teFp x+(k-1)*teQrp x+(k-1)^2*teRp x < 1/28 := by
    nlinarith only [hmF,hmQ,hmR,hd1,hd2]
  have hr : (1-x)/(x+1)^3 < -(1/28) := by
    rw [show (1-x)/(x+1)^3 = -((x-1)/(x+1)^3) by ring]
    linarith only [hratio]
  unfold teDeltap
  linarith only [hdisp,hr,hBr,hQt,hK]

private noncomputable def teTangent (x k : ℝ) : ℝ := teFace x k+(teP x k+teDelta x k)/6
private noncomputable def teTangentp (x k : ℝ) : ℝ := teFacep x k+(tePp x k+teDeltap x k)/6
private theorem te_tangent_deriv {x k : ℝ} (hx : 2 ≤ x) (hk : 0 < k) :
    HasDerivAt (fun x => teTangent x k) (teTangentp x k) x := by
  have hx0 : 0 < x := by linarith
  have hd := (te_face_deriv hx0 hk).add (((te_p_deriv (k := k) hx).add (te_delta_deriv hx0 hk)).div_const 6)
  convert hd using 1
  · funext y; rfl
  · rfl

private theorem te_tangentp_neg {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : k = 1 ∨ k = 20/19) : teTangentp x k < 0 := by
  have hk0 : 1 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hk1 : k ≤ 20/19 := by rcases hk with rfl | rfl <;> norm_num
  have hT := te_facep_neg hx hx1 hk
  have hP := te_pp_upper hx hx1 hk0 hk1
  have hD := te_deltap_upper hx hx1 hk0 hk1
  unfold teTangentp
  linarith only [hT,hP,hD]

private theorem te_initial {k : ℝ} (hk : k = 1 ∨ k = 20/19) :
    teFace 2 k < 0 ∧ teTangent 2 k < 0 := by
  rcases hk with rfl | rfl <;>
    norm_num [teFace,teTangent,teP,teDelta,teA,teB,teCorr,teC,teQ,teC1,teE1,
      teQt,teK,teJ,teA0,teBracket,teF,teQr,teR,teL,teE]

/-- Both ends of the alpha tangent are negative on the two geometric beta faces. -/
theorem ssS5T_endpoint_tangents {x k : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hk : k = 1 ∨ k = 20/19) :
    ssS5T x (k*x) 1 < 0 ∧ ssS5T x (k*x) 1+ssS5Ta x (k*x)/6 < 0 := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  have h0 := te_initial hk
  have hface := ss_le_of_deriv (f := fun z => -teFace z k) (f' := fun z => -teFacep z k) hx
    (fun z hz => (te_face_deriv (by linarith [hz.1]) hk0).neg)
    (fun z hz => by have h := te_facep_neg hz.1.le (hz.2.le.trans hx1) hk; linarith only [h])
  have htan := ss_le_of_deriv (f := fun z => -teTangent z k) (f' := fun z => -teTangentp z k) hx
    (fun z hz => (te_tangent_deriv hz.1 hk0).neg)
    (fun z hz => by have h := te_tangentp_neg hz.1.le (hz.2.le.trans hx1) hk; linarith only [h])
  rw [te_endpoint_factor hx0 hk0,te_alpha_face_rep hx0 hk0]
  change teFace x k < 0 ∧ teTangent x k < 0
  constructor <;> linarith only [h0.1,h0.2,hface,htan]

end SmoothedOctagon

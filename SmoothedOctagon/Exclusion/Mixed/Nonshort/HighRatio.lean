module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Transport
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Incoming
public import SmoothedOctagon.Exclusion.Mixed.CentralScale
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale

/-!
# The mixed high-ratio exclusion

Lowering the scale and raising the middle margin reduce the comparison to
two displacement ranges. The variance ceiling and incoming Jensen slack
exclude the larger range. Exact normalization gives the physical contradiction.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

/-- The original raised transport minus the Jensen multiplier is the natural quadratic. -/
theorem mhtDelta_quadratic_identity {u q : ℝ} (hu : u ≠ -6) (hq : q ≠ 0) :
    mhtDelta (3/2) (mhtD u) 7 (mhtV u) q-mhtM u/4*mhtIncomingJ u (1-1/q) =
      mhtA u*(1-1/q)^2+mhtB u*(1-1/q)+mhtC u := by
  obtain ⟨hA,hB,hC⟩ := mht_coefficients hu
  rw [hA,hB,hC]
  unfold mhtDelta mhtTransportW mhtTransportQ mhtTransportY mhtTransportA mhtTransportH
    mhtIncomingJ mhtG0 mhtM mhtY mhtD mhtW mhtQ mhtV mhtEps
  unfold mhtS mhtD mhtW
  have h6 : u+6 ≠ 0 := by intro hh; apply hu; linarith only [hh]
  field_simp
  ring

/-- The larger-D boundary is excluded by the actual incoming switching floor. -/
theorem mhtDelta_largeD_pos {D q : ℝ} (hD : D ∈ Icc (3/2:ℝ) (11/6)) (hq : 1 < q)
    (hqW : q < (D+3/2)/D)
    (hfloor : m2F (D/(D+3/2)) q ≤ m2Sec 1 (3/2) D) :
    0 < mhtDelta (3/2) D 7 (m2Sec 1 (3/2) D) q := by
  let u := 2*D-3
  have hu : u ∈ Icc (0:ℝ) (2/3) := by dsimp [u]; constructor <;> linarith only [hD.1,hD.2]
  have hdu : mhtD u=D := by dsimp [mhtD,u]; ring
  have hwu : mhtW u=D+3/2 := by dsimp [mhtW,u]; ring
  have hv := mhtSec_variance_ceiling hD
  have hv' : m2Sec 1 (3/2) D < mhtV u := by
    dsimp [mhtV,mhtEps,u]
    linarith only [hv]
  have hJ : 0 < mhtIncomingJ u (1-1/q) := by
    apply mhtIncomingJ_pos hu hq
    · change q < mhtW u/mhtD u
      simpa only [hwu,hdu] using hqW
    · change m2F (mhtD u/mhtW u) q ≤ m2Sec 1 (3/2) D
      simpa only [hwu,hdu] using hfloor
    · dsimp [u]
      exact hv
  have hquad := mht_quadratic_pos hu (1-1/q)
  have hne : u ≠ -6 := by linarith only [hu.1]
  have hid := mhtDelta_quadratic_identity hne (by linarith only [hq] : q ≠ 0)
  have hM := (mht_geometry hu).2.2.2.2.2.2.1
  have hraised : 0 < mhtDelta (3/2) D 7 (mhtV u) q := by
    rw [hdu] at hid
    have hpos : 0 < mhtM u/4*mhtIncomingJ u (1-1/q) := mul_pos (by positivity) hJ
    linarith only [hid,hquad,hpos]
  have hi := mhtDelta_value_identity (3/2) D 7 (m2Sec 1 (3/2) D) (mhtV u) q
  have hY : 0 < mhtTransportY (3/2) D := by unfold mhtTransportY; nlinarith only [hD.1]
  have hp : 0 < (mhtV u-m2Sec 1 (3/2) D)*mhtTransportY (3/2) D*
      (7*((3/2)+1)+mhtTransportY (3/2) D) := by positivity
  linarith only [hi,hp,hraised]

/-- Along the physical secant path, raising C decreases the transport comparison. -/
theorem mhtDelta_raise_C {C0 D q : ℝ} (hC0 : 1 < C0) (hC1 : C0 ≤ 3/2)
    (hD : 4/3 < D) (hq : 1 < q) (hshape : D < C0^2)
    (hgap : 6 < D^2+2*C0*D) (hinitial : m2g C0 D ≤ m2Sec 1 C0 D) :
    mhtDelta (3/2) D 7 (m2Sec 1 (3/2) D) q ≤
      mhtDelta C0 D 7 (m2Sec 1 C0 D) q := by
  have hD1 : 1 < D := by linarith only [hD]
  have hh := mhtT_le_of_deriv (f := fun C => -mhtDelta C D 7 (m2Sec 1 C D) q)
    (f' := fun C => -mhtDeltaC C D q (m2Sec 1 C D) (mhtSecC C D)) hC1
    (fun C hC => (mhtDelta_hasDerivAt_C (by linarith only [hC0,hC.1]) hq
      (mhtSec_hasDerivAt_C (by linarith only [hC0,hC.1]) hD1)).neg)
    (fun C hC => by
      have hC' : C ∈ Icc (1:ℝ) (3/2) := ⟨by linarith only [hC0,hC.1],hC.2.le⟩
      have hgc : 6 < D^2+2*C*D := by
        have hp := mul_nonneg (by linarith only [hC.1] : 0≤C-C0) (by linarith only [hD] : 0≤D)
        nlinarith only [hgap,hp]
      have hv := mhtSec_ge_floor (by linarith only [hC0,hC.1] : 0<C) hD1
      have hvc := mhtSecC_pos_on_path hC0 hC.1.le hD1 hshape hinitial
      exact le_of_lt (neg_pos.mpr (mhtDeltaC_neg hC' hD.le hq hgc hv hvc.le)))
  linarith only [hh]

/-- The full normalized contradiction uses only original window inequalities. -/
theorem mhtDelta_physical_pos {C D K q : ℝ} (hC0 : 1 < C) (hC1 : C ≤ 3/2)
    (hD : D ∈ Ioo (4/3:ℝ) (11/6)) (hK : 7 ≤ K) (hq : 1 < q)
    (hqW : q < (C+D)/D) (hshape : D < C^2) (hgap : 6 < D^2+2*C*D)
    (hinitial : m2g C D ≤ m2Sec 1 C D)
    (hfloor : m2F (D/(C+D)) q ≤ m2Sec 1 C D) :
    0 < mhtDelta C D K (m2Sec 1 C D) q := by
  have hD1 : 1 < D := by linarith only [hD.1]
  have hscale := mhtDelta_lower_scale hC0.le hD1 hq (mhtSec_lt_left hC0 hD1 hshape).le hK
  have hraise := mhtDelta_raise_C hC0 hC1 hD.1 hq hshape hgap hinitial
  have hb : 0 < mhtDelta (3/2) D 7 (m2Sec 1 (3/2) D) q := by
    by_cases hDs : D ≤ 3/2
    · exact mhtDelta_smallD_pos ⟨hD.1.le,hDs⟩
        (by have hs := mhtSec_lt_left (by norm_num : (1:ℝ)<3/2) hD1
              (by nlinarith only [hD.2] : D < (3/2:ℝ)^2)
            norm_num [m2g] at hs
            linarith only [hs])
    · have hDl : 3/2 ≤ D := le_of_not_ge hDs
      have hqW' : q < (D+3/2)/D := by
        have hh : (C+D)/D ≤ (D+3/2)/D := by
          apply div_le_div_of_nonneg_right _ (by linarith only [hD.1])
          linarith only [hC1]
        exact lt_of_lt_of_le hqW hh
      apply mhtDelta_largeD_pos ⟨hDl,hD.2.le⟩ hq hqW'
      have hf := mhtIncoming_floor_anti (by linarith only [hC0] : 0<C) hC1 hDl hq hqW
      have hv : m2Sec 1 C D ≤ m2Sec 1 (3/2) D := by
        apply mhtS_le_of_deriv hC1
          (fun s hs => mhtSec_hasDerivAt_C (by linarith only [hC0,hs.1]) hD1)
        intro s hs
        exact (mhtSecC_pos_on_path hC0 hs.1.le hD1 hshape hinitial).le
      have hfloor' : m2F (D/(D+C)) q ≤ m2Sec 1 C D := by
        simpa only [add_comm] using hfloor
      exact le_trans hf (le_trans hfloor' hv)
  linarith only [hb,hraise,hscale]

/-- Secants are homogeneous under the actual positive margin normalization. -/
theorem mhtSec_normalize {a c d : ℝ} (ha : 0 < a) (hc : 0 < c) (had : a < d) :
    m2Sec a c d = m2Sec 1 (c/a) (d/a) := by
  have hd : 1 < d/a := (lt_div_iff₀ ha).mpr (by simpa using had)
  rw [m2Sec_of_ne (ne_of_lt had),m2Sec_of_ne (ne_of_lt hd)]
  have hrat : (d/a+c/a)/(1+c/a)=(d+c)/(a+c) := by field_simp
  rw [hrat]
  have hap : a+c ≠ 0 := by positivity
  have hdp : d+c ≠ 0 := by linarith only [ha,hc,had]
  have hda : d-a ≠ 0 := by linarith only [had]
  field_simp

/-- The cleared physical ceiling/floor difference is exactly the normalized transport. -/
theorem mhtDelta_normalize {a c d r v : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hr : 0 < r) :
    a^4*mhtDelta (c/a) (d/a) ((a^2+4)/a^2) v ((c+d)*(d+r)/(d^2+4)) =
      (d^2+4)^2*(m2g d r-
        nsrWU a (m2bStar a c) c d (m2U (a/(a+m2bStar a c))) v) := by
  have hT : 0 < a+c := by positivity
  have hW : 0 < c+d := by positivity
  have hZ : 0 < d+r := by positivity
  have hK : 0 < a^2+4 := by positivity
  have hQ : 0 < d^2+4 := by positivity
  have hb : a+m2bStar a c=(a^2+4)/(a+c) := by unfold m2bStar; ring
  have hl : Real.log ((m2bStar a c+a)*(a+c)/(a^2+4))=0 := by
    rw [show m2bStar a c+a=(a^2+4)/(a+c) by rw [add_comm]; exact hb]
    rw [show (a^2+4)/(a+c)*(a+c)/(a^2+4)=1 by field_simp]
    exact Real.log_one
  unfold mhtDelta mhtTransportW mhtTransportQ mhtTransportY mhtTransportA mhtTransportH
    nsrWU m2wOf m2h m2Stat m2Y
  rw [hl]
  rw [show m2bStar a c+a=(a^2+4)/(a+c) by rw [add_comm]; exact hb,hb]
  unfold m2g m2U
  field_simp
  ring

/-- The physical switching inequality puts the original normalized comparison below zero. -/
theorem mhtDelta_window_neg (W : M2Window) :
    mhtDelta (W.c/W.a) (W.d/W.a) ((W.a^2+4)/W.a^2) W.v W.nq < 0 := by
  have ha := W.a_pos
  have hb : 0 < W.b := by linarith [W.a_lt_b]
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hr : 0 < W.r := by linarith [W.a_le_r]
  have hw1 : W.w ≤ nsrWU W.a W.b W.c W.d (m2U (W.a/(W.a+W.b))) W.v := by
    have he := nsr_w_mono_u (a:=W.a) (b:=W.b) (c:=W.c) (d:=W.d)
      (u:=W.u) (U:=m2U (W.a/(W.a+W.b))) (v:=W.v) ha hd
    have hwu : W.w=nsrWU W.a W.b W.c W.d W.u W.v := by rw [W.w_eq,W.h_eq]; rfl
    have hu := W.u_le
    rw [m2g_eq_m2U (by positivity)] at hu
    have hY : 0 < m2Y W.a W.c W.d := by unfold m2Y; nlinarith [W.a_lt_d]
    have hp : 0 ≤ (m2U (W.a/(W.a+W.b))-W.u)*
        ((W.a^2+4)*(W.a*(W.a^2+4)+(W.a+W.b)*m2Y W.a W.c W.d)/
          (W.a*(W.d^2+4)^2)) := mul_nonneg (sub_nonneg.mpr hu) (by positivity)
    linarith only [he,hwu,hp]
  have hw2 := nsr_wU_lt_star (v:=W.v) ha W.a_lt_b hc W.a_lt_d W.central
  have hdiff : m2g W.d W.r-
      nsrWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a/(W.a+m2bStar W.a W.c))) W.v < 0 := by
    linarith only [W.w_ge,hw1,hw2]
  have hneg := mul_neg_of_pos_of_neg (by positivity : 0<(W.d^2+4)^2) hdiff
  have hid := mhtDelta_normalize (v:=W.v) ha hc hd hr
  change W.a^4*mhtDelta (W.c/W.a) (W.d/W.a) ((W.a^2+4)/W.a^2) W.v W.nq = _ at hid
  rw [← hid] at hneg
  exact neg_of_mul_neg_right hneg (by positivity)

/-- The high-ratio exclusion for the original physical window. -/
theorem nsr_high_t_analytic (W : M2Window) : W.nt < 2/5 := by
  obtain ⟨ht,ht2,hx,_hk1,hq,hqW,hv,_hvU,hg,_hF,_hak⟩ := nsr_window_basic W
  by_contra hcon
  push Not at hcon
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hT : 0 < W.a+W.c := by positivity
  have ha2 := nsr_a_sq W
  have hTT := nsr_t_lt_T (lt_trans ht2 (by norm_num : (1/2:ℝ)<1)) hx hv hg
  have hx3 : W.nx < 1/3 := by
    by_contra hh
    push Not at hh
    have hh' := nsr_T_anti (xa:=1/3) (by norm_num) hh ht.le hTT.le
    norm_num at hh'
    linarith only [hh',hcon]
  let C := W.c/W.a
  let D := W.d/W.a
  let K := (W.a^2+4)/W.a^2
  have hC0 : 1 < C := by dsimp [C]; rw [lt_div_iff₀ ha]; simpa using W.a_lt_c
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hCa : W.c ≤ (3/2)*W.a := by
    unfold M2Window.nt at hcon
    have hh := (le_div_iff₀ hT).mp hcon
    linarith only [hh]
  have hC1 : C ≤ 3/2 := by dsimp [C]; rw [div_le_iff₀ ha]; linarith only [hCa]
  have hD2 : D < 11/6 := by
    unfold M2Window.nx at hx3
    have hh := (div_lt_iff₀ hT).mp hx3
    dsimp [D]
    rw [div_lt_iff₀ ha]
    linarith only [hh,hCa]
  have hK : 7 ≤ K := by
    dsimp [K]
    rw [le_div_iff₀ (sq_pos_of_pos ha)]
    linarith only [ha2]
  have hgap : 6 < D^2+2*C*D := by
    have hh := nsr_centre_gap' W
    have he : (D^2+2*C*D)*W.a^2=W.d^2+2*W.c*W.d := by dsimp [C,D]; field_simp
    have hp := sq_pos_of_pos ha
    nlinarith only [hh,ha2,he,hp]
  have hD1 : 4/3 < D := by
    have hp := mul_nonneg (by linarith only [hC1] : 0≤3/2-C) hD0.le
    by_contra hh
    push Not at hh
    have hp2 := mul_nonneg hD0.le (by linarith only [hh] : 0≤4/3-D)
    nlinarith only [hgap,hp,hp2,hh]
  have hshape : D < C^2 := by
    have he : (C^2-D)*W.a^2=W.c^2-W.a*W.d := by dsimp [C,D]; field_simp
    have hp := sq_pos_of_pos ha
    have hh := W.logconc
    nlinarith only [he,hp,hh]
  have hv' : W.v=m2Sec 1 C D := by rw [W.v_eq]; exact mhtSec_normalize ha hc W.a_lt_d
  have hinitial : m2g C D ≤ m2Sec 1 C D := by
    have he : m2g C D=m2g W.c W.d := by dsimp [C,D]; unfold m2g; field_simp
    rw [he,← hv']
    exact W.v_ge
  have hqW' : W.nq < (C+D)/D := by
    have he : (1+W.nx)/(W.nt+W.nx)=(C+D)/D := by
      unfold M2Window.nt M2Window.nx
      dsimp [C,D]
      field_simp [ha.ne',hd.ne']
      ring
    rwa [he] at hqW
  have hfloor : m2F (D/(C+D)) W.nq ≤ m2Sec 1 C D := by
    have he : D/(C+D)=W.d/(W.c+W.d) := by dsimp [C,D]; field_simp
    rw [he,← hv']
    exact W.v_floor
  have hp := mhtDelta_physical_pos hC0 hC1 ⟨hD1,hD2⟩ hK hq hqW' hshape hgap hinitial hfloor
  have hn := mhtDelta_window_neg W
  change mhtDelta C D K W.v W.nq < 0 at hn
  rw [hv'] at hn
  linarith only [hp,hn]

/-- The high-ratio exclusion for every actual reverse-successor window. -/
theorem nsr_high_t' (W : M2Window) : W.nt < 2 / 5 := nsr_high_t_analytic W

end SmoothedOctagon

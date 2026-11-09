module

public import SmoothedOctagon.Exclusion.Forward.Casimir.Branch

/-!
# The conditional forward Casimir theorem

On the natural norm polygon `δu + δv ≤ 1/32`, the Casimir exceeds
`9193/50000`. Positive central pairing, four norm vertices and the two
closed scalar branches give the comparison.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

theorem fc_f_small {r : ℝ} (hr0 : 1 ≤ r) (hr1 : r ≤ 5/4) : ff_f r ≤ 1/384 := by
  have h := fc_f_le_cube_integral hr0
  have hp : (r-1)^3 ≤ (1/4:ℝ)^3 := pow_le_pow_left₀ (by linarith only [hr0]) (by linarith only [hr1]) 3
  nlinarith only [h,hp]

theorem fc_phi_bounds {U z w : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3) :
    0 ≤ ff_Phi U z w ∧ ff_Phi U z w ≤ 1/128 := by
  have hK : 0 < 1+U := by linarith only [hU]
  have harg : 1 ≤ 4/(1+U) := (le_div_iff₀ hK).2 (by linarith only [hU3])
  have harg' : 4/(1+U) ≤ 5/4 := (div_le_iff₀ hK).2 (by linarith only [hU])
  have hn1 := fc_f_nonneg_integral (by linarith only [hz] : 1 ≤ (1+z)/2)
  have hn2 := fc_f_nonneg_integral (by linarith only [hz,hzw] : 1 ≤ (1+w)/2)
  have hn3 := fc_f_nonneg_integral harg
  have hu1 := fc_f_small (by linarith only [hz] : 1 ≤ (1+z)/2) (by linarith only [hzw,hw])
  have hu2 := fc_f_small (by linarith only [hz,hzw] : 1 ≤ (1+w)/2) (by linarith only [hw])
  have hu3 := fc_f_small harg harg'
  unfold ff_Phi
  constructor <;> linarith only [hn1,hn2,hn3,hu1,hu2,hu3]

theorem fc_e0_ge {U : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3) : 3/4 ≤ ff_e0 U := by
  have hK : 0 < 1+U := by linarith only [hU]
  have hi : (1/4:ℝ) ≤ 1/(1+U) := (le_div_iff₀ hK).2 (by linarith only [hU3])
  unfold ff_e0
  linarith only [hi,hU3]

/-- The strict positive central pairing from the original integral.
This is the physical positivity input; no fixed1/100 correction is used. -/
theorem fc_central_pairing_pos_integral {U z w : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3) : 0 < ff_e0 U-ff_Phi U z w := by
  have hK : 0 < 1+U := by linarith only [hU]
  have hr3 : 1 ≤ 4/(1+U) := (le_div_iff₀ hK).2 (by linarith only [hU3])
  have hr3' : 4/(1+U) ≤ 5/4 := (div_le_iff₀ hK).2 (by linarith only [hU])
  have hf : ∀ r : ℝ, 1 ≤ r → r ≤ 5/4 → ff_f r ≤ (1/4:ℝ)^3/6 := by
    intro r hr0 hr1
    have hc := fc_f_le_cube_integral hr0
    have hp : (r-1)^3 ≤ (1/4:ℝ)^3 := pow_le_pow_left₀ (by linarith only [hr0]) (by linarith only [hr1]) 3
    linarith only [hc,hp]
  have h1 := hf ((1+z)/2) (by linarith only [hz]) (by linarith only [hzw,hw])
  have h2 := hf ((1+w)/2) (by linarith only [hz,hzw]) (by linarith only [hw])
  have h3 := hf (4/(1+U)) hr3 hr3'
  have he := fc_e0_ge hU hU3
  unfold ff_Phi
  linarith only [h1,h2,h3,he]


/-- Positivity comes from the original integral correction throughout the
entire norm polygon, including its zero vertex. -/
theorem fc_pairing_pos {U z w x y : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 < ff_e0 U-ff_Phi U z w+(1+z)*x+(1+w)*y := by
  have hc := fc_central_pairing_pos_integral hU hU3 hz hzw hw
  have hx' := mul_nonneg (by linarith only [hz] : 0 ≤ 1+z) hx
  have hy' := mul_nonneg (by linarith only [hz,hzw] : 0 ≤ 1+w) hy
  linarith only [hc,hx',hy']

noncomputable def fcExtraCurve (U T : ℝ) : ℝ :=
  fcScale U*(9/4+3*T-(ff_e0 U+7*T/3)^2)

theorem fc_cas_scale (U u v E : ℝ) :
    ff_cas U u v E=fcScale U*(4*u*v-E^2) := by
  unfold ff_cas fcScale
  ring

/-- The two lower polygon vertices use no logarithmic truncation: their
only estimate is dropping the nonnegative exact correction. -/
theorem fc_extra_curve_lower {U z w T : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3) (hT : 0 ≤ T) :
    fcExtraCurve U T ≤ ff_cas U (3/4) (3/4+T)
      (ff_e0 U-ff_Phi U z w+(1+w)*T) := by
  have hphi := (fc_phi_bounds hU hU3 hz hzw hw).1
  have hE0 := fc_pairing_pos hU hU3 hz hzw hw (x := 0) le_rfl hT
  simp only [mul_zero,add_zero] at hE0
  have hmajor : ff_e0 U-ff_Phi U z w+(1+w)*T ≤ ff_e0 U+7*T/3 := by
    have hm := mul_le_mul_of_nonneg_right (by linarith only [hw] : 1+w ≤ 7/3) hT
    linarith only [hm,hphi]
  have hM0 : 0 ≤ ff_e0 U+7*T/3 := hE0.le.trans hmajor
  have hsq := (sq_le_sq₀ hE0.le hM0).2 hmajor
  have hscale : 0 ≤ fcScale U := by unfold fcScale; positivity
  unfold fcExtraCurve
  rw [fc_cas_scale]
  exact mul_le_mul_of_nonneg_left (by nlinarith only [hsq]) hscale

/-- Conditional fourvertex assembly. The remaining scalar obligations are
exactly the two lower curves and the common logarithm-corrected sum curve. -/
theorem fc_casimir_of_curves {U z w du dv E G : ℝ}
    (hU : 11/5 ≤ U) (hU3 : U ≤ 3) (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3)
    (hbudget : z+w ≤ 5*(U-1)/3) (hdu : 0 ≤ du) (hdv : 0 ≤ dv)
    (hsum : du+dv ≤ 1/32) (hdv' : dv ≤ 1/64)
    (hE : E=ff_e0 U-ff_Phi U z w+(1+z)*du+(1+w)*dv)
    (hzero : G < fcExtraCurve U 0) (hhalf : G < fcExtraCurve U (1/64))
    (hsumcurve : G < fcSumCurve U) :
    G < ff_cas U (3/4+du) (3/4+dv) E := by
  let e := ff_e0 U-ff_Phi U z w
  let s := 1+z
  let t := 1+w
  have hU0 : 0 < U := by linarith only [hU]
  have hscale : 0 < fcScale U := by unfold fcScale; positivity
  have hq : ∀ x y : ℝ, fcScale U*fcNormQ e s t x y=
      ff_cas U (3/4+x) (3/4+y) (e+s*x+t*y) := by
    intro x y
    rw [fc_cas_scale]
    rfl
  have hx0 : G < fcScale U*fcNormQ e s t 0 0 := by
    rw [hq]
    simpa only [e,s,t,mul_zero,add_zero] using
      hzero.trans_le (fc_extra_curve_lower hU hU3 hz hzw hw (T := 0) le_rfl)
  have hx1 : G < fcScale U*fcNormQ e s t 0 (1/64) := by
    rw [hq]
    simpa only [e,s,t,mul_zero,add_zero] using
      hhalf.trans_le (fc_extra_curve_lower hU hU3 hz hzw hw (T := (1/64:ℝ)) (by norm_num))
  have htop : ∀ y ∈ Icc (0:ℝ) (1/64), G < fcScale U*fcNormQ e s t (1/32-y) y := by
    intro y hy
    rw [hq]
    have hEpos := fc_pairing_pos hU hU3 hz hzw hw (x := 1/32-y)
      (by linarith only [hy.2]) hy.1
    exact hsumcurve.trans_le (fc_sum_curve_lower hU hU3 hz hzw hw hbudget hy.1 hy.2 hEpos.le rfl)
  have htop0 := htop 0 ⟨le_rfl,by norm_num⟩
  have htop1 := htop (1/64) ⟨by norm_num,le_rfl⟩
  have hpolygon := fcNormQ_polygon (e := e) (s := s) (t := t) (c := (1/32:ℝ))
    (k := G/fcScale U) (by norm_num) hdu hdv hsum (by linarith only [hdv'])
    ((div_lt_iff₀ hscale).2 (by nlinarith only [hx0]))
    ((div_lt_iff₀ hscale).2 (by nlinarith only [hx1]))
    ((div_lt_iff₀ hscale).2 (by norm_num at htop0; nlinarith only [htop0]))
    ((div_lt_iff₀ hscale).2 (by norm_num at htop1; nlinarith only [htop1]))
  have hres := (div_lt_iff₀ hscale).mp hpolygon
  rw [mul_comm, hq] at hres
  simpa only [e,s,t,hE] using hres

noncomputable def fcCoordinateE (t : ℝ) : ℝ := 1+t-1/(8*t)
noncomputable def fcCoordinateH (t : ℝ) : ℝ := 2+(1-2*t)/(8*t^2)
noncomputable def fcExtraCoordinate (T t : ℝ) : ℝ :=
  (9/4+3*T-(fcCoordinateE t+7*T/3)^2)/(16*(1-t)^2)

theorem fc_coordinate_pair_factor {t : ℝ} (ht : 0 < t) :
    fcCoordinateE t*fcCoordinateH t-9/4=(2*t+1)*(4*t-1)^3/(64*t^3) := by
  unfold fcCoordinateE fcCoordinateH
  field_simp
  ring

theorem fc_coordinate_pair_bounds {t : ℝ} (ht0 : 1/4 ≤ t) (ht1 : t ≤ 5/16) :
    9/4 ≤ fcCoordinateE t*fcCoordinateH t ∧ 11/4 ≤ fcCoordinateE t+fcCoordinateH t := by
  have ht : 0 < t := by linarith only [ht0]
  have h4 : 0 ≤ 4*t-1 := by linarith only [ht0]
  have hp : 0 ≤ (2*t+1)*(4*t-1)^3/(64*t^3) := by positivity
  have hpair := fc_coordinate_pair_factor ht
  have he : 3/4 ≤ fcCoordinateE t := by
    have hfactor : 0 ≤ (4*t-1)*(2*t+1) := mul_nonneg (by linarith only [ht0]) (by positivity)
    unfold fcCoordinateE
    have hrecip : 1/(8*t) ≤ 1/4+t := (div_le_iff₀ (by positivity : 0 < 8*t)).2 (by nlinarith only [hfactor])
    linarith only [hrecip]
  have hh : 2 ≤ fcCoordinateH t := by
    unfold fcCoordinateH
    have hnum : 0 ≤ 1-2*t := by linarith only [ht1]
    have hdiv : 0 ≤ (1-2*t)/(8*t^2) := by positivity
    linarith only [hdiv]
  exact ⟨by linarith only [hp,hpair],by linarith only [he,hh]⟩

theorem fc_extraCoordinate_hasDerivAt {T t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fcExtraCoordinate T)
      ((9/4+3*T-(fcCoordinateE t+7*T/3)*(fcCoordinateH t+7*T/3))/(8*(1-t)^3)) t := by
  have hdpos : 0 < 1-t := by linarith only [ht1]
  have hE : HasDerivAt fcCoordinateE (1+1/(8*t^2)) t := by
    have hh := ((hasDerivAt_id t).const_add 1).sub
      ((((hasDerivAt_id t).const_mul 8).inv (by dsimp; positivity)).const_mul 1)
    convert hh using 1
    · ext q; simp [fcCoordinateE,one_div]
    · simp only [id_eq]
      field_simp [ht.ne']
      ring
  have h := (((hE.add_const (7*T/3)).pow 2).const_sub (9/4+3*T)).div
    ((((hasDerivAt_id t).const_sub 1).pow 2).const_mul 16) (by dsimp; positivity)
  convert h using 1
  · ext q; simp [fcExtraCoordinate,fcCoordinateE,one_div]
  · simp only [id_eq,Pi.pow_apply]
    have hh : fcCoordinateH t=fcCoordinateE t+(1-t)*(1+1/(8*t^2)) := by
      unfold fcCoordinateE fcCoordinateH
      field_simp [ht.ne']
      ring
    rw [hh]
    generalize fcCoordinateE t=e
    generalize 1+1/(8*t^2)=ep
    have hd : 1-t ≠ 0 := by linarith only [ht1]
    field_simp [hd]
    ring

theorem fc_extraCoordinate_antitone {T : ℝ} (hT : 0 ≤ T) :
    AntitoneOn (fcExtraCoordinate T) (Icc (1/4) (5/16)) := by
  have hd : ∀ t ∈ Icc (1/4:ℝ) (5/16), HasDerivAt (fcExtraCoordinate T)
      ((9/4+3*T-(fcCoordinateE t+7*T/3)*(fcCoordinateH t+7*T/3))/(8*(1-t)^3)) t := by
    intro t ht
    exact fc_extraCoordinate_hasDerivAt (by linarith only [ht.1]) (by linarith only [ht.2])
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' := interior_subset ht
    rw [(hd t ht').deriv]
    have hp := fc_coordinate_pair_bounds ht'.1 ht'.2
    have hcross := mul_le_mul_of_nonneg_left hp.2 (by positivity : 0 ≤ 7*T/3)
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hp.1,hcross,sq_nonneg (7*T/3),hT]
    · have ht1 : t < 1 := by linarith only [ht'.2]
      positivity

theorem fc_extra_coordinate_eq {U T : ℝ} (hU : 0 < U) :
    fcExtraCoordinate T (1/(1+U))=fcExtraCurve U T := by
  have hK : 1+U ≠ 0 := by linarith only [hU]
  unfold fcExtraCoordinate fcCoordinateE fcExtraCurve fcScale ff_e0
  field_simp [hU.ne',hK]
  ring

/-- The easy two norm vertices are controlled by monotonicity of their
original rational curves and exact endpoint substitution. -/
theorem fc_extra_curve_gt {U T : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hT : T=0 ∨ T=1/64) : (9193/50000:ℝ) < fcExtraCurve U T := by
  have hU0 : 0 < U := by linarith only [hU]
  have hK : 0 < 1+U := by linarith only [hU]
  have ht0 : (1/4:ℝ) ≤ 1/(1+U) := (le_div_iff₀ hK).2 (by linarith only [hU3])
  have ht1 : 1/(1+U) ≤ (5/16:ℝ) := (div_le_iff₀ hK).2 (by linarith only [hU])
  have hT0 : 0 ≤ T := by rcases hT with rfl|rfl <;> norm_num
  have hm := fc_extraCoordinate_antitone hT0 ⟨ht0,ht1⟩ (show (5/16:ℝ) ∈ Icc (1/4) (5/16) by norm_num) ht1
  rw [fc_extra_coordinate_eq hU0] at hm
  have hend : (9193/50000:ℝ) < fcExtraCoordinate T (5/16) := by
    rcases hT with rfl|rfl <;> norm_num [fcExtraCoordinate,fcCoordinateE]
  exact hend.trans_le hm

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set
noncomputable def fcCoordinateCurve (P d t : ℝ) : ℝ :=
  (P-(fcCoordinateE t+d)^2)/(16*(1-t)^2)
noncomputable def fcCeilingShift : ℝ := 7/96-1/819

theorem fc_coordinateCurve_hasDerivAt {P d t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fcCoordinateCurve P d)
      ((P-(fcCoordinateE t+d)*(fcCoordinateH t+d))/(8*(1-t)^3)) t := by
  have hdpos : 0 < 1-t := by linarith only [ht1]
  have hE : HasDerivAt fcCoordinateE (1+1/(8*t^2)) t := by
    have hh := ((hasDerivAt_id t).const_add 1).sub
      ((((hasDerivAt_id t).const_mul 8).inv (by dsimp; positivity)).const_mul 1)
    convert hh using 1
    · ext q; simp [fcCoordinateE,one_div]
    · simp only [id_eq]
      field_simp [ht.ne']
      ring
  have h := (((hE.add_const d).pow 2).const_sub P).div
    ((((hasDerivAt_id t).const_sub 1).pow 2).const_mul 16) (by dsimp; positivity)
  convert h using 1
  · rfl
  · simp only [id_eq,Pi.pow_apply]
    have hh : fcCoordinateH t=fcCoordinateE t+(1-t)*(1+1/(8*t^2)) := by
      unfold fcCoordinateE fcCoordinateH
      field_simp [ht.ne']
      ring
    rw [hh]
    generalize fcCoordinateE t=e
    generalize 1+1/(8*t^2)=ep
    have hd : 1-t ≠ 0 := by linarith only [ht1]
    field_simp [hd]
    ring

theorem fc_coordinate_curve_eq {U P d : ℝ} (hU : 0 < U) :
    fcCoordinateCurve P d (1/(1+U))=fcScale U*(P-(ff_e0 U+d)^2) := by
  have hK : 1+U ≠ 0 := by linarith only [hU]
  unfold fcCoordinateCurve fcCoordinateE fcScale ff_e0
  field_simp [hU.ne',hK]
  ring

theorem fc_sum_curve_first {U : ℝ} (hhi : U ≤ 13/5) : fcSumCurve U=fcBranchCurve U := by
  have hshape : fcShapeCeiling U=(5*U+1)/6 := by
    unfold fcShapeCeiling; exact min_eq_right (by linarith only [hhi])
  unfold fcSumCurve fcBranchCurve fcSumMajorant
  rw [hshape]
  have hM : ff_e0 U+((5*U+1)/6)/32-fcLogCorrection (((5*U+1)/6)/2-1)=fcBranchM U := by
    unfold fcBranchM fcBranchM0 fcBranchLog fcBranchX
    rw [show ((5*U+1)/6)/2-1=(5*U-11)/12 by ring]
    ring
  rw [hM]

theorem fc_sum_curve_second {U : ℝ} (hlo : 13/5 ≤ U) :
    fcSumCurve U=fcCoordinateCurve (75/32) fcCeilingShift (1/(1+U)) := by
  have hshape : fcShapeCeiling U=7/3 := by
    unfold fcShapeCeiling; exact min_eq_left (by linarith only [hlo])
  have hU0 : 0 < U := by linarith only [hlo]
  rw [fc_coordinate_curve_eq hU0]
  unfold fcSumCurve fcSumMajorant
  rw [hshape]
  have hL : fcLogCorrection (((7/3:ℝ))/2-1)=1/819 := by norm_num [fcLogCorrection]
  rw [hL]
  unfold fcCeilingShift
  ring

/-- After the shape ceiling the exact same curve increases in U, by the
coordinate pair factor and the positive intrinsic shift. -/
theorem fc_ceiling_curve_antitone :
    AntitoneOn (fcCoordinateCurve (75/32) fcCeilingShift) (Icc (1/4) (5/16)) := by
  have hd : (1/16:ℝ) < fcCeilingShift := by norm_num [fcCeilingShift]
  have hd0 : 0 ≤ fcCeilingShift := by linarith only [hd]
  apply fc_antitoneOn_Icc
    (f' := fun t => (75/32-(fcCoordinateE t+fcCeilingShift)*(fcCoordinateH t+fcCeilingShift))/(8*(1-t)^3))
  · intro t ht
    exact fc_coordinateCurve_hasDerivAt (by linarith only [ht.1]) (by linarith only [ht.2])
  · intro t ht
    have hp := fc_coordinate_pair_bounds ht.1 ht.2
    have hcross := mul_le_mul_of_nonneg_left hp.2 hd0
    have hnum : 75/32-(fcCoordinateE t+fcCeilingShift)*(fcCoordinateH t+fcCeilingShift) ≤ 0 := by
      nlinarith only [hp.1,hcross,hd,sq_nonneg fcCeilingShift]
    apply div_nonpos_of_nonpos_of_nonneg hnum
    have ht1 : t < 1 := by linarith only [ht.2]
    positivity

theorem fc_sum_curve_gt {U : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3) :
    (9193/50000:ℝ) < fcSumCurve U := by
  rcases le_total U (13/5) with hfirst | hsecond
  · rw [fc_sum_curve_first hfirst]
    exact fc_branch_curve_gt hU hfirst
  · have hK : 0 < 1+U := by linarith only [hU]
    have ht0 : (1/4:ℝ) ≤ 1/(1+U) := (le_div_iff₀ hK).2 (by linarith only [hU3])
    have ht1 : 1/(1+U) ≤ (5/18:ℝ) := (div_le_iff₀ hK).2 (by linarith only [hsecond])
    have hcoord := fc_ceiling_curve_antitone ⟨ht0,by linarith only [ht1]⟩
      (show (5/18:ℝ) ∈ Icc (1/4) (5/16) by norm_num) ht1
    have hboundary := fc_sum_curve_second (U := (13/5:ℝ)) le_rfl
    norm_num at hboundary
    rw [← fc_sum_curve_second hsecond,← hboundary] at hcoord
    have hstart : (9193/50000:ℝ) < fcSumCurve (13/5) := by
      rw [fc_sum_curve_first (U := (13/5:ℝ)) le_rfl]
      exact fc_branch_curve_gt (by norm_num) le_rfl
    exact hstart.trans_le hcoord

/-- The conditional Casimir lower bound on the norm polygon `du + dv ≤ 1/32`, `dv ≤ 1/64`. -/
theorem ff_casimir_lower {U z w du dv E : ℝ}
    (hU : 11/5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3)
    (hbudget : z+w ≤ 5*(U-1)/3) (hdu : 0 ≤ du) (hdv : 0 ≤ dv)
    (hsum : du+dv ≤ 1/32) (hdv' : dv ≤ 1/64)
    (hE : E=ff_e0 U-ff_Phi U z w+(1+z)*du+(1+w)*dv) :
    (9193/50000:ℝ) < ff_cas U (3/4+du) (3/4+dv) E := by
  exact fc_casimir_of_curves hU hU3.le hz hzw hw hbudget hdu hdv hsum hdv' hE
    (fc_extra_curve_gt hU hU3.le (T := 0) (Or.inl rfl))
    (fc_extra_curve_gt hU hU3.le (T := (1/64:ℝ)) (Or.inr rfl))
    (fc_sum_curve_gt hU hU3.le)

end SmoothedOctagon

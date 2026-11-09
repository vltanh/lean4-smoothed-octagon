module

public import SmoothedOctagon.Exclusion.Forward.Log
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The forward norm polygon and shape equalization

Quadratic chords reduce the norm polygon to four vertices. The original
reciprocal integral for the central correction controls shape equalization.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

/-- The original norm Gram bracket at fixed central pairing and shapes. -/
noncomputable def fcNormQ (e s t x y : ℝ) : ℝ :=
  4*(3/4+x)*(3/4+y)-(e+s*x+t*y)^2

/-- A strict endpoint lower bound propagates through a concave quadratic
chord. No nondegeneracy of the evaluation point is needed. -/
theorem fc_chord_strict {f : ℝ → ℝ} {b x k A : ℝ}
    (hb : 0 < b) (hx0 : 0 ≤ x) (hxb : x ≤ b) (hA : 0 ≤ A)
    (hkey : b*f x=(b-x)*f 0+x*f b+A*b*x*(b-x))
    (h0 : k < f 0) (h1 : k < f b) : k < f x := by
  by_cases hx : x=0
  · simpa only [hx] using h0
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hl := mul_le_mul_of_nonneg_left h0.le (by linarith only [hxb] : 0 ≤ b-x)
  have hr := mul_lt_mul_of_pos_left h1 hxpos
  have hp : 0 ≤ A*b*x*(b-x) := by positivity
  nlinarith only [hl,hr,hp,hkey,hb]

/-- The complete four-vertex norm-polygon reduction, for any positive
sum threshold. It is proved by the original quadratic chord identities. -/
theorem fcNormQ_polygon {e s t c x y k : ℝ} (hc : 0 < c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x+y ≤ c) (hymax : y ≤ c/2)
    (h00 : k < fcNormQ e s t 0 0)
    (h01 : k < fcNormQ e s t 0 (c/2))
    (h10 : k < fcNormQ e s t c 0)
    (h11 : k < fcNormQ e s t (c/2) (c/2)) : k < fcNormQ e s t x y := by
  have hleft : k < fcNormQ e s t 0 y := by
    apply fc_chord_strict (f := fun v => fcNormQ e s t 0 v)
      (b := c/2) (A := t^2) (by linarith only [hc]) hy hymax (sq_nonneg _)
    · unfold fcNormQ; ring
    · exact h00
    · exact h01
  have hright : k < fcNormQ e s t (c-y) y := by
    apply fc_chord_strict (f := fun v => fcNormQ e s t (c-v) v)
      (b := c/2) (A := 4+(t-s)^2) (by linarith only [hc]) hy hymax (by positivity)
    · unfold fcNormQ; ring
    · simpa only [sub_zero] using h10
    · simpa only [show c-c/2=c/2 by ring] using h11
  apply fc_chord_strict (f := fun v => fcNormQ e s t v y)
    (b := c-y) (A := s^2) (by linarith only [hc,hymax]) hx (by linarith only [hsum]) (sq_nonneg _)
  · unfold fcNormQ; ring
  · exact hleft
  · exact hright

noncomputable def fcFPrime (r : ℝ) : ℝ := (r-1)^2/(2*r^2)

theorem fc_f_hasDerivAt {r : ℝ} (hr : 0 < r) : HasDerivAt ff_f (fcFPrime r) r := by
  have h := (((hasDerivAt_id r).sub ((hasDerivAt_id r).inv hr.ne')).div_const 2).sub
    (hasDerivAt_log hr.ne')
  convert h using 1
  · rfl
  · simp only [id_eq]
    unfold fcFPrime
    field_simp
    ring

theorem fc_fPrime_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt fcFPrime ((r-1)/r^3) r := by
  have h := (((hasDerivAt_id r).sub_const 1).pow 2).div
    ((hasDerivAt_pow 2 r).const_mul 2) (by positivity)
  convert h using 1
  · rfl
  · simp only [id_eq,Pi.pow_apply]
    field_simp
    ring

open MeasureTheory

/-- The original central correction is exactly the positive reciprocal
integral in the paper, including its zero-length endpoint. -/
theorem fc_f_eq_integral {r : ℝ} (hr : 1 ≤ r) :
    ff_f r=∫ s in (1:ℝ)..r, (s-1)^2/(2*s^2) := by
  have hc : ContinuousOn fcFPrime (Icc (1:ℝ) r) := by
    intro s hs
    exact (fc_fPrime_hasDerivAt (by linarith only [hs.1])).continuousAt.continuousWithinAt
  have hd : ∀ s ∈ uIcc (1:ℝ) r, HasDerivAt ff_f (fcFPrime s) s := by
    intro s hs
    rw [uIcc_of_le hr] at hs
    exact fc_f_hasDerivAt (by linarith only [hs.1])
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hr)
  norm_num [ff_f] at hi
  simpa only [fcFPrime,ff_f] using hi.symm

/-- Integrating the original kernel against the elementary polynomial
majorant gives the cubic bound without a numerical Phi allowance. -/
theorem fc_f_le_cube_integral {r : ℝ} (hr : 1 ≤ r) : ff_f r ≤ (r-1)^3/6 := by
  have hc : ContinuousOn fcFPrime (Icc (1:ℝ) r) := by
    intro s hs
    exact (fc_fPrime_hasDerivAt (by linarith only [hs.1])).continuousAt.continuousWithinAt
  have hpoly : Continuous (fun s : ℝ => (s-1)^2/2) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hr (hc.intervalIntegrable_of_Icc hr)
    (hpoly.intervalIntegrable 1 r) (fun s hs => by
      have hs0 : 0 < s := by linarith only [hs.1]
      unfold fcFPrime
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
      nlinarith only [hs.1])
  have hd : ∀ s ∈ uIcc (1:ℝ) r,
      HasDerivAt (fun s : ℝ => (s-1)^3/6) ((s-1)^2/2) s := by
    intro s _
    have h := (((hasDerivAt_id s).sub_const 1).pow 3).div_const 6
    convert h using 1
    · rfl
    · simp only [id_eq]; ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hpoly.intervalIntegrable 1 r)
  simp only [sub_self,zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_div,sub_zero] at hi
  unfold fcFPrime at hm
  rw [← fc_f_eq_integral hr] at hm
  rw [hi] at hm
  exact hm

theorem fc_f_nonneg_integral {r : ℝ} (hr : 1 ≤ r) : 0 ≤ ff_f r := by
  rw [fc_f_eq_integral hr]
  exact intervalIntegral.integral_nonneg_of_forall hr (fun u => by positivity)

theorem fc_f_convex : ConvexOn ℝ (Ici 1) ff_f := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fcFPrime)
    (f'' := fun r => (r-1)/r^3) (convex_Ici 1)
  · intro r hr
    exact (fc_f_hasDerivAt (by have hr1 : 1 ≤ r := hr; linarith only [hr1])).continuousAt.continuousWithinAt
  · intro r hr
    exact (fc_f_hasDerivAt (by have hr1 : 1 ≤ r := interior_subset hr; linarith only [hr1])).hasDerivWithinAt
  · intro r hr
    exact (fc_fPrime_hasDerivAt (by have hr1 : 1 ≤ r := interior_subset hr; linarith only [hr1])).hasDerivWithinAt
  · intro r hr
    have hr1 : 1 ≤ r := interior_subset hr
    exact div_nonneg (by linarith only [hr1]) (by positivity)

/-- The two logarithmic shape corrections dominate their symmetric value. -/
theorem fc_f_midpoint {s t : ℝ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    2*ff_f ((s+t)/4) ≤ ff_f (s/2)+ff_f (t/2) := by
  have hconv := fc_f_convex.2
  have h := hconv (show s/2 ∈ Ici (1:ℝ) by change 1 ≤ s/2; linarith only [hs])
    (show t/2 ∈ Ici (1:ℝ) by change 1 ≤ t/2; linarith only [ht]) (a := (1/2:ℝ)) (b := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have heq : (1/2)*(s/2)+(1/2)*(t/2)=(s+t)/4 := by ring
  rw [heq] at h
  linarith only [h]

/-- Exact sum-edge equalization, retaining the two shape logarithms.
The only dropped term is the nonnegative reciprocal-scale correction. -/
theorem fc_shape_equalization {e s t c y E phi : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (hymax : y ≤ c/2) (hphi : 0 ≤ phi)
    (hE : E=e-ff_f (s/2)-ff_f (t/2)-phi+s*(c-y)+t*y) :
    E ≤ e-2*ff_f ((s+t)/4)+c*((s+t)/2) := by
  have hmid := fc_f_midpoint hs (hs.trans hst)
  have hw : s*(c-y)+t*y ≤ c*((s+t)/2) := by
    have hp := mul_nonneg (by linarith only [hymax] : 0 ≤ c/2-y)
      (by linarith only [hst] : 0 ≤ t-s)
    nlinarith only [hp]
  linarith only [hE,hmid,hw,hphi]

theorem fc_fPrime_mono : MonotoneOn fcFPrime (Ici 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
  · intro r hr
    have hr0 : 0 < r := by have hr1 : 1 ≤ r := hr; linarith only [hr1]
    exact (fc_fPrime_hasDerivAt hr0).continuousAt.continuousWithinAt
  · intro r hr
    have hr1 : 1 ≤ r := interior_subset hr
    exact (fc_fPrime_hasDerivAt (by linarith only [hr1])).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr1 : 1 ≤ r := interior_subset hr
    rw [(fc_fPrime_hasDerivAt (by linarith only [hr1])).deriv]
    exact div_nonneg (by linarith only [hr1]) (by positivity)

theorem fc_fPrime_shape_le {s : ℝ} (hs0 : 2 ≤ s) (hs1 : s ≤ 7/3) :
    fcFPrime (s/2) ≤ 1/98 := by
  have h := fc_fPrime_mono (show s/2 ∈ Ici (1:ℝ) by change 1 ≤ s/2; linarith only [hs0])
    (show (7/6:ℝ) ∈ Ici 1 by norm_num) (by linarith only [hs1])
  norm_num [fcFPrime] at h
  exact h

noncomputable def fcShapePairing (e s : ℝ) : ℝ := e-2*ff_f (s/2)+s/32

theorem fc_shapePairing_hasDerivAt {e s : ℝ} (hs : 0 < s) :
    HasDerivAt (fcShapePairing e) (1/32-fcFPrime (s/2)) s := by
  have h := ((((fc_f_hasDerivAt (by linarith only [hs] : 0 < s/2)).comp s
    ((hasDerivAt_id s).div_const 2)).const_mul 2).const_sub e).add
      ((hasDerivAt_id s).div_const 32)
  convert h using 1
  · rfl
  · ring

theorem fc_shapePairing_mono (e : ℝ) : MonotoneOn (fcShapePairing e) (Icc 2 (7/3)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro s hs
    exact (fc_shapePairing_hasDerivAt (e := e) (by linarith only [hs.1])).continuousAt.continuousWithinAt
  · intro s hs
    have hs' := interior_subset hs
    exact (fc_shapePairing_hasDerivAt (e := e) (by linarith only [hs'.1])).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs' := interior_subset hs
    rw [(fc_shapePairing_hasDerivAt (e := e) (by linarith only [hs'.1])).deriv]
    have hbound := fc_fPrime_shape_le hs'.1 hs'.2
    linarith only [hbound]

noncomputable def fcShapeCeiling (U : ℝ) : ℝ := min (7/3) ((5*U+1)/6)

theorem fc_shapeCeiling_mem {U : ℝ} (hU : 11/5 ≤ U) :
    fcShapeCeiling U ∈ Icc (2:ℝ) (7/3) := by
  constructor
  · unfold fcShapeCeiling; exact le_min (by norm_num) (by linarith only [hU])
  · exact min_le_left _ _

/-- The original physical shape budget implies precisely the paper's
symmetric shape ceiling, without a stronger interval assumption. -/
theorem fc_mean_le_ceiling {U s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 7/3)
    (hbudget : s+t ≤ (5*U+1)/3) :
    (s+t)/2 ∈ Icc (2:ℝ) (fcShapeCeiling U) := by
  constructor
  · linarith only [hs,hst]
  · unfold fcShapeCeiling
    exact le_min (by linarith only [hst,ht]) (by linarith only [hbudget])

theorem fc_shape_equalization_ceiling {U e s t y E phi : ℝ}
    (hU : 11/5 ≤ U) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 7/3)
    (hbudget : s+t ≤ (5*U+1)/3) (hymax : y ≤ 1/64) (hphi : 0 ≤ phi)
    (hE : E=e-ff_f (s/2)-ff_f (t/2)-phi+s*(1/32-y)+t*y) :
    E ≤ fcShapePairing e (fcShapeCeiling U) := by
  have hmean := fc_mean_le_ceiling hs hst ht hbudget
  have hceiling := fc_shapeCeiling_mem hU
  have hfirst := fc_shape_equalization (c := (1/32:ℝ)) hs hst (by linarith only [hymax]) hphi hE
  have hsecond := fc_shapePairing_mono e ⟨hmean.1,hmean.2.trans hceiling.2⟩ hceiling hmean.2
  dsimp only [fcShapePairing] at hsecond
  rw [show ((s+t)/2)/2=(s+t)/4 by ring] at hsecond
  change E ≤ e-2*ff_f (fcShapeCeiling U/2)+fcShapeCeiling U/32
  linarith only [hfirst,hsecond]

noncomputable def fcLogCorrection (x : ℝ) : ℝ := 2*x^3/(3*(1+x)*(2+x))
noncomputable def fcLogCorrection' (x : ℝ) : ℝ :=
  (2/3)*(1+1/(1+x)^2-8/(2+x)^2)
noncomputable def fcLogCorrection'' (x : ℝ) : ℝ :=
  (4/3)*(8/(2+x)^3-1/(1+x)^3)
noncomputable def fcLogCorrection''' (x : ℝ) : ℝ :=
  4*(1/(1+x)^4-8/(2+x)^4)

/-- The reciprocal-kernel decomposition is used only for differentiation. -/
theorem fc_logCorrection_resolvent {x : ℝ} (hx : 0 ≤ x) :
    fcLogCorrection x=(2/3)*(x-3-1/(1+x)+8/(2+x)) := by
  have hx1 : 1+x ≠ 0 := by linarith only [hx]
  have hx2 : 2+x ≠ 0 := by linarith only [hx]
  unfold fcLogCorrection
  field_simp
  ring

theorem fc_logCorrection_hasDerivAt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt fcLogCorrection (fcLogCorrection' x) x := by
  have hx1 : 1+x ≠ 0 := by linarith only [hx]
  have hx2 : 2+x ≠ 0 := by linarith only [hx]
  have h := ((hasDerivAt_pow 3 x).const_mul 2).div
    ((((hasDerivAt_id x).const_add 1).const_mul 3).mul
      ((hasDerivAt_id x).const_add 2)) (by dsimp; positivity)
  convert h using 1
  · rfl
  · simp only [id_eq,Pi.mul_apply]
    unfold fcLogCorrection'
    field_simp
    ring

/-- Positive reciprocal-integral remainder for the logarithmic correction. -/
theorem fc_logCorrection_remainder_hasDerivAt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x => 2*ff_f (1+x)-fcLogCorrection x)
      (x^4/(3*(1+x)^2*(2+x)^2)) x := by
  have hx1 : 0 < 1+x := by linarith only [hx]
  have hx2 : 0 < 2+x := by linarith only [hx]
  have h := (((fc_f_hasDerivAt hx1).comp x ((hasDerivAt_id x).const_add 1)).const_mul 2).sub
    (fc_logCorrection_hasDerivAt hx)
  convert h using 1
  · rfl
  · unfold fcFPrime fcLogCorrection'
    field_simp
    ring

theorem fc_logCorrection_le {x : ℝ} (hx : 0 ≤ x) :
    fcLogCorrection x ≤ 2*ff_f (1+x) := by
  have h := ff_le_of_deriv (lo := (0:ℝ)) (hi := x) hx
    (f := fun x => 2*ff_f (1+x)-fcLogCorrection x)
    (f' := fun x => x^4/(3*(1+x)^2*(2+x)^2))
    (fun t ht => fc_logCorrection_remainder_hasDerivAt ht.1)
    (fun t ht => by positivity)
  have hzero : 2*ff_f (1+(0:ℝ))-fcLogCorrection 0=0 := by norm_num [ff_f,fcLogCorrection]
  rw [hzero] at h
  linarith only [h]

noncomputable def fcSumMajorant (U : ℝ) : ℝ :=
  ff_e0 U+fcShapeCeiling U/32-fcLogCorrection (fcShapeCeiling U/2-1)
noncomputable def fcScale (U : ℝ) : ℝ := (1+U)^2/(16*U^2)
noncomputable def fcSumCurve (U : ℝ) : ℝ := fcScale U*(75/32-(fcSumMajorant U)^2)

/-- The complete original sum-edge pairing is bounded by the paper's
one-dimensional logarithm-corrected majorant. -/
theorem fc_sum_pairing_le {U z w y E : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3)
    (hbudget : z+w ≤ 5*(U-1)/3) (hy : y ≤ 1/64)
    (hE : E=ff_e0 U-ff_Phi U z w+(1+z)*(1/32-y)+(1+w)*y) :
    E ≤ fcSumMajorant U := by
  have hU0 : 0 < 1+U := by linarith only [hU]
  have hscale : 1 ≤ 4/(1+U) := (le_div_iff₀ hU0).2 (by linarith only [hU3])
  have hphi := fc_f_nonneg_integral hscale
  have hfirst := fc_shape_equalization_ceiling (e := ff_e0 U)
    (s := 1+z) (t := 1+w) (E := E) hU (by linarith only [hz]) (by linarith only [hzw])
    (by linarith only [hw]) (by linarith only [hbudget]) hy hphi
    (by rw [hE]; unfold ff_Phi; ring)
  have hshape := fc_shapeCeiling_mem hU
  have hL := fc_logCorrection_le (by linarith only [hshape.1] : 0 ≤ fcShapeCeiling U/2-1)
  rw [show 1+(fcShapeCeiling U/2-1)=fcShapeCeiling U/2 by ring] at hL
  unfold fcShapePairing at hfirst
  unfold fcSumMajorant
  linarith only [hfirst,hL]

theorem fc_sum_norm_product {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/64) :
    (75/32:ℝ) ≤ 4*(3/4+(1/32-y))*(3/4+y) := by
  have hp := mul_nonneg hy0 (by linarith only [hy1] : 0 ≤ 1/32-y)
  nlinarith only [hp]

/-- The sum-edge curve is a genuine lower bound for the original Casimir,
with no sign assumption on a substituted approximation. -/
theorem fc_sum_curve_lower {U z w y E : ℝ} (hU : 11/5 ≤ U) (hU3 : U ≤ 3)
    (hz : 1 ≤ z) (hzw : z ≤ w) (hw : w ≤ 4/3)
    (hbudget : z+w ≤ 5*(U-1)/3) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/64)
    (hE0 : 0 ≤ E)
    (hE : E=ff_e0 U-ff_Phi U z w+(1+z)*(1/32-y)+(1+w)*y) :
    fcSumCurve U ≤ ff_cas U (3/4+(1/32-y)) (3/4+y) E := by
  have hmajorant := fc_sum_pairing_le hU hU3 hz hzw hw hbudget hy1 hE
  have hM0 : 0 ≤ fcSumMajorant U := hE0.trans hmajorant
  have hsq := (sq_le_sq₀ hE0 hM0).2 hmajorant
  have hprod := fc_sum_norm_product hy0 hy1
  have hscale : 0 ≤ fcScale U := by unfold fcScale; positivity
  have hm := mul_le_mul_of_nonneg_left (by linarith only [hsq,hprod] :
    75/32-(fcSumMajorant U)^2 ≤ 4*(3/4+(1/32-y))*(3/4+y)-E^2) hscale
  unfold fcSumCurve ff_cas fcScale at *
  convert hm using 1; ring

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Forward.Log
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv

/-!
# Shape convexity and the unit boundary of the asymmetric neighbour

Dividing by the positive row multiplier exposes the reciprocal curvature.
The unit-shape boundary is controlled by logarithm bounds.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def asymLogSimpson (q : ℝ) : ℝ :=
  (q-1)*(q^2+10*q+1)/(6*q*(q+1))

/-- The reciprocal Simpson bound, verified by its nonnegative derivative remainder. -/
theorem asym_log_simpson {q : ℝ} (hq : 1 ≤ q) : log q ≤ asymLogSimpson q := by
  exact ff_log_le_simpson hq

/-- A simple lower bound for the opposite floor on the full asymmetric scale interval. -/
theorem asym_opposite_floor_gt {ν : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3) :
    (16/21:ℝ) < ff_F (4/7) (49/(16+9*ν)) := by
  have hd : 0 < 16+9*ν := by linarith only [hν]
  have hr : (49/43:ℝ) ≤ 49/(16+9*ν) := by
    rw [div_le_div_iff₀ (by norm_num) hd]
    nlinarith only [hν3]
  have hm := ff_F_mono (x := (4/7:ℝ)) (by norm_num)
    (r := (49/43:ℝ)) (by norm_num) hr
  have hl := asym_log_simpson (q := (49/43:ℝ)) (by norm_num)
  have hformula : ff_F (4/7) (49/43) = 59/43-(14/3)*log (49/43) := by
    norm_num [ff_F]
    ring
  have hrat : (16/21:ℝ) < 59/43-(14/3)*asymLogSimpson (49/43) := by
    norm_num [asymLogSimpson]
  rw [hformula] at hm
  linarith only [hrat,hl,hm]


/-- The lower logarithm tangent leaves a nonnegative curvature brace. -/
theorem asym_curvature_brace_nonneg {ν x L : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hx : 0 ≤ x) (hx1 : x ≤ 1/2) (hL : x-x^2/2 ≤ L) :
    0 ≤ ν*((1+ν)*x^3+x^2-x+L)-(1+ν)^2*(16/21)*x^3 := by
  have hν0 : 0 ≤ ν := by linarith only [hν]
  have hK : 1+ν ≤ 4 := by linarith only [hν3]
  have hc : (1+ν)*(16-5*ν) ≤ 16 := by
    have hp := mul_le_mul hK (show 16-5*ν ≤ 4 by linarith only [hν])
      (show 0 ≤ 16-5*ν by linarith only [hν3]) (by norm_num : (0:ℝ) ≤ 4)
    norm_num at hp
    exact hp
  have hlog := mul_le_mul_of_nonneg_left hL hν0
  have hcoef := mul_le_mul_of_nonneg_right hc (pow_nonneg hx 3)
  have hshape := mul_le_mul_of_nonneg_left hx1 (sq_nonneg x)
  have hnorm := mul_le_mul_of_nonneg_right hν (sq_nonneg x)
  have hid : ν*((1+ν)*x^3+x^2-x+L)-(1+ν)^2*(16/21)*x^3 =
      ν*(x^2-x+L)-(1+ν)*(16-5*ν)/21*x^3 := by ring
  rw [hid]
  nlinarith only [hlog,hcoef,hshape,hnorm,sq_nonneg x]

end SmoothedOctagon


namespace SmoothedOctagon
open Real

/-- The coefficient of the opposite floor in the neighbour-shape curvature is positive. -/
theorem asym_curvature_coefficient_pos {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    0 < 1/s^3-x^3/(1+s*x)^3 := by
  have hT : 0 < 1+s*x := by positivity
  have hpow : (s*x)^3 < (1+s*x)^3 :=
    pow_lt_pow_left₀ (by linarith) (mul_nonneg hs.le hx) (by norm_num)
  rw [mul_pow] at hpow
  rw [sub_pos,div_lt_div_iff₀ (by positivity) (by positivity)]
  simpa [mul_comm] using hpow

/-- The exact second derivative in the paper, with L=log h and s=1+z. -/
noncomputable def asymUzz (ν s h F L : ℝ) : ℝ :=
  let K := 1+ν
  let x := h-1
  let T := 1+s*x
  2/K*(h-1/h-L)+1/s^2+2*h*K*(F-1)/s^3+
    2*h/(K*T^3)*(ν*(K*x^3+x^2-x+L)-K^2*F*x^3)

/-- Positive row curvature follows from the simple floor and the two logarithm bounds. -/
theorem asymUzz_pos {ν s h F L : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hs : 2 ≤ s) (hh : 1 ≤ h) (hh1 : h ≤ 3/2) (hF : (16/21:ℝ) ≤ F)
    (hLl : h-1-(h-1)^2/2 ≤ L) (hLu : L ≤ h-1) : 0 < asymUzz ν s h F L := by
  let K := 1+ν
  let x := h-1
  let T := 1+s*x
  have hK0 : 0 < K := by dsimp [K]; linarith only [hν]
  have hK4 : K ≤ 4 := by dsimp [K]; linarith only [hν3]
  have hs0 : 0 < s := by linarith only [hs]
  have hh0 : 0 < h := by linarith only [hh]
  have hx : 0 ≤ x := by dsimp [x]; linarith only [hh]
  have hx1 : x ≤ 1/2 := by dsimp [x]; linarith only [hh1]
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hmonoid : asymUzz ν s h F L-asymUzz ν s h (16/21) L =
      2*h*K*(1/s^3-x^3/T^3)*(F-16/21) := by
    dsimp [asymUzz,K,x,T]
    field_simp
    ring
  have hmono : asymUzz ν s h (16/21) L ≤ asymUzz ν s h F L := by
    have hp := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*h*K)
      (asym_curvature_coefficient_pos hs0 hx).le) (sub_nonneg.mpr hF)
    rw [← hmonoid] at hp
    linarith only [hp]
  have hbrace := asym_curvature_brace_nonneg hν hν3 hx hx1 hLl
  have hminid : asymUzz ν s h (16/21) L-
      ((s-10*K/21)/s^3+x*(2/(h*K)-10*K/(21*s^3))) =
      2/K*(x-L)+2*h/(K*T^3)*(ν*(K*x^3+x^2-x+L)-K^2*(16/21)*x^3) := by
    dsimp [asymUzz,K,x,T]
    field_simp
    ring
  have hrem : 0 ≤ asymUzz ν s h (16/21) L-
      ((s-10*K/21)/s^3+x*(2/(h*K)-10*K/(21*s^3))) := by
    rw [hminid]
    exact add_nonneg (mul_nonneg (by positivity) (by dsimp [x]; linarith only [hLu]))
      (mul_nonneg (by positivity) hbrace)
  have hprod : h*K ≤ 6 := by
    have hp := mul_le_mul hh1 hK4 hK0.le (by norm_num : (0:ℝ) ≤ 3/2)
    norm_num at hp
    exact hp
  have hfirst : (1/3:ℝ) ≤ 2/(h*K) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hprod]
  have hcube : (8:ℝ) ≤ s^3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hs 3
    norm_num at hp
    exact hp
  have hsecond : 10*K/(21*s^3) ≤ (5/21:ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hK4,hcube]
  have hpositive : 0 < (s-10*K/21)/s^3 := by
    exact div_pos (by linarith only [hs,hK4]) (by positivity)
  have hnonneg : 0 ≤ x*(2/(h*K)-10*K/(21*s^3)) :=
    mul_nonneg hx (by linarith only [hfirst,hsecond])
  linarith only [hpositive,hnonneg,hrem,hmono]

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set

/-- The natural rational majorant for the derivative on the unit-shape boundary. -/
noncomputable def asymUnitSlopeBound (q : ℝ) : ℝ :=
  12*q/7-4*(q-1)/(q+1)-71/42-(2*q-1)/(36*q)
noncomputable def asymUnitSlopeBound' (q : ℝ) : ℝ :=
  12/7-8/(q+1)^2-1/(36*q^2)
noncomputable def asymUnitSlopeBound'' (q : ℝ) : ℝ :=
  16/(q+1)^3+1/(18*q^3)

theorem asymUnitSlopeBound_deriv {q : ℝ} (hq : 0 < q) :
    HasDerivAt asymUnitSlopeBound (asymUnitSlopeBound' q) q := by
  have hp : q+1 ≠ 0 := by positivity
  have hd := ((((hasDerivAt_id q).const_mul 12).div_const 7).sub
    ((((hasDerivAt_id q).sub_const 1).const_mul 4).div ((hasDerivAt_id q).add_const 1) hp)).sub_const (71/42)
  have he := hd.sub ((((hasDerivAt_id q).const_mul 2).sub_const 1).div
    ((hasDerivAt_id q).const_mul 36) (by change 36*q ≠ 0; positivity))
  convert he using 1
  · rfl
  · dsimp [asymUnitSlopeBound']; field_simp; ring

theorem asymUnitSlopeBound_second {q : ℝ} (hq : 0 < q) :
    HasDerivAt asymUnitSlopeBound' (asymUnitSlopeBound'' q) q := by
  have hp : q+1 ≠ 0 := by positivity
  have hd := ((hasDerivAt_const q (12/7)).sub
    ((hasDerivAt_const q 8).div (((hasDerivAt_id q).add_const 1).pow 2) (pow_ne_zero 2 hp))).sub
    ((hasDerivAt_const q 1).div (((hasDerivAt_id q).pow 2).const_mul 36) (by change 36*q^2 ≠ 0; positivity))
  convert hd using 1
  · rfl
  · dsimp [asymUnitSlopeBound'']; field_simp; ring

theorem asymUnitSlopeBound_neg {q : ℝ} (hq : 7/6 ≤ q) (hq1 : q ≤ 70/51) :
    asymUnitSlopeBound q < 0 := by
  have hc : ConvexOn ℝ (Icc (7/6:ℝ) (70/51)) asymUnitSlopeBound := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun x hx => (asymUnitSlopeBound_deriv (by linarith only [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => (asymUnitSlopeBound_deriv (by
        have hi := interior_subset hx; linarith only [hi.1])).hasDerivWithinAt)
      (fun x hx => (asymUnitSlopeBound_second (by
        have hi := interior_subset hx; linarith only [hi.1])).hasDerivWithinAt) ?_
    intro x hx
    have hi := interior_subset hx
    have hx0 : 0 < x := by linarith only [hi.1]
    dsimp [asymUnitSlopeBound'']; positivity
  have hleft : asymUnitSlopeBound (7/6) < 0 := by norm_num [asymUnitSlopeBound]
  have hright : asymUnitSlopeBound (70/51) < 0 := by norm_num [asymUnitSlopeBound]
  exact (hc.le_max_of_mem_Icc (by norm_num) (by norm_num) ⟨hq,hq1⟩).trans_lt (max_lt hleft hright)

/-- The endpoint value uses just the strict floor and the reciprocal midpoint bound. -/
theorem asym_unit_initial_neg {q F : ℝ} (hq : 7/6 ≤ q) (hq1 : q ≤ 7/5)
    (hF : 16/21 < F) :
    (q-1)*(7*(1-F)/(3*q)+3/7)-log q < 0 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hqp : 0 < q+1 := by positivity
  have hqsub : 0 < q-1 := by linarith only [hq]
  have hfloor : 7*(1-F)/(3*q) < 5/(9*q) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hF,hq0]
  have hpoly : 27*q^2-64*q+35 < 0 := by
    have hp := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hq1)
    nlinarith only [hp,hq,hq1]
  have hbrace : 5/(9*q)+3/7-2/(q+1) < 0 := by
    have he : 5/(9*q)+3/7-2/(q+1) = (27*q^2-64*q+35)/(63*q*(q+1)) := by
      field_simp; ring
    rw [he]
    exact div_neg_of_neg_of_pos hpoly (by positivity)
  have hl := ff_log_ge_two (by linarith only [hq] : 1 ≤ q)
  have hm := mul_lt_mul_of_pos_left hfloor hqsub
  have hn := mul_neg_of_pos_of_neg hqsub hbrace
  have he : (q-1)*(5/(9*q)+3/7)-2*((q-1)/(q+1)) =
      (q-1)*(5/(9*q)+3/7-2/(q+1)) := by ring
  linarith only [hl,hm,hn,he]

end SmoothedOctagon


namespace SmoothedOctagon
open Real

/-- Completing a square bounds the two reciprocal terms in the unit-shape slope. -/
theorem asym_unit_reciprocal_bound {K h : ℝ} (hK : 0 < K) (hh : 0 < h) :
    1/h-2/(K*h^2) ≤ K/8 := by
  have he : K/8-(1/h-2/(K*h^2)) = (K*h-4)^2/(8*K*h^2) := by
    field_simp; ring
  have hn : 0 ≤ K/8-(1/h-2/(K*h^2)) := by rw [he]; positivity
  linarith only [hn]

/-- The original unit-shape row has negative slope for every h≥1. -/
theorem asym_unit_slope_neg {K h F : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4)
    (hh : 1 ≤ h) (hF : 16/21 < F) :
    2*(101/42+1/K-log (14/(3*K)))-K/2-2/(K*h^2)+1/h-
      (1-2/K)*(1+2*h-2*log h)-(14/3-K/2)*F < 0 := by
  have hK0 : 0 < K := by linarith only [hK]
  have hh0 : 0 < h := by linarith only [hh]
  let q := 14/(3*K)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq : 7/6 ≤ q := by dsimp [q]; rw [le_div_iff₀ (by positivity)]; linarith only [hK4]
  have hq1 : q ≤ 70/51 := by dsimp [q]; rw [div_le_iff₀ (by positivity)]; linarith only [hK]
  have hqL := ff_log_ge_two (by linarith only [hq] : 1 ≤ q)
  have hR := asymUnitSlopeBound_neg hq hq1
  have hpair := asym_unit_reciprocal_bound hK0 hh0
  have hlog := log_le_sub_one_of_pos hh0
  have hc : 0 ≤ 1-2/K := by rw [sub_nonneg,div_le_one hK0]; linarith only [hK]
  have hcm := mul_le_mul_of_nonneg_left
    (show (3:ℝ) ≤ 1+2*h-2*log h by linarith only [hlog]) hc
  have hb : 0 < 14/3-K/2 := by linarith only [hK4]
  have hbm := mul_lt_mul_of_pos_left hF hb
  have he : 2*(101/42+1/K-log q)-K/2+K/8-3*(1-2/K)-
      (14/3-K/2)*(16/21) =
      asymUnitSlopeBound q+4*(q-1)/(q+1)-2*log q := by
    dsimp [asymUnitSlopeBound,q]
    field_simp
    ring
  change 2*(101/42+1/K-log q)-K/2-2/(K*h^2)+1/h-
      (1-2/K)*(1+2*h-2*log h)-(14/3-K/2)*F < 0
  have hqL1 : 4*(q-1)/(q+1) ≤ 2*log q := by
    calc 4*(q-1)/(q+1) = 2*(2*((q-1)/(q+1))) := by ring
         _ ≤ 2*log q := mul_le_mul_of_nonneg_left hqL (by norm_num)
  linarith only [hR,hpair,hqL1,hcm,hbm,he]

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set

noncomputable def asymUnitRow (K F h : ℝ) : ℝ :=
  (2*h-1)*(101/42+1/K-log (14/(3*K)))-
    (K*h/2+1/2-2/(K*h)+1/K-log h)-
    (1-2/K)*(4*(h-1)+h*(h-1)-2*h*log h)-
    K/2*(14/(3*K)-1+(h-1)*(2*(14/(3*K))-1))*F

noncomputable def asymUnitRow' (K F h : ℝ) : ℝ :=
  2*(101/42+1/K-log (14/(3*K)))-K/2-2/(K*h^2)+1/h-
    (1-2/K)*(1+2*h-2*log h)-(14/3-K/2)*F

/-- The continuous original row has precisely the slope used in the boundary argument. -/
theorem asymUnitRow_deriv {K F h : ℝ} (hK : 0 < K) (hh : 0 < h) :
    HasDerivAt (asymUnitRow K F) (asymUnitRow' K F h) h := by
  have hi := hasDerivAt_id h
  have hl := hasDerivAt_log hh.ne'
  have hA := ((hi.const_mul 2).sub_const 1).mul_const (101/42+1/K-log (14/(3*K)))
  have hB := (((hi.const_mul K).div_const 2).add_const (1/2)).sub
    ((hasDerivAt_const h 2).div (hi.const_mul K) (by change K*h ≠ 0; positivity))
  have hB1 := (hB.add_const (1/K)).sub hl
  have hC := ((((hi.sub_const 1).const_mul 4).add (hi.mul (hi.sub_const 1))).sub
    ((hi.const_mul 2).mul hl)).const_mul (1-2/K)
  have hD := ((((hi.sub_const 1).mul_const (2*(14/(3*K))-1)).const_add (14/(3*K)-1)).const_mul (K/2)).mul_const F
  have hd := ((hA.sub hB1).sub hC).sub hD
  convert hd using 1
  · rfl
  · dsimp [asymUnitRow']; field_simp; ring

theorem asymUnitRow_at_one {K F : ℝ} (hK : 0 < K) :
    asymUnitRow K F 1 =
      (14/(3*K)-1)*(7*(1-F)/(3*(14/(3*K)))+3/7)-log (14/(3*K)) := by
  dsimp [asymUnitRow]
  rw [log_one]
  field_simp; ring

/-- The unit-shape boundary is negative on the whole positive factor ray h≥1. -/
theorem asymUnitRow_neg {K F h : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4)
    (hh : 1 ≤ h) (hF : 16/21 < F) : asymUnitRow K F h < 0 := by
  have hK0 : 0 < K := by linarith only [hK]
  have hq : 7/6 ≤ 14/(3*K) := by
    rw [le_div_iff₀ (by positivity)]; linarith only [hK4]
  have hq1 : 14/(3*K) ≤ 7/5 := by
    rw [div_le_iff₀ (by positivity)]; linarith only [hK]
  have hinit : asymUnitRow K F 1 < 0 := by
    rw [asymUnitRow_at_one hK0]
    exact asym_unit_initial_neg hq hq1 hF
  have hm := ff_le_of_deriv (f := fun x => -asymUnitRow K F x)
    (f' := fun x => -asymUnitRow' K F x) hh
    (fun x hx => (asymUnitRow_deriv hK0 (by linarith only [hx.1])).neg)
    (fun x hx => by
      have hs := asym_unit_slope_neg hK hK4 hx.1 hF
      change 0 ≤ -asymUnitRow' K F x
      dsimp [asymUnitRow']
      linarith only [hs])
  linarith only [hm,hinit]

end SmoothedOctagon


namespace SmoothedOctagon
open Real

/-- The original row with its removable factor singularity already cancelled. -/
noncomputable def asymContinuousRow (ν z h F : ℝ) : ℝ :=
  ff_alpha ν z h*ff_A ν z (4/3)-ff_B ν z h-
    (1+z)^2*(ν-z)/(z^2+ν)*
      ((h-1)+(z/(1+z))^2*h*(h-1)-z/(1+z)*h*log h)-
    ff_m ν z (4/3) h*F

theorem asymContinuousRow_eq_original {ν z h : ℝ} (hν : 0 < ν)
    (hz : 0 < z) (hh1 : h ≠ 1) :
    ff_resN ν z (4/3) h = asymContinuousRow ν z h
      (ff_F ((4/3)/(1+4/3)) ((1+4/3)^2/((4/3)^2+ν))) := by
  have hs : 0 < 1+z := by positivity
  have hZ : 0 < z^2+ν := by positivity
  have hx : h-1 ≠ 0 := sub_ne_zero.mpr hh1
  unfold ff_resN asymContinuousRow ff_n ff_F
  field_simp

theorem asymContinuousRow_unit {ν h F : ℝ} (hν : 0 < ν) (hh : 0 < h) :
    asymContinuousRow ν 1 h F = asymUnitRow (1+ν) F h := by
  have hK : 0 < 1+ν := by positivity
  have hq : ff_q ν 1 (4/3) = 14/(3*(1+ν)) := by unfold ff_q; field_simp; ring
  unfold asymContinuousRow
  unfold ff_A
  rw [hq]
  unfold ff_alpha ff_B ff_m ff_q asymUnitRow
  field_simp; ring

/-- The actual asymmetric row is negative on the complete unit-shape boundary. -/
theorem asym_original_unit_neg {ν h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hh : 1 < h) : ff_resN ν 1 (4/3) h < 0 := by
  have hν0 : 0 < ν := by linarith only [hν]
  rw [asymContinuousRow_eq_original hν0 (by norm_num) hh.ne']
  rw [asymContinuousRow_unit hν0 (by linarith only [hh])]
  apply asymUnitRow_neg (by linarith only [hν]) (by linarith only [hν3]) hh.le
  have he : ff_F ((4/3)/(1+4/3)) ((1+4/3)^2/((4/3)^2+ν)) =
      ff_F (4/7) (49/(16+9*ν)) := by
    congr 1 <;> field_simp <;> ring
  rw [he]
  exact asym_opposite_floor_gt hν hν3

end SmoothedOctagon

namespace SmoothedOctagon
open Real Polynomial

/-- The original normalized row's denominator, kept as a product. -/
noncomputable def asymRowDenom (ν h : ℝ) : ℝ[X] :=
  C ((1+ν)*h)*X*(1+C (h-1)*X)

/-- Clearing only the row denominators gives this unexpanded polynomial numerator.
Polynomial differentiation records the product and quotient rules. -/
noncomputable def asymRowNumerator (ν h F L : ℝ) : ℝ[X] :=
  let z : ℝ[X] := X-1
  let Z := z^2+C ν
  let K := 1+ν
  let q : ℝ[X] := C (7/(3*K))*X
  let T : ℝ[X] := 1+C (h-1)*X
  asymRowDenom ν h*(z+C (40/21+1/K))-C (K*h)*T-
    (C (h^2)*Z^2+C h*X*Z-z^2*X^2-C h*z^2*Z+C h*z^3*X-C (h*L)*z*Z*X)-
    C h*X*(C ν-z)*(C (h-1)*X^2+C (h*(h-1))*z^2-C (h*L)*z*X)-
    C (h*K^2*F)*(q-1+C (h-1)*(q*X-1))

noncomputable def asymRationalLog (p d : ℝ[X]) (s : ℝ) : ℝ :=
  p.eval s/d.eval s-log s
noncomputable def asymRationalLog' (p d : ℝ[X]) (s : ℝ) : ℝ :=
  (p.derivative*d-p*d.derivative).eval s/(d.eval s)^2-1/s
noncomputable def asymRationalLog'' (p d : ℝ[X]) (s : ℝ) : ℝ :=
  (p.derivative.derivative*d-p*d.derivative.derivative).eval s/(d.eval s)^2-
    2*(p.derivative*d-p*d.derivative).eval s*d.derivative.eval s/(d.eval s)^3+1/s^2

theorem asymRationalLog_deriv (p d : ℝ[X]) {s : ℝ} (hs : 0 < s) (hd : d.eval s ≠ 0) :
    HasDerivAt (asymRationalLog p d) (asymRationalLog' p d s) s := by
  have he := ((p.hasDerivAt s).div (d.hasDerivAt s) hd).sub (hasDerivAt_log hs.ne')
  convert he using 1
  · rfl
  · simp [asymRationalLog',Polynomial.eval_sub,Polynomial.eval_mul]

theorem asymRationalLog_second (p d : ℝ[X]) {s : ℝ} (hs : 0 < s) (hd : d.eval s ≠ 0) :
    HasDerivAt (asymRationalLog' p d) (asymRationalLog'' p d s) s := by
  let N := p.derivative*d-p*d.derivative
  have he := ((N.hasDerivAt s).div ((d.hasDerivAt s).pow 2) (pow_ne_zero 2 hd)).sub
    ((hasDerivAt_const s 1).div (hasDerivAt_id s) hs.ne')
  convert he using 1
  · rfl
  · dsimp [asymRationalLog'',N]
    simp only [Polynomial.derivative_sub,Polynomial.derivative_mul,
      Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_add]
    field_simp; ring

/-- The second neighbour-shape derivative of the normalized row. -/
theorem asymRow_curvature_identity {ν h F L s : ℝ} (hν : 0 < 1+ν)
    (hh : 0 < h) (hs : 0 < s) (hT : 0 < 1+(h-1)*s) :
    asymRationalLog'' (asymRowNumerator ν h F L) (asymRowDenom ν h) s =
      asymUzz ν s h F L := by
  dsimp [asymRationalLog'',asymRowNumerator,asymRowDenom]
  simp only [Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_mul,
    Polynomial.derivative_pow,Polynomial.derivative_C,Polynomial.derivative_X,
    Polynomial.derivative_one,Polynomial.derivative_zero,
    Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_zero,add_zero,zero_add,mul_zero,zero_mul,mul_one]
  dsimp [asymUzz]
  field_simp; ring

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set Polynomial

noncomputable def asymNormalizedRow (ν h F s : ℝ) : ℝ :=
  asymRationalLog (asymRowNumerator ν h F (log h)) (asymRowDenom ν h) s+
    log (3*(1+ν)/7)

/-- The polynomial quotient is exactly the original row divided by its positive multiplier. -/
theorem asymNormalizedRow_eq {ν h F z : ℝ} (hν : 0 < ν) (hh : 1 ≤ h) (hz : 0 < z) :
    asymNormalizedRow ν h F (1+z) = asymContinuousRow ν z h F/ff_alpha ν z h := by
  have hK : 0 < 1+ν := by positivity
  have hS : 0 < 1+z := by positivity
  have hh0 : 0 < h := by linarith only [hh]
  have hZ : 0 < z^2+ν := by positivity
  have hT : 0 < h*(1+z)-z := by nlinarith only [hh,hz]
  have hC : 0 < 3*(1+ν)/7 := by positivity
  have hq : ff_q ν z (4/3) = (1+z)/(3*(1+ν)/7) := by
    unfold ff_q; field_simp; ring
  have hlog : log (ff_q ν z (4/3)) = log (1+z)-log (3*(1+ν)/7) := by
    rw [hq,log_div hS.ne' hC.ne']
  unfold asymNormalizedRow asymRationalLog
  dsimp [asymRowNumerator,asymRowDenom]
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  unfold asymContinuousRow ff_A
  rw [hlog]
  unfold ff_alpha ff_B ff_m ff_q
  field_simp; ring

theorem asym_log_lower {h : ℝ} (hh : 1 ≤ h) : h-1-(h-1)^2/2 ≤ log h := by
  have hh1 : 0 ≤ h-1 := by linarith only [hh]
  have hp : 0 < h+1 := by linarith only [hh]
  have he : 2*((h-1)/(h+1))-(h-1-(h-1)^2/2) = (h-1)^3/(2*(h+1)) := by
    field_simp; ring
  have hn : 0 ≤ 2*((h-1)/(h+1))-(h-1-(h-1)^2/2) := by rw [he]; positivity
  have hl := ff_log_ge_two hh
  linarith only [hn,hl]

theorem asym_row_denom_pos {ν h s : ℝ} (hν : 0 < 1+ν) (hh : 1 ≤ h) (hs : 0 < s) :
    0 < (asymRowDenom ν h).eval s := by
  have hh0 : 0 < h := by linarith only [hh]
  have hx : 0 ≤ h-1 := by linarith only [hh]
  simp only [asymRowDenom,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X]
  positivity

/-- The actual normalized neighbour row is convex in the shape on the full rectangle. -/
theorem asymNormalizedRow_convex {ν h F : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hh : 1 ≤ h) (hh1 : h ≤ 3/2) (hF : 16/21 ≤ F) :
    ConvexOn ℝ (Icc (2:ℝ) (7/3)) (asymNormalizedRow ν h F) := by
  have hK : 0 < 1+ν := by linarith only [hν]
  have hh0 : 0 < h := by linarith only [hh]
  have hd : ∀ s ∈ Icc (2:ℝ) (7/3),
      HasDerivAt (asymNormalizedRow ν h F)
        (asymRationalLog' (asymRowNumerator ν h F (log h)) (asymRowDenom ν h) s) s := by
    intro s hs
    exact (asymRationalLog_deriv _ _ (by linarith only [hs.1])
      (asym_row_denom_pos hK hh (by linarith only [hs.1])).ne').add_const _
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
    (fun s hs => (asymRationalLog_second _ _ (by
      have hi := interior_subset hs; linarith only [hi.1])
      (asym_row_denom_pos hK hh (by
        have hi := interior_subset hs; linarith only [hi.1])).ne').hasDerivWithinAt) ?_
  intro s hs
  have hi := interior_subset hs
  have hs0 : 0 < s := by linarith only [hi.1]
  have hT : 0 < 1+(h-1)*s := by
    have hx : 0 ≤ h-1 := by linarith only [hh]
    positivity
  rw [asymRow_curvature_identity hK hh0 hs0 hT]
  exact (asymUzz_pos hν hν3 hi.1 hh hh1 hF (asym_log_lower hh)
    (log_le_sub_one_of_pos hh0)).le

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set

/-- Shape convexity and the unit boundary reduce the original row to its symmetric edge. -/
theorem asymContinuousRow_neg_of_symmetric {ν z h F : ℝ} (hν : 12/5 ≤ ν)
    (hν3 : ν ≤ 3) (hz : 1 ≤ z) (hz1 : z ≤ 4/3) (hh : 1 ≤ h) (hh1 : h ≤ 3/2)
    (hF : 16/21 < F) (hedge : asymContinuousRow ν (4/3) h F < 0) :
    asymContinuousRow ν z h F < 0 := by
  have hν0 : 0 < ν := by linarith only [hν]
  have hh0 : 0 < h := by linarith only [hh]
  have hpos : ∀ y : ℝ, 0 < y → 0 < ff_alpha ν y h := by
    intro y hy
    have hT : 0 < h*(1+y)-y := by nlinarith only [hh,hy]
    dsimp [ff_alpha]
    positivity
  have hleft : asymNormalizedRow ν h F 2 < 0 := by
    have he := asymNormalizedRow_eq (F := F) hν0 hh (by norm_num : (0:ℝ) < 1)
    norm_num only at he
    rw [he,asymContinuousRow_unit hν0 hh0]
    exact div_neg_of_neg_of_pos
      (asymUnitRow_neg (by linarith only [hν]) (by linarith only [hν3]) hh hF)
      (hpos 1 (by norm_num))
  have hright : asymNormalizedRow ν h F (7/3) < 0 := by
    have he := asymNormalizedRow_eq (F := F) hν0 hh (by norm_num : (0:ℝ) < 4/3)
    norm_num only at he
    rw [he]
    exact div_neg_of_neg_of_pos hedge (hpos (4/3) (by norm_num))
  have hc := asymNormalizedRow_convex hν hν3 hh hh1 hF.le
  have he := hc.le_max_of_mem_Icc (by norm_num) (by norm_num)
    (show 1+z ∈ Icc (2:ℝ) (7/3) by constructor <;> linarith)
  have hn : asymNormalizedRow ν h F (1+z) < 0 := he.trans_lt (max_lt hleft hright)
  rw [asymNormalizedRow_eq hν0 hh (by linarith only [hz])] at hn
  have he := (div_lt_iff₀ (hpos z (by linarith only [hz]))).mp hn
  simpa only [zero_mul] using he

end SmoothedOctagon

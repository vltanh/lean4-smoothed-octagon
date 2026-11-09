module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Moments
public import SmoothedOctagon.Exclusion.Forward.Log
public import Mathlib.Analysis.Convex.Deriv

/-!
# Scale convexity on the symmetric neighbour boundary

The opposite floor has small first and second derivatives. Subtracting
the logarithm leaves a convex row, and a quadratic chord controls its loss.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def asymScaleT (K : ℝ) : ℝ := (42-9*K)/49
noncomputable def asymScaleFloor (K : ℝ) : ℝ := asymFloorT (asymScaleT K)
noncomputable def asymScaleFloor' (K : ℝ) : ℝ := -(9/49)*asymFloorT1 (asymScaleT K)
noncomputable def asymScaleFloor'' (K : ℝ) : ℝ := (9/49)^2*asymFloorT2 (asymScaleT K)

theorem asym_scaleT_bounds {K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    0 < asymScaleT K ∧ asymScaleT K ≤ 1/4 := by
  unfold asymScaleT
  constructor <;> linarith only [hK,hK4]

/-- The actual opposite floor in the reciprocal integral coordinate. -/
theorem asym_scaleFloor_eq {K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    asymScaleFloor K = ff_F (4/7) (49/(7+9*K)) := by
  have hd : 0 < 7+9*K := by linarith only [hK]
  have hdiff : 42-9*K ≠ 0 := by linarith only [hK4]
  have ht : 1-asymScaleT K = (7+9*K)/49 := by unfold asymScaleT; ring
  unfold asymScaleFloor asymFloorT
  rw [ht,log_div hd.ne' (by norm_num)]
  unfold ff_F
  rw [log_div (by norm_num) hd.ne']
  unfold asymScaleT
  field_simp [hd.ne',hdiff]
  field_simp [show 42-K*9 ≠ 0 by linarith only [hK4]]
  ring_nf
  field_simp [show 42-K*9 ≠ 0 by linarith only [hK4]]
  ring

theorem asym_scaleFloor_hasDerivAt {K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    HasDerivAt asymScaleFloor (asymScaleFloor' K) K := by
  obtain ⟨ht,ht1⟩ := asym_scaleT_bounds hK hK4
  have he := (asymFloorT_deriv1 ht (by linarith only [ht1])).comp K
    ((((hasDerivAt_id K).const_mul (9:ℝ)).const_sub 42).div_const 49)
  convert he using 1
  · rfl
  · unfold asymScaleFloor'
    ring

theorem asym_scaleFloor_second {K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    HasDerivAt asymScaleFloor' (asymScaleFloor'' K) K := by
  obtain ⟨ht,ht1⟩ := asym_scaleT_bounds hK hK4
  have he := ((asymFloorT_deriv2 ht (by linarith only [ht1])).comp K
    ((((hasDerivAt_id K).const_mul (9:ℝ)).const_sub 42).div_const 49)).const_mul (-(9/49):ℝ)
  convert he using 1
  · rfl
  · unfold asymScaleFloor''
    ring

/-- The first two scale losses follow from weighted reciprocal means. -/
theorem asym_scaleFloor_bounds {K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    -(1/30:ℝ) < asymScaleFloor' K ∧ asymScaleFloor' K < 0 ∧
    0 < asymScaleFloor'' K ∧ asymScaleFloor'' K < 1/32 := by
  obtain ⟨ht,ht1⟩ := asym_scaleT_bounds hK hK4
  have hp := asymFloorT1_pos ht (by linarith only [ht1])
  have hpp := asymFloorT2_pos ht (by linarith only [ht1])
  have hc := asym_floor_first_cap ht ht1
  have hcc := asym_floor_second_cap ht ht1
  dsimp [asymScaleFloor',asymScaleFloor'']
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [hc]
  · nlinarith only [hp]
  · nlinarith only [hpp]
  · exact hcc

noncomputable def asymScaleD (h : ℝ) : ℝ := 9*h/(7*(7*h-4))
noncomputable def asymScaleC (h : ℝ) : ℝ :=
  7*(16*h^3+41*h^2-64*h+16-4*h*(7*h-1)*log h)/(9*h*(7*h-4))

theorem asym_scaleD_bounds {h : ℝ} (hh : 1 ≤ h) (hh1 : h ≤ 3/2) :
    27/91 ≤ asymScaleD h ∧ asymScaleD h ≤ 3/7 := by
  have hd : 0 < 7*(7*h-4) := by linarith only [hh]
  unfold asymScaleD
  constructor
  · rw [le_div_iff₀ hd]; linarith only [hh1]
  · rw [div_le_iff₀ hd]; linarith only [hh]

/-- The scalar reciprocal-log remainder controls the inverse-scale coefficient. -/
theorem asym_scaleC_ge {h : ℝ} (hh : 1 ≤ h) : 7/3 ≤ asymScaleC h := by
  have hh0 : 0 < h := by linarith only [hh]
  have h7 : 0 < 7*h-4 := by linarith only [hh]
  have h7a : 0 < 7*h-1 := by linarith only [hh]
  have hhsub : 0 ≤ h-1 := by linarith only [hh]
  have hd : 0 < 9*h*(7*h-4) := by positivity
  have hf := ff_f_nonneg hh
  have hl : log h ≤ (h-1/h)/2 := by
    dsimp [ff_f] at hf
    simpa only [one_div] using (show log h ≤ (h-h⁻¹)/2 by linarith only [hf])
  have hc : 0 ≤ 4*h*(7*h-1) := by positivity
  have hm := mul_le_mul_of_nonneg_left hl hc
  have he : asymScaleC h-7/3-
      14*(h-1)*(h^2+12*h-7)/(9*h*(7*h-4)) =
      28*h*(7*h-1)*((h-1/h)/2-log h)/(9*h*(7*h-4)) := by
    unfold asymScaleC
    field_simp [hh0.ne',h7.ne']
    ring
  have hp : 0 ≤ 14*(h-1)*(h^2+12*h-7)/(9*h*(7*h-4)) := by
    have hp : 0 ≤ h^2+12*h-7 := by nlinarith only [hh,sq_nonneg h]
    positivity
  have hr : 0 ≤ 28*h*(7*h-1)*((h-1/h)/2-log h)/(9*h*(7*h-4)) := by
    have hlog : 0 ≤ (h-1/h)/2-log h := sub_nonneg.mpr hl
    positivity
  linarith only [he,hp,hr]

end SmoothedOctagon


namespace SmoothedOctagon
open Real Set

noncomputable def asymScaleB (h : ℝ) : ℝ :=
  (196*h*log h+84*log h-112*h^2+140*h+92)/(147*h-84)-log (49/9)

noncomputable def asymSymNormalized (K h : ℝ) : ℝ :=
  let z : ℝ := 4/3
  let ν := K-1
  (ff_alpha ν z h*ff_A ν z z-ff_B ν z h-
    (1+z)^2*(ν-z)/(z^2+ν)*
      ((h-1)+(z/(1+z))^2*h*(h-1)-z/(1+z)*h*log h)-
    ff_m ν z z h*asymScaleFloor K)/ff_alpha ν z h

noncomputable def asymScaleModel (h K : ℝ) : ℝ :=
  -asymScaleD h*K+asymScaleB h+asymScaleC h/K+
    (asymScaleD h*K-7/3)*asymScaleFloor K
noncomputable def asymScaleModel' (h K : ℝ) : ℝ :=
  -asymScaleD h-asymScaleC h/K^2+asymScaleD h*asymScaleFloor K+
    (asymScaleD h*K-7/3)*asymScaleFloor' K
noncomputable def asymScaleModel'' (h K : ℝ) : ℝ :=
  2*asymScaleC h/K^3+2*asymScaleD h*asymScaleFloor' K+
    (asymScaleD h*K-7/3)*asymScaleFloor'' K

/-- Collecting the scale in the actual normalized stationarity row. -/
theorem asym_sym_scale_identity {K h : ℝ} (hK : 17/5 ≤ K) (hh : 1 ≤ h) :
    asymSymNormalized K h-log K = asymScaleModel h K := by
  have hK0 : 0 < K := by linarith only [hK]
  have hh0 : 0 < h := by linarith only [hh]
  have hT : 0 < 7*h-4 := by linarith only [hh]
  have hZ : 0 < (4/3:ℝ)^2+(K-1) := by linarith only [hK]
  have hq : ff_q (K-1) (4/3) (4/3) = (49/9)/K := by unfold ff_q; field_simp [hK0.ne']; ring
  dsimp only [asymSymNormalized]
  unfold ff_A
  rw [hq,log_div (by norm_num : (49/9:ℝ) ≠ 0) hK0.ne']
  unfold ff_alpha ff_B ff_m ff_q asymScaleModel asymScaleD asymScaleB asymScaleC
  field_simp [hK0.ne',hh0.ne',hT.ne',hZ.ne']
  ring_nf
  field_simp [show -4+h*7 ≠ 0 by linarith only [hh],show -84+h*147 ≠ 0 by linarith only [hh]]
  ring

theorem asym_scaleModel_hasDerivAt {h K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    HasDerivAt (asymScaleModel h) (asymScaleModel' h K) K := by
  have hK0 : 0 < K := by linarith only [hK]
  have hi := hasDerivAt_id K
  have hF := asym_scaleFloor_hasDerivAt hK hK4
  have he := ((((hi.const_mul (-asymScaleD h)).add_const (asymScaleB h)).add
    ((hasDerivAt_const K (asymScaleC h)).div hi hK0.ne')).add
    (((hi.const_mul (asymScaleD h)).sub_const (7/3:ℝ)).mul hF))
  convert he using 1
  · rfl
  · dsimp [asymScaleModel']; field_simp; ring

theorem asym_scaleModel_second {h K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) :
    HasDerivAt (asymScaleModel' h) (asymScaleModel'' h K) K := by
  have hK0 : 0 < K := by linarith only [hK]
  have hi := hasDerivAt_id K
  have hF := asym_scaleFloor_hasDerivAt hK hK4
  have hF' := asym_scaleFloor_second hK hK4
  have he := ((((hasDerivAt_const K (-asymScaleD h)).sub
    ((hasDerivAt_const K (asymScaleC h)).div (hi.pow 2) (pow_ne_zero 2 hK0.ne'))).add
    (hF.const_mul (asymScaleD h))).add
    (((hi.const_mul (asymScaleD h)).sub_const (7/3:ℝ)).mul hF'))
  convert he using 1
  · rfl
  · dsimp [asymScaleModel'']; field_simp; ring

/-- The scale curvature is positive from three natural reciprocal bounds. -/
theorem asym_scaleModel_second_pos {h K : ℝ} (hh : 1 ≤ h) (hh1 : h ≤ 3/2)
    (hK : 17/5 ≤ K) (hK4 : K ≤ 4) : 0 < asymScaleModel'' h K := by
  have hK0 : 0 < K := by linarith only [hK]
  have hc := asym_scaleC_ge hh
  obtain ⟨hdlo,hdhi⟩ := asym_scaleD_bounds hh hh1
  obtain ⟨hflo,hfhi,hfflo,hffhi⟩ := asym_scaleFloor_bounds hK hK4
  have hd0 : 0 < asymScaleD h := by linarith only [hdlo]
  have hdKlo : 1 < asymScaleD h*K := by
    have hp := mul_le_mul hdlo hK (by linarith only [hK]) hd0.le
    nlinarith only [hp]
  have hdKhi : asymScaleD h*K < 7/3 := by
    have hp := mul_le_mul hdhi hK4 (by linarith only [hK]) (by norm_num : (0:ℝ) ≤ 3/7)
    nlinarith only [hp]
  have hK3 : K^3 ≤ 4^3 := pow_le_pow_left₀ hK0.le hK4 3
  have hfirst : (7/96:ℝ) ≤ 2*asymScaleC h/K^3 := by
    rw [le_div_iff₀ (by positivity : 0 < K^3)]
    nlinarith only [hc,hK3]
  have hfloor : -(1/24:ℝ) < (asymScaleD h*K-7/3)*asymScaleFloor'' K := by
    have hp := mul_lt_mul_of_pos_left hffhi (by linarith only [hdKhi] : 0 < 7/3-asymScaleD h*K)
    have hr : 7/3-asymScaleD h*K < 4/3 := by linarith only [hdKlo]
    nlinarith only [hp,hr]
  have hlinear : -(1/35:ℝ) < 2*asymScaleD h*asymScaleFloor' K := by
    have hp := mul_lt_mul_of_pos_left hflo (by positivity : 0 < 2*asymScaleD h)
    nlinarith only [hp,hdhi]
  dsimp [asymScaleModel'']
  linarith only [hfirst,hfloor,hlinear]

/-- Convexity in scale leaves only the two scale endpoints and the logarithmic chord. -/
theorem asym_scaleModel_convex {h : ℝ} (hh : 1 ≤ h) (hh1 : h ≤ 3/2) :
    ConvexOn ℝ (Icc (17/5) 4) (asymScaleModel h) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := asymScaleModel' h) (f'' := asymScaleModel'' h) (convex_Icc _ _)
  · intro K hK
    exact (asym_scaleModel_hasDerivAt hK.1 hK.2).continuousAt.continuousWithinAt
  · intro K hK
    exact (asym_scaleModel_hasDerivAt (interior_subset hK).1 (interior_subset hK).2).hasDerivWithinAt
  · intro K hK
    exact (asym_scaleModel_second (interior_subset hK).1 (interior_subset hK).2).hasDerivWithinAt
  · intro K hK
    exact (asym_scaleModel_second_pos hh hh1 (interior_subset hK).1 (interior_subset hK).2).le

end SmoothedOctagon

namespace SmoothedOctagon
open Real Set

noncomputable def asymLogAdjusted (K : ℝ) : ℝ := log K+(25/578)*K^2
noncomputable def asymLogAdjusted' (K : ℝ) : ℝ := 1/K+(25/289)*K
noncomputable def asymLogAdjusted'' (K : ℝ) : ℝ := 25/289-1/K^2

theorem asym_logAdjusted_hasDerivAt {K : ℝ} (hK : 0 < K) :
    HasDerivAt asymLogAdjusted (asymLogAdjusted' K) K := by
  have he := (hasDerivAt_log hK.ne').add ((hasDerivAt_pow 2 K).const_mul (25/578:ℝ))
  convert he using 1
  · rfl
  · dsimp [asymLogAdjusted']; norm_num; ring

theorem asym_logAdjusted_second {K : ℝ} (hK : 0 < K) :
    HasDerivAt asymLogAdjusted' (asymLogAdjusted'' K) K := by
  have he := (((hasDerivAt_const K 1).div (hasDerivAt_id K) hK.ne').add
    ((hasDerivAt_id K).const_mul (25/289:ℝ)))
  convert he using 1
  · rfl
  · dsimp [asymLogAdjusted'']; field_simp; ring

/-- The logarithm's curvature is at most its value at the left scale endpoint. -/
theorem asym_logAdjusted_convex : ConvexOn ℝ (Icc (17/5) 4) asymLogAdjusted := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := asymLogAdjusted') (f'' := asymLogAdjusted'') (convex_Icc _ _)
  · intro K hK
    exact (asym_logAdjusted_hasDerivAt (by linarith only [hK.1])).continuousAt.continuousWithinAt
  · intro K hK
    exact (asym_logAdjusted_hasDerivAt (by
      have hi := interior_subset hK; linarith only [hi.1])).hasDerivWithinAt
  · intro K hK
    exact (asym_logAdjusted_second (by
      have hi := interior_subset hK; linarith only [hi.1])).hasDerivWithinAt
  · intro K hK
    have hi := interior_subset hK
    have hK0 : 0 < K := by linarith only [hi.1]
    have hsq : (17/5:ℝ)^2 ≤ K^2 := by
      exact pow_le_pow_left₀ (by norm_num) hi.1 2
    unfold asymLogAdjusted''
    have hp : 1/K^2 ≤ (25/289:ℝ) := by
      rw [div_le_iff₀ (sq_pos_of_pos hK0)]
      nlinarith only [hsq]
    linarith only [hp]

/-- The short scale interval gives a uniform quadratic logarithmic chord loss. -/
theorem asym_log_chord {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    log ((1-θ)*(17/5)+θ*4)-(1-θ)*log (17/5)-θ*log 4 ≤
      (9/578)*θ*(1-θ) := by
  have hc := asym_logAdjusted_convex.2
    (show (17/5:ℝ) ∈ Icc (17/5) 4 by norm_num)
    (show (4:ℝ) ∈ Icc (17/5) 4 by norm_num)
    (show 0 ≤ 1-θ by linarith only [hθ1]) hθ (by ring)
  simp only [smul_eq_mul] at hc
  dsimp [asymLogAdjusted] at hc
  nlinarith only [hc]

/-- Completing a square closes the full scale interval from its two endpoint margins. -/
theorem asym_neg_of_scale_endpoints {f : ℝ → ℝ} (hf : ConvexOn ℝ (Icc (17/5) 4) f)
    (h0 : f (17/5)+log (17/5) ≤ -(1/288:ℝ))
    (h1 : f 4+log 4 ≤ -(1/192:ℝ))
    {K : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4) : f K+log K < 0 := by
  let θ : ℝ := (5*K-17)/3
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith only [hK]
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith only [hK4]
  have hθc : 0 ≤ 1-θ := by linarith only [hθ1]
  have heq : (1-θ)*(17/5)+θ*4=K := by dsimp [θ]; ring
  have hc := hf.2 (show (17/5:ℝ) ∈ Icc (17/5) 4 by norm_num)
    (show (4:ℝ) ∈ Icc (17/5) 4 by norm_num) hθc hθ (by ring)
  simp only [smul_eq_mul] at hc
  rw [heq] at hc
  have hl := asym_log_chord hθ hθ1
  rw [heq] at hl
  have ha := mul_le_mul_of_nonneg_left h0 hθc
  have hb := mul_le_mul_of_nonneg_left h1 hθ
  have hloss : (9/578:ℝ)*θ*(1-θ) ≤ (1/64)*θ*(1-θ) := by
    have hp : 0 ≤ θ*(1-θ) := mul_nonneg hθ hθc
    nlinarith only [hp]
  have hs := sq_nonneg (θ-4/9)
  nlinarith only [hc,hl,ha,hb,hloss,hs]

end SmoothedOctagon

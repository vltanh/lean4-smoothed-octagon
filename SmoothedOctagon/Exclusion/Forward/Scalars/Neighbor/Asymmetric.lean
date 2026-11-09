module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Endpoints
public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Scale

/-!
# The asymmetric neighbour residual

Both shape boundaries are negative. Shape convexity proves the closed
rectangle comparison, and the physical domain lies inside it.
-/

@[expose] public section

namespace SmoothedOctagon
open Real

/-- The symmetric normalized model is the original row with its actual opposite floor. -/
theorem asym_symmetric_normalized_bridge {ν h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3) :
    asymContinuousRow ν (4/3) h (ff_F (4/7) (asymBoundaryH ν))/ff_alpha ν (4/3) h =
      asymSymNormalized (1+ν) h := by
  have hfloor := asym_scaleFloor_eq (K := 1+ν) (by linarith only [hν]) (by linarith only [hν3])
  have hfloor' : asymScaleFloor (1+ν)=ff_F (4/7) (asymBoundaryH ν) := by
    rw [hfloor]
    unfold asymBoundaryH
    congr 1
    congr 1
    ring
  unfold asymSymNormalized
  dsimp only
  simp only [add_sub_cancel_left]
  rw [hfloor']
  rfl

/-- The symmetric scale boundary is negative after subtracting the logarithmic chord loss. -/
theorem asym_symmetric_normalized_neg {K h : ℝ} (hK : 17/5 ≤ K) (hK4 : K ≤ 4)
    (hh : 1 ≤ h) (hh1 : h ≤ 3/2) : asymSymNormalized K h < 0 := by
  have hlo : asymScaleModel h (17/5)+log (17/5) ≤ -(1/288:ℝ) := by
    have hc := asym_original_lt_boundaryMajorant (ν := 12/5) (by norm_num) (by norm_num) hh
    have he := asym_symmetric_normalized_bridge (ν := 12/5) (h := h) (by norm_num) (by norm_num)
    have hs := asym_sym_scale_identity (K := 17/5) (by norm_num) hh
    have hn := asym_boundary_lower_endpoint hh hh1
    norm_num only [show 1+(12/5:ℝ)=17/5 by norm_num] at he
    rw [he] at hc
    linarith only [hc,hs,hn]
  have hhi : asymScaleModel h 4+log 4 ≤ -(1/192:ℝ) := by
    have hc := asym_original_lt_boundaryMajorant (ν := 3) (by norm_num) (by norm_num) hh
    have he := asym_symmetric_normalized_bridge (ν := 3) (h := h) (by norm_num) (by norm_num)
    have hs := asym_sym_scale_identity (K := 4) (by norm_num) hh
    have hn := asym_boundary_upper_endpoint hh hh1
    norm_num only [show 1+(3:ℝ)=4 by norm_num] at he
    rw [he] at hc
    linarith only [hc,hs,hn]
  have hn := asym_neg_of_scale_endpoints (asym_scaleModel_convex hh hh1) hlo hhi hK hK4
  have he := asym_sym_scale_identity hK hh
  linarith only [hn,he]

/-- The continuous original residual is negative along the entire symmetric boundary. -/
theorem asym_continuous_symmetric_neg {ν h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hh : 1 ≤ h) (hh1 : h ≤ 3/2) :
    asymContinuousRow ν (4/3) h (ff_F (4/7) (asymBoundaryH ν)) < 0 := by
  have hn := asym_symmetric_normalized_neg
    (K := 1+ν) (by linarith only [hν]) (by linarith only [hν3]) hh hh1
  rw [← asym_symmetric_normalized_bridge hν hν3] at hn
  have hα : 0 < ff_alpha ν (4/3) h := by
    have hK : 0 < 1+ν := by linarith only [hν]
    have hT : 0 < h*(1+4/3)-4/3 := by linarith only [hh]
    have hZ : 0 < (4/3:ℝ)^2+ν := by linarith only [hν]
    unfold ff_alpha
    positivity
  have hhneg := (div_lt_iff₀ hα).mp hn
  simpa only [zero_mul] using hhneg

/-- Both shape boundaries and convexity prove negativity on the full closed rectangle. -/
theorem asym_continuous_row_neg {ν z h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hz : 1 ≤ z) (hz1 : z ≤ 4/3) (hh : 1 ≤ h) (hh1 : h ≤ 3/2) :
    asymContinuousRow ν z h (ff_F (4/7) (asymBoundaryH ν)) < 0 := by
  exact asymContinuousRow_neg_of_symmetric hν hν3 hz hz1 hh hh1
    (asym_opposite_floor_gt hν hν3) (asym_continuous_symmetric_neg hν hν3 hh hh1)

/-- The actual asymmetric neighbour residual is negative on the physical factor domain. -/
theorem asym_original_row_neg {ν z h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hz : 1 ≤ z) (hz1 : z ≤ 4/3) (hh : 1 < h) (hh1 : h ≤ 3/2) :
    ff_resN ν z (4/3) h < 0 := by
  have hν0 : 0 < ν := by linarith only [hν]
  have hz0 : 0 < z := by linarith only [hz]
  rw [asymContinuousRow_eq_original hν0 hz0 hh.ne']
  have hf : ff_F ((4/3)/(1+4/3)) ((1+4/3)^2/((4/3)^2+ν)) =
      ff_F (4/7) (asymBoundaryH ν) := by
    congr 1
    · norm_num
    · unfold asymBoundaryH
      field_simp
      ring
  rw [hf]
  exact asym_continuous_row_neg hν hν3 hz hz1 hh.le hh1

end SmoothedOctagon


namespace SmoothedOctagon

/-- The physical asymmetric face lies in the closed analytic comparison rectangle. -/
theorem asym_physical_face_neg {U z h : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4/3)
    (hU : 9/5+3*z/5 ≤ U) (hU3 : U < 3)
    (hhl : (1+z)^2/(z^2+U) ≤ h)
    (hhu : h ≤ (1+z)*(5*U-2-3*(4/3))/(3*(z^2+U))) :
    ff_resN U z (4/3) h < 0 := by
  have hUlo : 12/5 ≤ U := by linarith only [hU,hz]
  have hU0 : 0 < U := by linarith only [hUlo]
  have hZ : 0 < z^2+U := by positivity
  have hI : 1 < (1+z)^2/(z^2+U) := by
    rw [lt_div_iff₀ hZ]
    nlinarith only [hz,hU3]
  have hh : 1 < h := hI.trans_le hhl
  have hgain : 0 ≤ (3-U)*(10*z+1) := mul_nonneg (by linarith only [hU3]) (by linarith only [hz])
  have htop : (1+z)*(5*U-2-3*(4/3))/(3*(z^2+U)) ≤ (3/2:ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 3*(z^2+U))]
    nlinarith only [hgain,sq_nonneg (z-1)]
  exact asym_original_row_neg hUlo hU3.le hz hz' hh (hhu.trans htop)

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Row

/-!
# Rational majorants at the two neighbour scale endpoints

The reciprocal Simpson bound controls the factor logarithm and exterior
floor. A cubic logarithm lower bound keeps the comparison strict.
-/

@[expose] public section

namespace SmoothedOctagon
open Real

/-- Strict cubic logarithm lower bound from the next positive reciprocal moment. -/
theorem asym_log_cubic_lt {q : ℝ} (hq : 1 < q) :
    2*((q-1)/(q+1))+2*((q-1)/(q+1))^3/3 < log q := by
  have ht : 0 < (q-1)/(q+1) := div_pos (by linarith only [hq]) (by linarith only [hq])
  obtain ⟨ht0,ht1⟩ := ff_tau_bounds hq.le
  have hl := ff_log_ge_sum ht0 ht1 3
  rw [← ff_log_atanh (by linarith only [hq])] at hl
  norm_num [Finset.sum_range_succ] at hl
  have hp : 0 < ((q-1)/(q+1))^5 := pow_pos ht 5
  nlinarith only [hl,hp]

noncomputable def asymBoundaryRow (ν F L Q h : ℝ) : ℝ :=
  let z : ℝ := 4/3
  let S := 1+z
  let Z := z^2+ν
  let K := 1+ν
  let T := h*S-z
  let q := S^2/K
  let A := 59/21+1/K-Q
  let B := Z*h/S+1-z^2*S/(Z*h)-z^2/S+z^3/Z-z*L
  (K*T/Z*A-B-S^2*(ν-z)/Z*((h-1)+(z/S)^2*h*(h-1)-z/S*h*L)-
    K^2/(S*Z)*(q-1+(h-1)*(q*S-1))*F)/(K*T/Z)

noncomputable def asymBoundaryH (ν : ℝ) : ℝ := 49/(16+9*ν)
noncomputable def asymBoundaryFloor (ν : ℝ) : ℝ :=
  37/49+(2/49)*(asymBoundaryH ν-1)+
    (4/7)*(asymBoundaryH ν-1)^2/(3*(asymBoundaryH ν+1))
noncomputable def asymBoundaryQ (ν : ℝ) : ℝ := 49/(9*(1+ν))
noncomputable def asymCubicLog (q : ℝ) : ℝ := 2*((q-1)/(q+1))*(1+((q-1)/(q+1))^2/3)
noncomputable def asymBoundaryMajorant (ν h : ℝ) : ℝ :=
  asymBoundaryRow ν (asymBoundaryFloor ν) (asymLogSimpson h) (asymCubicLog (asymBoundaryQ ν)) h

/-- The Simpson floor is a lower bound for the actual opposite floor. -/
theorem asym_boundary_floor_le {ν : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3) :
    asymBoundaryFloor ν ≤ ff_F (4/7) (asymBoundaryH ν) := by
  have hd : 0 < 16+9*ν := by linarith only [hν]
  have hH : 1 < asymBoundaryH ν := by
    unfold asymBoundaryH
    rw [one_lt_div hd]
    linarith only [hν3]
  have hH0 : 0 < asymBoundaryH ν := by linarith only [hH]
  have hl := asym_log_simpson hH.le
  have hcoef : 0 < (4/7)*asymBoundaryH ν/(asymBoundaryH ν-1) := by positivity
  have hp := mul_le_mul_of_nonneg_left hl hcoef.le
  have he : ff_F (4/7) (asymBoundaryH ν)-asymBoundaryFloor ν =
      (4/7)*asymBoundaryH ν/(asymBoundaryH ν-1)*(asymLogSimpson (asymBoundaryH ν)-log (asymBoundaryH ν)) := by
    unfold ff_F asymBoundaryFloor asymLogSimpson
    field_simp [hH0.ne',show asymBoundaryH ν-1 ≠ 0 by linarith only [hH],
      show asymBoundaryH ν+1 ≠ 0 by linarith only [hH]]
    ring
  linarith only [he,hp]

end SmoothedOctagon


namespace SmoothedOctagon
open Real

noncomputable def asymBoundaryLogWeight (ν h : ℝ) : ℝ :=
  (4/3)*(ν-4/3)/(1+ν)+(4/3)*ν*(7/3)/((1+ν)*((7/3)*h-4/3))
noncomputable def asymBoundaryFloorWeight (ν h : ℝ) : ℝ :=
  9*h*(1+ν)/(7*(7*h-4))-7/3

/-- The two logarithms and the exterior floor keep their original row coefficients. -/
theorem asym_boundary_row_difference {ν h F0 F1 L0 L1 Q0 Q1 : ℝ}
    (hν : 12/5 ≤ ν) (hh : 1 ≤ h) :
    asymBoundaryRow ν F1 L1 Q1 h-asymBoundaryRow ν F0 L0 Q0 h =
      asymBoundaryLogWeight ν h*(L1-L0)-(Q1-Q0)+asymBoundaryFloorWeight ν h*(F1-F0) := by
  have hK : 0 < 1+ν := by linarith only [hν]
  have hZ : 0 < (4/3:ℝ)^2+ν := by linarith only [hν]
  have hT : 0 < (7/3)*h-4/3 := by linarith only [hh]
  have hT7 : 0 < 7*h-4 := by linarith only [hh]
  have hh0 : 0 < h := by linarith only [hh]
  unfold asymBoundaryRow asymBoundaryLogWeight asymBoundaryFloorWeight
  dsimp
  field_simp [hK.ne',hZ.ne',hT.ne',hT7.ne',hh0.ne']
  ring_nf
  field_simp [show -4+h*7 ≠ 0 by linarith only [hh]]
  ring

/-- The row reconstructed from its logarithm values is the continuous original residual. -/
theorem asym_boundary_row_original {ν F h : ℝ} (hν : 12/5 ≤ ν) (hh : 1 ≤ h) :
    asymBoundaryRow ν F (log h) (log (asymBoundaryQ ν)) h =
      asymContinuousRow ν (4/3) h F/ff_alpha ν (4/3) h := by
  have hK : 0 < 1+ν := by linarith only [hν]
  have hZ : 0 < (4/3:ℝ)^2+ν := by linarith only [hν]
  have hT : 0 < (7/3)*h-4/3 := by linarith only [hh]
  have hh0 : 0 < h := by linarith only [hh]
  have hq : ff_q ν (4/3) (4/3)=asymBoundaryQ ν := by
    unfold ff_q asymBoundaryQ
    field_simp
    ring
  unfold asymContinuousRow ff_A
  rw [hq]
  unfold asymBoundaryRow ff_alpha ff_B ff_m ff_q asymBoundaryQ
  dsimp
  field_simp [hK.ne',hZ.ne',hT.ne',hh0.ne']
  ring

theorem asym_boundary_weights {ν h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hh : 1 ≤ h) : 0 < asymBoundaryLogWeight ν h ∧ asymBoundaryFloorWeight ν h < 0 := by
  have hK : 0 < 1+ν := by linarith only [hν]
  have hT : 0 < (7/3)*h-4/3 := by linarith only [hh]
  have hT7 : 0 < 7*(7*h-4) := by linarith only [hh]
  constructor
  · unfold asymBoundaryLogWeight
    have hν0 : 0 < ν := by linarith only [hν]
    have hνz : 0 < ν-4/3 := by linarith only [hν]
    positivity
  · unfold asymBoundaryFloorWeight
    rw [sub_neg,div_lt_iff₀ hT7]
    have hx : 0 ≤ h-1 := by linarith only [hh]
    have hprod : h*(1+ν) ≤ 4*h := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (show 1+ν ≤ 4 by linarith only [hν3]) (show 0 ≤ h by linarith only [hh])
    nlinarith only [hprod,hh]

/-- Simpson and the strict cubic logarithm bound majorize the actual normalized row. -/
theorem asym_original_lt_boundaryMajorant {ν h : ℝ} (hν : 12/5 ≤ ν) (hν3 : ν ≤ 3)
    (hh : 1 ≤ h) :
    asymContinuousRow ν (4/3) h (ff_F (4/7) (asymBoundaryH ν))/ff_alpha ν (4/3) h <
      asymBoundaryMajorant ν h := by
  have hq : 1 < asymBoundaryQ ν := by
    have hK : 0 < 9*(1+ν) := by linarith only [hν]
    unfold asymBoundaryQ
    rw [one_lt_div hK]
    linarith only [hν3]
  have hlh := asym_log_simpson hh
  have hqlog := asym_log_cubic_lt hq
  have hqlog' : asymCubicLog (asymBoundaryQ ν) < log (asymBoundaryQ ν) := by
    dsimp [asymCubicLog]
    nlinarith only [hqlog]
  have hfloor := asym_boundary_floor_le hν hν3
  obtain ⟨hwlog,hwfloor⟩ := asym_boundary_weights hν hν3 hh
  have h1 := mul_nonneg hwlog.le (sub_nonneg.mpr hlh)
  have h2 := mul_nonneg_of_nonpos_of_nonpos hwfloor.le (sub_nonpos.mpr hfloor)
  have he := asym_boundary_row_difference (F1 := asymBoundaryFloor ν)
    (F0 := ff_F (4/7) (asymBoundaryH ν)) (L1 := asymLogSimpson h) (L0 := log h)
    (Q1 := asymCubicLog (asymBoundaryQ ν)) (Q0 := log (asymBoundaryQ ν)) hν hh
  rw [asym_boundary_row_original hν hh] at he
  change _ < asymBoundaryRow ν (asymBoundaryFloor ν) (asymLogSimpson h)
    (asymCubicLog (asymBoundaryQ ν)) h
  linarith only [he,h1,h2,hqlog']

end SmoothedOctagon

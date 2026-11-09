module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Majorant

/-!
# The asymmetric neighbour scale endpoint comparisons

The rational majorants have three reciprocal poles. Their exact tangent
remainders and simple residue bounds give strict margins on the factor interval.
-/

@[expose] public section

namespace SmoothedOctagon

noncomputable def asymPoleRow (a b c d e h : ℝ) : ℝ :=
  -a*h+b/((7/3)*h-4/3)+c/(h+1)-d/h+e
noncomputable def asymPoleSlope (a b c d h : ℝ) : ℝ :=
  -a-(7/3)*b/((7/3)*h-4/3)^2-c/(h+1)^2+d/h^2

private theorem asym_inv_tangent {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    1/x-1/y+(x-y)/y^2=(x-y)^2/(y^2*x) := by
  field_simp
  ring

/-- The three simple reciprocal poles give an exact tangent remainder. -/
theorem asym_pole_remainder {a b c d e h v : ℝ} (hh : 1 ≤ h) (hv : 1 ≤ v) :
    asymPoleRow a b c d e h-asymPoleRow a b c d e v-
      (h-v)*asymPoleSlope a b c d v =
    (h-v)^2*((49/9)*b/(((7/3)*v-4/3)^2*((7/3)*h-4/3))+
      c/((v+1)^2*(h+1))-d/(v^2*h)) := by
  have hh0 : 0 < h := by linarith only [hh]
  have hv0 : 0 < v := by linarith only [hv]
  have hTh : 0 < (7/3)*h-4/3 := by linarith only [hh]
  have hTv : 0 < (7/3)*v-4/3 := by linarith only [hv]
  have hhp : 0 < h+1 := by linarith only [hh]
  have hvp : 0 < v+1 := by linarith only [hv]
  have ht := asym_inv_tangent hTh.ne' hTv.ne'
  have hp := asym_inv_tangent hhp.ne' hvp.ne'
  have hu := asym_inv_tangent hh0.ne' hv0.ne'
  unfold asymPoleRow asymPoleSlope
  linear_combination b*ht+c*hp-d*hu

/-- Natural bounds on the residues make the exact reciprocal remainder negative. -/
theorem asym_pole_below_tangent {a b c d e h v B C D : ℝ}
    (hh : 1 ≤ h) (hh1 : h ≤ 3/2) (hv : 1 ≤ v)
    (hb : 0 ≤ b) (hb1 : b ≤ B) (hc : 0 ≤ c) (hc1 : c ≤ C) (hd : D ≤ d)
    (hbudget : (49/9)*B/((7/3)*v-4/3)^2+(3/5)*C/(v+1)^2-D/v^2 ≤ 0) :
    asymPoleRow a b c d e h ≤
      asymPoleRow a b c d e v+(h-v)*asymPoleSlope a b c d v := by
  have hh0 : 0 < h := by linarith only [hh]
  have hv0 : 0 < v := by linarith only [hv]
  have hTh : 0 < (7/3)*h-4/3 := by linarith only [hh]
  have hTv : 0 < (7/3)*v-4/3 := by linarith only [hv]
  have hhp : 0 < h+1 := by linarith only [hh]
  have hvp : 0 < v+1 := by linarith only [hv]
  have hr : h/((7/3)*h-4/3) ≤ 1 := by
    rw [div_le_one hTh]; linarith only [hh]
  have hp : h/(h+1) ≤ (3/5:ℝ) := by
    rw [div_le_iff₀ hhp]; linarith only [hh1]
  have hB : (49/9)*b/((7/3)*v-4/3)^2*(h/((7/3)*h-4/3)) ≤
      (49/9)*B/((7/3)*v-4/3)^2 := by
    calc
      _ ≤ (49/9)*b/((7/3)*v-4/3)^2*1 :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ _ := by simp only [mul_one]; gcongr
  have hC : c/(v+1)^2*(h/(h+1)) ≤ (3/5)*C/(v+1)^2 := by
    calc
      _ ≤ c/(v+1)^2*(3/5) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by
        have he : c/(v+1)^2*(3/5)=(3/5)*c/(v+1)^2 := by ring
        rw [he]; gcongr
  have hD : D/v^2 ≤ d/v^2 := div_le_div_of_nonneg_right hd (sq_nonneg v)
  have he : h*((49/9)*b/(((7/3)*v-4/3)^2*((7/3)*h-4/3))+
      c/((v+1)^2*(h+1))-d/(v^2*h)) =
      (49/9)*b/((7/3)*v-4/3)^2*(h/((7/3)*h-4/3))+
      c/(v+1)^2*(h/(h+1))-d/v^2 := by
    field_simp [hh0.ne',hv0.ne',hTh.ne',hTv.ne',hhp.ne',hvp.ne']
  have hrem : (49/9)*b/(((7/3)*v-4/3)^2*((7/3)*h-4/3))+
      c/((v+1)^2*(h+1))-d/(v^2*h) ≤ 0 := by
    have hm : h*((49/9)*b/(((7/3)*v-4/3)^2*((7/3)*h-4/3))+
      c/((v+1)^2*(h+1))-d/(v^2*h)) ≤ 0 := by
      rw [he]
      linarith only [hB,hC,hD,hbudget]
    nlinarith only [hh0,hm]
  have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (h-v)) hrem
  rw [← asym_pole_remainder hh hv] at h
  linarith only [h]

end SmoothedOctagon


namespace SmoothedOctagon
open Real

noncomputable def asymBoundaryA (ν : ℝ) : ℝ :=
  (4/3)*(ν-4/3)/(1+ν)*(4/7-1/6)
noncomputable def asymBoundaryB (ν F : ℝ) : ℝ :=
  (4/3)*((1+ν)^2*F-ν^2+ν*((4/3)^2+3*(4/3)+1))/((1+ν)*(7/3)^2)+
    (4/3)*ν*(7/3)/(1+ν)*asymLogSimpson (4/7)
noncomputable def asymBoundaryC (ν : ℝ) : ℝ :=
  8*(4/3)^2/(3*(1+ν))*(1-ν/(1+2*(4/3)))
noncomputable def asymBoundaryD (ν : ℝ) : ℝ :=
  (5*(4/3)^2+6*(4/3)-ν)/(6*(1+ν))
noncomputable def asymBoundaryConstant (ν F Q : ℝ) : ℝ :=
  asymBoundaryRow ν F 0 Q 1-
    asymPoleRow (asymBoundaryA ν) (asymBoundaryB ν F) (asymBoundaryC ν) (asymBoundaryD ν) 0 1

/-- The actual rational row majorant has exactly the three reciprocal poles. -/
theorem asym_boundary_pole_identity {ν F Q h : ℝ} (hν : 12/5 ≤ ν) (hh : 1 ≤ h) :
    asymBoundaryRow ν F (asymLogSimpson h) Q h =
      asymPoleRow (asymBoundaryA ν) (asymBoundaryB ν F) (asymBoundaryC ν)
        (asymBoundaryD ν) (asymBoundaryConstant ν F Q) h := by
  have hK : 0 < 1+ν := by linarith only [hν]
  have hZ : 0 < (4/3:ℝ)^2+ν := by linarith only [hν]
  have hT : 0 < (7/3)*h-4/3 := by linarith only [hh]
  have hT7 : 0 < 7*h-4 := by linarith only [hh]
  have hh0 : 0 < h := by linarith only [hh]
  have hhp : 0 < h+1 := by linarith only [hh]
  unfold asymBoundaryConstant asymBoundaryRow asymPoleRow asymBoundaryA asymBoundaryB
    asymBoundaryC asymBoundaryD asymLogSimpson
  dsimp
  norm_num
  field_simp [hK.ne',hZ.ne',hT.ne',hT7.ne',hh0.ne',hhp.ne']
  ring_nf
  field_simp [show -4+h*7 ≠ 0 by linarith only [hh],
    show ν+1 ≠ 0 by linarith only [hν],show h+1 ≠ 0 by linarith only [hh]]
  ring

/-- The two natural endpoint residue bounds. -/
theorem asym_boundary_endpoint_residues :
    (0 < asymBoundaryB (12/5) (asymBoundaryFloor (12/5)) ∧
      asymBoundaryB (12/5) (asymBoundaryFloor (12/5)) < 1/5 ∧
      0 < asymBoundaryC (12/5) ∧ asymBoundaryC (12/5) < 1/2 ∧
      7/10 < asymBoundaryD (12/5)) ∧
    (0 < asymBoundaryB 3 (asymBoundaryFloor 3) ∧
      asymBoundaryB 3 (asymBoundaryFloor 3) < 5/36 ∧
      0 < asymBoundaryC 3 ∧ asymBoundaryC 3 < 2/9 ∧
      asymBoundaryD 3=125/216) := by
  norm_num [asymBoundaryB,asymBoundaryC,asymBoundaryD,asymBoundaryFloor,
    asymBoundaryH,asymLogSimpson]

end SmoothedOctagon


namespace SmoothedOctagon
open Real

/-- At the lower scale endpoint, the whole factor interval lies below one fixed tangent. -/
theorem asym_boundary_lower_endpoint {h : ℝ} (hh : 1 ≤ h) (hh1 : h ≤ 3/2) :
    asymBoundaryMajorant (12/5) h < -(1/288:ℝ) := by
  let a := asymBoundaryA (12/5)
  let b := asymBoundaryB (12/5) (asymBoundaryFloor (12/5))
  let c := asymBoundaryC (12/5)
  let d := asymBoundaryD (12/5)
  let E := asymBoundaryConstant (12/5) (asymBoundaryFloor (12/5)) (asymCubicLog (asymBoundaryQ (12/5)))
  have hr := asym_boundary_endpoint_residues.1
  change 0 < b ∧ b < 1/5 ∧ 0 < c ∧ c < 1/2 ∧ 7/10 < d at hr
  have hv : (1:ℝ) ≤ 7/5 := by norm_num
  have hp := asym_pole_below_tangent (a := a) (b := b) (c := c) (d := d) (e := E)
    (v := 7/5) (B := 1/5) (C := 1/2) (D := 7/10) hh hh1 hv hr.1.le hr.2.1.le
    hr.2.2.1.le hr.2.2.2.1.le hr.2.2.2.2.le (by norm_num)
  have hs : 0 < asymPoleSlope a b c d (7/5) := by
    norm_num [a,b,c,d,asymPoleSlope,asymBoundaryA,asymBoundaryB,asymBoundaryC,
      asymBoundaryD,asymBoundaryFloor,asymBoundaryH,asymLogSimpson]
  have hvneg : asymPoleRow a b c d E (7/5)+(1/10)*asymPoleSlope a b c d (7/5) < -(1/288:ℝ) := by
    norm_num [a,b,c,d,E,asymPoleSlope,asymPoleRow,asymBoundaryConstant,asymBoundaryRow,
      asymBoundaryA,asymBoundaryB,asymBoundaryC,asymBoundaryD,asymBoundaryFloor,asymBoundaryH,
      asymLogSimpson,asymCubicLog,asymBoundaryQ]
  have hm := mul_le_mul_of_nonneg_right (show h-7/5 ≤ (1/10:ℝ) by linarith only [hh1]) hs.le
  have hmain : asymPoleRow a b c d E h < -(1/288:ℝ) := by linarith only [hp,hm,hvneg]
  unfold asymBoundaryMajorant
  rw [asym_boundary_pole_identity (by norm_num : (12/5:ℝ) ≤ 12/5) hh]
  exact hmain

/-- At the upper scale endpoint, the tangent slopes down from the left end. -/
theorem asym_boundary_upper_endpoint {h : ℝ} (hh : 1 ≤ h) (hh1 : h ≤ 3/2) :
    asymBoundaryMajorant 3 h < -(1/192:ℝ) := by
  let a := asymBoundaryA 3
  let b := asymBoundaryB 3 (asymBoundaryFloor 3)
  let c := asymBoundaryC 3
  let d := asymBoundaryD 3
  let E := asymBoundaryConstant 3 (asymBoundaryFloor 3) (asymCubicLog (asymBoundaryQ 3))
  have hr := asym_boundary_endpoint_residues.2
  change 0 < b ∧ b < 5/36 ∧ 0 < c ∧ c < 2/9 ∧ d=125/216 at hr
  have hv : (1:ℝ) ≤ 7/6 := by norm_num
  have hp := asym_pole_below_tangent (a := a) (b := b) (c := c) (d := d) (e := E)
    (v := 7/6) (B := 5/36) (C := 2/9) (D := 125/216) hh hh1 hv hr.1.le hr.2.1.le
    hr.2.2.1.le hr.2.2.2.1.le hr.2.2.2.2.ge (by norm_num)
  have hs : asymPoleSlope a b c d (7/6) < 0 := by
    norm_num [a,b,c,d,asymPoleSlope,asymBoundaryA,asymBoundaryB,asymBoundaryC,
      asymBoundaryD,asymBoundaryFloor,asymBoundaryH,asymLogSimpson]
  have hvneg : asymPoleRow a b c d E (7/6)-(1/6)*asymPoleSlope a b c d (7/6) < -(1/192:ℝ) := by
    norm_num [a,b,c,d,E,asymPoleSlope,asymPoleRow,asymBoundaryConstant,asymBoundaryRow,
      asymBoundaryA,asymBoundaryB,asymBoundaryC,asymBoundaryD,asymBoundaryFloor,asymBoundaryH,
      asymLogSimpson,asymCubicLog,asymBoundaryQ]
  have hm := mul_le_mul_of_nonpos_right (show -(1/6:ℝ) ≤ h-7/6 by linarith only [hh]) hs.le
  have hmain : asymPoleRow a b c d E h < -(1/192:ℝ) := by linarith only [hp,hm,hvneg]
  unfold asymBoundaryMajorant
  rw [asym_boundary_pole_identity (by norm_num : (12/5:ℝ) ≤ 3) hh]
  exact hmain

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Strong

/-!
# The quadratic lower bridge order

The positive gains in the affine gap comparison pay for the two costs of
curving the barrier. Bounds on the contact threshold's derivative and three
normalized denominator comparisons leave a sum of positive terms and a square.
Contact feasibility gives the required domain without an extra displacement bound.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

local syntax "analytic_deriv" : tactic
macro_rules
| `(tactic| analytic_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> analytic_deriv
  | apply HasDerivAt.sub <;> analytic_deriv
  | apply HasDerivAt.pow <;> analytic_deriv
  | apply HasDerivAt.mul <;> analytic_deriv
  | apply HasDerivAt.div <;> first | analytic_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> analytic_deriv)

private noncomputable def quadF (a r v : ℝ) : ℝ :=
  (1+v*r)/((1+(v-a)*r)*(1+(v+1-a)*r))
private noncomputable def quadFD (a r v : ℝ) : ℝ :=
  r*((1+(v-a)*r)^2+2*a*r*(1+(v-a)*r)+a*r^2) /
    ((1+(v-a)*r)^2*((1+(v-a)*r)+r)^2)

private theorem quadF_deriv {a r v : ℝ} (hv : 1/5 ≤ v-a) (hr : 0 ≤ r) :
    HasDerivAt (quadF a r) (-quadFD a r v) v := by
  have h1 : 0 < 1+(v-a)*r := by
    have : 0 ≤ v-a := by linarith only [hv]
    positivity
  have h2 : 0 < 1+(v+1-a)*r := by
    have : 0 ≤ v+1-a := by linarith only [hv]
    positivity
  unfold quadF quadFD
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]
    field_simp (disch := first | positivity | nlinarith)
    ring

private theorem quadFD_bounds {a r v : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hv : 1/5 ≤ v-a) (hr : 0 ≤ r) :
    0 ≤ quadFD a r v ∧ quadFD a r v ≤ r/(1+r/5) := by
  let u := 1+(v-a)*r
  have hu : 1 ≤ u := by
    have : 0 ≤ v-a := by linarith only [hv]
    have hm := mul_nonneg this hr
    dsimp [u]
    linarith only [hm]
  have hu0 : 0 < u := by linarith only [hu]
  have hur : 0 < u+r := by positivity
  have hnum : 0 ≤ u^2+2*a*r*u+a*r^2 := by positivity
  have hgap : 0 ≤ u^2*(u-1)+(u-a)*(2*r*u+r^2) := by
    have : 0 ≤ u-1 := by linarith only [hu]
    have : 0 ≤ u-a := by linarith only [hu,ha1]
    positivity
  have hcomp : u^2+2*a*r*u+a*r^2 ≤ u*(u+r)^2 := by
    have he : u*(u+r)^2-(u^2+2*a*r*u+a*r^2) =
      u^2*(u-1)+(u-a)*(2*r*u+r^2) := by ring
    linarith only [he,hgap]
  have hfrac : (u^2+2*a*r*u+a*r^2)/(u^2*(u+r)^2) ≤ 1/u := by
    rw [div_le_div_iff₀ (by positivity) hu0]
    have hm := mul_le_mul_of_nonneg_left hcomp hu0.le
    nlinarith only [hm]
  have hcomp2 : 1+r/5 ≤ u := by
    have hm := mul_le_mul_of_nonneg_right hv hr
    dsimp [u]
    linarith only [hm]
  constructor
  · unfold quadFD
    change 0 ≤ r*(u^2+2*a*r*u+a*r^2)/(u^2*(u+r)^2)
    positivity
  · change r*(u^2+2*a*r*u+a*r^2)/(u^2*(u+r)^2) ≤ r/(1+r/5)
    have hm := mul_le_mul_of_nonneg_left hfrac hr
    calc r*(u^2+2*a*r*u+a*r^2)/(u^2*(u+r)^2) ≤ r/u := by convert hm using 1 <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left hr (by positivity) hcomp2

private theorem quadM_deriv {a r v : ℝ} (hv : 1/5 ≤ v-a) (hr : 0 ≤ r) :
    HasDerivAt (fun v => ordContactM a v r) (-(1-r)*quadFD a r v) v := by
  have h := ((quadF_deriv hv hr).const_mul (1-r)).const_add 1
  have he : (fun v => ordContactM a v r) = (fun v => 1+(1-r)*quadF a r v) := by
    funext u
    dsimp [ordContactM,quadF]
    ring
  rw [he]
  exact h.congr_deriv (by ring)

private theorem quad_M_variation {a r k K : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hk : 1/5 ≤ k-a) (hkK : k ≤ K) (hr : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ ordContactM a k r-ordContactM a K r ∧
    ordContactM a k r-ordContactM a K r ≤ r*(1-r)*(K-k)/(1+r/5) := by
  let C := r*(1-r)/(1+r/5)
  have hrm : 0 ≤ 1-r := by linarith only [hr1]
  have hv : ∀ v ∈ Icc k K, 1/5 ≤ v-a := by intro v hv; linarith only [hk,hv.1]
  have hbound : ∀ v ∈ Icc k K, 0 ≤ (1-r)*quadFD a r v ∧ (1-r)*quadFD a r v ≤ C := by
    intro v hvI
    have h := quadFD_bounds ha ha1 (hv v hvI) hr
    refine ⟨mul_nonneg hrm h.1,?_⟩
    have hm := mul_le_mul_of_nonneg_left h.2 hrm
    dsimp [C]
    convert hm using 1; ring
  have hanti := ss_le_of_deriv (f := fun v => -ordContactM a v r)
    (f' := fun v => (1-r)*quadFD a r v) hkK
    (fun v hvI => by convert (quadM_deriv (hv v hvI) hr).neg using 1; ring)
    (fun v hvI => (hbound v ⟨hvI.1.le,hvI.2.le⟩).1)
  have hcost := ss_le_of_deriv (f := fun v => ordContactM a v r+C*v)
    (f' := fun v => C-(1-r)*quadFD a r v) hkK
    (fun v hvI => by
      convert (quadM_deriv (hv v hvI) hr).add ((hasDerivAt_id' v).const_mul C) using 1; ring)
    (fun v hvI => by linarith only [(hbound v ⟨hvI.1.le,hvI.2.le⟩).2])
  constructor
  · linarith only [hanti]
  · have he : C*(K-k) = r*(1-r)*(K-k)/(1+r/5) := by dsimp [C]; ring
    nlinarith only [hcost,he]

private theorem quad_k_bounds {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 7/13) :
    3/4 < ordStrongK a ∧ ordStrongK a ≤ 4/5 ∧
    1/5 < ordStrongK a-a ∧ ordStrongK a-a ≤ 3/10 ∧ 2/ordStrongK a-1 ≤ 8/5 := by
  have h8 : 0 < 8-a := by linarith only [ha1]
  have hk : 3/4 < ordStrongK a := by
    unfold ordStrongK
    rw [lt_div_iff₀ h8]
    linarith only [ha1]
  have hk1 : ordStrongK a ≤ 4/5 := by
    unfold ordStrongK
    rw [div_le_iff₀ h8]
    linarith only [ha]
  have hkh : 10/13 < ordStrongK a := by
    unfold ordStrongK
    rw [lt_div_iff₀ h8]
    linarith only [ha1]
  refine ⟨hk,hk1,?_,?_,?_⟩
  · linarith only [hk,ha1]
  · linarith only [hk1,ha]
  · rw [sub_le_iff_le_add,div_le_iff₀ (by linarith only [hk])]
    linarith only [hkh]

private theorem quad_D_lower {a r : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 7/13)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    r*((19/20)*(1-r)+(1/2)*r)/((1+3*r/10)*(1+13*r/10)) ≤
      ordContactM a (ordStrongK a) r-
        ordStrongK a*ordStrongB0 (ordStrongK a) (ordStrongK a-a) r := by
  let k := ordStrongK a
  let h := k-a
  have hkall := quad_k_bounds ha ha1
  have hk : 3/4 < k := hkall.1
  have hk1 : k ≤ 4/5 := hkall.2.1
  have hh : 1/5 < h := hkall.2.2.1
  have hh1 : h ≤ 3/10 := hkall.2.2.2.1
  have hk0 : 0 ≤ 1-k := by linarith only [hk1]
  have hpos : 0 < 1+h := by linarith only [hh]
  have hpos2 : 0 < 2+h := by linarith only [hh]
  have hcoef : 19/20 ≤ 2-k*(1+h) := by
    have hm1 := mul_le_mul_of_nonneg_left (show 1+h ≤ 13/10 by linarith only [hh1])
      (show 0 ≤ k by linarith only [hk])
    have hm2 := mul_le_mul_of_nonneg_right hk1 (by norm_num : (0:ℝ) ≤ 13/10)
    linarith only [hm1,hm2]
  have hkmul : 0 ≤ (1-k)*(1+h) := mul_nonneg hk0 hpos.le
  have hcoef2 : 1/2 ≤ (1-k)*(1+h)*(2+h) := by
    have hm : (1/5:ℝ)*(6/5)*(11/5) ≤ (1-k)*(1+h)*(2+h) := by
      gcongr <;> nlinarith only [hk1,hh,hr,hkmul]
    linarith only [hm]
  have hN : r*((19/20)*(1-r)+(1/2)*r) ≤
      r*((1-r)*(2-k*(1+h))+r*(1-k)*(1+h)*(2+h)) := by
    have hh0 : 0 ≤ 1-r := by linarith only [hr1]
    have hm1 := mul_le_mul_of_nonneg_left hcoef hh0
    have hm2 := mul_le_mul_of_nonneg_left hcoef2 hr
    have hadd : (19/20)*(1-r)+(1/2)*r ≤
        (1-r)*(2-k*(1+h))+r*(1-k)*(1+h)*(2+h) := by nlinarith only [hm1,hm2]
    exact mul_le_mul_of_nonneg_left hadd hr
  have hden : (1+h*r)*(1+(1+h)*r) ≤ (1+3*r/10)*(1+13*r/10) := by
    gcongr <;> nlinarith only [hh1,hr]
  have hdenp : 0 < (1+h*r)*(1+(1+h)*r) := by
    have : 0 < h := by linarith only [hh]
    positivity
  have hN0 : 0 ≤ r*((1-r)*(2-k*(1+h))+r*(1-k)*(1+h)*(2+h)) := by
    have : 0 ≤ 2-k*(1+h) := by linarith only [hcoef]
    have : 0 ≤ 1-k := by linarith only [hk1]
    have : 0 ≤ 1-r := by linarith only [hr1]
    positivity
  have hgain := ord_strong_contact_gain (by linarith only [ha] : 0 < a)
    (by linarith only [ha1] : a < 1) (by linarith only [hk] : 0 < k)
    (by linarith only [hk1] : k < 1) hr hr1
  change _ ≤ ordContactM a k r-k*ordStrongB0 k h r
  rw [hgain]
  change _ ≤ r*((1-r)*(2-k*(1+h))+r*(1-k)*(1+h)*(2+h))/((1+h*r)*(1+(1+h)*r))
  exact (div_le_div_of_nonneg_right hN (by positivity)).trans
    (div_le_div_of_nonneg_left hN0 hdenp hden)

private theorem quad_denominator_gain {a r : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 7/13)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    r*(1-r)/(5*(1+2*r)^2) ≤
      ordStrongK a*(ordStrongB0 (ordStrongK a) (ordStrongK a-a) r-ordStrongB a r) := by
  let k := ordStrongK a
  let h := k-a
  have hka := quad_k_bounds ha ha1
  have hk : 0 < k := by linarith only [hka.1]
  have hk1 : k ≤ 4/5 := hka.2.1
  have hh : 0 < h := by linarith only [hka.2.2.1]
  have hh1 : h ≤ 3/10 := hka.2.2.2.1
  have hden0 : 0 < 1+(1+h)*r := by positivity
  have hden : 0 < 1+(2-a)*r := by
    have : 0 < 2-a := by linarith only [ha1]
    positivity
  have he : k*(ordStrongB0 k h r-ordStrongB a r) =
      r*(1-r)*(2-k)*(1-k)/((1+(1+h)*r)*(1+(2-a)*r)) := by
    dsimp [ordStrongB0,ordStrongB,k,h]
    field_simp (disch := first | positivity | nlinarith)
    ring
  have hcoef : (1/5:ℝ) ≤ (2-k)*(1-k) := by
    have hm : (6/5:ℝ)*(1/5) ≤ (2-k)*(1-k) := by gcongr <;> linarith only [hk1]
    linarith only [hm]
  have hdenle : (1+(1+h)*r)*(1+(2-a)*r) ≤ (1+2*r)^2 := by
    rw [pow_two]
    gcongr <;> linarith only [hh1,ha]
  have hN : 0 ≤ r*(1-r)*(2-k)*(1-k) := by
    have : 0 ≤ 1-r := by linarith only [hr1]
    have : 0 ≤ 2-k := by linarith only [hk1]
    have : 0 ≤ 1-k := by linarith only [hk1]
    positivity
  change _ ≤ k*(ordStrongB0 k h r-ordStrongB a r)
  rw [he]
  calc r*(1-r)/(5*(1+2*r)^2) = r*(1-r)*(1/5)/(1+2*r)^2 := by field_simp
    _ ≤ r*(1-r)*(2-k)*(1-k)/(1+2*r)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hm := mul_le_mul_of_nonneg_left hcoef
        (show 0 ≤ r*(1-r) by
          have : 0 ≤ 1-r := by linarith only [hr1]
          positivity)
      nlinarith only [hm]
    _ ≤ _ := div_le_div_of_nonneg_left hN (by positivity) hdenle

private theorem quad_E_lower {a r : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 7/13)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    7*r*(1-r)/(24*(1+2*r)^2) ≤
      ordStrongB a r-ordGapMajorant (a/(1+(1-a/2)*r)) r := by
  let H := 4+(12-7*a)*r+(8-5*a)*r^2
  let Q := (1+r)*(4*(1-a)*(7*r+1)+a*(9*r+11))+2*a*(1-a)*r*(5-r)
  let L := 1+(2-a)*r
  let W := (1+2*r)^2
  have ha0 : 0 < a := by linarith only [ha]
  have haone : a < 1 := by linarith only [ha1]
  have h2a : 0 < 2-a := by linarith only [ha1]
  have hrm : 0 ≤ 1-r := by linarith only [hr1]
  have hH : 0 < H := by
    have : 0 < 12-7*a := by linarith only [ha1]
    have : 0 < 8-5*a := by linarith only [ha1]
    dsimp [H]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hQbound : 7*(1+r)*(1+3*r/2) ≤ Q := by
    have hrem : 0 ≤ (1+r)*((7*a-3)+(35/2-19*a)*r)+2*a*(1-a)*r*(5-r) := by
      have : 0 ≤ 7*a-3 := by linarith only [ha]
      have : 0 ≤ 35/2-19*a := by linarith only [ha1]
      have : 0 ≤ 1-a := by linarith only [ha1]
      have : 0 ≤ 5-r := by linarith only [hr1]
      positivity
    dsimp [Q]
    nlinarith only [hrem]
  have hLbound : L ≤ 1+3*r/2 := by
    have hm := mul_nonneg (show 0 ≤ a-1/2 by linarith only [ha]) hr
    dsimp [L]
    nlinarith only [hm]
  have hQ7 : 7 ≤ Q/((1+r)*L) := by
    rw [le_div_iff₀ (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hLbound (show 0 ≤ 7*(1+r) by positivity)
    nlinarith only [hm,hQbound]
  have hHbound : H ≤ 4*W := by
    have hn : 0 ≤ (4+7*a)*r+(8+5*a)*r^2 := by positivity
    dsimp [H,W]
    nlinarith only [hn]
  have hca : (1/6:ℝ) ≤ a/(2*(2-a)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [ha]
  have hNum : (1/6:ℝ)*r*(1-r)*7 ≤ (a/(2*(2-a)))*r*(1-r)*(Q/((1+r)*L)) := by
    have hm1 := mul_le_mul_of_nonneg_right hca (show 0 ≤ r*(1-r)*7 by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hQ7 (show 0 ≤ (a/(2*(2-a)))*r*(1-r) by positivity)
    nlinarith only [hm1,hm2]
  have hNum0 : 0 ≤ (a/(2*(2-a)))*r*(1-r)*(Q/((1+r)*L)) := by
    have : 0 ≤ (1/6:ℝ)*r*(1-r)*7 := by positivity
    linarith only [hNum,this]
  calc 7*r*(1-r)/(24*(1+2*r)^2) = ((1/6:ℝ)*r*(1-r)*7)/(4*W) := by dsimp [W]; field_simp; ring
    _ ≤ ((a/(2*(2-a)))*r*(1-r)*(Q/((1+r)*L)))/(4*W) :=
      div_le_div_of_nonneg_right hNum (by positivity)
    _ ≤ ((a/(2*(2-a)))*r*(1-r)*(Q/((1+r)*L)))/H :=
      div_le_div_of_nonneg_left hNum0 hH hHbound
    _ = _ := by
      rw [ord_strong_majorant_gain ha0 haone hr hr1]
      dsimp [Q,H,L]
      field_simp (disch := first | positivity | nlinarith)


private theorem quad_curving_costs {a r K : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 7/13)
    (hK : 3/4 < K) (hK1 : K < 9/10) (hr : 0 ≤ r) :
    (1-a)*a*r/(1+(K+3*a)*r) ≤ r/(4*(1+9*r/4)) ∧
    (1-a)*a*r*(2+(2*K+3*a)*r)/(1+(K+3*a)*r)^2 ≤
      r*(2+7*r/2)/(4*(1+9*r/4)^2) := by
  let U := 1+(K+3*a)*r
  let V := 1+9*r/4
  have ha0 : 0 < a := by linarith only [ha]
  have haone : 0 < 1-a := by linarith only [ha1]
  have hcoeff : (1-a)*a ≤ 1/4 := by nlinarith only [sq_nonneg (a-1/2)]
  have hU : 0 < U := by
    have : 0 < K+3*a := by linarith only [hK,ha]
    dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hUV : V ≤ U := by
    have hm := mul_nonneg (show 0 ≤ K+3*a-9/4 by linarith only [hK,ha]) hr
    dsimp [U,V]
    nlinarith only [hm]
  have hN : (1-a)*a*r ≤ r/4 := by
    have hm := mul_le_mul_of_nonneg_right hcoeff hr
    linarith only [hm]
  have hlast : 2+(2*K+3*a)*r ≤ 2+7*r/2 := by
    have hm := mul_nonneg (show 0 ≤ 7/2-(2*K+3*a) by linarith only [hK1,ha1]) hr
    nlinarith only [hm]
  have hlast0 : 0 ≤ 2+(2*K+3*a)*r := by
    have : 0 ≤ 2*K+3*a := by linarith only [hK,ha]
    positivity
  have hN2 : (1-a)*a*r*(2+(2*K+3*a)*r) ≤ (r/4)*(2+7*r/2) :=
    mul_le_mul hN hlast hlast0 (by positivity)
  have hUV2 : V^2 ≤ U^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hUV) (show 0 ≤ U+V by positivity)
    nlinarith only [hm]
  constructor
  · change (1-a)*a*r/U ≤ r/(4*V)
    calc (1-a)*a*r/U ≤ (r/4)/U := div_le_div_of_nonneg_right hN hU.le
      _ ≤ (r/4)/V := div_le_div_of_nonneg_left (by positivity) hV hUV
      _ = _ := by field_simp
  · change (1-a)*a*r*(2+(2*K+3*a)*r)/U^2 ≤ r*(2+7*r/2)/(4*V^2)
    calc (1-a)*a*r*(2+(2*K+3*a)*r)/U^2 ≤ ((r/4)*(2+7*r/2))/U^2 :=
        div_le_div_of_nonneg_right hN2 (sq_nonneg _)
      _ ≤ ((r/4)*(2+7*r/2))/V^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hUV2
      _ = _ := by field_simp

private theorem quad_B_cost {a r : ℝ} (ha1 : a ≤ 7/13)
    (hr : 0 ≤ r) (hr1 : r < 1) (hrecip : 2/ordStrongK a-1 ≤ 8/5) : ordStrongB a r ≤ (13-r)/(5+7*r) := by
  have hden : 0 < 1+(2-a)*r := by
    have : 0 < 2-a := by linarith only [ha1]
    positivity
  have hden0 : 0 < 1+7*r/5 := by positivity
  have hdenle : 1+7*r/5 ≤ 1+(2-a)*r := by
    have hm := mul_nonneg (show 0 ≤ 2-a-7/5 by linarith only [ha1]) hr
    nlinarith only [hm]
  have hrm : 0 ≤ 1-r := by linarith only [hr1]
  have hN := mul_le_mul_of_nonneg_left hrecip hrm
  have hf := (div_le_div_of_nonneg_right hN hden.le).trans
    (div_le_div_of_nonneg_left (show 0 ≤ (1-r)*(8/5) by positivity) hden0 hdenle)
  have he : 1+(1-r)*(8/5)/(1+7*r/5) = (13-r)/(5+7*r) := by field_simp; ring
  dsimp [ordStrongB]
  linarith only [hf,he]

private noncomputable def quadDlb (r : ℝ) : ℝ :=
  r*((19/20)*(1-r)+(1/2)*r)/((1+3*r/10)*(1+13*r/10))
private noncomputable def quadGlb (r : ℝ) : ℝ := r*(1-r)/(5*(1+2*r)^2)
private noncomputable def quadSlopeCost (r : ℝ) : ℝ := r*(2+7*r/2)/(4*(1+9*r/4)^2)
private noncomputable def quadMLoss (r : ℝ) : ℝ := r^2*(1-r)/(4*(1+9*r/4)*(1+r/5))
private noncomputable def quadS (r : ℝ) : ℝ := (1+2*r)^2/r

private theorem quad_D_normalized {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (19/20-9*r/20)*(1+2*r) ≤ quadS r*quadDlb r := by
  let F := 19/20-9*r/20
  let U := 1+2*r
  let V := (1+3*r/10)*(1+13*r/10)
  have hF : 0 < F := by dsimp [F]; linarith only [hr1]
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hVU : V ≤ U := by
    have hp := mul_nonneg hr.le (show 0 ≤ 40-39*r by linarith only [hr1])
    dsimp [V,U]
    nlinarith only [hp]
  have he : quadS r*quadDlb r = F*U^2/V := by
    dsimp [quadS,quadDlb,F,U,V]
    field_simp
    ring
  change F*U ≤ _
  rw [he]
  calc F*U = F*U^2/U := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hV hVU

private theorem quad_slope_normalized {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    quadS r*quadSlopeCost r*((13-r)/(5+7*r)) ≤ 13/10+r/10+(3/10)*r*(1-r) := by
  let U := 1+2*r
  let V := 1+9*r/4
  let B := (4+7*r)*(13-r)/(8*(5+7*r))
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hUV : U ≤ V := by dsimp [U,V]; linarith only [hr]
  have hUV2 : U^2 ≤ V^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hUV) (show 0 ≤ V+U by positivity)
    nlinarith only [hp]
  have hfrac : U^2/V^2 ≤ 1 := (div_le_one (by positivity)).mpr hUV2
  have hB : 0 ≤ B := by
    have : 0 ≤ 13-r := by linarith only [hr1]
    dsimp [B]; positivity
  have he : quadS r*quadSlopeCost r*((13-r)/(5+7*r)) = (U^2/V^2)*B := by
    dsimp [quadS,quadSlopeCost,U,V,B]
    field_simp; ring
  have hscale := mul_le_mul_of_nonneg_right hfrac hB
  have hdiv : B = 13/10+3*r/40+7*r*(1-r)/(5*(5+7*r)) := by
    dsimp [B]
    field_simp; ring
  have hrem : 7/(5*(5+7*r)) ≤ (3/10:ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hr]
  have hrem' := mul_le_mul_of_nonneg_left hrem
    (show 0 ≤ r*(1-r) by
      have : 0 ≤ 1-r := by linarith only [hr1]
      positivity)
  have hrem'' : 7*r*(1-r)/(5*(5+7*r)) ≤ (3/10)*r*(1-r) := by
    convert hrem' using 1 <;> ring
  rw [he]
  nlinarith only [hscale,hdiv,hrem'',hr]

private theorem quad_M_normalized {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    quadS r*quadMLoss r ≤ r*(1-r)*(1+9*r/5)/4 := by
  let U := 1+2*r
  let V := 1+9*r/4
  let W := 1+r/5
  let F := 1+9*r/5
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hUV : U ≤ V := by dsimp [U,V]; linarith only [hr]
  have hUWF : U ≤ W*F := by
    have : 0 ≤ r^2 := sq_nonneg r
    dsimp [U,W,F]
    nlinarith only [this]
  have hprod := mul_le_mul hUV hUWF hU.le hV.le
  have hfrac : U^2/(V*W) ≤ F := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hprod]
  have he : quadS r*quadMLoss r = (r*(1-r)/4)*(U^2/(V*W)) := by
    dsimp [quadS,quadMLoss,U,V,W]
    field_simp
  have hrm : 0 ≤ 1-r := by linarith only [hr1]
  have hm := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ r*(1-r)/4 by positivity)
  rw [he]
  dsimp [F] at hm
  nlinarith only [hm]

private theorem quad_budget_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < quadDlb r+2*quadGlb r-quadSlopeCost r*((13-r)/(5+7*r))-quadMLoss r := by
  have hD := quad_D_normalized hr hr1
  have hSlope := quad_slope_normalized hr hr1
  have hM := quad_M_normalized hr hr1
  have hG : quadS r*(2*quadGlb r) = (2/5)*(1-r) := by
    dsimp [quadS,quadGlb]
    field_simp
  have hpos : 0 < (1+r^3)/20+(2/5)*r*(1-r)^2 := by positivity
  have he : (19/20-9*r/20)*(1+2*r)+(2/5)*(1-r)-
      (13/10+r/10+(3/10)*r*(1-r))-r*(1-r)*(1+9*r/5)/4 =
      (1+r^3)/20+(2/5)*r*(1-r)^2 := by ring
  have hnorm : 0 < quadS r*(quadDlb r+2*quadGlb r-
      quadSlopeCost r*((13-r)/(5+7*r))-quadMLoss r) := by
    nlinarith only [hD,hSlope,hM,hG,hpos,he]
  exact (mul_pos_iff_of_pos_left (by dsimp [quadS]; positivity)).mp hnorm


private theorem quad_scalar_contact {a b r K j : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 7/13)
    (hb : 0 < b) (hbmax : b ≤ a/(1+(1-a/2)*r)) (hr : 0 ≤ r) (hr1 : r < 1)
    (hkK : ordStrongK a ≤ K) (hK1 : K < 9/10) (hkj : ordStrongK a ≤ j)
    (hη : K-ordStrongK a = (1-a)*a*r/(1+(K+3*a)*r))
    (hj : j-ordStrongK a = (1-a)*a*r*(2+(2*K+3*a)*r)/(1+(K+3*a)*r)^2) :
    j*((ss_gB 1 (1-b)-m2Sec (1-b) 1 (1-b*r)) /
        (m2Sec (1-b) 1 (1-b*r)-ss_gB 1 (1-b*r))) < ordContactM a K r := by
  let k := ordStrongK a
  let B := ordStrongB a r
  let B0 := ordStrongB0 k (k-a) r
  let E := B-ordGapMajorant (a/(1+(1-a/2)*r)) r
  let D := ordContactM a k r-k*B0
  have ha0 : 0 < a := by linarith only [ha]
  have haone : a < 1 := by linarith only [ha1]
  have hkall := quad_k_bounds ha ha1
  have hk0 : 0 < k := by dsimp [k]; linarith only [hkall.1]
  have hk1 : k ≤ 4/5 := hkall.2.1
  have hj0 : 0 < j := hk0.trans_le hkj
  have hR := ss_gap_ratio_majorant ha0 haone hb hbmax hr hr1
  rcases hr.eq_or_lt with hrzero | hrpos
  · subst r
    have hjk : j = k := by
      simp only [mul_zero,add_zero] at hj
      dsimp [k]
      linarith only [hj]
    have he : k*ordGapMajorant a 0 = 2 := by
      dsimp [k,ordStrongK,ordGapMajorant]
      have h2 : 0 < 2-a := by linarith only [ha1]
      have h8 : 0 < 8-a := by linarith only [ha1]
      norm_num
      field_simp (disch := first | positivity | nlinarith)
    simp only [mul_zero,add_zero,div_one] at hR
    have hm := mul_lt_mul_of_pos_left hR hk0
    rw [he] at hm
    rw [hjk]
    simpa only [ordContactM,mul_zero,sub_zero,add_zero,mul_one,div_one,one_add_one_eq_two] using hm
  have hD := quad_D_lower ha ha1 hr hr1
  have hGain := quad_denominator_gain ha ha1 hr hr1
  have hE := quad_E_lower ha ha1 hr hr1
  change 7*r*(1-r)/(24*(1+2*r)^2) ≤ E at hE
  have hrm : 0 ≤ 1-r := by linarith only [hr1]
  have hEbase : 0 ≤ 7*r*(1-r)/(24*(1+2*r)^2) := by positivity
  have hJE1 := mul_le_mul_of_nonneg_left hE hj0.le
  have hJE2 := mul_le_mul_of_nonneg_right (show 3/4 ≤ j by linarith only [hkall.1,hkj]) hEbase
  have hJEbase : quadGlb r ≤ (3/4)*(7*r*(1-r)/(24*(1+2*r)^2)) := by
    have hp := mul_nonneg (by norm_num : (0:ℝ) ≤ 3/160) (show 0 ≤ r*(1-r) by positivity)
    dsimp [quadGlb]
    field_simp
    nlinarith only [hp]
  have hJE : quadGlb r ≤ j*E := hJEbase.trans (hJE2.trans hJE1)
  have hK : 3/4 < K := lt_of_lt_of_le hkall.1 hkK
  have hcosts := quad_curving_costs ha ha1 hK hK1 hr
  have hηcost : K-k ≤ r/(4*(1+9*r/4)) := by
    change K-ordStrongK a ≤ _
    rw [hη]
    exact hcosts.1
  have hjcost : j-k ≤ quadSlopeCost r := by
    change j-ordStrongK a ≤ _
    rw [hj]
    exact hcosts.2
  have hBcost := quad_B_cost ha1 hr hr1 hkall.2.2.2.2
  have hrecip0 : 0 ≤ 2/k-1 := by
    rw [sub_nonneg,le_div_iff₀ hk0]
    linarith only [hk1]
  have hB0 : 0 ≤ B := by
    have hden : 0 < 1+(2-a)*r := by
      have : 0 < 2-a := by linarith only [ha1]
      positivity
    change 0 ≤ 1+(1-r)*(2/k-1)/(1+(2-a)*r)
    positivity
  have hSlope : (j-k)*B ≤ quadSlopeCost r*((13-r)/(5+7*r)) :=
    mul_le_mul hjcost hBcost hB0 (by dsimp [quadSlopeCost]; positivity)
  have hMvar := quad_M_variation ha0 haone hkall.2.2.1.le hkK hr hr1
  have hMcost : ordContactM a k r-ordContactM a K r ≤ quadMLoss r := by
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hηcost (show 0 ≤ r*(1-r) by positivity))
      (show 0 ≤ 1+r/5 by positivity)
    have he : (r*(1-r)*(r/(4*(1+9*r/4))))/(1+r/5) = quadMLoss r := by
      dsimp [quadMLoss]
      field_simp
    have hstep : r*(1-r)*(K-k)/(1+r/5) ≤ quadMLoss r := by
      simpa only [he] using hm
    exact hMvar.2.trans hstep
  have hbudget := quad_budget_pos hrpos hr1
  have he : ordContactM a K r-j*ordGapMajorant (a/(1+(1-a/2)*r)) r =
      D+k*(B0-B)+j*E-(j-k)*B-(ordContactM a k r-ordContactM a K r) := by
    dsimp [D,E]
    ring
  change quadDlb r ≤ D at hD
  change quadGlb r ≤ k*(B0-B) at hGain
  have hpos : 0 < ordContactM a K r-j*ordGapMajorant (a/(1+(1-a/2)*r)) r := by
    nlinarith only [he,hD,hGain,hJE,hSlope,hMcost,hbudget]
  have hstrict := mul_lt_mul_of_pos_left hR hj0
  linarith only [hstrict,hpos]


/-- The quadratic lower barrier in the normalized endpoint. -/
noncomputable def ordQuadP (x z : ℝ) : ℝ :=
  1/x+ssKs x*(1-z)+(1/x)*(1-z)^2/(1+3*(1-z))
/-- The negative slope of the quadratic lower barrier. -/
noncomputable def ordQuadJ (x z : ℝ) : ℝ :=
  ssKs x+(1/x)*(1-z)/(1+3*(1-z))+(1/x)*(1-z)/(1+3*(1-z))^2

theorem ord_quadP_hasDerivAt {x z : ℝ} (hx : 0 < x) (hz : z ≤ 1) :
    HasDerivAt (ordQuadP x) (-ordQuadJ x z) z := by
  have hd : 0 < 1+3*(1-z) := by linarith only [hz]
  unfold ordQuadP ordQuadJ
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]
    field_simp (disch := first | positivity | nlinarith)
    ring

theorem ord_quadP_pos {x z : ℝ} (hx : 0 < x) (hz : z ≤ 1) : 0 < ordQuadP x z := by
  have hs : 0 ≤ 1-z := by linarith only [hz]
  have hk : 0 ≤ ssKs x := by unfold ssKs; positivity
  have hd : 0 < 1+3*(1-z) := by positivity
  unfold ordQuadP
  positivity

private theorem quad_cost_identities {a K r : ℝ} (ha : 0 < a) (hK : 0 < K) (hr : 0 ≤ r) :
    (1-a)*(a*r/(1+K*r))/(1+3*(a*r/(1+K*r))) = (1-a)*a*r/(1+(K+3*a)*r) ∧
    (1-a)*(a*r/(1+K*r))/(1+3*(a*r/(1+K*r)))+
      (1-a)*(a*r/(1+K*r))/(1+3*(a*r/(1+K*r)))^2 =
        (1-a)*a*r*(2+(2*K+3*a)*r)/(1+(K+3*a)*r)^2 := by
  have hden : 0 < 1+K*r := by positivity
  have hden2 : 0 < 1+(K+3*a)*r := by positivity
  constructor <;> field_simp (disch := positivity) <;> ring

/-- The curved barrier has a strictly negative derivative at every contact. -/
theorem ss_quad_contact {x z : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hz : z ≤ 1) (hPz : ordQuadP x z < z) :
    ordQuadJ x z*(ss_gB 1 (ordQuadP x z)-m2Sec (ordQuadP x z) 1 z)*z*(x-z) <
      (m2Sec (ordQuadP x z) 1 z-ss_gB 1 z)*((2*z-ordQuadP x z)*x-z^2) := by
  have hx0 : 0 < x := by linarith only [hx]
  let a := 1-1/x
  let k := ordStrongK a
  let s := 1-z
  let p := ordQuadP x z
  let K := k+(1/x)*s/(1+3*s)
  let j := ordQuadJ x z
  let b := 1-p
  let r := s/b
  have hell2 : 1/x ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hx
  have hell6 : 6/13 ≤ 1/x := by
    have hh := one_div_le_one_div_of_le hx0 hx2
    norm_num at hh
    simpa only [one_div] using hh
  have ha : 1/2 ≤ a := by dsimp [a]; linarith only [hell2]
  have ha1 : a ≤ 7/13 := by dsimp [a]; linarith only [hell6]
  have ha0 : 0 < a := by linarith only [ha]
  have haone : a < 1 := by linarith only [ha1]
  have heK : ssKs x = k := by
    have h8 : 0 < 8-a := by linarith only [ha1]
    dsimp [k,a,ordStrongK,ssKs] at *
    field_simp (disch := first | positivity | nlinarith)
    ring
  have hkall := quad_k_bounds ha ha1
  have hk0 : 0 < k := by linarith only [hkall.1]
  have hs : 0 ≤ s := by dsimp [s]; linarith only [hz]
  have hd : 0 < 1+3*s := by positivity
  have hp : 0 < p := ord_quadP_pos hx0 hz
  have hpz : p < z := hPz
  have hP0 : p = 1/x+k*s+(1/x)*s^2/(1+3*s) := by
    dsimp [p,ordQuadP,s]
    rw [heK]
  have hps : 1/x+k*s ≤ p := by
    rw [hP0]
    have hh : 0 ≤ (1/x)*s^2/(1+3*s) := by positivity
    linarith only [hh]
  have hsbar : (1+k)*s < a := by
    have he1 : 1/x = 1-a := by dsimp [a]; ring
    have he2 : z = 1-s := by dsimp [s]; ring
    nlinarith only [hps,hpz,he1,he2]
  have hs1 : s < 1/3 := by
    have hm := mul_nonneg (show 0 ≤ k-3/4 by linarith only [hkall.1]) hs
    nlinarith only [hm,hsbar,ha1]
  have hkK : k ≤ K := by
    have hη0 : 0 ≤ (1/x)*s/(1+3*s) := by positivity
    dsimp [K]
    linarith only [hη0]
  have hK : 0 < K := hk0.trans_le hkK
  have hηbound : (1/x)*s/(1+3*s) < 1/12 := by
    rw [div_lt_iff₀ hd]
    have hm := mul_le_mul_of_nonneg_right hell2 hs
    nlinarith only [hm,hs1]
  have hK1 : K < 9/10 := by dsimp [K]; linarith only [hηbound,hkall.2.1]
  have hjdef : j = K+(1/x)*s/(1+3*s)^2 := by
    dsimp [j,ordQuadJ,K,s]
    rw [heK]
  have hkj : k ≤ j := by
    have hh : 0 ≤ (1/x)*s/(1+3*s)^2 := by positivity
    linarith only [hjdef,hkK,hh]
  have hKden : 0 < 1+K*r := by
    have hb : 0 < b := by dsimp [b]; linarith only [hpz,hz]
    have hr : 0 ≤ r := div_nonneg hs hb.le
    positivity
  have hb : 0 < b := by dsimp [b]; linarith only [hpz,hz]
  have hb1 : b < 1 := by dsimp [b]; linarith only [hp]
  have hr : 0 ≤ r := div_nonneg hs hb.le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hb]
    dsimp [b,s]
    linarith only [hpz]
  have hbr : b*r = s := by dsimp [r]; field_simp
  have hep : p = 1-b := by dsimp [b]; ring
  have hez : z = 1-b*r := by dsimp [s] at hbr; linarith only [hbr]
  have hell : 1-a = 1/x := by dsimp [a]; ring
  have hpK : p = 1-a+K*s := by
    rw [hell,hP0]
    dsimp [K]
    ring
  have hbk : b = a/(1+K*r) := by
    apply (eq_div_iff hKden.ne').mpr
    have hbrK := congrArg (fun v : ℝ => K*v) hbr
    nlinarith only [hpK,hep,hbrK]
  have hsform : s = a*r/(1+K*r) := by
    rw [show a*r/(1+K*r) = (a/(1+K*r))*r by ring,← hbk]
    exact hbr.symm
  have hbmax : b ≤ a/(1+(1-a/2)*r) := by
    rw [hbk]
    have hbase : 0 < 1+(1-a/2)*r := by
      have : 0 < 1-a/2 := by linarith only [ha1]
      positivity
    apply div_le_div_of_nonneg_left ha0.le hbase
    have hkbase := (ord_strong_k_range ha0 haone).2.2
    have hm := mul_nonneg (show 0 ≤ K-(1-a/2) by linarith only [hkbase,hkK]) hr
    linarith only [hm]
  have hη : K-ordStrongK a = (1-a)*a*r/(1+(K+3*a)*r) := by
    have hη0 : K-ordStrongK a = (1/x)*s/(1+3*s) := by dsimp [K,k]; ring
    rw [hη0,← hell,hsform]
    exact (quad_cost_identities ha0 hK hr).1
  have hj : j-ordStrongK a = (1-a)*a*r*(2+(2*K+3*a)*r)/(1+(K+3*a)*r)^2 := by
    have hj0 : j-ordStrongK a = (1/x)*s/(1+3*s)+(1/x)*s/(1+3*s)^2 := by
      rw [hjdef]
      dsimp [K,k]
      ring
    rw [hj0,← hell,hsform]
    exact (quad_cost_identities ha0 hK hr).2
  have hscalar := quad_scalar_contact ha ha1 hb hbmax hr hr1 hkK hK1 hkj hη hj
  rw [← hep,← hez] at hscalar
  have hMeq := ord_contact_threshold_eq ha0 haone hK.le hr hr1
  have haz : 1-a*r/(1+K*r) = z := by
    rw [show a*r/(1+K*r) = (a/(1+K*r))*r by ring,← hbk,← hez]
  rw [haz,← hbk,← hep] at hMeq
  have hphysical : ordContactM a K r = ((2*z-p)*x-z^2)/(z*(x-z)) := by
    rw [hMeq]
    have he1 : 1-(1-a)*z = (x-z)/x := by rw [hell]; field_simp
    have hz0 : 0 < z := hp.trans hpz
    have hzx : 0 < x-z := by linarith only [hx,hz]
    rw [he1]
    field_simp (disch := first | positivity | nlinarith)
    ring
  rw [hphysical] at hscalar
  have hRight : 0 < m2Sec p 1 z-ss_gB 1 z := sub_pos.mpr (ss_sec_gt_right hp hpz hz)
  have hF : 0 < z*(x-z) := mul_pos (hp.trans hpz) (by linarith only [hx,hz])
  have hscalar' : (j*(ss_gB 1 p-m2Sec p 1 z))/(m2Sec p 1 z-ss_gB 1 z) <
      ((2*z-p)*x-z^2)/(z*(x-z)) := by simpa only [mul_div_assoc] using hscalar
  have hc := (div_lt_div_iff₀ hRight hF).mp hscalar'
  dsimp [p,j] at hc
  convert hc using 1 <;> ring


end SmoothedOctagon

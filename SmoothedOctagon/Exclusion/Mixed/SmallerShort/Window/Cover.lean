module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Residual
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Case M2, smaller-short side: the window point satisfies every residual of the cover

For the data `D : M2Short` of a smaller-short window, the point `D.ss_pt` lies in the root box `B₀`
(`ss_box_*`) and every residual `f₀, …, f₂₇` is nonnegative (`ss_f0`, …, `ss_f27`).

## Main API

* `ss_box_r`, `ss_box_delta`, `ss_box_al`, `ss_box_rho`, `ss_box_v`, `ss_box_E`.
* `ss_f0`, …, `ss_f27`; `ss_arctan_split`:
  `arctan(√3 Y/X) = π/6 + arctan((3Y - X)/(√3(X + Y)))` for `X, Y > 0`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmallerShort Real

/-- `A_oct < 2501/800` (as `ff_octagonCost_lt'` of case F). -/
private lemma ss_octagonCost_lt : octagonCost < 2501 / 800 := by
  have h12 : √12 < 3.4641017 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h32 : 5.6568542 < √32 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h8 : 2.8284271 < √8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  have h12p : 0 ≤ √12 := Real.sqrt_nonneg _
  have hD : 0 < √8 - 1 := by linarith
  have hN : 0 ≤ 8 - √32 - Real.log 2 := by
    have : √32 < 5.6569 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [octagonCost, octagonDensity, mul_div_assoc', div_lt_iff₀ hD]
  have : √12 * (8 - √32 - Real.log 2) ≤ 3.4641017 * (8 - √32 - Real.log 2) :=
    mul_le_mul_of_nonneg_right h12.le hN
  nlinarith

/-- **The centred angle**: `arctan(√3 Y/X) = π/6 + arctan s`,
`s = (3Y - X)/(√3(X + Y))`, for `X, Y > 0`. -/
theorem ss_arctan_split {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    arctan (√3 * Y / X) = π / 6 + arctan ((3 * Y - X) / (√3 * (X + Y))) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hlt : (√3)⁻¹ * ((3 * Y - X) / (√3 * (X + Y))) < 1 := by
    have e : (√3)⁻¹ * ((3 * Y - X) / (√3 * (X + Y))) = (3 * Y - X) / (3 * (X + Y)) := by
      field_simp; rw [h3]
    rw [e, div_lt_one (by positivity)]
    linarith
  rw [← Real.arctan_inv_sqrt_three, Real.arctan_add hlt]
  congr 1
  have e1 : (√3)⁻¹ + (3 * Y - X) / (√3 * (X + Y)) = 4 * Y / (√3 * (X + Y)) := by
    field_simp; ring
  have e2 : 1 - (√3)⁻¹ * ((3 * Y - X) / (√3 * (X + Y))) = 4 * X / (3 * (X + Y)) := by
    have e : (√3)⁻¹ * ((3 * Y - X) / (√3 * (X + Y))) = (3 * Y - X) / (3 * (X + Y)) := by
      field_simp; rw [h3]
    rw [e]; field_simp; ring
  rw [e1, e2]
  field_simp
  rw [h3]

namespace M2Short

variable (D : M2Short)

/-! ### The root box -/

theorem ss_box_rho : 1 / 226 ≤ D.a ^ 2 / (D.a ^ 2 + 4) ∧ D.a ^ 2 / (D.a ^ 2 + 4) ≤ 3 / 20 := by
  have := D.a_ge; have := D.scale; have := D.a_pos
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; linarith

theorem ss_box_v : 3 / 4 ≤ D.v ∧ D.v ≤ 1 := by
  refine ⟨D.ss_v_ge, ?_⟩
  have h := D.ss_Ut
  have : 0 < D.a / (D.a + D.b) := by have := D.a_pos; have := D.ss_b_pos; positivity
  have := D.ss_t_le
  nlinarith

/-- `E² < 13/4 - 16(17/20)²(27/256) < (23/16)²`. -/
theorem ss_E_sq : D.E ^ 2 < (23 / 16) ^ 2 := by
  have hρ := D.ss_box_rho
  have hv := D.ss_box_v
  have hu := D.ss_u_le
  have hu0 : 0 ≤ D.u := by
    have := ss_sec_ge_34 D.a_pos D.ss_C_pos D.ss_B_pos; rw [← D.u_eq] at this; linarith
  set ρ := D.a ^ 2 / (D.a ^ 2 + 4) with hρdef
  have hΓ : 16 * D.Γ * (1 - ρ) ^ 2 = 4 * D.v * D.u - D.E ^ 2 := by
    rw [D.Γ_eq, hρdef]; unfold m2Gam
    have : 1 - D.a ^ 2 / (D.a ^ 2 + 4) ≠ 0 := by rw [← hρdef]; linarith [hρ.2]
    field_simp
  have h1 : (17 / 20) ^ 2 ≤ (1 - ρ) ^ 2 := by nlinarith [hρ.1, hρ.2]
  have h2 : 27 / 256 * (17 / 20) ^ 2 < D.Γ * (1 - ρ) ^ 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 (by norm_num))
      (mul_lt_mul_of_pos_right D.cas_gt (pow_pos (by linarith [hρ.2]) 2))
  have h4 : D.v * D.u ≤ 1 * (13 / 16) := mul_le_mul hv.2 hu hu0 (by norm_num)
  nlinarith

theorem ss_box_E : -23 / 16 ≤ D.E ∧ D.E ≤ 9 / 20 := by
  have h := D.ss_E_sq
  have hup := ss_E_le_three (by have := D.a_pos; have := D.ss_C_pos; positivity) D.ss_r_le
    (by have := D.a_pos; have := D.ss_b_pos; positivity) D.ss_t_le
    (by have := D.a_pos; positivity) D.ss_rho_le D.ss_Ur D.ss_Ut D.ss_E'
  constructor
  · nlinarith
  · linarith [D.ss_box_rho.2]

theorem ss_box_r : 1 / 10 ≤ D.a / (D.a + D.C) ∧ D.a / (D.a + D.C) ≤ 1 / 2 := by
  refine ⟨?_, D.ss_r_le⟩
  have ha := D.a_pos; have hb := D.ss_b_pos; have hC := D.ss_C_pos
  set r := D.a / (D.a + D.C) with hr
  set t := D.a / (D.a + D.b) with ht
  set ρ := D.a ^ 2 / (D.a ^ 2 + 4) with hρ
  have hr0 : 0 < r := by positivity
  have ht0 : 0 < t := by positivity
  have hρ0 : 0 < ρ := by positivity
  have hρrt : ρ ≤ r * t := D.ss_rho_le
  have htr : t ≤ r := D.ss_t_le_r
  have hUt : D.v ≤ 1 - t + t ^ 2 := D.ss_Ut
  have hE : D.E = 1 + r + t - ρ + Real.log (ρ / (r * t)) - (1 - D.u) / r - (1 - D.v) / t :=
    D.ss_E'
  have hl : Real.log (ρ / (r * t)) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one (by positivity)).2 hρrt)
  have h1 : 1 - t ≤ (1 - D.v) / t := by rw [le_div_iff₀ ht0]; nlinarith
  have h2 : 3 / 16 / r ≤ (1 - D.u) / r := by
    apply div_le_div_of_nonneg_right _ hr0.le; linarith [D.ss_u_le]
  have hEr : D.E ≤ 3 * r - 3 / 16 / r := by
    rw [hE]; linarith
  have hlow := D.ss_box_E.1
  by_contra hcon
  push Not at hcon
  have : -23 / 16 < 3 * r - 3 / 16 / r := by linarith [D.ss_E_sq, hlow]
  have : -23 / 16 ≤ 3 * r - 3 / 16 / r := by linarith
  rw [show 3 * r - 3 / 16 / r = (48 * r ^ 2 - 3) / (16 * r) by field_simp; ring,
    le_div_iff₀ (by positivity)] at this
  nlinarith

theorem ss_box_delta : 0 ≤ D.B / D.C - 1 ∧ D.B / D.C - 1 ≤ 2 := by
  have hC := D.ss_C_pos; have hB := D.ss_B_pos
  constructor
  · rw [sub_nonneg, le_div_iff₀ hC]; linarith [D.ss_C_le_B]
  · have hg := D.u_ge.trans D.ss_u_le
    unfold m2g at hg
    rw [div_le_iff₀ (by positivity)] at hg
    rw [sub_le_iff_le_add, div_le_iff₀ hC]
    nlinarith [D.ss_C_le_B]

theorem ss_box_al : 1 ≤ D.A / D.a ∧ D.A / D.a ≤ 631 / 100 := by
  have ha := D.a_pos; have hA := D.ss_A_pos
  constructor
  · rw [le_div_iff₀ ha]; linarith [D.a_le_A]
  · rw [div_le_iff₀ ha]
    have := D.scale_A; have := D.a_ge
    nlinarith

/-! ### The residuals -/

theorem ss_f0 : 0 ≤ D.ss_pt.f0 := by rw [Point.f0, ss_pt_u, ss_pt_ua, sub_self]

theorem ss_f1 : 0 ≤ D.ss_pt.f1 := by rw [Point.f1, ss_pt_u, ss_pt_r]; linarith [D.ss_Ur]

theorem ss_f2 : 0 ≤ D.ss_pt.f2 := by
  rw [Point.f2, ss_pt_r, ss_pt_v, ss_pt_rho]
  exact ss_v_floor (by have := D.a_pos; have := D.ss_C_pos; positivity) D.ss_t_le D.ss_rho_le
    D.ss_Ut

theorem ss_f3 : 0 ≤ D.ss_pt.f3 := by
  rw [Point.f3, ss_pt_A, ss_pt_u, ss_pt_al, ss_pt_be]
  have hA := D.ss_A_pos; have hB := D.ss_B_pos; have ha := D.a_pos
  have h1 : D.A * D.B / (D.A + D.B) ^ 2 ≤ 1 - D.u := by
    have := D.ss_UrA
    have e : D.A / (D.A + D.B) - (D.A / (D.A + D.B)) ^ 2 = D.A * D.B / (D.A + D.B) ^ 2 := by
      field_simp; ring
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ((D.A + D.B) / D.a))
  have e2 : ((D.A + D.B) / D.a) ^ 2 * (D.A * D.B / (D.A + D.B) ^ 2) = D.A / D.a * (D.B / D.a) := by
    field_simp
  linarith

theorem ss_f4 : 0 ≤ D.ss_pt.f4 := by rw [Point.f4, ss_pt_gam]; linarith [D.cas_gt]

theorem ss_f5 : 0 ≤ D.ss_pt.f5 := by rw [Point.f5, ss_pt_gam]; linarith [D.cas_lt]

theorem ss_f6 : 0 ≤ D.ss_pt.f6 := by rw [Point.f6, ss_pt_w]; linarith [D.w_ge]

theorem ss_f7 : 0 ≤ D.ss_pt.f7 := by
  rw [Point.f7, ss_pt_w, ss_pt_ti]
  have hA := D.ss_A_pos; have hB := D.ss_B_pos
  have hti : D.A ^ 2 / (D.A ^ 2 + 4) / (D.A / (D.A + D.B)) ≤ D.A / (D.A + D.Pf) := by
    rw [div_le_iff₀ (by positivity)]; linarith [D.ss_rhoA_le]
  have h0 : 0 ≤ D.A ^ 2 / (D.A ^ 2 + 4) / (D.A / (D.A + D.B)) := by positivity
  have hU := ss_m2U_anti hti (by linarith [D.ss_tA_le])
  unfold m2U at hU
  linarith [D.ss_UtA]

theorem ss_f8 : 0 ≤ D.ss_pt.f8 := by
  rw [Point.f8, Point.Rbar, Point.m0, Point.zeta, ss_pt_ti, ss_pt_TB, ss_pt_w, ss_pt_EL, ss_pt_u,
    ss_pt_rhoA, mul_one_div, one_div_one_div]
  have hA := D.ss_A_pos; have hB := D.ss_B_pos; have hP := D.ss_Pf_pos
  exact ss_Rbar (by positivity) (by positivity) D.ss_tA_le (by positivity) D.ss_rhoA_le D.w_ge
    D.ss_UtA D.ss_EL'

theorem ss_f9 : 0 ≤ D.ss_pt.f9 := by
  rw [Point.f9, ss_pt_rhoA]
  have := D.scale_A
  have : D.A ^ 2 / (D.A ^ 2 + 4) ≤ 3 / 20 := by rw [div_le_iff₀ (by positivity)]; linarith
  linarith

theorem ss_f10 : 0 ≤ D.ss_pt.f10 := by
  rw [Point.f10, ss_pt_rhoA, ss_pt_EL]
  have hA := D.ss_A_pos; have hB := D.ss_B_pos; have hP := D.ss_Pf_pos
  have := ss_E_le_three (by positivity) D.ss_rA_le (by positivity) D.ss_tA_le (by positivity)
    D.ss_rhoA_le D.ss_UrA D.ss_UtA D.ss_EL'
  linarith

theorem ss_f11 : 0 ≤ D.ss_pt.f11 := by
  rw [Point.f11, Point.gap1, ss_pt_r, ss_pt_rho, ss_pt_v, ss_pt_E, ss_pt_u]
  have ha := D.a_pos; have hb := D.ss_b_pos; have hC := D.ss_C_pos
  exact ss_gap_nonneg (by positivity) (by positivity) D.ss_t_le (by positivity) D.ss_rho_le
    D.ss_Ut D.ss_E'

theorem ss_f12 : 0 ≤ D.ss_pt.f12 := by
  rw [Point.f12, Point.Eupperpoly, ss_pt_r, ss_pt_rho, ss_pt_v, ss_pt_E, ss_pt_u]
  have ha := D.a_pos; have hb := D.ss_b_pos
  have := ss_E_upper (by positivity) D.ss_t_le_r (by positivity) D.ss_rho_le D.ss_Ut D.ss_E'
  have e : 2 * (D.a / (D.a + D.C)) * (D.a / (D.a + D.C)) ^ 2 = 2 * (D.a / (D.a + D.C)) ^ 3 := by
    ring
  linarith

theorem ss_f13 : 0 ≤ D.ss_pt.f13 := by
  rw [Point.f13, ss_pt_rho, ss_pt_E]
  have ha := D.a_pos; have hb := D.ss_b_pos; have hC := D.ss_C_pos
  have := ss_E_le_three (by positivity) D.ss_r_le (by positivity) D.ss_t_le (by positivity)
    D.ss_rho_le D.ss_Ur D.ss_Ut D.ss_E'
  linarith

theorem ss_f14 : 0 ≤ D.ss_pt.f14 := D.mid

theorem ss_f15 : 0 ≤ D.ss_pt.f15 := by
  rw [Point.f15, Point.fouter, ss_pt_rhoA, ss_pt_w, ss_pt_EL, ss_pt_u, ss_pt_ra]
  have hA := D.ss_A_pos; have hB := D.ss_B_pos; have hP := D.ss_Pf_pos
  exact ss_gap_nonneg (by positivity) (by positivity) D.ss_tA_le (by positivity) D.ss_rhoA_le
    D.ss_UtA D.ss_EL'

theorem ss_f16 : 0 ≤ D.ss_pt.f16 := by
  rw [Point.f16, ss_pt_r, ss_pt_rho]
  have h := D.ss_rho_le
  have := mul_le_mul_of_nonneg_left D.ss_t_le_r
    (by have := D.a_pos; have := D.ss_C_pos; positivity : (0 : ℝ) ≤ D.a / (D.a + D.C))
  nlinarith

theorem ss_f17 : 0 ≤ D.ss_pt.f17 := by
  rw [Point.f17, ss_pt_x, ss_pt_al, sub_nonneg]
  exact div_le_div_of_nonneg_right D.A_lt_C.le D.a_pos.le

theorem ss_f18 : 0 ≤ D.ss_pt.f18 := by
  rw [Point.f18, ss_pt_al, ss_pt_delta, ss_pt_x]
  have ha := D.a_pos; have hC := D.ss_C_pos
  have hS := ss_order D.a_pos D.a_lt_C D.ss_A_pos D.A_lt_C D.ss_C_le_B (D.u_eq.symm.trans D.u_eq')
  have e : D.A / D.a - 1 - (D.B / D.C - 1) * (1 + 2 * (D.C / D.a) / 7) =
      (D.A - (D.a * D.B / D.C + 2 / 7 * (D.B - D.C))) / D.a := by
    field_simp; ring
  rw [e]
  exact div_nonneg (by linarith) ha.le

theorem ss_f19 : 0 ≤ D.ss_pt.f19 := by
  rw [Point.f19, ss_pt_rho, ss_pt_al, ss_pt_be]
  have ha := D.a_pos; have hA := D.ss_A_pos; have hB := D.ss_B_pos
  have hc := D.central_A
  have h2 : (D.B + D.A) * (2 * D.A) ≤ (D.B + D.A) * (D.A + D.Pf) :=
    mul_le_mul_of_nonneg_left (by linarith [D.A_lt_Pf]) (by positivity)
  have e : 1 - D.a ^ 2 / (D.a ^ 2 + 4) * ((D.A / D.a) ^ 2 + 2 * (D.A / D.a) * (D.B / D.a) + 1) =
      (4 - D.A ^ 2 - 2 * D.A * D.B) / (D.a ^ 2 + 4) := by
    field_simp; ring
  rw [e]
  exact div_nonneg (by nlinarith) (by positivity)

theorem ss_f20 : 0 ≤ D.ss_pt.f20 := by
  rw [Point.f20, ss_pt_rho, ss_pt_be, ss_pt_x]
  have ha := D.a_pos
  have e : 1 - D.a ^ 2 / (D.a ^ 2 + 4) * (1 + D.B / D.a * (D.C / D.a)) =
      (4 - D.C * D.B) / (D.a ^ 2 + 4) := by
    field_simp; ring
  rw [e]
  exact div_nonneg (by linarith [D.star_CB]) (by positivity)

theorem ss_f21 : 0 ≤ D.ss_pt.f21 := by
  rw [Point.f21, ss_pt_u, ss_pt_delta]
  have hC := D.ss_C_pos; have hB := D.ss_B_pos
  have hg := D.u_ge
  unfold m2g at hg
  rw [div_le_iff₀ (by positivity)] at hg
  have e : (D.u - 1) * (2 + (D.B / D.C - 1)) ^ 2 + (1 + (D.B / D.C - 1)) =
      ((D.u - 1) * (D.C + D.B) ^ 2 + D.C * D.B) / D.C ^ 2 := by
    field_simp; ring
  rw [e]
  exact div_nonneg (by nlinarith) (by positivity)

theorem ss_f22 : 0 ≤ D.ss_pt.f22 := by rw [Point.f22, ss_pt_u]; linarith [D.ss_u_le]

/-- The defect field, read at `D.ss_pt`. -/
theorem ss_defect : 2 * D.ss_pt.Tk ≤ D.ss_pt.AA ∧ 0 < D.ss_pt.BB ∧ D.ss_pt.BB < D.ss_pt.AA ∧
    4 * D.ss_pt.Tk ≤ D.ss_pt.AA + D.ss_pt.BB ∧
    D.ss_pt.cost + (D.ss_pt.kap + 3 / 2) * (π / 3 - arctan (√3 * D.ss_pt.BB / D.ss_pt.AA)) ≤
      octagonCost := D.defect

theorem ss_f23 : 0 ≤ D.ss_pt.f23 := by rw [Point.f23]; linarith [D.ss_defect.1]

theorem ss_f24 : 0 ≤ D.ss_pt.f24 := by rw [Point.f24]; exact D.ss_defect.2.1.le

theorem ss_f25 : 0 ≤ D.ss_pt.f25 := by rw [Point.f25]; linarith [D.ss_defect.2.2.1]

theorem ss_f26 : 0 ≤ D.ss_pt.f26 := by rw [Point.f26]; linarith [D.ss_defect.2.2.2.1]

theorem ss_f27 : 0 ≤ D.ss_pt.f27 := by
  obtain ⟨h1, h2, h3, -, h5⟩ := D.ss_defect
  have hAA : 0 < D.ss_pt.AA := by linarith
  rw [ss_arctan_split hAA h2] at h5
  rw [Point.f27, Point.excess, Point.thetaCentered]
  have hk : 0 ≤ D.ss_pt.kap := Real.sqrt_nonneg _
  have hpi := Real.pi_gt_d4
  have hoct := ss_octagonCost_lt
  have : (D.ss_pt.kap + 3 / 2) * (6283 / 12000 - arctan ((3 * D.ss_pt.BB - D.ss_pt.AA) /
      (√3 * (D.ss_pt.AA + D.ss_pt.BB)))) ≤ (D.ss_pt.kap + 3 / 2) * (π / 3 - (π / 6 +
      arctan ((3 * D.ss_pt.BB - D.ss_pt.AA) / (√3 * (D.ss_pt.AA + D.ss_pt.BB))))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

end M2Short

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.Window
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Secant
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Centre

/-!
# Case M2, smaller-short side: the window data in the cover's coordinates

For the scalar data `D : M2Short` of a smaller-short window, `D.ss_pt` is the point
`(r, δ, α, ρ, v, E) = (a/(a + C), B/C - 1, A/a, a²/(a² + 4), v, E)` of the cover; its derived
quantities are those of the window (`ss_pt_u`: the cover's `u` is the actual common turn norm,
`ss_pt_ua`, `ss_pt_w`, `ss_pt_EL`, `ss_pt_gam`, ...).

## Main API

* `M2Short.ss_pt`; the basic facts `ss_C_le_B` (bridge order), `ss_u_le` (`u ≤ 13/16`),
  `ss_v_ge` (`3/4 ≤ v`), `ss_rho_le` (`ρ ≤ rt`), `ss_rhoA_le` (`ρ_A ≤ r_A t_A`), the incident
  norm bounds `ss_Ur`, `ss_Ut`, `ss_UrA`, `ss_UtA` and centre stationarity `ss_E'`, `ss_EL'` in
  ratio form.
* The point identities `ss_pt_*`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmallerShort

namespace M2Short

variable (D : M2Short)

/-- The point of the cover given by the window. -/
noncomputable def ss_pt : Point :=
  ⟨D.a / (D.a + D.C), D.B / D.C - 1, D.A / D.a, D.a ^ 2 / (D.a ^ 2 + 4), D.v, D.E⟩

theorem ss_b_pos : 0 < D.b := by linarith [D.a_pos, D.a_lt_b]
theorem ss_C_pos : 0 < D.C := by linarith [D.a_pos, D.a_lt_C]
theorem ss_A_pos : 0 < D.A := by linarith [D.a_pos, D.a_le_A]
theorem ss_B_pos : 0 < D.B := by linarith [D.a_pos, D.a_le_A, D.A_lt_B]
theorem ss_Pf_pos : 0 < D.Pf := by linarith [D.a_pos, D.a_le_A, D.A_lt_Pf]
theorem ss_pb_pos : 0 < D.pb := by linarith [D.a_pos, D.a_le_pb]

/-- **The bridge order** `C ≤ B`. -/
theorem ss_C_le_B : D.C ≤ D.B :=
  ss_bridge_order D.a_pos D.a_le_A D.A_lt_B D.u_eq D.u_eq' D.u_le'

/-- **`u ≤ 13/16`**. -/
theorem ss_u_le : D.u ≤ 13 / 16 := SmoothedOctagon.ss_u_le D.a_pos D.a_lt_C D.ss_C_le_B D.u_eq D.u_ge

theorem ss_v_ge : 3 / 4 ≤ D.v := D.v_eq ▸ ss_sec_ge_34 D.a_pos D.ss_b_pos D.ss_pb_pos

theorem ss_r_le : D.a / (D.a + D.C) ≤ 1 / 2 := by
  have := D.a_pos; have := D.a_lt_C
  rw [div_le_iff₀ (by linarith)]; linarith

theorem ss_t_le : D.a / (D.a + D.b) ≤ 1 / 2 := by
  have := D.a_pos; have := D.a_lt_b
  rw [div_le_iff₀ (by linarith)]; linarith

theorem ss_rA_le : D.A / (D.A + D.B) ≤ 1 / 2 := by
  have := D.ss_A_pos; have := D.A_lt_B
  rw [div_le_iff₀ (by linarith)]; linarith

theorem ss_tA_le : D.A / (D.A + D.Pf) ≤ 1 / 2 := by
  have := D.ss_A_pos; have := D.A_lt_Pf
  rw [div_le_iff₀ (by linarith)]; linarith

theorem ss_t_le_r : D.a / (D.a + D.b) ≤ D.a / (D.a + D.C) :=
  div_le_div_of_nonneg_left D.a_pos.le (by linarith [D.a_pos, D.ss_C_pos]) (by linarith [D.C_le_b])

/-- `ρ ≤ rt` (the positive central factor). -/
theorem ss_rho_le : D.a ^ 2 / (D.a ^ 2 + 4) ≤ D.a / (D.a + D.C) * (D.a / (D.a + D.b)) := by
  have ha := D.a_pos; have hb := D.ss_b_pos; have hC := D.ss_C_pos
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have key := mul_le_mul_of_nonneg_left D.central.le (sq_nonneg D.a)
  calc D.a ^ 2 * ((D.a + D.C) * (D.a + D.b)) = D.a ^ 2 * ((D.a + D.b) * (D.a + D.C)) := by ring
    _ ≤ D.a ^ 2 * (D.a ^ 2 + 4) := key
    _ = D.a * D.a * (D.a ^ 2 + 4) := by ring

/-- `ρ_A ≤ r_A t_A` (the positive factor of the outer centre). -/
theorem ss_rhoA_le : D.A ^ 2 / (D.A ^ 2 + 4) ≤ D.A / (D.A + D.B) * (D.A / (D.A + D.Pf)) := by
  have hA := D.ss_A_pos; have hB := D.ss_B_pos; have hP := D.ss_Pf_pos
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have key := mul_le_mul_of_nonneg_left D.central_A.le (sq_nonneg D.A)
  calc D.A ^ 2 * ((D.A + D.B) * (D.A + D.Pf)) = D.A ^ 2 * ((D.B + D.A) * (D.A + D.Pf)) := by ring
    _ ≤ D.A ^ 2 * (D.A ^ 2 + 4) := key
    _ = D.A * D.A * (D.A ^ 2 + 4) := by ring

theorem ss_Ur : D.u ≤ 1 - D.a / (D.a + D.C) + (D.a / (D.a + D.C)) ^ 2 := by
  have h := D.u_le
  rw [m2g_eq_m2U (by linarith [D.a_pos, D.ss_C_pos])] at h
  exact h

theorem ss_Ut : D.v ≤ 1 - D.a / (D.a + D.b) + (D.a / (D.a + D.b)) ^ 2 := by
  have h := D.v_le
  rw [m2g_eq_m2U (by linarith [D.a_pos, D.ss_b_pos])] at h
  exact h

theorem ss_UrA : D.u ≤ 1 - D.A / (D.A + D.B) + (D.A / (D.A + D.B)) ^ 2 := by
  have h := D.u_le'
  rw [m2g_comm, m2g_eq_m2U (by linarith [D.ss_A_pos, D.ss_B_pos])] at h
  exact h

theorem ss_UtA : D.w ≤ 1 - D.A / (D.A + D.Pf) + (D.A / (D.A + D.Pf)) ^ 2 := by
  have h := D.w_le
  rw [m2g_eq_m2U (by linarith [D.ss_A_pos, D.ss_Pf_pos])] at h
  exact h

/-- Centre stationarity at `a`, in the ratios `r = a/(a + C)`, `t = a/(a + b)`. -/
theorem ss_E' : D.E = 1 + D.a / (D.a + D.C) + D.a / (D.a + D.b) - D.a ^ 2 / (D.a ^ 2 + 4) +
    Real.log (D.a ^ 2 / (D.a ^ 2 + 4) / (D.a / (D.a + D.C) * (D.a / (D.a + D.b)))) -
    (1 - D.u) / (D.a / (D.a + D.C)) - (1 - D.v) / (D.a / (D.a + D.b)) := by
  rw [D.E_eq]; unfold m2E
  rw [show D.a / (D.a + D.b) * (D.a / (D.a + D.C)) = D.a / (D.a + D.C) * (D.a / (D.a + D.b)) from
    mul_comm _ _]
  ring

/-- Centre stationarity at `A`, in the ratios `r_A = A/(A + B)`, `t_A = A/(A + P_f)`. -/
theorem ss_EL' : D.EL = 1 + D.A / (D.A + D.B) + D.A / (D.A + D.Pf) - D.A ^ 2 / (D.A ^ 2 + 4) +
    Real.log (D.A ^ 2 / (D.A ^ 2 + 4) / (D.A / (D.A + D.B) * (D.A / (D.A + D.Pf)))) -
    (1 - D.u) / (D.A / (D.A + D.B)) - (1 - D.w) / (D.A / (D.A + D.Pf)) := by
  rw [D.EL_eq]; rfl

/-! ### The point -/

theorem ss_pt_r : D.ss_pt.r = D.a / (D.a + D.C) := rfl
theorem ss_pt_delta : D.ss_pt.delta = D.B / D.C - 1 := rfl
theorem ss_pt_al : D.ss_pt.al = D.A / D.a := rfl
theorem ss_pt_rho : D.ss_pt.rho = D.a ^ 2 / (D.a ^ 2 + 4) := rfl
theorem ss_pt_v : D.ss_pt.v = D.v := rfl
theorem ss_pt_E : D.ss_pt.E = D.E := rfl

theorem ss_pt_x : D.ss_pt.x = D.C / D.a := by
  have := D.a_pos; have := D.ss_C_pos
  rw [Point.x, ss_pt_r]; field_simp; ring

theorem ss_pt_be : D.ss_pt.be = D.B / D.a := by
  have := D.a_pos; have := D.ss_C_pos
  rw [Point.be, ss_pt_x, ss_pt_delta]; field_simp; ring

theorem ss_pt_A : D.ss_pt.A = (D.A + D.B) / D.a := by
  rw [Point.A, ss_pt_be, ss_pt_al]; ring

theorem ss_pt_u : D.ss_pt.u = D.u := by
  have ha := D.a_pos; have hC := D.ss_C_pos; have hB := D.ss_B_pos
  rw [D.u_eq, ss_sec_logDiv ha hC hB]
  have hxi : D.ss_pt.xi = D.C / (D.a + D.C) := by
    rw [Point.xi, ss_pt_r]; field_simp; ring
  have hh : D.ss_pt.h = (D.B + D.C) / (D.a + D.C) := by
    rw [Point.h, hxi, ss_pt_delta]; field_simp; ring
  rw [Point.u, hxi, hh, ss_pt_delta]
  have e : D.C / (D.a + D.C) / (2 + (D.B / D.C - 1)) =
      (D.C / (D.a + D.C)) ^ 2 / ((D.B + D.C) / (D.a + D.C)) := by
    have : D.B + D.C ≠ 0 := by positivity
    rw [show 2 + (D.B / D.C - 1) = (D.B + D.C) / D.C by field_simp; ring]
    field_simp
  rw [e]

theorem ss_pt_ua : D.ss_pt.ua = D.u := by
  have ha := D.a_pos; have hC := D.ss_C_pos; have hB := D.ss_B_pos; have hA := D.ss_A_pos
  rw [D.u_eq', m2Sec_comm, ss_sec_logDiv hA hB hC]
  have hax : D.ss_pt.ax = D.A / D.C := by
    rw [Point.ax, ss_pt_al, ss_pt_r]
    have : 1 - D.a / (D.a + D.C) = D.C / (D.a + D.C) := by field_simp; ring
    rw [this]; field_simp
  have hden : 1 + D.ss_pt.delta + D.ss_pt.ax = (D.A + D.B) / D.C := by
    rw [hax, ss_pt_delta]; field_simp; ring
  have hha : D.ss_pt.ha = (D.C + D.B) / (D.A + D.B) := by
    rw [Point.ha, hden, ss_pt_delta]; field_simp; ring
  have hxa : D.ss_pt.xa = D.B / (D.A + D.B) := by
    rw [Point.xa, hden, ss_pt_delta]; field_simp; ring
  rw [Point.ua, hha, hxa]

theorem ss_pt_gam : D.ss_pt.gam = D.Γ := by
  rw [D.Γ_eq, Point.gam, ss_pt_u, ss_pt_v, ss_pt_E, ss_pt_rho]; unfold m2Gam; ring

theorem ss_pt_lam : D.ss_pt.lam = (D.a ^ 2 + 4) / (D.A ^ 2 + 4) := by
  have := D.a_pos
  have e : 1 + D.a ^ 2 / (D.a ^ 2 + 4) * ((D.A / D.a) ^ 2 - 1) = (D.A ^ 2 + 4) / (D.a ^ 2 + 4) := by
    field_simp; ring
  rw [Point.lam, ss_pt_rho, ss_pt_al, e, one_div_div]

theorem ss_pt_D : D.ss_pt.D = (D.A / D.a) ^ 2 + 2 * (D.A / D.a) * (D.B / D.a) + 1 +
    2 * (D.C / D.a) - 2 * (D.B / D.a) * (D.C / D.a) := by
  rw [Point.D, ss_pt_be, ss_pt_x, ss_pt_al]

theorem ss_pt_w : D.ss_pt.w = D.w := by
  rw [D.w_transport, Point.w, Point.ed, ss_pt_lam, ss_pt_D, ss_pt_u, ss_pt_v, ss_pt_E, ss_pt_rho]
  ring

theorem ss_pt_EL : D.ss_pt.EL = D.EL := by
  rw [D.EL_transport, Point.EL, Point.ed, ss_pt_lam, ss_pt_D, ss_pt_u, ss_pt_E, ss_pt_rho]
  ring

theorem ss_pt_rhoA : D.ss_pt.rhoA = D.A ^ 2 / (D.A ^ 2 + 4) := by
  have := D.a_pos
  rw [Point.rhoA, ss_pt_lam, ss_pt_al, ss_pt_rho]; field_simp

theorem ss_pt_ti : D.ss_pt.ti = D.A ^ 2 / (D.A ^ 2 + 4) / (D.A / (D.A + D.B)) := by
  have := D.a_pos; have := D.ss_A_pos; have := D.ss_B_pos
  rw [Point.ti, ss_pt_lam, ss_pt_rho, ss_pt_al, ss_pt_A]; field_simp

theorem ss_pt_TB : D.ss_pt.TB = 1 / (D.A / (D.A + D.B)) := by
  have := D.a_pos; have := D.ss_A_pos; have := D.ss_B_pos
  rw [Point.TB, ss_pt_A, ss_pt_al]; field_simp

theorem ss_pt_ra : D.ss_pt.ra = D.A / (D.A + D.B) := by
  have := D.a_pos; have := D.ss_A_pos; have := D.ss_B_pos
  rw [Point.ra, ss_pt_A, ss_pt_al]; field_simp

end M2Short

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Order
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Envelope
public import SmoothedOctagon.Exclusion.Mixed.Short.Cover

/-!
# Hand proof of the smaller-short case: the normalized actual data

The actual data of a smaller-short window (`M2Short`), normalized by the central margin `a`, as a
record of real numbers with exactly the facts the hand gates S0-S6 use
(`MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION` §§1-5, `MIXED_GENERAL_SHORT_DEFECT_INTERFACE`;
inventories HS-S01 §3, HS-S2 §3, HS-S3 §3, HS-S4 §3, HS-S567 §3). The five inventories found that
the `M2Short` interface does not have to grow: every field below is an existing `M2Short` field or
an existing `ss_*` lemma, rewritten in the normalized coordinates. The gates are proved for an
`HsData` (plain reals) and transferred to `M2Short` by `M2Short.toHs`.

## Main API

* `HsData`: `x = C/a`, `be = B/a`, `al = A/a`, `rho = a²/(a² + 4)`, `t = a/(a + b)`, the norms
  `u, v, w`, the pairings `E, EL`, the Casimir `Γ` and the outer root parameter `τ = (A + P_f)/A`,
  with the shape, the opposite-turn range, centre stationarity, the Gram transport, the outer root
  (`EL_eq` at the outer centre, `root`), both Casimir forms and bounds, and the window defect at the
  point `HsData.pt = ⟨r, δ, α, ρ, v, E⟩` of the cover.
* `M2Short.toHs`: the normalized data of an actual window.
* Derived actual facts: `HsData.root_zero` (`R_τ(t, v) = 0`), `HsData.q_lt_seventh` (`ρ_A < 1/7`,
  `HAND_PROOF_REFINEMENTS` §2 at the outer centre), `HsData.u_le_V`, `HsData.u_ge_34`,
  `HsData.be_le_al_x`, `HsData.q_le_qc`, the orders `HsData.strong_order`, `HsData.upper_order_54`,
  `HsData.upper_order_98`, and `HsData.strong_box` (`α ≥ 1 + 13δ/5` for `x ≥ 2`,
  `HAND_PERIOD_EXCLUSION` (3)).
* `HsData.SmallShape`: the common small-shape domain (`HAND_PERIOD_EXCLUSION` (5), without `η`).

Not provided (not needed by any gate, inventories HS-S01 §0, HS-S567 §0.4): a strict `w > 3/4` (not
derivable from the `M2Short` fields alone; every gate uses only `w ≥ 3/4`) and a strict descending
root `w < U(1/τ)`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Certificates.SmallerShort

/-- **The normalized actual data of a smaller-short window** (inventory HS-S567 §3, items A1-A18).
All quantities are normalized by the central margin `a`; `τ = (A + P_f)/A` is the actual outer root
parameter (`t_A = 1/τ`), `q = hsQ al rho = ρ_A`, `r_A = hsRA al be`. -/
structure HsData where
  /-- `x = C/a`. -/
  x : ℝ
  /-- `β = B/a`. -/
  be : ℝ
  /-- `α = A/a`. -/
  al : ℝ
  /-- `ρ = a²/(a² + 4)`. -/
  rho : ℝ
  /-- `t = a/(a + b)`. -/
  t : ℝ
  u : ℝ
  v : ℝ
  E : ℝ
  w : ℝ
  EL : ℝ
  Γ : ℝ
  /-- `τ = (A + P_f)/A`. -/
  τ : ℝ
  /-- The shape (`SIX_VARIABLE_REDUCTION` (1)): `1 < x`, `1 ≤ α < x ≤ β`. -/
  one_lt_x : 1 < x
  /-- The root box `r ≥ 1/10` (`ss_box_r`). -/
  x_le_nine : x ≤ 9
  one_le_al : 1 ≤ al
  al_lt_x : al < x
  x_le_be : x ≤ be
  /-- The strengthened order (S) (`ss_order`). -/
  order27 : be / x + 2 / 7 * (be - x) ≤ al
  /-- The equal turn secants (`u_eq`, `u_eq'`). -/
  u_eq : u = m2Sec 1 x be
  u_eq' : u = m2Sec al be x
  /-- The forward switch `C → B` (`u_ge`): `g(x/β) ≤ u`. -/
  u_ge : m2g x be ≤ u
  /-- The incident ceilings `u ≤ U(r)`, `u ≤ U(r_A)` (`ss_Ur`, `ss_UrA`). -/
  u_le_r : u ≤ m2U (1 / (1 + x))
  u_le_rA : u ≤ m2U (hsRA al be)
  /-- The opposite-turn range (`SIX_VARIABLE_REDUCTION` (8)). -/
  rho_pos : 0 < rho
  rho_le : rho ≤ 3 / 20
  t_pos : 0 < t
  t_le_r : t ≤ 1 / (1 + x)
  rho_lt_rt : rho < 1 / (1 + x) * t
  v_ge : 3 / 4 ≤ v
  v_le : v ≤ m2U t
  /-- Centre stationarity at `a` (`E_eq`, `ss_E'`). -/
  E_eq : E = hsE x rho u t v
  /-- The Gram transport (`w_transport`, `EL_transport`). -/
  w_eq : w = hsW x be al rho u t v
  EL_eq : EL = hsEL x be al rho u t v
  /-- The outer root: `2 < τ < T = r_A/q` (`A_lt_Pf`, `central_A`). -/
  two_lt_τ : 2 < τ
  τ_lt : τ * hsQ al rho < hsRA al be
  /-- The outer norm: `3/4 ≤ w ≤ U(1/τ)` (`w_ge`, `ss_UtA`). -/
  w_ge : 3 / 4 ≤ w
  w_le : w ≤ m2U (1 / τ)
  /-- Centre stationarity at `A` (`EL_eq`, `ss_EL'`), the actual outer root. -/
  root : EL = (w - 1) * τ + 1 / τ + (u - 1) / hsRA al be + hsRA al be + 1 - hsQ al rho +
    log (τ * hsQ al rho / hsRA al be)
  /-- The outer scale cap `A² < 12/17` (`scale_A`). -/
  q_lt : hsQ al rho < 3 / 20
  /-- The two Gram determinants and the Casimir bounds (`Γ_eq`, `Γ_eq'`, `cas_lt`, `cas_gt`). -/
  Γ_eq : Γ = hsGam rho u v E
  Γ_eq' : Γ = hsGam (hsQ al rho) u w EL
  cas_lt : Γ < 9193 / 50000
  cas_gt : 27 / 256 < Γ
  /-- The cover's incoming norm at the actual point is `u` (`ss_pt_u`). -/
  pt_u : (⟨1 / (1 + x), be / x - 1, al, rho, v, E⟩ : Point).u = u
  /-- The window-defect inequality (`M2Short.defect`). -/
  defect :
    let pt : Point := ⟨1 / (1 + x), be / x - 1, al, rho, v, E⟩
    2 * pt.Tk ≤ pt.AA ∧ 0 < pt.BB ∧ pt.BB < pt.AA ∧ 4 * pt.Tk ≤ pt.AA + pt.BB ∧
      pt.cost + (pt.kap + 3 / 2) * (π / 3 - arctan (√3 * pt.BB / pt.AA)) ≤ octagonCost

namespace HsData

variable (H : HsData)

/-- The displacement `δ = β/x - 1 = B/C - 1`. -/
noncomputable def δ : ℝ := H.be / H.x - 1

/-- The outer scale `q = ρ_A`. -/
noncomputable def q : ℝ := hsQ H.al H.rho

/-- The cover's point `⟨r, δ, α, ρ, v, E⟩` (`M2Short.ss_pt`). -/
noncomputable def pt : Point := ⟨1 / (1 + H.x), H.be / H.x - 1, H.al, H.rho, H.v, H.E⟩

/-- **The common small-shape domain** (`HAND_PERIOD_EXCLUSION` (5), stated without `η`:
`13δ/5 ≤ α - 1 ≤ 3δ`; closed endpoints). -/
structure SmallShape : Prop where
  x_ge : 2 ≤ H.x
  x_le : H.x ≤ 13 / 6
  δ_nonneg : 0 ≤ H.δ
  δ_le : H.δ ≤ 1 / 19
  al_ge : 1 + 13 / 5 * H.δ ≤ H.al
  al_le : H.al ≤ 1 + 3 * H.δ

/-! ### Derived actual facts -/

/-- **The actual outer root** (`SIX_VARIABLE_REDUCTION` §4, inventory HS-S01 M17, HS-S567 I.4):
`R_τ(t, v) = 0` at the actual opposite turn (`root`, `E_eq`, `w_eq`, `EL_eq`). Status: stable. -/
theorem root_zero : hsR H.x H.be H.al H.rho H.u H.τ H.t H.v = 0 := by
  unfold hsR
  rw [← H.w_eq, ← H.EL_eq, H.root]
  ring

/-- `3/4 ≤ u` (`ss_sec_ge_34`). Status: stable. -/
theorem u_ge_34 : 3 / 4 ≤ H.u := by
  have hx := H.one_lt_x
  rw [H.u_eq]
  exact ss_sec_ge_34 one_pos (by linarith) (by linarith [H.x_le_be])

/-- **`u ≤ V(x)`** (`hs_u_le_V`; inventory HS-S3 R6). Status: stable. -/
theorem u_le_V : H.u ≤ m2Sec 1 H.x H.x := by
  rw [H.u_eq]
  exact hs_u_le_V H.one_lt_x H.x_le_be (by rw [← H.u_eq]; exact H.u_ge)

/-- `β ≤ αx` (from `order27`). Status: stable. -/
theorem be_le_al_x : H.be ≤ H.al * H.x := by
  have hx0 : 0 < H.x := by linarith [H.one_lt_x]
  have h : H.be / H.x ≤ H.al := by linarith [H.order27, H.x_le_be]
  exact (div_le_iff₀ hx0).1 h

/-- `q ≤ q_c` (`ρ < rt ≤ r²`, `hs_q_le_qc_iff`). Status: stable. -/
theorem q_le_qc : H.q ≤ hsQc H.x H.al := by
  have hx0 : 0 < H.x := by linarith [H.one_lt_x]
  unfold HsData.q
  rw [hs_q_le_qc_iff hx0 H.one_le_al H.rho_pos]
  have h1 : 1 / (1 + H.x) * H.t ≤ 1 / (1 + H.x) * (1 / (1 + H.x)) :=
    mul_le_mul_of_nonneg_left H.t_le_r (by positivity)
  have e : 1 / (1 + H.x) * (1 / (1 + H.x)) = 1 / (1 + H.x) ^ 2 := by
    rw [sq, one_div_mul_one_div]
  linarith [H.rho_lt_rt]

/-- **The outer scale bound `q = ρ_A < 1/7`** (`HAND_PROOF_REFINEMENTS` §2 at the outer centre,
`hs_rev_centre_scale` with `r = r_A`, `t = 1/τ`, norms `u, w`, pairing `E_L`; inventory HS-S01 M16,
HS-S2 R6, HS-S3 R1). Status: stable. -/
theorem q_lt_seventh : H.q < 1 / 7 := by
  have hal0 : 0 < H.al := by linarith [H.one_le_al]
  have hbe0 : 0 < H.be := by linarith [H.x_le_be, H.one_lt_x]
  have hτ : 0 < H.τ := by linarith [H.two_lt_τ]
  have hrA0 : 0 < hsRA H.al H.be := by unfold hsRA; positivity
  have hrA2 : hsRA H.al H.be < 1 / 2 := by
    unfold hsRA; rw [div_lt_iff₀ (by positivity)]; linarith [H.al_lt_x, H.x_le_be]
  have hq0 : 0 < H.q := by
    unfold HsData.q hsQ hsLam
    have h1 : 0 ≤ H.al ^ 2 - 1 := by nlinarith [H.one_le_al]
    have : 0 < 1 + H.rho * (H.al ^ 2 - 1) := by nlinarith [mul_nonneg H.rho_pos.le h1]
    have := H.rho_pos
    positivity
  have hτq := H.τ_lt
  refine hs_rev_centre_scale (r := hsRA H.al H.be) (t := 1 / H.τ) (ρ := H.q) (u := H.u)
    (v := H.w) (E := H.EL) hrA0 hrA2 (by positivity) ?_ hq0 ?_ H.q_lt H.u_ge_34 H.u_le_rA
    H.w_ge H.w_le ?_ ?_
  · rw [div_lt_iff₀ hτ]; linarith [H.two_lt_τ]
  · rw [mul_one_div, lt_div_iff₀ hτ]
    unfold HsData.q
    linarith
  · rw [H.root]
    have e : H.q / (hsRA H.al H.be * (1 / H.τ)) = H.τ * hsQ H.al H.rho / hsRA H.al H.be := by
      unfold HsData.q; field_simp
    rw [e]
    unfold HsData.q
    field_simp
    ring
  · have h := H.cas_lt
    rw [H.Γ_eq'] at h
    exact h

/-- **The strong lower order** at the actual shape (`hs_strong_order`). Status: stable. -/
theorem strong_order : H.be / H.x + hsKs H.x * (H.be - H.x) ≤ H.al :=
  hs_strong_order H.one_lt_x H.x_le_nine H.one_le_al H.al_lt_x H.x_le_be (H.u_eq.symm.trans H.u_eq')

/-- **The global upper order `5/4`** at the actual shape (`hs_upper_order_54`). Status: stable. -/
theorem upper_order_54 : H.al ≤ H.be / H.x + 5 / 4 * (H.be - H.x) :=
  hs_upper_order_54 H.one_lt_x H.one_le_al H.al_lt_x H.x_le_be (H.u_eq.symm.trans H.u_eq')

/-- **The global upper order `9/8`** at the actual shape (`hs_upper_order_98`). Status: stable. -/
theorem upper_order_98 (hx5 : H.x ≤ 5) : H.al ≤ H.be / H.x + 9 / 8 * (H.be - H.x) :=
  hs_upper_order_98 H.one_lt_x hx5 H.one_le_al H.al_lt_x H.x_le_be (H.u_eq.symm.trans H.u_eq')

/-- **The strong order on the small box** (`HAND_PERIOD_EXCLUSION` (3)): for `x ≥ 2`,
`α ≥ 1 + (1 + 4x(x + 1)/(7x + 1))δ ≥ 1 + 13δ/5` (`4x(x + 1)/(7x + 1)` increases, `8/5` at `2`).
Status: stable. -/
theorem strong_box (hx : 2 ≤ H.x) : 1 + 13 / 5 * H.δ ≤ H.al := by
  have h := H.strong_order
  have hx0 : 0 < H.x := by linarith
  have hδ : 0 ≤ H.δ := by
    unfold HsData.δ; rw [sub_nonneg, le_div_iff₀ hx0]; linarith [H.x_le_be]
  have hbe : H.be = H.x * (1 + H.δ) := by unfold HsData.δ; field_simp; ring
  have hk : 8 / 5 ≤ hsKs H.x * H.x := by
    unfold hsKs; rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith
  have e1 : H.be / H.x = 1 + H.δ := by rw [hbe]; field_simp
  have e2 : hsKs H.x * (H.be - H.x) = hsKs H.x * H.x * H.δ := by rw [hbe]; ring
  rw [e1, e2] at h
  nlinarith [mul_le_mul_of_nonneg_right hk hδ]

end HsData

/-! ### The actual window -/

namespace M2Short

variable (D : M2Short)

/-- **The normalized actual data are an `HsData`** (inventory HS-S567 §3: every field is an
`M2Short` field or an `ss_*` lemma: `a_lt_C`, `ss_box_r`, `a_le_A`, `A_lt_C`, `ss_C_le_B`,
`ss_order`, `u_eq`, `u_eq'` with `ss_sec_scale` and `m2Sec_comm`, `u_ge`, `ss_Ur`, `ss_UrA`,
`ss_box_rho`, `ss_t_le_r`, `central`, `ss_v_ge`, `ss_Ut`, `ss_E'`, `w_transport`, `EL_transport`
with `ss_pt_lam`, `A_lt_Pf`, `central_A`, `w_ge`, `ss_UtA`, `ss_EL'` (`t_A = 1/τ`), `scale_A`,
`Γ_eq`, `Γ_eq'` (`ss_pt_rhoA`), `cas_lt`, `cas_gt`, `ss_pt_u`, `defect`; the point
`⟨1/(1 + C/a), (B/a)/(C/a) - 1, A/a, ρ, v, E⟩` is `D.ss_pt`). Status: stable. -/
theorem toHs_spec : ∃ H : HsData, H.x = D.C / D.a ∧ H.be = D.B / D.a ∧ H.al = D.A / D.a ∧
    H.rho = D.a ^ 2 / (D.a ^ 2 + 4) ∧ H.t = D.a / (D.a + D.b) ∧ H.u = D.u ∧ H.v = D.v ∧
    H.E = D.E ∧ H.w = D.w ∧ H.EL = D.EL ∧ H.Γ = D.Γ ∧ H.τ = (D.A + D.Pf) / D.A := by
  have ha := D.a_pos
  have hC := D.ss_C_pos
  have hB := D.ss_B_pos
  have hA := D.ss_A_pos
  have hb := D.ss_b_pos
  have hPf := D.ss_Pf_pos
  have e_r : 1 / (1 + D.C / D.a) = D.a / (D.a + D.C) := by field_simp
  have e_lam : hsLam (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) = (D.a ^ 2 + 4) / (D.A ^ 2 + 4) := by
    unfold hsLam
    have e : 1 + D.a ^ 2 / (D.a ^ 2 + 4) * ((D.A / D.a) ^ 2 - 1) =
        (D.A ^ 2 + 4) / (D.a ^ 2 + 4) := by
      field_simp; ring
    rw [e, one_div_div]
  have e_q : hsQ (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) = D.A ^ 2 / (D.A ^ 2 + 4) := by
    unfold hsQ; rw [e_lam]; field_simp
  have e_rA : hsRA (D.A / D.a) (D.B / D.a) = D.A / (D.A + D.B) := by unfold hsRA; field_simp
  have e_tA : 1 / ((D.A + D.Pf) / D.A) = D.A / (D.A + D.Pf) := by rw [one_div_div]
  have e_pt : (⟨1 / (1 + D.C / D.a), D.B / D.a / (D.C / D.a) - 1, D.A / D.a,
      D.a ^ 2 / (D.a ^ 2 + 4), D.v, D.E⟩ : Point) = D.ss_pt := by
    unfold M2Short.ss_pt
    rw [e_r, div_div_div_cancel_right₀ ha.ne']
  have hE : D.E = hsE (D.C / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) D.u (D.a / (D.a + D.b)) D.v := by
    rw [D.ss_E']
    unfold hsE
    have e1 : D.a ^ 2 / (D.a ^ 2 + 4) * (1 + D.C / D.a) / (D.a / (D.a + D.b)) =
        D.a ^ 2 / (D.a ^ 2 + 4) / (D.a / (D.a + D.C) * (D.a / (D.a + D.b))) := by
      field_simp
    rw [e1, e_r]
    have e2 : (D.u - 1) * (1 + D.C / D.a) = -((1 - D.u) / (D.a / (D.a + D.C))) := by
      field_simp; ring
    rw [e2]
    ring
  refine ⟨
    { x := D.C / D.a, be := D.B / D.a, al := D.A / D.a, rho := D.a ^ 2 / (D.a ^ 2 + 4),
      t := D.a / (D.a + D.b), u := D.u, v := D.v, E := D.E, w := D.w, EL := D.EL, Γ := D.Γ,
      τ := (D.A + D.Pf) / D.A,
      one_lt_x := (one_lt_div ha).2 D.a_lt_C,
      x_le_nine := ?_,
      one_le_al := (one_le_div ha).2 D.a_le_A,
      al_lt_x := div_lt_div_of_pos_right D.A_lt_C ha,
      x_le_be := div_le_div_of_nonneg_right D.ss_C_le_B ha.le,
      order27 := ?_, u_eq := ?_, u_eq' := ?_, u_ge := ?_,
      u_le_r := by rw [e_r]; exact D.ss_Ur,
      u_le_rA := by rw [e_rA]; exact D.ss_UrA,
      rho_pos := by positivity,
      rho_le := D.ss_box_rho.2,
      t_pos := by positivity,
      t_le_r := by rw [e_r]; exact D.ss_t_le_r,
      rho_lt_rt := ?_,
      v_ge := D.ss_v_ge,
      v_le := D.ss_Ut,
      E_eq := hE,
      w_eq := ?_, EL_eq := ?_,
      two_lt_τ := by rw [lt_div_iff₀ hA]; linarith [D.A_lt_Pf],
      τ_lt := ?_,
      w_ge := D.w_ge,
      w_le := by rw [e_tA]; exact D.ss_UtA,
      root := ?_, q_lt := ?_,
      Γ_eq := by rw [D.Γ_eq]; unfold m2Gam hsGam; ring,
      Γ_eq' := by rw [D.Γ_eq', e_q]; unfold m2Gam hsGam; ring,
      cas_lt := D.cas_lt, cas_gt := D.cas_gt,
      pt_u := by rw [e_pt]; exact D.ss_pt_u,
      defect := by
        intro pt
        have hpt : pt = D.ss_pt := e_pt
        rw [hpt]
        exact D.ss_defect },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h := D.ss_box_r.1
    rw [le_div_iff₀ (by positivity)] at h
    rw [div_le_iff₀ ha]
    linarith
  · have h := ss_order ha D.a_lt_C hA D.A_lt_C D.ss_C_le_B (D.u_eq.symm.trans D.u_eq')
    have e : D.B / D.a / (D.C / D.a) + 2 / 7 * (D.B / D.a - D.C / D.a) =
        (D.a * D.B / D.C + 2 / 7 * (D.B - D.C)) / D.a := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h ha.le
  · rw [D.u_eq, ← ss_sec_scale (c := 1 / D.a) (by positivity) ha hC hB]
    congr 1 <;> field_simp
  · rw [D.u_eq', m2Sec_comm, ← ss_sec_scale (c := 1 / D.a) (by positivity) hA hB hC]
    congr 1 <;> field_simp
  · have e : m2g (D.C / D.a) (D.B / D.a) = m2g D.C D.B := by
      unfold m2g; field_simp
    rw [e]
    exact D.u_ge
  · rw [e_r, div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by positivity)]
    have key := mul_lt_mul_of_pos_left D.central (pow_pos ha 2)
    calc D.a ^ 2 * ((D.a + D.C) * (D.a + D.b)) = D.a ^ 2 * ((D.a + D.b) * (D.a + D.C)) := by ring
      _ < D.a ^ 2 * (D.a ^ 2 + 4) := key
      _ = D.a * D.a * (D.a ^ 2 + 4) := by ring
  · rw [D.w_transport]
    unfold hsW
    rw [← hE, e_lam]
    unfold hsDg
    ring
  · rw [D.EL_transport]
    unfold hsEL
    rw [← hE, e_lam]
    unfold hsDg
    ring
  · rw [e_q, e_rA, div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by positivity)]
    have key := mul_lt_mul_of_pos_left D.central_A (pow_pos hA 3)
    nlinarith
  · rw [D.ss_EL', e_q, e_rA]
    have e1 : D.A ^ 2 / (D.A ^ 2 + 4) / (D.A / (D.A + D.B) * (D.A / (D.A + D.Pf))) =
        (D.A + D.Pf) / D.A * (D.A ^ 2 / (D.A ^ 2 + 4)) / (D.A / (D.A + D.B)) := by
      field_simp
    rw [e1, e_tA]
    field_simp
    ring
  · rw [e_q, div_lt_iff₀ (by positivity)]
    linarith [D.scale_A]

/-- The normalized actual data (`toHs_spec`). -/
noncomputable def toHs : HsData := D.toHs_spec.choose

theorem toHs_x : D.toHs.x = D.C / D.a := D.toHs_spec.choose_spec.1
theorem toHs_be : D.toHs.be = D.B / D.a := D.toHs_spec.choose_spec.2.1
theorem toHs_al : D.toHs.al = D.A / D.a := D.toHs_spec.choose_spec.2.2.1
theorem toHs_rho : D.toHs.rho = D.a ^ 2 / (D.a ^ 2 + 4) := D.toHs_spec.choose_spec.2.2.2.1
theorem toHs_v : D.toHs.v = D.v := D.toHs_spec.choose_spec.2.2.2.2.2.2.1
theorem toHs_E : D.toHs.E = D.E := D.toHs_spec.choose_spec.2.2.2.2.2.2.2.1
theorem toHs_EL : D.toHs.EL = D.EL := D.toHs_spec.choose_spec.2.2.2.2.2.2.2.2.2.1
theorem toHs_Γ : D.toHs.Γ = D.Γ := D.toHs_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.1

theorem toHs_δ : D.toHs.δ = D.B / D.C - 1 := by
  have ha := D.a_pos
  rw [HsData.δ, toHs_x, toHs_be, div_div_div_cancel_right₀ ha.ne']

/-- The normalized point is the cover's point `D.ss_pt`. -/
theorem toHs_pt : D.toHs.pt = D.ss_pt := by
  have ha := D.a_pos
  have hC := D.ss_C_pos
  rw [HsData.pt, M2Short.ss_pt, toHs_x, toHs_be, toHs_al, toHs_rho, toHs_v, toHs_E,
    div_div_div_cancel_right₀ ha.ne']
  congr 1
  field_simp

/-- **The strong order on the small box** for the actual window (`HsData.strong_box`):
for `C/a ≥ 2`, `A/a ≥ 1 + (13/5)(B/C - 1)`. -/
theorem hs_strong_box (h1 : 2 ≤ D.C / D.a) : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a := by
  have h := D.toHs.strong_box (by rwa [D.toHs_x])
  rwa [D.toHs_δ, D.toHs_al] at h

/-- The small-shape domain for the actual window is the domain of its normalized data. -/
theorem hs_smallShape (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : 0 ≤ D.B / D.C - 1) (h4 : D.B / D.C - 1 ≤ 1 / 19)
    (h5 : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a) (h6 : D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1)) :
    D.toHs.SmallShape := by
  rw [← D.toHs_x] at h1 h2
  rw [← D.toHs_δ] at h3 h4 h5 h6
  rw [← D.toHs_al] at h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end M2Short

end SmoothedOctagon

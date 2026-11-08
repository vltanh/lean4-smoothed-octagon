module

public import SmoothedOctagon.Exclusion.Mixed.Comparison
public import SmoothedOctagon.Exclusion.Mixed.ChartAux.Phi

/-!
# Case M2: the boundary point of an actual window in the cover coordinates

`MIXED_NONSHORT_BLOWUP_REDUCTION` (BLOWUP) §1, (2)-(17b), `MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION`
§4, inventory E2 entries 12-16, 22. A point `p` of the covers *represents* the boundary of the
window `W` (`chAt W p`) if it has `a = W.a`, `c = W.c`, `l0 = 0`, `ε > 0`, `z₁ = δ₁ = (d - a)/(a + c)`
and `z₂ = δ₂ = (c + d)(d + r)/(d² + 4) - 1`. Both charts of `M2Window.chartPt` represent it.

## Main API

* `chAt`; `ch_at_d`, `ch_at_W`, `ch_at_Q`, `ch_at_Z`, `ch_at_r`, `ch_at_v`, … (the cover's
  reconstruction returns the actual `d, W, Q, Z, r, v`).
* `ch_at_phi`: `ε² Φ = R_d(U*; b*)`; `ch_at_u`, `ch_at_h`, `ch_at_w`, `ch_at_tn`, `ch_at_excess`:
  the cover's `u, h, w, tn, excess` are `u*, h*, w*, t*, γ²(u*, v, h*) - 23/125`.
* `ch_at_retained`: the sixteen common residuals `g₀, …, g₁₅` are nonnegative.
* `ch_F_strictMono`: `q ↦ F_x(q)` is strictly increasing on `[q₁, q₂] ⊂ (1, ∞)` for `x > 1/2`.
* `ch_d_le_c`: if `δ₁ < δ₂` then `d ≤ c` (BLOWUP (2b)-(2c), inventory E2 entry 12); hence
  `ch_at_g16`.
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates.Nonshort

/-- The point `p` of the covers represents the boundary point of the window `W`. -/
def chAt (W : M2Window) (p : Point) : Prop :=
  p.a = W.a ∧ p.c = W.c ∧ p.l0 = 0 ∧ 0 < p.eps ∧ p.z1 = (W.d - W.a) / (W.a + W.c) ∧
    p.z2 = (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) - 1

section

variable {W : M2Window} {p : Point}

private theorem pos_facts (W : M2Window) :
    0 < W.a ∧ 0 < W.c ∧ 0 < W.d ∧ 0 < W.r ∧ 0 < W.a + W.c ∧ 0 < W.c + W.d ∧ 0 < W.d + W.r ∧
      0 < W.d ^ 2 + 4 ∧ 0 < W.a ^ 2 + 4 := by
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hr : 0 < W.r := by linarith [W.a_le_r]
  exact ⟨ha, hc, hd, hr, by linarith, by linarith, by linarith, by positivity, by positivity⟩

theorem ch_at_T0 (hp : chAt W p) : p.T0 = W.a + W.c := by
  unfold Point.T0; rw [hp.1, hp.2.1]

theorem ch_at_K (hp : chAt W p) : p.K = W.a ^ 2 + 4 := by
  unfold Point.K; rw [hp.1]

theorem ch_at_z1 (hp : chAt W p) : 0 < p.z1 := by
  obtain ⟨_, _, _, _, hT, -⟩ := pos_facts W
  rw [hp.2.2.2.2.1]; exact div_pos (by linarith [W.a_lt_d]) hT

theorem ch_at_z2 (hp : chAt W p) : 0 < p.z2 := by
  obtain ⟨-, -, -, -, -, -, -, hQ, -⟩ := pos_facts W
  rw [hp.2.2.2.2.2, sub_pos, lt_div_iff₀ hQ, one_mul]; exact W.factor_d

theorem ch_at_d (hp : chAt W p) : p.d = W.d := by
  obtain ⟨_, _, _, _, hT, -⟩ := pos_facts W
  unfold Point.d; rw [ch_at_T0 hp, hp.2.2.2.2.1, hp.1]; field_simp; ring

theorem ch_at_W (hp : chAt W p) : p.W = W.c + W.d := by
  obtain ⟨_, _, _, _, hT, -⟩ := pos_facts W
  unfold Point.W; rw [ch_at_T0 hp, hp.2.2.2.2.1]; field_simp; ring

theorem ch_at_Q (hp : chAt W p) : p.Q = W.d ^ 2 + 4 := by
  unfold Point.Q; rw [ch_at_d hp]

theorem ch_at_q (hp : chAt W p) : p.q = (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) := by
  unfold Point.q; rw [hp.2.2.2.2.2]; ring

theorem ch_at_Z (hp : chAt W p) : p.Z = W.d + W.r := by
  obtain ⟨-, -, -, -, -, hW, -, hQ, -⟩ := pos_facts W
  unfold Point.Z; rw [ch_at_Q hp, ch_at_q hp, ch_at_W hp]; field_simp

theorem ch_at_r (hp : chAt W p) : p.r = W.r := by
  unfold Point.r; rw [ch_at_Z hp, ch_at_d hp]; ring

theorem ch_at_Y (hp : chAt W p) : p.Y = m2Y W.a W.c W.d := by
  unfold Point.Y m2Y; rw [ch_at_W hp, ch_at_T0 hp]

theorem ch_at_v (hp : chAt W p) : p.v = W.v := by
  obtain ⟨ha, hc, -⟩ := pos_facts W
  rw [ch_pt_v p (hp.1 ▸ ha) (hp.2.1 ▸ hc) (ch_at_z1 hp), hp.1, hp.2.1, ch_at_d hp, W.v_eq]

theorem ch_at_bStar (hp : chAt W p) : p.K / p.T0 - p.a = W.bStar := by
  rw [ch_at_K hp, ch_at_T0 hp, hp.1]; rfl

/-- `ε² Φ = R_d(U*; b*)` at the actual boundary point (BLOWUP (13), inventory E2 entry 22). -/
theorem ch_at_phi (hp : chAt W p) :
    p.eps ^ 2 * p.phi = m2RootAt W.a W.bStar W.c W.d W.r W.v W.ceilStar := by
  obtain ⟨ha, hc, -⟩ := pos_facts W
  rw [ch_phi_root p hp.2.2.1 (hp.1 ▸ ha) (hp.2.1 ▸ hc) (ch_at_z1 hp).le (ch_at_z2 hp).le,
    ch_at_bStar hp, ch_at_d hp, ch_at_r hp, ch_at_v hp, ch_at_T0 hp, ch_at_K hp, hp.1, hp.2.1]
  rfl

/-- `Φ* < 0`: the comparison `G(b*) < 0` (`m2_comparison`) in chart coordinates. -/
theorem ch_at_phi_neg (hp : chAt W p) : p.phi < 0 := by
  have h := ch_at_phi hp
  have hG := (m2_comparison W).1
  rw [← h] at hG
  have : 0 < p.eps ^ 2 := by have := hp.2.2.2.1; positivity
  by_contra hc
  push Not at hc
  have := mul_nonneg this.le hc
  linarith

theorem ch_at_D1 (hp : chAt W p) : p.eps * p.D1 = -chRu W.a W.bStar W.c W.d W.r := by
  obtain ⟨ha, hc, -⟩ := pos_facts W
  rw [ch_D1 p hp.2.2.1 (hp.1 ▸ ha) (hp.2.1 ▸ hc) (ch_at_z1 hp).le (ch_at_z2 hp).le,
    ch_at_bStar hp, ch_at_d hp, ch_at_r hp, hp.1, hp.2.1]

/-- The cover's `u` is the boundary root `u*` (BLOWUP (13)). -/
theorem ch_at_u (hp : chAt W p) : p.u = W.uStar := by
  obtain ⟨ha, hc, hd, hr, hT, hWd, hZ, hQ, hK⟩ := pos_facts W
  have heps := hp.2.2.2.1
  have hRu : chRu W.a W.bStar W.c W.d W.r < 0 := by
    have hbb : W.a + W.bStar = (W.a ^ 2 + 4) / (W.a + W.c) := by
      unfold M2Window.bStar m2bStar; ring
    refine ch_Ru_neg ha hc W.a_lt_d W.factor_d (by rw [hbb]; positivity) ?_
    rw [hbb]; field_simp; rfl
  have hD1 : p.eps * p.D1 = -chRu W.a W.bStar W.c W.d W.r := ch_at_D1 hp
  have hD1ne : p.D1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hD1; linarith
  have hphi := ch_at_phi hp
  have haff : m2RootAt W.a W.bStar W.c W.d W.r W.v W.ceilStar =
      m2RootAt W.a W.bStar W.c W.d W.r W.v 0 + W.ceilStar * chRu W.a W.bStar W.c W.d W.r := by
    unfold m2RootAt; exact ch_root_affine ha.ne'
  have hR1 : m2RootAt W.a W.bStar W.c W.d W.r W.v 1 - m2RootAt W.a W.bStar W.c W.d W.r W.v 0 =
      chRu W.a W.bStar W.c W.d W.r := by
    unfold m2RootAt; rw [ch_root_affine (u := 1) ha.ne']; ring
  unfold M2Window.uStar m2uRoot
  rw [hR1]
  have hu : p.u = W.ceilStar + p.eps * p.phi / p.D1 := by
    unfold Point.u Point.du Point.shift Point.u0 Point.z0 M2Window.ceilStar
    rw [hp.2.2.1, Point.rr, ch_at_T0 hp, ch_at_K hp, hp.1, mul_zero]
    unfold m2U; ring
  rw [hu]
  have hR0 : m2RootAt W.a W.bStar W.c W.d W.r W.v 0 =
      p.eps ^ 2 * p.phi - W.ceilStar * chRu W.a W.bStar W.c W.d W.r := by linarith
  rw [hR0, show chRu W.a W.bStar W.c W.d W.r = -(p.eps * p.D1) by linarith]
  have : p.eps ≠ 0 := heps.ne'
  field_simp
  ring

theorem ch_at_h (hp : chAt W p) : p.h = W.hStar := by
  obtain ⟨ha, hc, -⟩ := pos_facts W
  rw [ch_pt_h p hp.2.2.1 (hp.1 ▸ ha) (hp.2.1 ▸ hc), ch_at_bStar hp, ch_at_u hp, ch_at_v hp, hp.1,
    hp.2.1]
  rfl

theorem ch_at_w (hp : chAt W p) : p.w = W.wStar := by
  rw [ch_pt_w p, ch_at_u hp, ch_at_v hp, ch_at_h hp, hp.1, hp.2.1, ch_at_d hp]; rfl

theorem ch_at_tn (hp : chAt W p) : p.tn = W.tStar := by
  rw [ch_pt_tn p, ch_at_u hp, ch_at_v hp, ch_at_h hp, hp.1, hp.2.1, ch_at_d hp, ch_at_r hp]; rfl

theorem ch_at_excess (hp : chAt W p) :
    p.excess = m2Cas W.a W.uStar W.v W.hStar - 23 / 125 := by
  obtain ⟨ha, hc, -⟩ := pos_facts W
  rw [ch_pt_excess p (hp.1 ▸ ha) (hp.2.1 ▸ hc), ch_at_u hp, ch_at_v hp, ch_at_h hp, hp.1]

theorem ch_at_hd (hp : chAt W p) : p.hd = m2hd W.a W.c W.d W.v W.hStar := by
  unfold Point.hd m2hd; rw [ch_at_h hp, ch_at_v hp, ch_at_Y hp]

/-- **The common residuals** (BLOWUP §1, (2b), (13), (17)-(17b), inventory E2 §1.9). -/
theorem ch_at_retained (hp : chAt W p) : p.Retained := by
  obtain ⟨ha, hc, hd, hr, hT, hWd, hZ, hQ, hK⟩ := pos_facts W
  have hz1 := ch_at_z1 hp
  have hz2 := ch_at_z2 hp
  have hz0 : p.z0 = 0 := by unfold Point.z0; rw [hp.2.2.1, mul_zero]
  have hxc : 0 < p.xc := by
    unfold Point.xc; rw [ch_at_T0 hp, hp.2.1]; exact div_pos hc hT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- g₀ = c - a
    unfold Point.g0; rw [hp.1, hp.2.1]; linarith [W.a_lt_c]
  · -- g₁ = K - T²
    unfold Point.g1; rw [hz0, ch_at_K hp, ch_at_T0 hp]
    have : (W.a + W.c) ^ 2 ≤ (W.a + W.b) * (W.a + W.c) := by nlinarith [W.c_le_b]
    nlinarith [W.central]
  · unfold Point.g2; rw [hp.1]; linarith [W.scale]
  · unfold Point.g3; rw [hp.2.1, ch_at_d hp, ch_at_W hp]; linarith [W.margin_cd]
  · -- g₄ = (W/Q)(4 - dr - (2/15) Z)
    unfold Point.g4
    rw [hp.2.1, ch_at_d hp, hp.2.2.2.2.2]
    have key : W.c - 2 / 15 - (W.d + 2 / 15) * ((W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) - 1) =
        (W.c + W.d) / (W.d ^ 2 + 4) * (4 - W.d * W.r - 2 / 15 * (W.d + W.r)) := by
      field_simp; ring
    rw [key]
    exact mul_nonneg (by positivity) (by linarith [W.margin_dr])
  · -- g₅ = W (r - a)
    unfold Point.g5
    rw [hp.1, hp.2.1, ch_at_T0 hp, ch_at_Q hp, hp.2.2.2.2.1, hp.2.2.2.2.2]
    have key : 4 - W.a ^ 2 - 2 * W.a * W.c - (W.a + W.c) ^ 2 * ((W.d - W.a) / (W.a + W.c)) +
        (W.d ^ 2 + 4) * ((W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) - 1) =
        (W.c + W.d) * (W.r - W.a) := by
      field_simp; ring
    rw [key]
    exact mul_nonneg hWd.le (by linarith [W.a_le_r])
  · -- g₆ = (c² - ad)/T
    unfold Point.g6
    rw [hp.1, hp.2.1, hp.2.2.2.2.1]
    have key : W.c - W.a * (1 + (W.d - W.a) / (W.a + W.c)) = (W.c ^ 2 - W.a * W.d) / (W.a + W.c) := by
      field_simp; ring
    rw [key]
    exact div_nonneg (by linarith [W.logconc]) hT.le
  · unfold Point.g7; linarith [ch_at_phi_neg hp]
  · -- g₈ = upper_turn
    unfold Point.g8
    have h := ch_pt_upper p (hp.1 ▸ ha) (hp.2.1 ▸ hc) hz1.le
    rw [ch_at_v hp, hp.1, ch_at_T0 hp, ← m2g_eq_m2U hT] at h
    have hv : 0 ≤ m2g W.a W.c - W.v := by linarith [W.v_le]
    rw [← h] at hv
    exact nonneg_of_mul_nonneg_right (by linarith) (mul_pos hxc hz1)
  · -- g₉ = turn
    unfold Point.g9
    have h := ch_pt_turn p (hp.1 ▸ ha) (hp.2.1 ▸ hc) hz1.le
    rw [ch_at_v hp, hp.2.1, ch_at_d hp] at h
    have hv : 0 ≤ W.v - m2g W.c W.d := by linarith [W.v_ge]
    rw [← h] at hv
    exact nonneg_of_mul_nonneg_right (by linarith) (mul_pos hxc hz1)
  · -- g₁₀ = v - F_{d/W}(q)
    unfold Point.g10
    rw [ch_pt_Fend p hz2, ch_at_v hp, ch_at_d hp, ch_at_W hp, ch_at_q hp]
    linarith [W.v_floor]
  · unfold Point.g11; rw [ch_at_d hp]; linarith [W.d_le]
  · unfold Point.g12; rw [ch_at_r hp]; linarith [W.r_le]
  · unfold Point.g13; rw [ch_at_T0 hp]; linarith [W.pair_ac]
  · unfold Point.g14; rw [ch_at_W hp]; linarith [W.pair_cd]
  · unfold Point.g15; rw [ch_at_Z hp]; linarith [W.pair_dr]

end

/-- `q ↦ F_x(q) = 1 + x² q - x q log q/(q - 1)` is strictly increasing on `[q₁, q₂]` for
`x > 1/2` and `q₁ > 1` (BLOWUP (2c): `F_x'(q) = x² - x (q - 1 - log q)/(q - 1)² > x (x - 1/2)`). -/
theorem ch_F_strictMono {x q₁ q₂ : ℝ} (hx : 1 / 2 < x) (h1 : 1 < q₁) :
    StrictMonoOn (fun y => 1 + x ^ 2 * y - x * (y * Real.log y) / (y - 1)) (Set.Icc q₁ q₂) := by
  refine ch_strictMonoOn (f' := fun y => x ^ 2 - x * (y - 1 - Real.log y) / (y - 1) ^ 2) ?_ ?_
  · intro y hy
    have hy1 : 1 < y := lt_of_lt_of_le h1 hy.1
    have hy0 : y ≠ 0 := by linarith
    have hyne : y - 1 ≠ 0 := by linarith
    have hid := hasDerivAt_id' y
    have h := ((hasDerivAt_const y (1 : ℝ)).add (hid.const_mul (x ^ 2))).sub
      (((hid.mul (Real.hasDerivAt_log hy0)).const_mul x).div (hid.sub_const 1) hyne)
    convert h using 1
    simp only [Pi.mul_apply]
    field_simp
    ring
  · intro y hy
    have hy1 : 1 < y := lt_of_lt_of_le h1 hy.1.le
    have ht : 0 < y - 1 := by linarith
    have hlog := Real.lt_log_one_add_of_pos ht
    rw [show 1 + (y - 1) = y by ring] at hlog
    -- `y - 1 - log y < (y - 1)²/2`
    have hb : y - 1 - Real.log y < (y - 1) ^ 2 / 2 := by
      have : 2 * (y - 1) / (y - 1 + 2) ≥ (y - 1) - (y - 1) ^ 2 / 2 := by
        rw [ge_iff_le, le_div_iff₀ (by linarith)]
        nlinarith [pow_pos ht 3]
      linarith
    have hq : x * (y - 1 - Real.log y) / (y - 1) ^ 2 < x / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : 0 < x := by linarith
      nlinarith
    show 0 < x ^ 2 - x * (y - 1 - Real.log y) / (y - 1) ^ 2
    nlinarith

/-- **Chart-2 order** (BLOWUP (2b)-(2c), inventory E2 entry 12): if `δ₁ < δ₂` then `d ≤ c`. -/
theorem ch_d_le_c (W : M2Window)
    (h12 : (W.d - W.a) / (W.a + W.c) < (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) - 1) :
    W.d ≤ W.c := by
  obtain ⟨ha, hc, hd, hr, hT, hWd, hZ, hQ, hK⟩ := pos_facts W
  by_contra hdc
  push Not at hdc
  have hda : 0 < W.d - W.a := by linarith [W.a_lt_d]
  set x := W.d / (W.c + W.d) with hx
  have hx2 : 1 / 2 < x := by rw [hx, lt_div_iff₀ hWd]; linarith
  set q₁ := (W.d + W.c) / (W.a + W.c) with hq₁
  set q := (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) with hq
  have hq1 : 1 < q₁ := by rw [hq₁, lt_div_iff₀ hT]; linarith [W.a_lt_d]
  have hq1q : q₁ < q := by
    have : q₁ = 1 + (W.d - W.a) / (W.a + W.c) := by rw [hq₁]; field_simp; ring
    rw [this]; linarith
  have hmono := ch_F_strictMono (q₂ := q) hx2 hq1 ⟨le_rfl, hq1q.le⟩ ⟨hq1q.le, le_rfl⟩ hq1q
  have hfloor := W.v_floor
  rw [m2F_of_ne (by linarith)] at hfloor
  -- `F_x(q₁) - v = (d - c)(1/T - log(W/T)/(d - a)) > 0`
  have hv := W.v_eq
  rw [m2Sec_of_ne W.a_lt_d.ne] at hv
  have hlog := Real.log_lt_sub_one_of_pos (by linarith : 0 < q₁) hq1.ne'
  have hlogq : Real.log q₁ / (W.d - W.a) < 1 / (W.a + W.c) := by
    rw [div_lt_iff₀ hda]
    have : q₁ - 1 = (W.d - W.a) / (W.a + W.c) := by rw [hq₁]; field_simp; ring
    rw [this] at hlog
    calc Real.log q₁ < (W.d - W.a) / (W.a + W.c) := hlog
      _ = 1 / (W.a + W.c) * (W.d - W.a) := by ring
  have key : 1 + x ^ 2 * q₁ - x * (q₁ * Real.log q₁) / (q₁ - 1) - W.v =
      (W.d - W.c) * (1 / (W.a + W.c) - Real.log q₁ / (W.d - W.a)) := by
    have hq1m : q₁ - 1 = (W.d - W.a) / (W.a + W.c) := by rw [hq₁]; field_simp; ring
    rw [hq1m, hv, hx, hq₁]
    generalize Real.log ((W.d + W.c) / (W.a + W.c)) = L
    have hda' : W.d - W.a ≠ 0 := hda.ne'
    have hdc' : W.d + W.c ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 < (W.d - W.c) * (1 / (W.a + W.c) - Real.log q₁ / (W.d - W.a)) :=
    mul_pos (by linarith) (by linarith)
  have : 1 + x ^ 2 * q - x * (q * Real.log q) / (q - 1) ≤ W.v := by
    convert hfloor using 2; ring
  simp only at hmono
  linarith

theorem ch_at_g16 {W : M2Window} {p : Point} (hp : chAt W p)
    (h12 : (W.d - W.a) / (W.a + W.c) < (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) - 1) :
    0 ≤ p.g16 := by
  unfold Point.g16
  have h := ch_d_le_c W h12
  have : p.T0 * p.z1 = W.d - W.a := by
    rw [ch_at_T0 hp, hp.2.2.2.2.1]
    obtain ⟨-, -, -, -, hT, -⟩ := pos_facts W
    field_simp
  rw [this, hp.1, hp.2.1]
  linarith

end SmoothedOctagon

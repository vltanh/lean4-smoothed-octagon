module

public import SmoothedOctagon.Exclusion.Mixed.Location
public import SmoothedOctagon.Exclusion.Mixed.Reflection
public import SmoothedOctagon.Exclusion.Mixed.Extract.Compact
public import SmoothedOctagon.Exclusion.Mixed.Extract.Transport
public import SmoothedOctagon.Exclusion.Mixed.Extract.WindowAlg
public import SmoothedOctagon.Exclusion.Mixed.Short.Window
public import SmoothedOctagon.Exclusion.Mixed.Defect.Field

/-!
# Case M2: the scalar windows of an actual period

Let `m` be a global minimum of the active margins at a reverse centre (`m2_min_centre`), oriented
(`m2_reflect`) so that the smaller adjacent turn `c = a_{m+1} ≤ b = a_{m-1}` is outgoing. The
switch `m + 2` after the turn is

* forward (nonshort side): the pieces `m - 2, …, m + 3` carry the `M2Window`
  `0(p), 1(b), 0(a), 2(c), 0(d), 1(r)`, and the switch `m + 3` gives
  `M2Window.ForwardNext` or `M2Window.ReverseNext`;
* reverse (short side): the pieces `m - 2, …, m + 4` carry the `M2Short` window.

Ingredients, all on the costate cycle of the period and its covector calculus
(`NormalPeriod.M2Calculus`):

* the factor formulas from the margin transports of `Term.Cycle` (`m_act`, `m_grow`,
  `m_decr`, `m_quad`): `q = s_- s_+/K` (`++`), `K/(s_- s_+)` (`--`), `s_+/s_-` (`-+`),
  `s_- / s_+` (`+-`), and strict star `a_i a_{i+1} < 4` at every switch;
* the compact domain at the switching times (`Reduction.two_div_fifteen_le_margin` for every
  margin, and the pair sums `> 1/2` and margins `< 8` from the height bound `y ≤ 9/2`);
* the strict centre minima (`reverseRun_two_and_centre_min`) and three-arc log-concavity
  (`CostateCycle.three_arc`);
* the transports of the calculus (`M2Calculus.transport`): the centre frame
  `M m = [[h, -K²v/(8S²)], [S²u/8, -h]]`, `M (m + 2) = U_d` with `h_d = h + vY/8` and
  `w = (uK² + 16hY + vY²)/Q²`, and the next norm `t`, independent of the next margin; in the
  short window the Gram transport `w = λ²v + d²u - dλE`, `E_L = 2du - λE` to the outer centre;
* stationarity at the centre and at `d`, the turn secants, the switching inequalities and the
  missing-control floors;
* the Casimir bounds (`M2Calculus.cas_lt`, `cas_gt`) and the scale bound (`m2_centre`,
  `m2_scale`);
* for the short window, the middle missing-control slack and the two-turn window-defect
  inequality.

The short window uses `Mixed/Short/Window`: the same-lift transport to the outer centre
(`ss_alg_wEL`) and the middle slack `N_mid = (4/K_a²) G_L` from the missing control
`M2Calculus.mc_fwd` at the forward switch `C → B` (`ss_alg_mid`), the centre frames
(`ss_centre_frame`) and the reduced coordinates `u`, `β`, `x` at the window point
(`ss_point_*`). The window-defect field (`M2Short.defect`: the spectral cost–Casimir inequality on
the two-turn window, with its endpoint traces and the modulus filter) is `NormalPeriod.df_defect`
(`Mixed/Defect/`): the window angle of the costate frame (`df_window`) and the traces of
`Certificates.SmallerShort.Point` identified with the rotated triangular frames (`df_alg_traces`,
`df_alg_cost`).

Helpers (usable for both windows): `Mixed/Extract/Compact` (`NormalPeriod.wx_m_ge`,
`wx_half_le_m_add`, `wx_m_le`: the compact-domain bounds on the switch margins),
`Mixed/Extract/Transport` (`CostateCycle.wx_next_fwd`, `wx_next_rev`: the transports entry by
entry) and `Mixed/Extract/WindowAlg` (`wx_alg_hd`, `wx_alg_w`, `wx_alg_t`, `wx_alg_cas`: the
window identities for `h_d`, `w`, `t` and `γ²`). In `M2Window.ReverseNext` the bound `A ≥ a` is
global minimality itself; that `A` is a reverse centre is not needed.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The smaller-nonshort window**: at a global minimum `m` at a reverse centre with the smaller
turn outgoing and the switch `m + 2` forward, the pieces `m - 2, …, m + 3` carry an `M2Window`,
with `ForwardNext` or `ReverseNext` according to the switch `m + 3`. -/
theorem m2_window (P : NormalPeriod) (hc : P.IsCompetitive) (hK : P.InCompactDomain)
    (h : P.rep.ClassM2) (hN : 6 ≤ P.N) {m : ℤ}
    (hm : ∀ k, P.costateCycle.act m ≤ P.costateCycle.act k)
    (h2 : P.costateCycle.m2Fwd (m - 2)) (h1 : ¬ P.costateCycle.m2Fwd (m - 1))
    (h0 : ¬ P.costateCycle.m2Fwd m) (h3 : P.costateCycle.m2Fwd (m + 1))
    (hcb : P.costateCycle.act (m + 1) ≤ P.costateCycle.act (m - 1))
    (h4 : P.costateCycle.m2Fwd (m + 2)) :
    ∃ W : M2Window, W.p = P.costateCycle.act (m - 2) ∧ W.b = P.costateCycle.act (m - 1) ∧
      W.a = P.costateCycle.act m ∧ W.c = P.costateCycle.act (m + 1) ∧
      W.d = P.costateCycle.act (m + 2) ∧ W.r = P.costateCycle.act (m + 3) ∧
      (P.costateCycle.m2Fwd (m + 3) → W.ForwardNext) ∧
      (¬ P.costateCycle.m2Fwd (m + 3) → W.ReverseNext) := by
  obtain ⟨K⟩ := P.m2_calculus
  have hmix : P.rep.IsMixed := h.1
  have hact : ∀ j, P.activeMargin j = P.costateCycle.act j := fun j =>
    (P.costateCycle_m_lab j).symm
  -- the strict centre minima
  have hrev : ∀ j, ¬ P.costateCycle.m2Fwd j → P.rep.IsReverse j := fun j hj =>
    (P.rep.m2_fwd_or_rev j).resolve_left hj
  have hrun : P.rep.IsReverseRun (m - 1) 2 := by
    refine ⟨by norm_num, ?_, ?_, fun j hj1 hj2 => hrev j ?_⟩
    · rw [show m - 1 - 1 = m - 2 by ring]; exact h2
    · rw [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring]; exact h3
    · have : j = m - 1 ∨ j = m := by push_cast at hj2; omega
      rcases this with rfl | rfl
      · exact h1
      · exact h0
  obtain ⟨-, hap, hab, hac, had⟩ := reverseRun_two_and_centre_min P hmix hrun
  simp only [hact, show m - 1 + 1 = m by ring, show m - 1 - 1 = m - 2 by ring,
    show m - 1 + 2 = m + 1 by ring, show m - 1 + 3 = m + 2 by ring] at hap hab hac had
  -- the reverse-centre scale bound
  obtain ⟨D, -, -, hDa, -, -, hDΓ⟩ := m2_centre P K hmix h2 h1 h0 h3
  have hsc := m2_scale D (by rw [hDΓ]; linarith [K.cas_lt hc])
  rw [hDa] at hsc
  -- positivity
  have pos := fun k => P.costateCycle.act_pos k
  have p0 := pos (m - 2)
  have b0 := pos (m - 1)
  have a0 := pos m
  have c0 := pos (m + 1)
  have d0 := pos (m + 2)
  have r0 := pos (m + 3)
  -- signs, read at shifted indices
  have h1' : ¬ P.costateCycle.m2Fwd (m + 1 - 1) := by rw [add_sub_cancel_right]; exact h0
  have h3' : P.costateCycle.m2Fwd (m + 2 - 1) := by rw [show m + 2 - 1 = m + 1 by ring]; exact h3
  have h4' : P.costateCycle.m2Fwd (m + 3 - 1) := by rw [show m + 3 - 1 = m + 2 by ring]; exact h4
  -- factors
  have qm := P.costateCycle.m2_factor_rr h1 h0
  have q1 := P.costateCycle.m2_factor_rf h1' h3
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at q1
  have q2 := P.costateCycle.m2_factor_ff h3' h4
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at q2
  have qm1 := P.costateCycle.one_lt_q m
  have q11 := P.costateCycle.one_lt_q (m + 1)
  have q21 := P.costateCycle.one_lt_q (m + 2)
  have hqm : P.costateCycle.q m = (P.costateCycle.act m ^ 2 + 4) /
      ((P.costateCycle.act (m - 1) + P.costateCycle.act m) *
        (P.costateCycle.act m + P.costateCycle.act (m + 1))) := by
    rw [eq_div_iff (by positivity)]; exact qm
  have hq1 : P.costateCycle.q (m + 1) = (P.costateCycle.act (m + 1) + P.costateCycle.act (m + 2)) /
      (P.costateCycle.act m + P.costateCycle.act (m + 1)) := by
    rw [eq_div_iff (by positivity)]; exact q1
  have hq2 : P.costateCycle.q (m + 2) =
      (P.costateCycle.act (m + 1) + P.costateCycle.act (m + 2)) *
        (P.costateCycle.act (m + 2) + P.costateCycle.act (m + 3)) /
          (P.costateCycle.act (m + 2) ^ 2 + 4) := by
    rw [eq_div_iff (by positivity)]; exact q2
  -- strict star
  have st_pb := P.costateCycle.m2_star (m - 1)
  have st_ab := P.costateCycle.m2_star m
  have st_ac := P.costateCycle.m2_star (m + 1)
  have st_cd := P.costateCycle.m2_star (m + 2)
  have st_dr := P.costateCycle.m2_star (m + 3)
  rw [show m - 1 - 1 = m - 2 by ring] at st_pb
  rw [add_sub_cancel_right] at st_ac
  rw [show m + 2 - 1 = m + 1 by ring] at st_cd
  rw [show m + 3 - 1 = m + 2 by ring] at st_dr
  -- the compact domain
  have hmc := fun k j => P.wx_m_ge hK k j
  have third_cd := P.costateCycle.m2_third_fwd h3'
  rw [show m + 2 - 1 = m + 1 by ring] at third_cd
  have third_dr := P.costateCycle.m2_third_fwd h4'
  rw [show m + 3 - 1 = m + 2 by ring] at third_dr
  have m_cd := hmc (m + 2) (P.costateCycle.lab (m + 2) + 1)
  have m_dr := hmc (m + 3) (P.costateCycle.lab (m + 3) + 1)
  have pair := fun k => P.wx_half_le_m_add hK (k + 1) (j := P.costateCycle.lab k)
    (j' := P.costateCycle.lab (k + 1)) (P.costateCycle.lab_ne k).symm
  have pair_ac := pair m
  have pair_cd := pair (m + 1)
  have pair_dr := pair (m + 2)
  rw [P.costateCycle.m_act] at pair_ac pair_cd pair_dr
  rw [show m + 1 + 1 = m + 2 by ring] at pair_cd
  rw [show m + 2 + 1 = m + 3 by ring] at pair_dr
  have a_ge : 2 / 15 ≤ P.costateCycle.act m := hmc m _
  have d_le : P.costateCycle.act (m + 2) ≤ 8 := P.wx_m_le hK (m + 2) _
  have r_le : P.costateCycle.act (m + 3) ≤ 8 := P.wx_m_le hK (m + 3) _
  -- three-arc log-concavity on `a, c, d`
  have hlog := P.costateCycle.three_arc m (by
    rw [show m + 2 = m + 1 + 1 by ring,
      show P.costateCycle.lab (m + 1 + 1) = P.costateCycle.lab (m + 1) + 1 from h3,
      P.costateCycle.m2_lab_next_rev h0, sub_add_cancel])
  -- the covector calculus: secants, switching inequalities, floors, stationarity
  have sec_b := K.secant (m - 1)
    (by rw [show m - 1 - 1 = m - 2 by ring]; exact fun e => h1 (e.1 h2))
  rw [show m - 1 - 1 = m - 2 by ring, sub_add_cancel] at sec_b
  have sec_c := K.secant (m + 1) (by rw [add_sub_cancel_right]; exact fun e => h0 (e.2 h3))
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at sec_c
  have fge_pb := K.fwd_ge (m - 2) h2
  rw [show m - 2 + 1 = m - 1 by ring] at fge_pb
  have rle_b := K.rev_le (m - 1) h1
  rw [sub_add_cancel, m2g_comm] at rle_b
  have rle_a := K.rev_le m h0
  have fge_cd := K.fwd_ge (m + 1) h3
  rw [show m + 1 + 1 = m + 2 by ring] at fge_cd
  have fge_dr := K.fwd_ge (m + 2) h4
  rw [show m + 2 + 1 = m + 3 by ring] at fge_dr
  have fl_in := K.floor_in (m + 2) h3' h4
  rw [show m + 2 - 1 = m + 1 by ring] at fl_in
  have fl_out := K.floor_out (m + 2) h3' h4
  rw [show m + 2 + 1 = m + 3 by ring] at fl_out
  have stat_a := K.stat m (iff_of_false h1 h0)
  have stat_d := K.stat (m + 2) (iff_of_true h3' h4)
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at stat_d
  have hv1 : P.costateCycle.m2Norm K.M (m + 1) = P.costateCycle.m2Norm K.M m := by
    rw [sec_c.2, ← sec_c.1]
  have hu2 : P.costateCycle.m2Norm K.M (m - 2) = P.costateCycle.m2Norm K.M (m - 1) := by
    rw [sec_b.1, ← sec_b.2]
  rw [hv1] at fge_cd fl_in stat_d
  rw [hu2] at fge_pb
  -- the frames
  have tr0 := K.trace_eq m
  rw [Matrix.trace_fin_two] at tr0
  have e11 : K.M m 1 1 = -K.M m 0 0 := by linarith
  have hdet := K.det_eq m
  rw [Matrix.det_fin_two, e11] at hdet
  have hu' : P.costateCycle.m2Norm K.M (m - 1) =
      8 * K.M m 1 0 / (P.costateCycle.act (m - 1) + P.costateCycle.act m) ^ 2 := by
    have := P.costateCycle.m2_norm_next K.transport (m - 1)
    simp only [h1, ↓reduceIte, sub_add_cancel] at this
    exact this
  have hv' : P.costateCycle.m2Norm K.M m = -8 * K.M m 0 1 /
      (P.costateCycle.q m ^ 2 * (P.costateCycle.act m + P.costateCycle.act (m + 1)) ^ 2) := by
    unfold CostateCycle.m2Norm; simp only [h0, ↓reduceIte]
  have hw' : P.costateCycle.m2Norm K.M (m + 2) = 8 * P.costateCycle.q (m + 2) ^ 2 *
      K.M (m + 2) 1 0 / (P.costateCycle.act (m + 2) + P.costateCycle.act (m + 3)) ^ 2 := by
    unfold CostateCycle.m2Norm; simp only [h4, ↓reduceIte]
    rw [show m + 2 + 1 = m + 3 by ring]
  obtain ⟨x1, y1, z1, w1⟩ := P.costateCycle.wx_next_rev K.transport h0
  obtain ⟨x2, y2, z2, w2⟩ := P.costateCycle.wx_next_fwd K.transport h3
  rw [show m + 1 + 1 = m + 2 by ring] at x2 y2 z2 w2
  rw [e11] at x1 y1
  have hhd : K.M (m + 2) 0 0 = m2hd (P.costateCycle.act m) (P.costateCycle.act (m + 1))
      (P.costateCycle.act (m + 2)) (P.costateCycle.m2Norm K.M m) (K.M m 0 0) := by
    rw [x2, z1, w1, hv']
    exact wx_alg_hd a0 c0 hqm hq1
  have hww : P.costateCycle.m2Norm K.M (m + 2) = m2wOf (P.costateCycle.act m)
      (P.costateCycle.act (m + 1)) (P.costateCycle.act (m + 2)) (P.costateCycle.m2Norm K.M (m - 1))
      (P.costateCycle.m2Norm K.M m) (K.M m 0 0) := by
    rw [hw', z2, x1, y1, z1, w1, hu', hv']
    exact wx_alg_w a0 b0 c0 d0 r0 hqm hq1 hq2
  have hcas : m2Cas (P.costateCycle.act m) (P.costateCycle.m2Norm K.M (m - 1))
      (P.costateCycle.m2Norm K.M m) (K.M m 0 0) = K.Γ := by
    rw [hu', hv', ← wx_alg_cas a0 b0 c0 hqm, ← hdet]
  have hhq : K.M m 0 0 = m2h (P.costateCycle.act m) (P.costateCycle.act (m - 1))
      (P.costateCycle.act (m + 1)) (P.costateCycle.m2Norm K.M (m - 1))
      (P.costateCycle.m2Norm K.M m) := by
    unfold m2h
    rw [← stat_a]
    field_simp
    ring
  have hroot : m2Root (P.costateCycle.act m) (P.costateCycle.act (m + 1))
      (P.costateCycle.act (m + 2)) (P.costateCycle.act (m + 3))
      (P.costateCycle.m2Norm K.M (m - 1)) (P.costateCycle.m2Norm K.M m) (K.M m 0 0) = 0 := by
    unfold m2Root
    rw [← hww, ← hhd]
    linarith
  -- the window
  refine ⟨⟨P.costateCycle.act (m - 2), P.costateCycle.act (m - 1), P.costateCycle.act m,
    P.costateCycle.act (m + 1), P.costateCycle.act (m + 2), P.costateCycle.act (m + 3),
    P.costateCycle.m2Norm K.M (m - 1), P.costateCycle.m2Norm K.M m, K.M m 0 0,
    P.costateCycle.m2Norm K.M (m + 2), a0, hab, hac, hcb, hap, had, hm _, st_pb,
    by rw [mul_comm]; exact st_ab, st_ac, st_cd, st_dr, ?_, ?_, hlog, a_ge, ?_, ?_, d_le, r_le,
    pair_ac, pair_cd, pair_dr, hsc, by rw [sec_b.2, m2Sec_comm], sec_c.1, fge_pb, rle_b, rle_a,
    fge_cd, fge_dr, by rw [← hq2]; exact fl_in, by rw [← hq2]; exact fl_out, hhq, hww, hroot,
    by rw [hcas]; exact K.cas_lt hc, by rw [hcas]; exact K.cas_gt hc hK hmix⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, fun h5 => ?_, fun h5 => ?_⟩
  · -- the central factor
    have := mul_lt_mul_of_pos_right qm1 (show 0 < (P.costateCycle.act (m - 1) +
      P.costateCycle.act m) * (P.costateCycle.act m + P.costateCycle.act (m + 1)) by positivity)
    linarith
  · -- the factor of `d`
    have := mul_lt_mul_of_pos_right q21
      (show 0 < P.costateCycle.act (m + 2) ^ 2 + 4 by positivity)
    linarith
  · -- the inactive margin at the switch `c → d`
    have := mul_le_mul_of_nonneg_right m_cd
      (show 0 ≤ P.costateCycle.act (m + 1) + P.costateCycle.act (m + 2) by positivity)
    linarith
  · -- the inactive margin at the switch `d → r`
    have := mul_le_mul_of_nonneg_right m_dr
      (show 0 ≤ P.costateCycle.act (m + 2) + P.costateCycle.act (m + 3) by positivity)
    linarith
  · -- the next switch is forward
    have h5' : P.costateCycle.m2Fwd (m + 4 - 1) := by
      rw [show m + 4 - 1 = m + 3 by ring]; exact h5
    have q3 := P.costateCycle.m2_factor_ff h4' h5
    rw [show m + 3 - 1 = m + 2 by ring, show m + 3 + 1 = m + 4 by ring] at q3
    have q31 := P.costateCycle.one_lt_q (m + 3)
    have s0 := pos (m + 4)
    have hq3 : P.costateCycle.q (m + 3) =
        (P.costateCycle.act (m + 2) + P.costateCycle.act (m + 3)) *
          (P.costateCycle.act (m + 3) + P.costateCycle.act (m + 4)) /
            (P.costateCycle.act (m + 3) ^ 2 + 4) := by
      rw [eq_div_iff (by positivity)]; exact q3
    have st_rs := P.costateCycle.m2_star (m + 4)
    rw [show m + 4 - 1 = m + 3 by ring] at st_rs
    have fge_rs := K.fwd_ge (m + 3) h5
    rw [show m + 3 + 1 = m + 4 by ring] at fge_rs
    have fl_in' := K.floor_in (m + 3) h4' h5
    rw [show m + 3 - 1 = m + 2 by ring] at fl_in'
    have fl_out' := K.floor_out (m + 3) h4' h5
    rw [show m + 3 + 1 = m + 4 by ring] at fl_out'
    -- the next norm `t`
    have tr2 := K.trace_eq (m + 2)
    rw [Matrix.trace_fin_two] at tr2
    have e11' : K.M (m + 2) 1 1 = -K.M (m + 2) 0 0 := by linarith
    have hy2 : K.M (m + 2) 0 1 =
        -((P.costateCycle.act (m + 1) + P.costateCycle.act (m + 2)) ^ 2 *
          P.costateCycle.m2Norm K.M m / 8) := by
      have := P.costateCycle.m2_norm_next K.transport (m + 1)
      simp only [h3, ↓reduceIte] at this
      rw [show m + 1 + 1 = m + 2 by ring, hv1] at this
      rw [this]
      field_simp
    have ht : P.costateCycle.m2Norm K.M (m + 3) = m2Next (P.costateCycle.act m)
        (P.costateCycle.act (m + 1)) (P.costateCycle.act (m + 2)) (P.costateCycle.act (m + 3))
        (P.costateCycle.m2Norm K.M (m - 1)) (P.costateCycle.m2Norm K.M m) (K.M m 0 0) := by
      obtain ⟨-, -, z3, -⟩ := P.costateCycle.wx_next_fwd K.transport h4
      rw [show m + 2 + 1 = m + 3 by ring] at z3
      have ht0 : P.costateCycle.m2Norm K.M (m + 3) = 8 * P.costateCycle.q (m + 3) ^ 2 *
          K.M (m + 3) 1 0 / (P.costateCycle.act (m + 3) + P.costateCycle.act (m + 4)) ^ 2 := by
        unfold CostateCycle.m2Norm; simp only [h5, ↓reduceIte]
        rw [show m + 3 + 1 = m + 4 by ring]
      rw [ht0, z3, e11', hy2]
      unfold m2Next
      rw [← hhd, ← hww]
      exact wx_alg_t c0 d0 r0 s0 hq2 hq3 hw'
    rw [hq3] at fl_in' fl_out'
    exact ⟨P.costateCycle.act (m + 4), hm _, st_rs, by
      have := mul_lt_mul_of_pos_right q31
        (show 0 < P.costateCycle.act (m + 3) ^ 2 + 4 by positivity)
      linarith, fge_rs.trans_eq ht, fl_in', fl_out'.trans_eq ht⟩
  · -- the next switch is reverse
    have q3 := P.costateCycle.m2_factor_fr h4' h5
    rw [show m + 3 - 1 = m + 2 by ring, show m + 3 + 1 = m + 4 by ring] at q3
    have q31 := P.costateCycle.one_lt_q (m + 3)
    have s0 := pos (m + 4)
    have hlog' := P.costateCycle.three_arc (m + 2) (by
      rw [show m + 2 + 2 = m + 3 + 1 by ring, P.costateCycle.m2_lab_next_rev h5,
        show m + 3 = m + 2 + 1 by ring,
        show P.costateCycle.lab (m + 2 + 1) = P.costateCycle.lab (m + 2) + 1 from h4,
        add_sub_cancel_right])
    rw [show m + 2 + 2 = m + 4 by ring, show m + 2 + 1 = m + 3 by ring] at hlog'
    have sec_r := K.secant (m + 3) (by
      rw [show m + 3 - 1 = m + 2 by ring]; exact fun e => h5 (e.1 h4))
    rw [show m + 3 - 1 = m + 2 by ring, show m + 3 + 1 = m + 4 by ring] at sec_r
    have rle_r := K.rev_le (m + 3) h5
    rw [show m + 3 + 1 = m + 4 by ring, sec_r.2, ← sec_r.1] at rle_r
    refine ⟨P.costateCycle.act (m + 4), hm _, ?_, by rw [mul_comm]; exact hlog',
      sec_r.1.trans (m2Sec_comm _ _ _), rle_r⟩
    have := mul_lt_mul_of_pos_right q31
      (show 0 < P.costateCycle.act (m + 3) + P.costateCycle.act (m + 4) by positivity)
    linarith

/-- **The smaller-short window**: at a global minimum `m` at a reverse centre with the smaller
turn outgoing and the switch `m + 2` reverse, the pieces `m - 2, …, m + 4` carry an `M2Short`. -/
theorem m2_short_window (P : NormalPeriod) (hc : P.IsCompetitive) (hK : P.InCompactDomain)
    (h : P.rep.ClassM2) (hN : 6 ≤ P.N) {m : ℤ}
    (hm : ∀ k, P.costateCycle.act m ≤ P.costateCycle.act k)
    (h2 : P.costateCycle.m2Fwd (m - 2)) (h1 : ¬ P.costateCycle.m2Fwd (m - 1))
    (h0 : ¬ P.costateCycle.m2Fwd m) (h3 : P.costateCycle.m2Fwd (m + 1))
    (hcb : P.costateCycle.act (m + 1) ≤ P.costateCycle.act (m - 1))
    (h4 : ¬ P.costateCycle.m2Fwd (m + 2)) :
    ∃ D : M2Short, D.pb = P.costateCycle.act (m - 2) ∧ D.b = P.costateCycle.act (m - 1) ∧
      D.a = P.costateCycle.act m ∧ D.C = P.costateCycle.act (m + 1) ∧
      D.B = P.costateCycle.act (m + 2) ∧ D.A = P.costateCycle.act (m + 3) ∧
      D.Pf = P.costateCycle.act (m + 4) := by
  obtain ⟨K⟩ := P.m2_calculus
  set Y := P.costateCycle with hY
  have hmix : P.rep.IsMixed := h.1
  have hact : ∀ j, P.activeMargin j = Y.act j := fun j => (P.costateCycle_m_lab j).symm
  have hrev : ∀ j, ¬ Y.m2Fwd j → P.rep.IsReverse j := fun j hj =>
    (P.rep.m2_fwd_or_rev j).resolve_left hj
  -- the reverse run after the short bridge: switches `m + 2`, `m + 3` reverse, `m + 4` forward
  obtain ⟨⟨f, hf⟩, -⟩ := hmix
  obtain ⟨k, L, hrunA, hk1, hk2⟩ := P.rep.m2_exists_reverseRun hf (hrev _ h4)
  have hL := h.2.1 k L hrunA
  subst hL
  have hk : k = m + 2 := by
    have : k = m + 1 ∨ k = m + 2 := by push_cast at hk2; omega
    rcases this with rfl | rfl
    · exact absurd ⟨h3, hrunA.2.2.2 (m + 1) le_rfl (by push_cast; omega)⟩
        (P.rep.m2_not_fwd_and_rev (m + 1))
    · rfl
  subst hk
  have h5 : ¬ Y.m2Fwd (m + 3) := fun e =>
    P.rep.m2_not_fwd_and_rev (m + 3) ⟨e, hrunA.2.2.2 (m + 3) (by omega) (by push_cast; omega)⟩
  have h6 : Y.m2Fwd (m + 4) := by
    have := hrunA.2.2.1; rwa [show m + 2 + ((2 : ℕ) : ℤ) = m + 4 by push_cast; ring] at this
  -- the strict centre minima at `a` and at `A`
  have hruna : P.rep.IsReverseRun (m - 1) 2 := by
    refine ⟨by norm_num, ?_, ?_, fun j hj1 hj2 => hrev j ?_⟩
    · rw [show m - 1 - 1 = m - 2 by ring]; exact h2
    · rw [show m - 1 + ((2 : ℕ) : ℤ) = m + 1 by push_cast; ring]; exact h3
    · have : j = m - 1 ∨ j = m := by push_cast at hj2; omega
      rcases this with rfl | rfl
      · exact h1
      · exact h0
  obtain ⟨-, hap, hab, hac, -⟩ := reverseRun_two_and_centre_min P h.1 hruna
  simp only [hact, show m - 1 + 1 = m by ring, show m - 1 - 1 = m - 2 by ring,
    show m - 1 + 2 = m + 1 by ring] at hap hab hac
  obtain ⟨-, hAC', hAB, hAPf, -⟩ := reverseRun_two_and_centre_min P h.1 hrunA
  simp only [hact, show m + 2 + 1 = m + 3 by ring, show m + 2 - 1 = m + 1 by ring,
    show m + 2 + 2 = m + 4 by ring] at hAC' hAB hAPf
  -- positivity
  have pos := fun k => Y.act_pos k
  have b0 := pos (m - 1)
  have a0 := pos m
  have c0 := pos (m + 1)
  have B0 := pos (m + 2)
  have A0 := pos (m + 3)
  have P0 := pos (m + 4)
  -- signs at shifted indices
  have h1' : ¬ Y.m2Fwd (m + 1 - 1) := by rw [add_sub_cancel_right]; exact h0
  have h3' : Y.m2Fwd (m + 2 - 1) := by rw [show m + 2 - 1 = m + 1 by ring]; exact h3
  have h4' : ¬ Y.m2Fwd (m + 3 - 1) := by rw [show m + 3 - 1 = m + 2 by ring]; exact h4
  have h5' : ¬ Y.m2Fwd (m + 4 - 1) := by rw [show m + 4 - 1 = m + 3 by ring]; exact h5
  -- factors
  have qm := Y.m2_factor_rr h1 h0
  have q1 := Y.m2_factor_rf h1' h3
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at q1
  have q2 := Y.m2_factor_fr h3' h4
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at q2
  have q3 := Y.m2_factor_rr h4' h5
  rw [show m + 3 - 1 = m + 2 by ring, show m + 3 + 1 = m + 4 by ring] at q3
  have qm1 := Y.one_lt_q m
  have q21 := Y.one_lt_q (m + 2)
  have q31 := Y.one_lt_q (m + 3)
  have hqm : Y.q m = (Y.act m ^ 2 + 4) / ((Y.act (m - 1) + Y.act m) * (Y.act m + Y.act (m + 1))) := by
    rw [eq_div_iff (by positivity)]; exact qm
  have hq1 : Y.q (m + 1) = (Y.act (m + 1) + Y.act (m + 2)) / (Y.act m + Y.act (m + 1)) := by
    rw [eq_div_iff (by positivity)]; exact q1
  have hq2 : Y.q (m + 2) = (Y.act (m + 1) + Y.act (m + 2)) / (Y.act (m + 2) + Y.act (m + 3)) := by
    rw [eq_div_iff (by positivity)]; exact q2
  have hq3 : Y.q (m + 3) = (Y.act (m + 3) ^ 2 + 4) /
      ((Y.act (m + 2) + Y.act (m + 3)) * (Y.act (m + 3) + Y.act (m + 4))) := by
    rw [eq_div_iff (by positivity)]; exact q3
  -- strict star
  have st_pb := Y.m2_star (m - 1)
  have st_ab := Y.m2_star m
  have st_aC := Y.m2_star (m + 1)
  have st_CB := Y.m2_star (m + 2)
  have st_BA := Y.m2_star (m + 3)
  have st_APf := Y.m2_star (m + 4)
  rw [show m - 1 - 1 = m - 2 by ring] at st_pb
  rw [add_sub_cancel_right] at st_aC
  rw [show m + 2 - 1 = m + 1 by ring] at st_CB
  rw [show m + 3 - 1 = m + 2 by ring] at st_BA
  rw [show m + 4 - 1 = m + 3 by ring] at st_APf
  -- the turn secants
  have sec_b := K.secant (m - 1)
    (by rw [show m - 1 - 1 = m - 2 by ring]; exact fun e => h1 (e.1 h2))
  rw [show m - 1 - 1 = m - 2 by ring, sub_add_cancel] at sec_b
  have sec_C := K.secant (m + 1) (by rw [add_sub_cancel_right]; exact fun e => h0 (e.2 h3))
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at sec_C
  have sec_B := K.secant (m + 2) (by
    rw [show m + 2 - 1 = m + 1 by ring]; exact fun e => h4 (e.1 h3))
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at sec_B
  have sec_P := K.secant (m + 4) (by
    rw [show m + 4 - 1 = m + 3 by ring]; exact fun e => h5 (e.2 h6))
  rw [show m + 4 - 1 = m + 3 by ring] at sec_P
  have hu1 : Y.m2Norm K.M (m + 1) = Y.m2Norm K.M m := by rw [sec_C.2, ← sec_C.1]
  have hu2 : Y.m2Norm K.M (m + 2) = Y.m2Norm K.M m := by rw [sec_B.2, ← sec_B.1, hu1]
  have hv2 : Y.m2Norm K.M (m - 2) = Y.m2Norm K.M (m - 1) := by rw [sec_b.1, ← sec_b.2]
  -- the switching inequalities
  have fge_pb := K.fwd_ge (m - 2) h2
  rw [show m - 2 + 1 = m - 1 by ring, hv2] at fge_pb
  have rle_b := K.rev_le (m - 1) h1
  rw [sub_add_cancel, m2g_comm] at rle_b
  have rle_a := K.rev_le m h0
  have fge_C := K.fwd_ge (m + 1) h3
  rw [show m + 1 + 1 = m + 2 by ring, hu1] at fge_C
  have rle_B := K.rev_le (m + 2) h4
  rw [show m + 2 + 1 = m + 3 by ring, hu2] at rle_B
  have rle_A := K.rev_le (m + 3) h5
  rw [show m + 3 + 1 = m + 4 by ring] at rle_A
  -- the centre frames
  obtain ⟨cfa_E, cfa_Γ⟩ := ss_centre_frame P K h1 h0
  obtain ⟨cfA_E, cfA_Γ⟩ := ss_centre_frame P K (k := m + 3) h4' h5
  rw [show m + 3 - 1 = m + 2 by ring, show m + 3 + 1 = m + 4 by ring, hu2] at cfA_E
  rw [show m + 3 - 1 = m + 2 by ring, hu2] at cfA_Γ
  -- the scale bounds
  obtain ⟨Da, -, -, hDa, -, -, hDaΓ⟩ := m2_centre P K h.1 h2 h1 h0 h3
  have hsc := m2_scale Da (by rw [hDaΓ]; linarith [K.cas_lt hc])
  rw [hDa] at hsc
  obtain ⟨DA, -, -, hDA, -, -, hDAΓ⟩ := m2_centre P K h.1 (k := m + 3)
    (by rw [show m + 3 - 2 = m + 1 by ring]; exact h3) h4' h5
    (by rw [show m + 3 + 1 = m + 4 by ring]; exact h6)
  have hscA := m2_scale DA (by rw [hDAΓ]; linarith [K.cas_lt hc])
  rw [hDA] at hscA
  -- the frames: `M m = [[h, y₀], [z₀, -h]]`, transported to `C`, `B`, `A`
  have tr0 := K.trace_eq m
  rw [Matrix.trace_fin_two] at tr0
  have e11 : K.M m 1 1 = -K.M m 0 0 := by linarith
  have hv' : Y.m2Norm K.M (m - 1) = 8 * K.M m 1 0 / (Y.act (m - 1) + Y.act m) ^ 2 := by
    have := Y.m2_norm_next K.transport (m - 1)
    simp only [h1, ↓reduceIte, sub_add_cancel] at this
    exact this
  have hu' : Y.m2Norm K.M m = -8 * K.M m 0 1 /
      (Y.q m ^ 2 * (Y.act m + Y.act (m + 1)) ^ 2) := by
    unfold CostateCycle.m2Norm; simp only [h0, ↓reduceIte]
  have hw' : Y.m2Norm K.M (m + 3) = -8 * K.M (m + 3) 0 1 /
      (Y.q (m + 3) ^ 2 * (Y.act (m + 3) + Y.act (m + 4)) ^ 2) := by
    unfold CostateCycle.m2Norm; simp only [h5, ↓reduceIte]
    rw [show m + 3 + 1 = m + 4 by ring]
  obtain ⟨x1, y1, z1, w1⟩ := Y.wx_next_rev K.transport h0
  obtain ⟨x2, y2, z2, w2⟩ := Y.wx_next_fwd K.transport h3
  rw [show m + 1 + 1 = m + 2 by ring] at x2 y2 z2 w2
  obtain ⟨x3, y3, -, -⟩ := Y.wx_next_rev K.transport h4
  rw [show m + 2 + 1 = m + 3 by ring] at x3 y3
  rw [e11] at x1 y1
  obtain ⟨hwt, hELt⟩ := ss_alg_wEL a0 b0 c0 B0 A0 P0 hqm hq1 hq2 hq3 x1 y1 z1 w1 x2 y2 z2 w2 x3 y3
  rw [← hv', ← hu', ← hw'] at hwt
  rw [← hu'] at hELt
  -- the middle slack
  have hGL := K.mc_fwd (m + 2) h3'
  rw [show m + 2 - 1 = m + 1 by ring] at hGL
  rw [ss_alg_mid a0 b0 c0 B0 hqm hq1 x1 y1 z1 w1 x2 y2 z2, ← hv', ← hu'] at hGL
  have hmid := nonneg_of_mul_nonneg_right hGL (show (0 : ℝ) < (Y.act m ^ 2 + 4) ^ 2 / 4
    by positivity)
  -- the window
  refine ⟨{
    pb := Y.act (m - 2), b := Y.act (m - 1), a := Y.act m, C := Y.act (m + 1), B := Y.act (m + 2)
    A := Y.act (m + 3), Pf := Y.act (m + 4), u := Y.m2Norm K.M m, v := Y.m2Norm K.M (m - 1)
    w := Y.m2Norm K.M (m + 3), E := 16 * K.M m 0 0 / (Y.act m ^ 2 + 4)
    EL := 16 * K.M (m + 3) 0 0 / (Y.act (m + 3) ^ 2 + 4), Γ := K.Γ
    a_pos := a0, a_lt_b := hab, a_lt_C := hac, a_le_A := hm _, a_le_pb := hm _, A_lt_B := hAB
    A_lt_Pf := hAPf, C_le_b := hcb, A_lt_C := hAC', star_pb := st_pb
    star_ab := by rw [mul_comm]; exact st_ab
    star_aC := st_aC, star_CB := st_CB, star_BA := st_BA, star_APf := st_APf
    central := by
      have := mul_lt_mul_of_pos_right qm1
        (show 0 < (Y.act (m - 1) + Y.act m) * (Y.act m + Y.act (m + 1)) by positivity)
      rw [show Y.act m + Y.act (m - 1) = Y.act (m - 1) + Y.act m by ring]
      linarith
    central_A := by
      have := mul_lt_mul_of_pos_right q31
        (show 0 < (Y.act (m + 2) + Y.act (m + 3)) * (Y.act (m + 3) + Y.act (m + 4)) by positivity)
      linarith
    a_ge := P.wx_m_ge hK m _, scale := hsc, scale_A := hscA
    u_eq := sec_C.1
    u_eq' := by rw [← hu1]; exact sec_B.1
    v_eq := by rw [sec_b.2, m2Sec_comm]
    u_le := rle_a, u_ge := fge_C, u_le' := rle_B, v_le := rle_b, v_ge := fge_pb, w_le := rle_A
    w_ge := by rw [sec_P.1]; exact m2Sec_ge A0 P0 (pos _)
    E_eq := cfa_E, EL_eq := cfA_E, Γ_eq := cfa_Γ, Γ_eq' := cfA_Γ
    cas_lt := K.cas_lt hc, cas_gt := K.cas_gt hc hK h.1
    w_transport := hwt, EL_transport := hELt
    mid := by
      rw [Certificates.SmallerShort.Point.fmid, Certificates.SmallerShort.Point.pmid,
        ss_point_be a0 c0, ss_point_x a0 c0, ss_point_u a0 c0 B0, ← sec_C.1]
      exact hmid
    defect := P.df_defect hc h.1 (by omega) K h2 h1 h0 h3 h4 hAC' }, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

end SmoothedOctagon

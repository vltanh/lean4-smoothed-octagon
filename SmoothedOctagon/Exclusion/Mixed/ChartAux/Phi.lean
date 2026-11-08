module

public import SmoothedOctagon.Exclusion.Mixed.ChartAux.Root
public import SmoothedOctagon.Certificates.Nonshort

/-!
# Case M2 charts: the centred root identity

Exact identities of `MIXED_NONSHORT_BLOWUP_REDUCTION` (BLOWUP) at a point of the boundary covers
(`Certificates/Nonshort.lean`) with `l0 = 0`, in the cover's own coordinates.

* `ch_log_H`: `log (1 + z) = z - z²/2 + z³ H(z)` for every `z`.
* `ch_phi_root`: `ε² Φ = R_d(U*; b*)` (BLOWUP (9)-(13)).
* `ch_D1`: `ε D₁ = -R_u(b*)` (BLOWUP (3)-(4)).
* `ch_pt_h`: the cover's `h` is the central diagonal `m2h a b* c u v` of its `u`, `v`.
* `ch_pt_excess`: `excess = γ²(u, v, h) - 23/125` (BLOWUP (14)-(16)).
* `ch_pt_w`, `ch_pt_tn`: the cover's `w`, `tn` are `m2wOf`, `m2Next` of its `u`, `v`, `h`.
* `ch_pt_v`: the cover's `v` is `Sec(a, c, d)` (`z₁ > 0`).
* `ch_pt_upper`, `ch_pt_turn`: `x_c z₁ upper_turn = U(a/T) - v`, `x_c z₁ turn = v - g_c(d)`
  (BLOWUP (17), (17a)).
* `ch_pt_Fend`: `Fend = F_{d/W}(q)` (`z₂ > 0`, BLOWUP (17b)).
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates.Nonshort

theorem ch_log_H (z : ℝ) : Real.log (1 + z) = z - z ^ 2 / 2 + z ^ 3 * Hlog z := by
  unfold Hlog
  split_ifs with h
  · subst h; simp
  · have : z ^ 3 ≠ 0 := pow_ne_zero 3 h
    field_simp
    ring

theorem ch_phi_root (p : Point) (hl0 : p.l0 = 0) (ha : 0 < p.a) (hc : 0 < p.c) (h1 : 0 ≤ p.z1)
    (h2 : 0 ≤ p.z2) :
    p.eps ^ 2 * p.phi =
      m2Root p.a p.c p.d p.r (m2U (p.a * p.T0 / p.K)) p.v
        (m2h p.a (p.K / p.T0 - p.a) p.c (m2U (p.a * p.T0 / p.K)) p.v) := by
  have hT : 0 < p.T0 := by unfold Point.T0; linarith
  have hK : 0 < p.K := by unfold Point.K; positivity
  have hW : 0 < p.W := by unfold Point.W; positivity
  have hQ : 0 < p.Q := by unfold Point.Q; positivity
  have hq : 0 < p.q := by unfold Point.q; linarith
  have hZ : 0 < p.Z := by unfold Point.Z; positivity
  have hcd : p.c + p.d = p.W := by unfold Point.W Point.d Point.T0 Point.z1; ring
  have hdr : p.d + p.r = p.Z := by unfold Point.r; ring
  have hL2 : Real.log ((p.c + p.d) * (p.d + p.r) / (p.d ^ 2 + 4)) =
      p.z2 - p.z2 ^ 2 / 2 + p.z2 ^ 3 * p.H2 := by
    rw [hcd, hdr, show p.d ^ 2 + 4 = p.Q from rfl,
      show p.W * p.Z / p.Q = 1 + p.z2 by unfold Point.Z Point.q; field_simp]
    exact ch_log_H _
  have hL0 : Real.log (p.K / p.T0 * (p.a + p.c) / (p.a ^ 2 + 4)) = 0 := by
    rw [show p.K / p.T0 * (p.a + p.c) / (p.a ^ 2 + 4) = 1 by
      unfold Point.T0 at hT ⊢; unfold Point.K at hK ⊢; field_simp]
    simp
  have hcdr : p.c + p.d + p.r = p.W + p.r := by rw [hcd]
  unfold m2Root m2h m2Stat m2hd m2wOf m2Y m2U
  simp only [sub_add_cancel]
  rw [hL2, hL0, hcdr, hcd, hdr]
  have hW' : (p.a + p.c) * (1 + p.eps * p.l1) ≠ 0 := hW.ne'
  have hQ' : (p.a + (p.a + p.c) * (p.eps * p.l1)) ^ 2 + 4 ≠ 0 := hQ.ne'
  have hq' : 1 + p.eps * p.l2 ≠ 0 := hq.ne'
  have h1' : 1 + p.eps * p.l1 ≠ 0 := by unfold Point.z1 at h1; positivity
  have hT' : p.a + p.c ≠ 0 := hT.ne'
  have hK' : p.a ^ 2 + 4 ≠ 0 := hK.ne'
  have ha' : p.a ≠ 0 := ha.ne'
  simp only [Point.phi, Point.base, Point.N, Point.H0, Point.H1, Point.H2, Point.Bv, Point.v,
    Point.v0, Point.dv, Point.tt, Point.xc, Point.r, Point.Z, Point.q, Point.Q, Point.W, Point.d,
    Point.z0, Point.z1, Point.z2, Point.T0, Point.K, hl0, centeredPolynomialCancelled]
  generalize Hlog (p.eps * p.l1) = H1
  generalize Hlog (p.eps * p.l2) = H2
  generalize p.a = a at *
  generalize p.c = c at *
  generalize p.eps = e at *
  generalize p.l1 = l1 at *
  generalize p.l2 = l2 at *
  field_simp
  ring

/-- `ε D₁ = -R_u(b*)` (BLOWUP (3)-(4), inventory E2 entry 13). -/
theorem ch_D1 (p : Point) (hl0 : p.l0 = 0) (ha : 0 < p.a) (hc : 0 < p.c) (h1 : 0 ≤ p.z1)
    (h2 : 0 ≤ p.z2) :
    p.eps * p.D1 = -chRu p.a (p.K / p.T0 - p.a) p.c p.d p.r := by
  have hT : 0 < p.T0 := by unfold Point.T0; linarith
  have hK : 0 < p.K := by unfold Point.K; positivity
  have hW : 0 < p.W := by unfold Point.W; positivity
  have hQ : 0 < p.Q := by unfold Point.Q; positivity
  have hq : 0 < p.q := by unfold Point.q; linarith
  have hdr : p.d + p.r = p.Z := by unfold Point.r; ring
  rw [ch_Ru_eq ha.ne', show p.a + (p.K / p.T0 - p.a) = p.K / p.T0 by ring, hdr]
  have hW' : (p.a + p.c) * (1 + p.eps * p.l1) ≠ 0 := hW.ne'
  have hQ' : (p.a + (p.a + p.c) * (p.eps * p.l1)) ^ 2 + 4 ≠ 0 := hQ.ne'
  have hq' : 1 + p.eps * p.l2 ≠ 0 := hq.ne'
  have h1' : 1 + p.eps * p.l1 ≠ 0 := by unfold Point.z1 at h1; positivity
  have hT' : p.a + p.c ≠ 0 := hT.ne'
  have hK' : p.a ^ 2 + 4 ≠ 0 := hK.ne'
  have ha' : p.a ≠ 0 := ha.ne'
  simp only [Point.D1, Point.Z, Point.q, Point.Q, Point.W, Point.d, Point.z0, Point.z1, Point.z2,
    Point.T0, Point.K, hl0, m2Y]
  generalize p.a = a at *
  generalize p.c = c at *
  generalize p.eps = e at *
  generalize p.l1 = l1 at *
  generalize p.l2 = l2 at *
  field_simp
  ring

/-- The cover's `h` is the central diagonal at `b* = K/T - a` of its `u` and `v` (BLOWUP (15)). -/
theorem ch_pt_h (p : Point) (hl0 : p.l0 = 0) (ha : 0 < p.a) (hc : 0 < p.c) :
    p.h = m2h p.a (p.K / p.T0 - p.a) p.c p.u p.v := by
  have hT : 0 < p.T0 := by unfold Point.T0; linarith
  have hK : 0 < p.K := by unfold Point.K; positivity
  have hlog1 : Real.log (p.K / p.T0 * (p.a + p.c) / (p.a ^ 2 + 4)) = 0 := by
    rw [show p.K / p.T0 * (p.a + p.c) / (p.a ^ 2 + 4) = 1 by
      unfold Point.T0 at hT ⊢; unfold Point.K at hK ⊢; field_simp]
    simp
  unfold m2h m2Stat
  simp only [sub_add_cancel]
  rw [hlog1]
  have hT' : p.a + p.c ≠ 0 := hT.ne'
  have hK' : p.a ^ 2 + 4 ≠ 0 := hK.ne'
  have ha' : p.a ≠ 0 := ha.ne'
  simp only [Point.h, Point.h0, Point.dh, Point.u, Point.u0, Point.du, Point.v, Point.v0, Point.S,
    Point.rr, Point.tt, Point.rho, Point.z0, Point.T0, Point.K, hl0, mul_zero, add_zero,
    Real.log_one]
  field_simp
  ring

/-- **The centred Casimir** (BLOWUP (14)-(16)): `excess = γ²(u, v, h) - 23/125`. -/
theorem ch_pt_excess (p : Point) (ha : 0 < p.a) (hc : 0 < p.c) :
    p.excess = m2Cas p.a p.u p.v p.h - 23 / 125 := by
  have hT : 0 < p.a + p.c := by linarith
  have hK : 0 < p.a ^ 2 + 4 := by positivity
  simp only [Point.excess, m2Cas, Point.u, Point.v, Point.h, Point.u0, Point.v0, Point.h0,
    Point.rr, Point.tt, Point.rho, Point.K, Point.T0]
  field_simp
  ring

/-- The cover's `w` is the transported norm of its `u`, `v`, `h`. -/
theorem ch_pt_w (p : Point) :
    p.w = m2wOf p.a p.c p.d p.u p.v p.h := by
  have hcd : p.c + p.d = p.W := by unfold Point.W Point.d Point.T0 Point.z1; ring
  unfold m2wOf m2Y Point.w Point.Y
  rw [hcd]
  unfold Point.K Point.T0 Point.Q
  ring

/-- The cover's `tn` is the next transported norm of its `u`, `v`, `h`. -/
theorem ch_pt_tn (p : Point) :
    p.tn = m2Next p.a p.c p.d p.r p.u p.v p.h := by
  have hcd : p.c + p.d = p.W := by unfold Point.W Point.d Point.T0 Point.z1; ring
  have hdr : p.d + p.r = p.Z := by unfold Point.r; ring
  unfold m2Next
  rw [← ch_pt_w p, hdr]
  unfold m2hd m2Y Point.tn Point.hd Point.Kr Point.Y Point.Q
  rw [hcd]
  unfold Point.T0
  ring

/-- The cover's `v` is the turn secant `Sec(a, c, d)` (BLOWUP (17)). -/
theorem ch_pt_v (p : Point) (ha : 0 < p.a) (hc : 0 < p.c) (h1 : 0 < p.z1) :
    p.v = m2Sec p.a p.c p.d := by
  have hT : 0 < p.T0 := by unfold Point.T0; linarith
  have hd : p.a ≠ p.d := by
    unfold Point.d; intro h; have : p.T0 * p.z1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h' <;> linarith
  rw [m2Sec_of_ne hd]
  have hlog : Real.log ((p.d + p.c) / (p.a + p.c)) = p.z1 - p.z1 ^ 2 / 2 + p.z1 ^ 3 * p.H1 := by
    rw [show (p.d + p.c) / (p.a + p.c) = 1 + p.z1 by
      unfold Point.d; unfold Point.T0 at hT ⊢; field_simp; ring]
    exact ch_log_H _
  rw [hlog]
  have hT' : p.a + p.c ≠ 0 := hT.ne'
  have h1' : 1 + p.eps * p.l1 ≠ 0 := by unfold Point.z1 at h1; positivity
  have h1'' : p.eps * p.l1 ≠ 0 := h1.ne'
  have hdc : p.a + (p.a + p.c) * (p.eps * p.l1) + p.c ≠ 0 := by unfold Point.z1 at h1; positivity
  simp only [Point.v, Point.v0, Point.dv, Point.tt, Point.xc, Point.d, Point.T0, Point.z1,
    Point.H1]
  generalize Hlog (p.eps * p.l1) = H1
  generalize p.eps * p.l1 = z at *
  field_simp
  ring

/-- `x_c z₁ upper_turn = U(a/T) - v` (BLOWUP (17a)). -/
theorem ch_pt_upper (p : Point) (ha : 0 < p.a) (hc : 0 < p.c) (h1 : 0 ≤ p.z1) :
    p.xc * p.z1 * p.upperTurn = m2U (p.a / p.T0) - p.v := by
  have hT : 0 < p.a + p.c := by linarith
  have h1' : 1 + p.eps * p.l1 ≠ 0 := by unfold Point.z1 at h1; positivity
  simp only [Point.upperTurn, Point.v, Point.v0, Point.dv, Point.tt, Point.xc, Point.T0, Point.z1,
    m2U]
  generalize Hlog (p.eps * p.l1) = H1
  generalize p.eps * p.l1 = z at *
  field_simp
  ring

/-- `x_c z₁ turn = v - g_c(d)` (BLOWUP (17)). -/
theorem ch_pt_turn (p : Point) (ha : 0 < p.a) (hc : 0 < p.c) (h1 : 0 ≤ p.z1) :
    p.xc * p.z1 * p.turn = p.v - m2g p.c p.d := by
  have hT : 0 < p.a + p.c := by linarith
  have h1' : 1 + p.eps * p.l1 ≠ 0 := by unfold Point.z1 at h1; positivity
  have hcd : p.c + (p.a + (p.a + p.c) * (p.eps * p.l1)) ≠ 0 := by
    unfold Point.z1 at h1; positivity
  simp only [Point.turn, Point.v, Point.v0, Point.dv, Point.tt, Point.xc, Point.T0, Point.z1,
    Point.d, m2g]
  generalize Hlog (p.eps * p.l1) = H1
  generalize p.eps * p.l1 = z at *
  field_simp
  ring

/-- `Fend = F_{d/W}(q)` (BLOWUP (17b)). -/
theorem ch_pt_Fend (p : Point) (h2 : 0 < p.z2) : p.Fend = m2F (p.d / p.W) p.q := by
  have hq : p.q ≠ 1 := by unfold Point.q; linarith
  rw [m2F_of_ne hq]
  have hlog := ch_log_H p.z2
  unfold Point.Fend Point.L2
  rw [show p.q - 1 = p.z2 by unfold Point.q; ring, show p.q = 1 + p.z2 by rfl, hlog]
  unfold Point.H2
  have : p.z2 ≠ 0 := h2.ne'
  field_simp

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.Centre
public import SmoothedOctagon.Exclusion.Mixed.Extract.Transport
public import SmoothedOctagon.Exclusion.Mixed.Short.Residual

/-!
# Case M2, smaller-short side: the covector algebra of the short window

The transport of the covector between the two reverse centres of a short window, on the frames `M i`
of the covector calculus (`NormalPeriod.M2Calculus`). In the centre frame
`M m = [[h, y₀], [z₀, -h]]` of a reverse centre `a` (`v = 8z₀/(b + a)²`, `u = -8y₀/(q_a²(a + C)²)`,
`E = 16h/K_a`), transport through the reverse switch after `a`, the forward switch after the turn
`C` and the reverse switch after the turn `B` (factors `q_a = K_a/((b + a)(a + C))`,
`(C + B)/(a + C)`, `(C + B)/(B + A)`) gives the frame of the outer centre `A`.

The same-lift transport formulas for `w` and `E_L` and the middle-switch slack `N_mid` are
identities of this transport: `w = λ²v + d²u - dλE`, `E_L = 2du - λE` (`ss_alg_wEL`), and the
missing control `G_L ≥ 0` at the forward switch `C → B` (`M2Calculus.mc_fwd`) equals
`(K_a²/4) N_mid` (`ss_alg_mid`).

## Main API

* `ss_alg_wEL`, `ss_alg_mid`: the two identities, as real algebra.
* `ss_point_u`, `ss_point_be`, `ss_point_x`: the cover's `u`, `β`, `x` at the window point.
* `ss_centre_frame`: centre stationarity `E = m2E …` and the Gram determinant `Γ = m2Gam …` at a
  reverse centre, with `E = 16 (M k)₀₀/K` (as in `m2_centre`).
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates.SmallerShort

/-- **The same-lift transport to the outer centre**: with `λ = K_a/K_A`, the norm `w` and the
pairing `E_L` at `A` are `w = λ²v + d²u - dλE` and `E_L = 2du - λE`. -/
theorem ss_alg_wEL {a b C B A Pf h y0 z0 qm q1 q2 q3 : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (hB : 0 < B) (hA : 0 < A) (hPf : 0 < Pf)
    (hqm : qm = (a ^ 2 + 4) / ((b + a) * (a + C))) (hq1 : q1 = (C + B) / (a + C))
    (hq2 : q2 = (C + B) / (B + A)) (hq3 : q3 = (A ^ 2 + 4) / ((B + A) * (A + Pf)))
    {m1_00 m1_01 m1_10 m1_11 m2_00 m2_01 m2_10 m2_11 m3_00 m3_01 : ℝ}
    (e1_00 : m1_00 = -h - y0 / qm ^ 2) (e1_01 : m1_01 = h - qm ^ 2 * z0 + y0 / qm ^ 2 - -h)
    (e1_10 : m1_10 = -(y0 / qm ^ 2)) (e1_11 : m1_11 = h + y0 / qm ^ 2)
    (e2_00 : m2_00 = q1 ^ 2 * m1_10 + m1_11) (e2_01 : m2_01 = -(q1 ^ 2 * m1_10))
    (e2_10 : m2_10 = -m1_00 + q1 ^ 2 * m1_10 - m1_01 / q1 ^ 2 + m1_11)
    (e2_11 : m2_11 = m1_00 - q1 ^ 2 * m1_10)
    (e3_00 : m3_00 = m2_11 - m2_01 / q2 ^ 2)
    (e3_01 : m3_01 = m2_00 - q2 ^ 2 * m2_10 + m2_01 / q2 ^ 2 - m2_11) :
    -8 * m3_01 / (q3 ^ 2 * (A + Pf) ^ 2) =
        ((a ^ 2 + 4) / (A ^ 2 + 4)) ^ 2 * (8 * z0 / (b + a) ^ 2) +
        ((a ^ 2 + 4) / (A ^ 2 + 4) * (a ^ 2 / (a ^ 2 + 4)) *
          ((A / a) ^ 2 + 2 * (A / a) * (B / a) + 1 + 2 * (C / a) - 2 * (B / a) * (C / a))) ^ 2 *
          (-8 * y0 / (qm ^ 2 * (a + C) ^ 2)) -
        (a ^ 2 + 4) / (A ^ 2 + 4) * (a ^ 2 / (a ^ 2 + 4)) *
          ((A / a) ^ 2 + 2 * (A / a) * (B / a) + 1 + 2 * (C / a) - 2 * (B / a) * (C / a)) *
          ((a ^ 2 + 4) / (A ^ 2 + 4)) * (16 * h / (a ^ 2 + 4)) ∧
    16 * m3_00 / (A ^ 2 + 4) =
        2 * ((a ^ 2 + 4) / (A ^ 2 + 4) * (a ^ 2 / (a ^ 2 + 4)) *
          ((A / a) ^ 2 + 2 * (A / a) * (B / a) + 1 + 2 * (C / a) - 2 * (B / a) * (C / a))) *
          (-8 * y0 / (qm ^ 2 * (a + C) ^ 2)) -
        (a ^ 2 + 4) / (A ^ 2 + 4) * (16 * h / (a ^ 2 + 4)) := by
  subst e3_00 e3_01 e2_00 e2_01 e2_10 e2_11 e1_00 e1_01 e1_10 e1_11 hqm hq1 hq2 hq3
  have : 0 < a + C := add_pos ha hC
  have : 0 < b + a := by positivity
  have : 0 < C + B := by positivity
  have : 0 < B + A := by positivity
  have : 0 < A + Pf := by positivity
  constructor <;> (field_simp; ring)

/-- **The middle-switch slack**: the missing control at the forward switch `C → B`, read in the
frame of `B`, is `(K_a²/4) N_mid`. -/
theorem ss_alg_mid {a b C B h y0 z0 qm q1 : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (hB : 0 < B)
    (hqm : qm = (a ^ 2 + 4) / ((b + a) * (a + C))) (hq1 : q1 = (C + B) / (a + C))
    {m1_00 m1_01 m1_10 m1_11 m2_00 m2_01 m2_10 : ℝ}
    (e1_00 : m1_00 = -h - y0 / qm ^ 2) (e1_01 : m1_01 = h - qm ^ 2 * z0 + y0 / qm ^ 2 - -h)
    (e1_10 : m1_10 = -(y0 / qm ^ 2)) (e1_11 : m1_11 = h + y0 / qm ^ 2)
    (e2_00 : m2_00 = q1 ^ 2 * m1_10 + m1_11) (e2_01 : m2_01 = -(q1 ^ 2 * m1_10))
    (e2_10 : m2_10 = -m1_00 + q1 ^ 2 * m1_10 - m1_01 / q1 ^ 2 + m1_11) :
    4 * B * (C + B) * m2_00 + 2 * (B ^ 2 + 4) * m2_01 - 2 * (C + B) ^ 2 * m2_10 + C * (C + B) +
        (B ^ 2 + 4) =
      (a ^ 2 + 4) ^ 2 / 4 *
        ((1 - a ^ 2 / (a ^ 2 + 4)) * ((B / a) ^ 2 * (a ^ 2 / (a ^ 2 + 4)) +
          B / a * (a ^ 2 / (a ^ 2 + 4)) * (C / a) + a ^ 2 / (a ^ 2 + 4) * (C / a) ^ 2 -
          a ^ 2 / (a ^ 2 + 4) + 1) - 8 * z0 / (b + a) ^ 2 -
        a ^ 2 / (a ^ 2 + 4) * (16 * h / (a ^ 2 + 4)) * (B / a * (C / a) - 2 * (C / a) - 1) -
        a ^ 2 / (a ^ 2 + 4) * (-8 * y0 / (qm ^ 2 * (a + C) ^ 2)) *
          ((B / a) ^ 2 * (a ^ 2 / (a ^ 2 + 4)) * (C / a) ^ 2 -
            (B / a) ^ 2 * (a ^ 2 / (a ^ 2 + 4)) + (B / a) ^ 2 -
            4 * (B / a) * (a ^ 2 / (a ^ 2 + 4)) * (C / a) ^ 2 -
            4 * (B / a) * (a ^ 2 / (a ^ 2 + 4)) * (C / a) + 2 * (B / a) * (C / a) +
            3 * (a ^ 2 / (a ^ 2 + 4)) * (C / a) ^ 2 + 4 * (a ^ 2 / (a ^ 2 + 4)) * (C / a) +
            a ^ 2 / (a ^ 2 + 4) + (C / a) ^ 2)) := by
  subst e2_00 e2_01 e2_10 e1_00 e1_01 e1_10 e1_11 hqm hq1
  have : 0 < a + C := add_pos ha hC
  have : 0 < b + a := by positivity
  have : 0 < C + B := by positivity
  field_simp
  ring

/-- The cover's `x` at the window point. -/
theorem ss_point_x {a C δ al ρ v E : ℝ} (ha : 0 < a) (hC : 0 < C) :
    (⟨a / (a + C), δ, al, ρ, v, E⟩ : Point).x = C / a := by
  have := add_pos ha hC
  rw [Point.x]; field_simp; ring

/-- The cover's `β` at the window point. -/
theorem ss_point_be {a C B al ρ v E : ℝ} (ha : 0 < a) (hC : 0 < C) :
    (⟨a / (a + C), B / C - 1, al, ρ, v, E⟩ : Point).be = B / a := by
  rw [Point.be, ss_point_x ha hC]; field_simp; ring

/-- The cover's `u` at the window point is the secant `Sec(a, C, B)`. -/
theorem ss_point_u {a C B al ρ v E : ℝ} (ha : 0 < a) (hC : 0 < C) (hB : 0 < B) :
    (⟨a / (a + C), B / C - 1, al, ρ, v, E⟩ : Point).u = m2Sec a C B := by
  rw [ss_sec_logDiv ha hC hB]
  have hxi : (⟨a / (a + C), B / C - 1, al, ρ, v, E⟩ : Point).xi = C / (a + C) := by
    rw [Point.xi]; field_simp; ring
  have hh : (⟨a / (a + C), B / C - 1, al, ρ, v, E⟩ : Point).h = (B + C) / (a + C) := by
    rw [Point.h, hxi]; field_simp; ring
  rw [Point.u, hxi, hh]
  have e : C / (a + C) / (2 + (B / C - 1)) = (C / (a + C)) ^ 2 / ((B + C) / (a + C)) := by
    have : B + C ≠ 0 := by positivity
    rw [show 2 + (B / C - 1) = (B + C) / C by field_simp; ring]
    field_simp
  exact congrArg (fun z => 1 + z - C / (a + C) * logDiv ((B + C) / (a + C))) e

/-- **Centre stationarity and the Gram determinant at a reverse centre** (the core of
`m2_centre`): with `E = 16 (M k)₀₀/K_k`, `E = m2E a_k a_{k-1} a_{k+1} n_{k-1} n_k` and
`Γ = m2Gam a_k n_{k-1} n_k E`. -/
theorem ss_centre_frame (P : NormalPeriod) (K : P.M2Calculus) {k : ℤ}
    (h1 : ¬ P.costateCycle.m2Fwd (k - 1)) (h0 : ¬ P.costateCycle.m2Fwd k) :
    16 * K.M k 0 0 / (P.costateCycle.act k ^ 2 + 4) =
        m2E (P.costateCycle.act k) (P.costateCycle.act (k - 1)) (P.costateCycle.act (k + 1))
          (P.costateCycle.m2Norm K.M (k - 1)) (P.costateCycle.m2Norm K.M k) ∧
      K.Γ = m2Gam (P.costateCycle.act k) (P.costateCycle.m2Norm K.M (k - 1))
        (P.costateCycle.m2Norm K.M k) (16 * K.M k 0 0 / (P.costateCycle.act k ^ 2 + 4)) := by
  set C := P.costateCycle with hC
  have ha := C.act_pos k
  have hp0 := C.act_pos (k - 1)
  have hn0 := C.act_pos (k + 1)
  have hq := C.m2_factor_rr h1 h0
  have hK : 0 < C.act k ^ 2 + 4 := by positivity
  have hui : C.m2Norm K.M (k - 1) = 8 * K.M k 1 0 / (C.act (k - 1) + C.act k) ^ 2 := by
    have := C.m2_norm_next K.transport (k - 1)
    simp only [h1, ↓reduceIte, sub_add_cancel] at this
    exact this
  have huo : C.m2Norm K.M k = -8 * K.M k 0 1 / (C.q k ^ 2 * (C.act k + C.act (k + 1)) ^ 2) := by
    unfold CostateCycle.m2Norm; simp only [h0, ↓reduceIte]
  have hst := K.stat k (iff_of_false h1 h0)
  have htr := K.trace_eq k
  have hdet := K.det_eq k
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  constructor
  · have hm := m2E_mul (C.m2Norm K.M (k - 1)) (C.m2Norm K.M k) ha hp0 hn0
    rw [← hst] at hm
    have : C.act k * (16 * K.M k 0 0 / (C.act k ^ 2 + 4)) =
        C.act k * m2E (C.act k) (C.act (k - 1)) (C.act (k + 1)) (C.m2Norm K.M (k - 1))
          (C.m2Norm K.M k) := by
      rw [hm, show C.act (k - 1) + C.act k = C.act k + C.act (k - 1) by ring]
      field_simp
      ring
    exact mul_left_cancel₀ ha.ne' this
  · rw [hui, huo, ← hdet]
    unfold m2Gam
    have hs : 0 < C.act (k - 1) + C.act k := by positivity
    have ht : 0 < C.act k + C.act (k + 1) := by positivity
    have e11 : K.M k 1 1 = -K.M k 0 0 := by linarith
    rw [e11]
    have hqe : C.q k = (C.act k ^ 2 + 4) / ((C.act (k - 1) + C.act k) * (C.act k + C.act (k + 1))) := by
      rw [eq_div_iff (by positivity)]; exact hq
    rw [hqe]
    field_simp
    ring

end SmoothedOctagon

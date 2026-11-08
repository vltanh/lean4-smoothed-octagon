module

public import SmoothedOctagon.Exclusion.Mixed.Scalar

/-!
# Case M2: the algebra of the smaller-nonshort window

`MIXED_SMALLER_TURN_CONTINUATION` (CONT) (8), (10), (14), (16) and inventory E2 §1.4, as identities
between real numbers. In the centre frame the multiplier is `[[h, y₀], [z₀, -h]]` with
`u = 8 z₀/S²`, `v = -8 y₀/(q_a² T²)` and `q_a = K/(ST)` (`S = b + a`, `T = a + c`, `K = a² + 4`);
transport through the reverse switch after `a` and the forward switch after `c` (factors
`q_c = W/T`, `q_d = WZ/Q`) gives the frame of `d`, whose diagonal is `h_d` and whose outgoing norm
is `w` (CONT (10)); one more forward transport gives the next norm `t` (CONT (14), (16)).

## Main API

* `wx_alg_hd`: `h_d = h + vY/8` (`m2hd`).
* `wx_alg_w`: `8 q_d² (U_d)₂₁/Z² = (uK² + 16hY + vY²)/Q²` (`m2wOf`).
* `wx_alg_t`: `8 q_r² (U_r)₂₁/(r + s)² = (Q²v - 16 h_d Z² + w Z⁴)/K_r²`.
* `wx_alg_cas`: `det U_a = uvK²/64 - h²` (`m2Cas`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- CONT (10): the diagonal of the frame of `d`. -/
theorem wx_alg_hd {a b c d h y0 qm q1 : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hqm : qm = (a ^ 2 + 4) / ((b + a) * (a + c))) (hq1 : q1 = (c + d) / (a + c)) :
    q1 ^ 2 * -(y0 / qm ^ 2) + (h + y0 / qm ^ 2) =
      m2hd a c d (-8 * y0 / (qm ^ 2 * (a + c) ^ 2)) h := by
  subst hqm hq1
  unfold m2hd m2Y
  have : 0 < a + c := by positivity
  field_simp
  ring

/-- CONT (10): the outgoing norm of `d`. -/
theorem wx_alg_w {a b c d r h y0 z0 qm q1 q2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hr : 0 < r)
    (hqm : qm = (a ^ 2 + 4) / ((b + a) * (a + c))) (hq1 : q1 = (c + d) / (a + c))
    (hq2 : q2 = (c + d) * (d + r) / (d ^ 2 + 4)) :
    8 * q2 ^ 2 * (-(-h - y0 / qm ^ 2) + q1 ^ 2 * -(y0 / qm ^ 2) -
        (h - qm ^ 2 * z0 + y0 / qm ^ 2 - -h) / q1 ^ 2 + (h + y0 / qm ^ 2)) / (d + r) ^ 2 =
      m2wOf a c d (8 * z0 / (b + a) ^ 2) (-8 * y0 / (qm ^ 2 * (a + c) ^ 2)) h := by
  subst hqm hq1 hq2
  unfold m2wOf m2Y
  have : 0 < a + c := by positivity
  field_simp
  ring

/-- CONT (14), (16): the norm of a forward switch after `r`, to an active margin `s`. -/
theorem wx_alg_t {c d r s v w X2 Z2 q2 q3 : ℝ} (hc : 0 < c) (hd : 0 < d) (hr : 0 < r)
    (hs : 0 < s) (hq2 : q2 = (c + d) * (d + r) / (d ^ 2 + 4))
    (hq3 : q3 = (d + r) * (r + s) / (r ^ 2 + 4)) (hw : w = 8 * q2 ^ 2 * Z2 / (d + r) ^ 2) :
    8 * q3 ^ 2 * (-X2 + q2 ^ 2 * Z2 - -((c + d) ^ 2 * v / 8) / q2 ^ 2 + -X2) / (r + s) ^ 2 =
      ((d ^ 2 + 4) ^ 2 * v - 16 * X2 * (d + r) ^ 2 + w * (d + r) ^ 4) / (r ^ 2 + 4) ^ 2 := by
  subst hq2 hq3 hw
  field_simp
  ring

/-- CONT (8): the squared Casimir in the centre frame. -/
theorem wx_alg_cas {a b c h y0 z0 qm : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hqm : qm = (a ^ 2 + 4) / ((b + a) * (a + c))) :
    h * -h - y0 * z0 = m2Cas a (8 * z0 / (b + a) ^ 2) (-8 * y0 / (qm ^ 2 * (a + c) ^ 2)) h := by
  subst hqm
  unfold m2Cas
  field_simp
  ring

end SmoothedOctagon

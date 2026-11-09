module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Window
public import SmoothedOctagon.Exclusion.Mixed.Hand.Gap

/-!
# Case M2, forward successor by hand: the actual Casimir on the first-event stationary line

In the normalized coordinates, the first-event root equation makes the diagonal at `d` an affine
function of the outgoing norm `w`, `H_d(w) = (B/p)(Wv + Zw - S_d)` (`fhHd`, `Z = qB/W`, `S_d` the
normalized cost derivative `fhSd`), and the actual squared Casimir is
`Γ(w) = (4B²vw - H_d(w)²)/(16s²)` (`fhGam`, `s = k - t²`).

## Main API

* `fh_window_cas`: `γ² = Γ(w_actual)`; `fh_window_wU`: `w_actual < w_U` (the central upper envelope
  `fhwU`); `fh_window_w34`: `w_actual ≥ 3/4`.
* `fh_gam_anti`: `Γ` decreases between two norms where `2v - eH_d/p ≤ 0`.
* `fh_cas_slope`: **the stationary monotonicity** `2v - eH_d(w)/p < 0` for `w ≥ 3/4`,
  under `t ≥ 1/3`, `χ = pe ≥ 4/7`,
  `t ≤ r ≤ p`, `j < 1/4` and the incoming floor.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The normalized cost derivative at `d`, `S_d = C_d/T`. -/
noncomputable def fhSd (t x k q L : ℝ) : ℝ :=
  (1 - t) + q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ^ 2 / (1 + x)
    - (t + x) ^ 2 / (q * (k + 2 * t * x + x ^ 2) / (1 + x)) + (t + x) ^ 3 / (k + 2 * t * x + x ^ 2)
    - (t + x) * L

/-- The diagonal at `d` on the first-event stationary line, `16 h_d/T² = (B/p)(Wv + Zw - S_d)`. -/
noncomputable def fhHd (t x k q v L w : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) / (t + x) *
    ((1 + x) * v + q * (k + 2 * t * x + x ^ 2) / (1 + x) * w - fhSd t x k q L)

/-- The squared Casimir on the stationary line, `Γ(w) = (4B²vw - H_d(w)²)/(16s²)`. -/
noncomputable def fhGam (t x k q v L w : ℝ) : ℝ :=
  (4 * (k + 2 * t * x + x ^ 2) ^ 2 * v * w - fhHd t x k q v L w ^ 2) / (16 * (k - t ^ 2) ^ 2)

/-- The central upper-envelope norm `w_U = (k² - kt + t² + H_U Y + vY²)/B²`. -/
noncomputable def fhwU (t x k v : ℝ) : ℝ :=
  (k ^ 2 - k * t + t ^ 2 + (k / t * (v - 1 + t ^ 2) + t * (2 - t)) * (x * (x + 2))
    + v * (x * (x + 2)) ^ 2) / (k + 2 * t * x + x ^ 2) ^ 2

/-- **The actual squared Casimir on the stationary line**: `γ² = Γ(w_actual)`. -/
theorem fh_window_cas (W : M2Window) :
    m2Cas W.a W.u W.v W.h = fhGam W.nt W.nx W.nk W.nq W.v (Real.log W.nq) W.w := by
  obtain ⟨hT, ht, hx, hk, hq, ha, hc, hd, hK, hQ, hZ, hqd⟩ := fh_window_coords W
  set t := W.nt
  set x := W.nx
  set k := W.nk
  set q := W.nq
  set T := W.a + W.c
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by linarith
  have hS := nh_m2Stat_d (r := W.r) hT hx hB hq hc hd hQ hZ (by rw [hqd])
  -- the root equation gives the diagonal at `d`
  have hd0 : 0 < W.d := by linarith [W.a_lt_d, W.a_pos]
  have hH : m2hd W.a W.c W.d W.v W.h = (W.d ^ 2 + 4) * ((W.c + W.d) * W.v - m2Stat W.c W.d W.r) /
      (16 * W.d) + (W.d ^ 2 + 4) * (W.d + W.r) / (16 * W.d) * W.w := by
    have e := W.root
    unfold m2Root at e
    rw [← W.w_eq] at e
    field_simp
    field_simp at e
    linarith
  have hcd : W.c + W.d = (1 + x) * T := by rw [hc, hd]; ring
  have hhd : m2hd W.a W.c W.d W.v W.h = T ^ 2 / 16 * fhHd t x k q W.v (Real.log q) W.w := by
    rw [hH, hS, hQ, hZ, hcd, hd]
    unfold fhHd fhSd
    have htx : 0 < t + x := by linarith
    field_simp
    ring
  -- `γ² = Q²vw/64 - h_d²`
  have hcas : m2Cas W.a W.u W.v W.h = (W.d ^ 2 + 4) ^ 2 * W.v / 64 * W.w - m2hd W.a W.c W.d W.v W.h ^ 2 := by
    rw [W.w_eq]
    unfold m2Cas m2wOf m2hd
    field_simp
    ring
  have hs : 4 = T ^ 2 * (k - t ^ 2) := by
    have : W.a ^ 2 = t ^ 2 * T ^ 2 := by rw [ha]; ring
    nlinarith
  have hs0 : k - t ^ 2 ≠ 0 := by
    intro h0; rw [h0] at hs; norm_num at hs
  have hT4 : T ^ 4 = 16 / (k - t ^ 2) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hs0)]
    have : T ^ 4 * (k - t ^ 2) ^ 2 = (T ^ 2 * (k - t ^ 2)) ^ 2 := by ring
    rw [this, ← hs]; norm_num
  rw [hcas, hhd, hQ]
  unfold fhGam
  calc (T ^ 2 * (k + 2 * t * x + x ^ 2)) ^ 2 * W.v / 64 * W.w - (T ^ 2 / 16 * fhHd t x k q W.v (Real.log q) W.w) ^ 2
      = T ^ 4 * (4 * (k + 2 * t * x + x ^ 2) ^ 2 * W.v * W.w - fhHd t x k q W.v (Real.log q) W.w ^ 2) / 256 := by
        ring
    _ = _ := by rw [hT4]; field_simp; ring

/-- **The actual outgoing norm is below the central upper envelope**: `w_actual < w_U`. The
transported norm increases with the central incident norm, so `w ≤ w_U(b)`, and `w_U(b) < w_U(b*)`
at the boundary margin. -/
theorem fh_window_wU (W : M2Window) : W.w < fhwU W.nt W.nx W.nk W.v := by
  obtain ⟨hT, ht, hx, hk, hq, ha, hc, hd, hK, hQ, hZ, hqd⟩ := fh_window_coords W
  have ha0 := W.a_pos
  have hd0 : 0 < W.d := by linarith [W.a_lt_d]
  -- `w ≤ w_U(b) < w_U(b*)`
  have hw1 : W.w ≤ nhWU W.a W.b W.c W.d (m2U (W.a / (W.a + W.b))) W.v := by
    have e := nh_w_mono_u (a := W.a) (b := W.b) (c := W.c) (d := W.d)
      (u := W.u) (U := m2U (W.a / (W.a + W.b))) (v := W.v) ha0 hd0
    have hwu : W.w = nhWU W.a W.b W.c W.d W.u W.v := by rw [W.w_eq, W.h_eq]; rfl
    have hu := W.u_le
    rw [m2g_eq_m2U (by linarith [W.a_lt_b])] at hu
    have hY : 0 < m2Y W.a W.c W.d := by unfold m2Y; nlinarith [W.a_lt_d, W.a_lt_c]
    have hb : 0 < W.a + W.b := by linarith [W.a_lt_b]
    have : 0 ≤ (m2U (W.a / (W.a + W.b)) - W.u) * ((W.a ^ 2 + 4) * (W.a * (W.a ^ 2 + 4)
        + (W.a + W.b) * m2Y W.a W.c W.d) / (W.a * (W.d ^ 2 + 4) ^ 2)) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  have hw2 := nh_wU_lt_star (v := W.v) ha0 W.a_lt_b (by linarith [W.a_lt_c]) W.a_lt_d W.central
  -- the boundary value in normalized coordinates
  have hB : 0 < W.nk + 2 * W.nt * W.nx + W.nx ^ 2 := by positivity
  have hh := nh_m2h_star (v := W.v) hT ht hk ha hc hK
  have hU : m2U (W.a / (W.a + m2bStar W.a W.c)) = m2U (W.a * (W.a + W.c) / (W.a ^ 2 + 4)) := by
    have e : W.a + m2bStar W.a W.c = (W.a ^ 2 + 4) / (W.a + W.c) := by unfold m2bStar; ring
    rw [e, div_div_eq_mul_div]
  have hu : m2U (W.a * (W.a + W.c) / (W.a ^ 2 + 4)) * W.nk ^ 2 =
      W.nk ^ 2 - W.nk * W.nt + W.nt ^ 2 := by
    have hX : W.a * (W.a + W.c) / (W.a ^ 2 + 4) = W.nt / W.nk := by
      unfold M2Window.nt M2Window.nk
      have : 0 < W.a ^ 2 + 4 := by positivity
      field_simp
    rw [hX]; unfold m2U; field_simp
  obtain ⟨hw, -⟩ := nh_m2wOf_star (u := m2U (W.a * (W.a + W.c) / (W.a ^ 2 + 4))) (v := W.v)
    hT hB ha hc hd hK hQ hu hh hk
  have : nhWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a / (W.a + m2bStar W.a W.c))) W.v =
      fhwU W.nt W.nx W.nk W.v := by
    unfold nhWU; rw [hU, hw]; unfold fhwU; ring_nf
  linarith

/-- The actual outgoing norm is at least `3/4` (`w ≥ g_d(r) ≥ 3/4`). -/
theorem fh_window_w34 (W : M2Window) : 3 / 4 ≤ W.w := by
  have h := W.w_ge
  have hd0 : 0 < W.d := by linarith [W.a_lt_d, W.a_pos]
  have hr0 : 0 < W.r := by linarith [W.a_le_r, W.a_pos]
  have : 3 / 4 ≤ m2g W.d W.r := by
    unfold m2g
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (W.d - W.r)]
  linarith

/-- `Γ` is a concave quadratic: if `2v - eH_d/p ≤ 0` at `w₁ ≤ w₂` (`e = q/W`, `B, p > 0`), then
`Γ(w₂) ≤ Γ(w₁)`. -/
theorem fh_gam_anti {t x k q v L w1 w2 : ℝ} (hB : 0 < k + 2 * t * x + x ^ 2) (hp : 0 < t + x)
    (hW : 0 < 1 + x) (hw : w1 ≤ w2)
    (h1 : 2 * v - q / (1 + x) * fhHd t x k q v L w1 / (t + x) ≤ 0)
    (h2 : 2 * v - q / (1 + x) * fhHd t x k q v L w2 / (t + x) ≤ 0) :
    fhGam t x k q v L w2 ≤ fhGam t x k q v L w1 := by
  unfold fhGam
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hHd : fhHd t x k q v L w2 = fhHd t x k q v L w1 +
      (k + 2 * t * x + x ^ 2) / (t + x) * (q * (k + 2 * t * x + x ^ 2) / (1 + x)) * (w2 - w1) := by
    unfold fhHd; ring
  have key : (4 * (k + 2 * t * x + x ^ 2) ^ 2 * v * w2 - fhHd t x k q v L w2 ^ 2) -
      (4 * (k + 2 * t * x + x ^ 2) ^ 2 * v * w1 - fhHd t x k q v L w1 ^ 2) =
      (w2 - w1) * (k + 2 * t * x + x ^ 2) ^ 2 *
        ((2 * v - q / (1 + x) * fhHd t x k q v L w1 / (t + x)) +
          (2 * v - q / (1 + x) * fhHd t x k q v L w2 / (t + x))) := by
    rw [hHd]; field_simp; ring
  have : (w2 - w1) * (k + 2 * t * x + x ^ 2) ^ 2 *
        ((2 * v - q / (1 + x) * fhHd t x k q v L w1 / (t + x)) +
          (2 * v - q / (1 + x) * fhHd t x k q v L w2 / (t + x))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by have := sub_nonneg.2 hw; positivity) (by linarith)
  linarith

/-- The scalar core of the stationary monotonicity: with `A = Z/p ∈ [15/11, 2]`, `χ ≥ 4/7`,
`A > 2χ`, `v, w ≥ 3/4` and the floor bound `L ≥ 1 + χ - (1 - v)/χ`, the slope
`2v - AL - A²(w - 1) - (1 - χ)` is negative. -/
theorem fh_slope_core {A χ v L w : ℝ} (hA0 : 15 / 11 ≤ A) (hA1 : A ≤ 2) (hχ : 4 / 7 ≤ χ)
    (hAχ : 2 * χ < A) (hv : 3 / 4 ≤ v) (hw : 3 / 4 ≤ w) (hL : 1 + χ - (1 - v) / χ ≤ L) :
    2 * v - A * L - A ^ 2 * (w - 1) - (1 - χ) < 0 := by
  have hχ0 : 0 < χ := by linarith
  have h1 : A * (1 + χ - (1 - v) / χ) ≤ A * L := mul_le_mul_of_nonneg_left hL (by linarith)
  have h2 : -(A ^ 2 * (w - 1)) ≤ A ^ 2 / 4 := by nlinarith [sq_nonneg A]
  -- `χ · (2v - A(1 + χ - (1 - v)/χ) + A²/4 - 1 + χ) = χ f(A, χ) + (v - 3/4)(2χ - A) ≤ χ f(A, χ)`
  have e : χ * (2 * v - A * (1 + χ - (1 - v) / χ) + A ^ 2 / 4 - 1 + χ) =
      χ * (A ^ 2 / 4 - A * (1 + χ) + 1 / 2 + χ) + A / 4 + (v - 3 / 4) * (2 * χ - A) := by
    field_simp; ring
  have hf : χ * (A ^ 2 / 4 - A * (1 + χ) + 1 / 2 + χ) + A / 4 < 0 := by
    -- `f(A, χ) ≤ f(A, 4/7) < 0`
    have hq : (A - 15 / 11) * (A - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hmono : χ * (A ^ 2 / 4 - A * (1 + χ) + 1 / 2 + χ) + A / 4 ≤
        χ * (A ^ 2 / 4 - A * (1 + 4 / 7 - 7 / 16) + 1 / 2 + 4 / 7) := by
      have hpos : 0 ≤ 16 * χ * (A - 1) + 7 * A := by
        have := mul_nonneg hχ0.le (by linarith : (0 : ℝ) ≤ A - 1); nlinarith
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ χ - 4 / 7) hpos]
    have hneg : A ^ 2 / 4 - A * (1 + 4 / 7 - 7 / 16) + 1 / 2 + 4 / 7 < 0 := by nlinarith
    nlinarith
  have h3 : (v - 3 / 4) * (2 * χ - A) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h4 : χ * (2 * v - A * (1 + χ - (1 - v) / χ) + A ^ 2 / 4 - 1 + χ) < 0 := by linarith
  have h5 : 2 * v - A * (1 + χ - (1 - v) / χ) + A ^ 2 / 4 - 1 + χ < 0 := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith

/-- **The stationary monotonicity**: on the small-gap domain, with `t ≤ r ≤ p` (`r = Z - p`),
`χ = pq/W ≥ 4/7` and the incoming floor, `2v - eH_d(w)/p < 0` for every `w ≥ 3/4`. -/
theorem fh_cas_slope {t x k q v w : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 < 2 * t + x - 1)
    (hj4 : 2 * t + x - 1 < 1 / 4) (hk : 1 ≤ k) (hq : 1 < q)
    (hr0 : t ≤ q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x))
    (hr1 : q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ≤ t + x)
    (hχ : 4 / 7 ≤ (t + x) * q / (1 + x)) (hv : 3 / 4 ≤ v)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) (hw : 3 / 4 ≤ w) :
    2 * v - q / (1 + x) * fhHd t x k q v (Real.log q) w / (t + x) < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hp : 0 < t + x := by linarith
  have hq0 : 0 < q := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  set A := q * (k + 2 * t * x + x ^ 2) / ((1 + x) * (t + x)) with hAdef
  set χ := (t + x) * q / (1 + x) with hχdef
  set L' := Real.log q + ((1 + x) * v - (1 - t) + (t + x) ^ 2 / (1 + x)) / (t + x) with hL'
  have hid : q / (1 + x) * fhHd t x k q v (Real.log q) w / (t + x) =
      A * L' + A ^ 2 * (w - 1) + (1 - χ) := by
    rw [hAdef, hχdef, hL']; unfold fhHd fhSd; field_simp; ring
  rw [hid]
  -- the floor bound on `L'`
  have hL : 1 + χ - (1 - v) / χ ≤ L' := by
    rw [m2F_of_ne hq.ne'] at hF
    have hq1 : 0 < q - 1 := by linarith
    have hη : 0 < (t + x) / (1 + x) := by positivity
    have hlog : (q - 1) * (1 - v + ((t + x) / (1 + x)) ^ 2 * q) / ((t + x) / (1 + x) * q) ≤ Real.log q := by
      rw [div_le_iff₀ (by positivity)]
      have : (t + x) / (1 + x) * q * Real.log q / (q - 1) ≥ 1 - v + ((t + x) / (1 + x)) ^ 2 * q := by linarith
      rw [ge_iff_le, le_div_iff₀ hq1] at this
      linarith
    have e2 : (q - 1) * (1 - v + ((t + x) / (1 + x)) ^ 2 * q) / ((t + x) / (1 + x) * q) +
        ((1 + x) * v - (1 - t) + (t + x) ^ 2 / (1 + x)) / (t + x) = 1 + χ - (1 - v) / χ := by
      rw [hχdef]; field_simp; ring
    rw [hL', ← e2]; linarith
  -- the ranges of `A` and `χ`
  have hpj : t + x < 5 / 4 - t := by linarith
  have hA0 : 15 / 11 ≤ A := by
    have e : A = 1 + (q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x)) / (t + x) := by
      rw [hAdef]; field_simp; ring
    rw [e]
    have : 4 / 11 ≤ t / (t + x) := by rw [le_div_iff₀ hp]; linarith
    have : t / (t + x) ≤ (q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x)) / (t + x) :=
      div_le_div_of_nonneg_right hr0 hp.le
    linarith
  have hA1 : A ≤ 2 := by
    have e : A = 1 + (q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x)) / (t + x) := by
      rw [hAdef]; field_simp; ring
    rw [e]
    have : (q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x)) / (t + x) ≤ 1 := by
      rw [div_le_one hp]; exact hr1
    linarith
  have hAχ : 2 * χ < A := by
    have hs : 2 * (t + x) ^ 2 < k + 2 * t * x + x ^ 2 := by nlinarith
    have e : A - 2 * χ = q * (k + 2 * t * x + x ^ 2 - 2 * (t + x) ^ 2) / ((1 + x) * (t + x)) := by
      rw [hAdef, hχdef]; field_simp
    have : 0 < q * (k + 2 * t * x + x ^ 2 - 2 * (t + x) ^ 2) / ((1 + x) * (t + x)) := by
      apply div_pos (mul_pos hq0 (by linarith)) (by positivity)
    linarith
  have := fh_slope_core hA0 hA1 hχ hAχ hv hw hL
  linarith

end SmoothedOctagon

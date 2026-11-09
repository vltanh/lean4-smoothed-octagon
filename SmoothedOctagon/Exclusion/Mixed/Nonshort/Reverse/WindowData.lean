module

public import SmoothedOctagon.Exclusion.Mixed.Comparison
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.Residual

/-!
# Case M2, reverse successor: the normalized data of an actual window

The normalized coordinates of an actual smaller-nonshort window `W : M2Window`: `t = a/T`,
`x = (d - a)/T`, `k = K/T²`, `q = WZ/Q` (`T = a + c`, `K = a² + 4`), and the necessary conditions
they satisfy without any successor assumption.

## Main API

* `M2Window.nt`, `nx`, `nk`, `nq`.
* `nsr_link_N`: `N(t, x, k, q, v, log q)·T = tBqW·G(b*)`, so the boundary comparison
  `G(b*) < 0` (`m2_comparison`) gives `nsr_window_N_neg`: `N < 0`.
-/

@[expose] public section

namespace SmoothedOctagon

namespace M2Window

variable (W : M2Window)

/-- `t = a/(a + c)`. -/
noncomputable def nt : ℝ := W.a / (W.a + W.c)

/-- `x = (d - a)/(a + c)`. -/
noncomputable def nx : ℝ := (W.d - W.a) / (W.a + W.c)

/-- `k = (a² + 4)/(a + c)²`. -/
noncomputable def nk : ℝ := (W.a ^ 2 + 4) / (W.a + W.c) ^ 2

/-- `q = (c + d)(d + r)/(d² + 4)`. -/
noncomputable def nq : ℝ := (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4)

end M2Window

/-- The normalized residual `R`: with `W = 1 + x`,
`p = t + x`, `Y = x(x + 2)`, `B = k + 2tx + x²`, `Z = qB/W`,
`R = (1 - t) + Z - p²/W - p²/Z + p³/B - pL - Wv - Z w_U + p(H₀ + 2vY)/B`. -/
noncomputable def nsrR (t x k q v L : ℝ) : ℝ :=
  (1 - t) + q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ^ 2 / (1 + x)
    - (t + x) ^ 2 / (q * (k + 2 * t * x + x ^ 2) / (1 + x))
    + (t + x) ^ 3 / (k + 2 * t * x + x ^ 2) - (t + x) * L - (1 + x) * v
    - q * (k + 2 * t * x + x ^ 2) / (1 + x) *
      ((k ^ 2 - k * t + t ^ 2 + (k / t * (v - 1 + t ^ 2) + t * (2 - t)) * (x * (x + 2))
        + v * (x * (x + 2)) ^ 2) / (k + 2 * t * x + x ^ 2) ^ 2)
    + (t + x) * ((k / t * (v - 1 + t ^ 2) + t * (2 - t)) + 2 * v * (x * (x + 2)))
      / (k + 2 * t * x + x ^ 2)

/-- `N = tBqW·R`. -/
theorem nsrN_eq_R {t x k q v L : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) (hq : 0 < q) :
    nsrN t x k q v L = t * (k + 2 * t * x + x ^ 2) * q * (1 + x) * nsrR t x k q v L := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  unfold nsrN nsrR
  field_simp
  ring

/-- The central diagonal at the boundary with the upper incident norm:
`h(U*, b*) = (T²/16) H₀`, `H₀ = (k/t)(v - 1 + t²) + t(2 - t)`. -/
theorem nsr_m2h_star {a c T t k v : ℝ} (hT : 0 < T) (ht : 0 < t) (hk : 0 < k) (ha : a = t * T)
    (hc : c = (1 - t) * T) (hK : a ^ 2 + 4 = k * T ^ 2) :
    m2h a (m2bStar a c) c (m2U (a * (a + c) / (a ^ 2 + 4))) v =
      T ^ 2 / 16 * (k / t * (v - 1 + t ^ 2) + t * (2 - t)) := by
  have hac : a + c = T := by rw [ha, hc]; ring
  have hb : m2bStar a c = k * T - a := by
    unfold m2bStar; rw [hac, hK]; field_simp
  have hlog : Real.log ((m2bStar a c + a) * (a + c) / (a ^ 2 + 4)) = 0 := by
    rw [show (m2bStar a c + a) * (a + c) / (a ^ 2 + 4) = 1 by
      rw [hb, hac, hK]; field_simp; ring]
    exact Real.log_one
  unfold m2h
  unfold m2Stat
  rw [hlog, hb, hac, hK]
  subst ha hc
  have h1 : t * T + (k * T - t * T) = k * T := by ring
  have h2 : k * T - t * T + t * T = k * T := by ring
  rw [h1, h2]
  unfold m2U
  field_simp
  ring

/-- The transported norm and the diagonal at `d`, at the boundary with the upper incident norm. -/
theorem nsr_m2wOf_star {a c d T t x k u v h H : ℝ} (hT : 0 < T) (_hB : 0 < k + 2 * t * x + x ^ 2)
    (ha : a = t * T) (hc : c = (1 - t) * T) (hd : d = (t + x) * T) (hK : a ^ 2 + 4 = k * T ^ 2)
    (hQ : d ^ 2 + 4 = T ^ 2 * (k + 2 * t * x + x ^ 2)) (hu : u * k ^ 2 = k ^ 2 - k * t + t ^ 2)
    (hh : h = T ^ 2 / 16 * H) (hk : 0 < k) :
    m2wOf a c d u v h = (k ^ 2 - k * t + t ^ 2 + H * (x * (x + 2)) + v * (x * (x + 2)) ^ 2) /
        (k + 2 * t * x + x ^ 2) ^ 2 ∧
      m2hd a c d v h = T ^ 2 / 16 * (H + 2 * v * (x * (x + 2))) := by
  have hY : m2Y a c d = T ^ 2 * (x * (x + 2)) := by
    unfold m2Y; rw [ha, hc, hd]; ring
  constructor
  · unfold m2wOf
    rw [hY, hK, hQ, hh]
    have hu' : u = (k ^ 2 - k * t + t ^ 2) / k ^ 2 := by field_simp; linarith
    rw [hu']
    field_simp
  · unfold m2hd
    rw [hY, hh]
    ring

/-- The cost derivative at `d` in normalized form. -/
theorem nsr_m2Stat_d {c d r T t x k q L : ℝ} (hT : 0 < T) (hx : 0 < x)
    (_hB : 0 < k + 2 * t * x + x ^ 2) (hq : 0 < q) (hc : c = (1 - t) * T) (hd : d = (t + x) * T)
    (hQ : d ^ 2 + 4 = T ^ 2 * (k + 2 * t * x + x ^ 2))
    (hZ : d + r = q * (k + 2 * t * x + x ^ 2) / (1 + x) * T)
    (hL : Real.log ((c + d) * (d + r) / (d ^ 2 + 4)) = L) :
    m2Stat c d r = T * ((1 - t) + q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ^ 2 / (1 + x)
      - (t + x) ^ 2 / (q * (k + 2 * t * x + x ^ 2) / (1 + x)) + (t + x) ^ 3 / (k + 2 * t * x + x ^ 2)
      - (t + x) * L) := by
  have hr : r = q * (k + 2 * t * x + x ^ 2) / (1 + x) * T - d := by linarith
  unfold m2Stat
  rw [hL, hQ, hZ]
  have hcd : c + d = (1 + x) * T := by rw [hc, hd]; ring
  rw [hcd, hr, hd]
  have hW : 0 < 1 + x := by linarith
  field_simp
  ring

/-- The normalized root identity: `G(b*) = R_d(U*; b*) = T·R`. -/
theorem nsr_root_star {a c d r v T t x k q : ℝ} (hT : 0 < T) (ht : 0 < t) (hx : 0 < x)
    (hk : 0 < k) (hq : 0 < q) (ha : a = t * T) (hc : c = (1 - t) * T) (hd : d = (t + x) * T)
    (hK : a ^ 2 + 4 = k * T ^ 2) (hQ : d ^ 2 + 4 = T ^ 2 * (k + 2 * t * x + x ^ 2))
    (hZ : d + r = q * (k + 2 * t * x + x ^ 2) / (1 + x) * T)
    (hqd : (c + d) * (d + r) / (d ^ 2 + 4) = q) :
    m2RootAt a (m2bStar a c) c d r v (m2U (a * (a + c) / (a ^ 2 + 4))) =
      T * nsrR t x k q v (Real.log q) := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hh := nsr_m2h_star (v := v) hT ht hk ha hc hK
  have hu : m2U (a * (a + c) / (a ^ 2 + 4)) * k ^ 2 = k ^ 2 - k * t + t ^ 2 := by
    have hac : a + c = T := by rw [ha, hc]; ring
    unfold m2U; rw [hac, hK, ha]; field_simp
  obtain ⟨hw, hhd⟩ := nsr_m2wOf_star (v := v) hT hB ha hc hd hK hQ hu hh hk
  have hS := nsr_m2Stat_d (r := r) hT hx hB hq hc hd hQ hZ (by rw [hqd])
  unfold m2RootAt m2Root
  rw [hw, hhd, hS, hQ, hZ]
  have hcd : c + d = (1 + x) * T := by rw [hc, hd]; ring
  rw [hcd, hd]
  unfold nsrR
  have hW : 0 < 1 + x := by linarith
  field_simp

/-- **The link with the boundary comparison**: `N·T = tBqW·G(b*)`. -/
theorem nsr_link_N (W : M2Window) :
    nsrN W.nt W.nx W.nk W.nq W.v (Real.log W.nq) * (W.a + W.c) =
      W.nt * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) * W.nq * (1 + W.nx) *
        m2RootAt W.a W.bStar W.c W.d W.r W.v W.ceilStar := by
  have ha0 := W.a_pos
  have hc0 : 0 < W.c := by linarith [W.a_lt_c]
  have hd0 : 0 < W.d := by linarith [W.a_lt_d]
  have hr0 : 0 < W.r := by linarith [W.a_le_r]
  have hT : 0 < W.a + W.c := by positivity
  have ht : 0 < W.nt := by unfold M2Window.nt; positivity
  have hx : 0 < W.nx := by unfold M2Window.nx; apply div_pos (by linarith [W.a_lt_d]) hT
  have hk : 0 < W.nk := by unfold M2Window.nk; positivity
  have hq : 0 < W.nq := by unfold M2Window.nq; positivity
  have ha : W.a = W.nt * (W.a + W.c) := by unfold M2Window.nt; field_simp
  have hc : W.c = (1 - W.nt) * (W.a + W.c) := by unfold M2Window.nt; field_simp; ring
  have hd : W.d = (W.nt + W.nx) * (W.a + W.c) := by
    unfold M2Window.nt M2Window.nx; field_simp; ring
  have hK : W.a ^ 2 + 4 = W.nk * (W.a + W.c) ^ 2 := by unfold M2Window.nk; field_simp
  have hQ : W.d ^ 2 + 4 = (W.a + W.c) ^ 2 * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) := by
    have : W.nk * (W.a + W.c) ^ 2 = W.a ^ 2 + 4 := hK.symm
    have e1 : W.d ^ 2 = (W.nt + W.nx) ^ 2 * (W.a + W.c) ^ 2 := by rw [← mul_pow, ← hd]
    have e2 : W.a ^ 2 = W.nt ^ 2 * (W.a + W.c) ^ 2 := by rw [← mul_pow, ← ha]
    nlinarith
  have hcd : W.c + W.d = (1 + W.nx) * (W.a + W.c) := by linear_combination hc + hd
  have hZ : W.d + W.r = W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) / (1 + W.nx) * (W.a + W.c) := by
    have hB : 0 < W.nk + 2 * W.nt * W.nx + W.nx ^ 2 := by positivity
    have hq' : W.nq * (W.d ^ 2 + 4) = (W.c + W.d) * (W.d + W.r) := by
      unfold M2Window.nq; field_simp
    rw [hQ, hcd] at hq'
    have hW : 0 < 1 + W.nx := by linarith
    field_simp
    nlinarith [hq']
  have hroot := nsr_root_star (v := W.v) hT ht hx hk hq ha hc hd hK hQ hZ rfl
  unfold M2Window.bStar M2Window.ceilStar
  rw [hroot, nsrN_eq_R ht hx hk hq]
  ring

/-- **The actual normalized residual is negative** (from `G(b*) < 0`, `m2_comparison`). -/
theorem nsr_window_N_neg (W : M2Window) : nsrN W.nt W.nx W.nk W.nq W.v (Real.log W.nq) < 0 := by
  have hG := (m2_comparison W).1
  have h := nsr_link_N W
  have hc0 : 0 < W.c := by linarith [W.a_lt_c, W.a_pos]
  have hT : 0 < W.a + W.c := by linarith [W.a_pos]
  have ht : 0 < W.nt := by unfold M2Window.nt; have := W.a_pos; positivity
  have hx : 0 < W.nx := by unfold M2Window.nx; apply div_pos (by linarith [W.a_lt_d]) hT
  have hk : 0 < W.nk := by unfold M2Window.nk; positivity
  have hq : 0 < W.nq := by
    unfold M2Window.nq
    have : 0 < W.d := by linarith [W.a_lt_d, W.a_pos]
    have : 0 < W.r := by linarith [W.a_le_r, W.a_pos]
    positivity
  have hpos : 0 < W.nt * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) * W.nq * (1 + W.nx) := by positivity
  have : nsrN W.nt W.nx W.nk W.nq W.v (Real.log W.nq) * (W.a + W.c) < 0 := by
    rw [h]; exact mul_neg_of_pos_of_neg hpos hG
  by_contra hcon
  push Not at hcon
  have := mul_nonneg hcon hT.le
  linarith

/-- **The normalized necessary conditions of an actual window** (no successor assumption):
`0 < t < 1/2`, `x > 0`, `k > 1`, `1 < q < W/p`, `v = Sec(t, 1 - t, t + x)`, `v ≤ U(t)`,
`v ≥ g_c(d) = 1 - (1 - t)p/W²`, `v ≥ F_{p/W}(q)`, and `a²(k - t²) = 4t²`. -/
theorem nsr_window_basic (W : M2Window) :
    0 < W.nt ∧ W.nt < 1 / 2 ∧ 0 < W.nx ∧ 1 < W.nk ∧ 1 < W.nq ∧
      W.nq < (1 + W.nx) / (W.nt + W.nx) ∧ W.v = nsrSecN W.nt W.nx ∧
      W.v ≤ 1 - W.nt + W.nt ^ 2 ∧
      1 - (1 - W.nt) * (W.nt + W.nx) / (1 + W.nx) ^ 2 ≤ W.v ∧
      m2F ((W.nt + W.nx) / (1 + W.nx)) W.nq ≤ W.v ∧
      W.a ^ 2 * (W.nk - W.nt ^ 2) = 4 * W.nt ^ 2 := by
  have ha0 := W.a_pos
  have hc0 : 0 < W.c := by linarith [W.a_lt_c]
  have hd0 : 0 < W.d := by linarith [W.a_lt_d]
  have hr0 : 0 < W.r := by linarith [W.a_le_r]
  have hT : 0 < W.a + W.c := by positivity
  have hda : 0 < W.d - W.a := by linarith [W.a_lt_d]
  have ht : 0 < W.nt := by unfold M2Window.nt; positivity
  have hx : 0 < W.nx := by unfold M2Window.nx; positivity
  have h1x : 1 + W.nx = (W.c + W.d) / (W.a + W.c) := by
    unfold M2Window.nx; field_simp; ring
  have htx : W.nt + W.nx = W.d / (W.a + W.c) := by
    unfold M2Window.nt M2Window.nx; field_simp; ring
  have h1t : 1 - W.nt = W.c / (W.a + W.c) := by
    unfold M2Window.nt; field_simp; ring
  refine ⟨ht, ?_, hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold M2Window.nt; rw [div_lt_iff₀ hT]; linarith [W.a_lt_c]
  · unfold M2Window.nk; rw [lt_div_iff₀ (by positivity)]
    have := W.c_le_b; have := W.central; nlinarith
  · unfold M2Window.nq; rw [lt_div_iff₀ (by positivity)]; linarith [W.factor_d]
  · rw [h1x, htx, div_div_div_cancel_right₀ hT.ne']
    unfold M2Window.nq; rw [div_lt_div_iff₀ (by positivity) hd0]
    have := W.star_dr
    have : 0 < W.c + W.d := by positivity
    nlinarith
  · rw [W.v_eq, m2Sec_of_ne (ne_of_lt W.a_lt_d)]
    unfold nsrSecN
    rw [h1x, h1t, show (W.d + W.c) / (W.a + W.c) = (W.c + W.d) / (W.a + W.c) by ring]
    unfold M2Window.nx
    field_simp
    ring
  · have h := W.v_le
    rw [m2g_eq_m2U hT] at h
    unfold m2U at h; unfold M2Window.nt; exact h
  · have h := W.v_ge
    have hcd : 0 < W.c + W.d := by positivity
    unfold m2g at h
    rw [h1t, htx, h1x]
    have e : (W.c ^ 2 + W.c * W.d + W.d ^ 2) / (W.c + W.d) ^ 2 =
        1 - W.c / (W.a + W.c) * (W.d / (W.a + W.c)) / ((W.c + W.d) / (W.a + W.c)) ^ 2 := by
      field_simp; ring
    linarith
  · have h := W.v_floor
    rw [htx, h1x, div_div_div_cancel_right₀ hT.ne']
    exact h
  · unfold M2Window.nk M2Window.nt
    field_simp
    ring

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Basic
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Swap
public import SmoothedOctagon.Exclusion.Mixed.Hand.Prereq
public import SmoothedOctagon.Exclusion.Mixed.Hand.Low
public import SmoothedOctagon.Exclusion.Mixed.Hand.Order

/-!
# Case M2, forward successor by hand: the necessary conditions of an actual window

For an actual window `W` with a forward successor, in the normalized coordinates `t, x, k, q`
(`M2Window.nt`, …):

* `fh_window_tStar`: the boundary next norm `𝒯_* ≥ 3/4` (`𝒯` decreases along the root set and
  `w* < w`);
* `fh_window_TP`: `4qW² C_*(3/4 - 𝒯_*) ≤ 0` in cleared form, through the exact transport
  identity `𝒯_* = 𝒯_U + e(Je² - 1)N/(tW²DE²)`;
* `fh_window_comb`: **the combined residual is negative**, `fhComb α M < 0` for `α > 0`, `M ≥ 0`;
* `fh_window_order`: `k < 2t + x` (the common order, from `nh_reverse_core`);
* `fh_window_quarter`: `t > 1/4` (from `nh_low_unit`);
* `fh_window_T`: `t < T(x)`, and `fh_window_x_lt_one`: `x < 1`, `fh_window_four`: `4t + x < 2`;
* `fh_window_swap`: `q < W/(4t + 2x - 1)` (the quantitative swap bound).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The normalized coordinates of an actual window. -/
theorem fh_window_coords (W : M2Window) :
    0 < W.a + W.c ∧ 0 < W.nt ∧ 0 < W.nx ∧ 0 < W.nk ∧ 0 < W.nq ∧
      W.a = W.nt * (W.a + W.c) ∧ W.c = (1 - W.nt) * (W.a + W.c) ∧
      W.d = (W.nt + W.nx) * (W.a + W.c) ∧ W.a ^ 2 + 4 = W.nk * (W.a + W.c) ^ 2 ∧
      W.d ^ 2 + 4 = (W.a + W.c) ^ 2 * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) ∧
      W.d + W.r = W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) / (1 + W.nx) * (W.a + W.c) ∧
      (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) = W.nq := by
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
  exact ⟨hT, ht, hx, hk, hq, ha, hc, hd, hK, hQ, hZ, rfl⟩

/-- **The boundary next norm is at least `3/4`**: on the root set `𝒯` is affine in `w` with negative
slope, `w* < w`, and the actual next norm is at least `g_r(s) ≥ 3/4`. -/
theorem fh_window_tStar (W : M2Window) (hF : W.ForwardNext) : 3 / 4 ≤ W.tStar := by
  obtain ⟨-, hroot, -, hlt⟩ := m2_comparison W
  obtain ⟨s, has, -, -, hts, -, -⟩ := hF
  have ha := W.a_pos
  have hd0 : 0 < W.d := by linarith [W.a_lt_d]
  have hr0 : 0 < W.r := by linarith [W.a_le_r]
  have hs0 : 0 < s := by linarith
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  have hKr : 0 < W.r ^ 2 + 4 := by positivity
  have hZ : 0 < W.d + W.r := by linarith
  set μ : ℝ := (W.d ^ 2 + 4) * (W.d + W.r) / (16 * W.d) with hμ
  set L : ℝ := (W.d ^ 2 + 4) * ((W.c + W.d) * W.v - m2Stat W.c W.d W.r) / (16 * W.d) with hL
  have hdiag : ∀ u h, m2Root W.a W.c W.d W.r u W.v h = 0 →
      m2hd W.a W.c W.d W.v h = L + μ * m2wOf W.a W.c W.d u W.v h := by
    intro u h e
    unfold m2Root at e
    rw [hL, hμ]
    field_simp
    field_simp at e
    linarith
  have hd_act := hdiag W.u W.h W.root
  rw [← W.w_eq] at hd_act
  have hd_star := hdiag W.uStar W.hStar hroot
  have hwS : m2wOf W.a W.c W.d W.uStar W.v W.hStar = W.wStar := rfl
  rw [hwS] at hd_star
  set B : ℝ := (W.d + W.r) ^ 3 * (4 - W.d * W.r) / (W.d * (W.r ^ 2 + 4) ^ 2) with hBdef
  have hBpos : 0 < B := by
    have : 0 < 4 - W.d * W.r := by linarith [W.star_dr]
    positivity
  set α0 : ℝ := ((W.d ^ 2 + 4) ^ 2 * W.v - 16 * L * (W.d + W.r) ^ 2) / (W.r ^ 2 + 4) ^ 2 with hα0
  have hnext : ∀ u h, m2hd W.a W.c W.d W.v h = L + μ * m2wOf W.a W.c W.d u W.v h →
      m2Next W.a W.c W.d W.r u W.v h = α0 - B * m2wOf W.a W.c W.d u W.v h := by
    intro u h e
    unfold m2Next
    rw [e, hα0, hBdef, hμ]
    field_simp
    ring
  have ht_act : W.t = α0 - B * W.w := by
    have := hnext W.u W.h (by rw [← W.w_eq]; exact hd_act)
    rw [← W.w_eq] at this; exact this
  have ht_star : W.tStar = α0 - B * W.wStar := by
    have := hnext W.uStar W.hStar (by rw [hwS]; exact hd_star)
    rw [hwS] at this; exact this
  have hg34 : 3 / 4 ≤ m2g W.r s := by
    unfold m2g
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (W.r - s)]
  have : 0 < B * (W.w - W.wStar) := mul_pos hBpos (by linarith)
  rw [ht_star]; rw [ht_act] at hts; nlinarith

/-- `E > 0` and `D > 0` on the actual normalized data (`q ≥ 1`, `k > t²`). -/
theorem fh_E_D_pos {t x k q : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hk : t ^ 2 < k)
    (hq : 1 ≤ q) : 0 < fhE t x k q ∧ 0 < fhD t x q := by
  have hW : 0 < 1 + x := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by nlinarith
  constructor
  · have e : fhE t x k q = ((q / (1 + x) * (k + 2 * t * x + x ^ 2) - (t + x)) ^ 2 + (k - t ^ 2)) /
        (k + 2 * t * x + x ^ 2) := by
      rw [eq_div_iff hB.ne']; unfold fhE; field_simp; ring
    rw [e]
    apply div_pos _ hB
    nlinarith [sq_nonneg (q / (1 + x) * (k + 2 * t * x + x ^ 2) - (t + x))]
  · unfold fhD
    have h1 : 1 / (1 + x) ≤ q / (1 + x) := div_le_div_of_nonneg_right hq hW.le
    have hJ : 0 < t + x * (x + 2) := by positivity
    have h2 : 1 / (1 + x) * (t + x * (x + 2)) ≤ q / (1 + x) * (t + x * (x + 2)) :=
      mul_le_mul_of_nonneg_right h1 hJ.le
    have h3 : 1 / (1 + x) * (t + x * (x + 2)) - (t + x) = x * (1 - t) / (1 + x) := by
      field_simp; ring
    have h4 : 0 < x * (1 - t) / (1 + x) := by
      apply div_pos (mul_pos hx (by linarith)) hW
    linarith

/-- **The cleared next-norm condition**:
`4qW² C_*(3/4 - 𝒯_*) = fhTP + 4q(W² - Jq²)N ≤ 0`. -/
theorem fh_window_TP (W : M2Window) (hF : W.ForwardNext) :
    fhTP W.nt W.nx W.nk W.nq W.v +
      4 * W.nq * ((1 + W.nx) ^ 2 - (W.nt + W.nx * (W.nx + 2)) * W.nq ^ 2) *
        nhN W.nt W.nx W.nk W.nq W.v (Real.log W.nq) ≤ 0 := by
  obtain ⟨hT, ht, hx, hk, hq, ha, hc, hd, hK, hQ, hZ, hqd⟩ := fh_window_coords W
  obtain ⟨-, ht2, -, hk1, hq1, -⟩ := nh_window_basic W
  have hts := fh_window_tStar W hF
  obtain ⟨-, hroot, -, -⟩ := m2_comparison W
  set t := W.nt
  set x := W.nx
  set k := W.nk
  set q := W.nq
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by linarith
  have hkt : t ^ 2 < k := by nlinarith
  obtain ⟨hE, hD⟩ := fh_E_D_pos ht (by linarith) hx hkt hq1.le
  -- the boundary root and next norm in normalized form
  have hR := fh_root_u (u := W.uStar) (v := W.v) hT ht hx hk hq ha hc hd hK hQ hZ hqd
  have hRs : fhRn t x k q W.v (Real.log q) W.uStar = 0 := by
    have h0 : m2RootAt W.a (m2bStar W.a W.c) W.c W.d W.r W.v W.uStar = 0 := hroot
    rw [hR] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact h
  have hTs : W.tStar = fhTn t x k q W.v W.uStar :=
    fh_next_u (u := W.uStar) (v := W.v) hT ht hx hk hq ha hc hd hK hQ hZ
  set U0 := m2U (t / k)
  have hRsub := fh_Rn_sub (v := W.v) (L := Real.log q) (u := W.uStar) (u' := U0) ht hx hk hq
  rw [hRs, fh_Rn_U ht hk] at hRsub
  have hTsub := fh_Tn_sub (q := q) (v := W.v) (u := W.uStar) (u' := U0) ht hx hk
  have hN := nhN_eq_R (v := W.v) (L := Real.log q) ht hx hk hq
  have hTP := fh_TP_eq (v := W.v) ht hx hk hq hE.ne'
  -- `u* - U = nhR·tB/(k²D)`
  have hdu : W.uStar - U0 = nhR t x k q W.v (Real.log q) * (t * (k + 2 * t * x + x ^ 2)) /
      (k ^ 2 * fhD t x q) := by
    have h1 : (W.uStar - U0) * (k ^ 2 * fhD t x q / (t * (k + 2 * t * x + x ^ 2))) =
        nhR t x k q W.v (Real.log q) := by linear_combination hRsub
    rw [← h1]
    field_simp
  have key : fhTP t x k q W.v + 4 * q * ((1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) *
      nhN t x k q W.v (Real.log q) =
      4 * q * (1 + x) ^ 2 * (t * (1 + x) ^ 2 * fhD t x q * fhE t x k q ^ 2 / (q / (1 + x))) *
        (3 / 4 - W.tStar) := by
    have hT0 : fhTn t x k q W.v U0 = W.tStar - (W.uStar - U0) *
        ((q / (1 + x)) ^ 2 * k ^ 2 * ((t + x * (x + 2)) * (q / (1 + x)) ^ 2 - 1) /
          (t * fhE t x k q ^ 2)) := by rw [hTs]; linarith
    rw [hTP, hT0, hN, hdu]
    field_simp
    ring
  rw [key]
  have hC : 0 ≤ 4 * q * (1 + x) ^ 2 * (t * (1 + x) ^ 2 * fhD t x q * fhE t x k q ^ 2 / (q / (1 + x))) := by
    positivity
  nlinarith

/-- **The combined residual is negative at an actual forward window**: for `α > 0`, `M ≥ 0`,
`αN + C_*(3/4 - 𝒯_*) + M(F_{p/W}(q) - v) < 0`, in the cleared form `fhComb`. -/
theorem fh_window_comb (W : M2Window) (hF : W.ForwardNext) {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    fhComb α M W.nt W.nx W.nk W.nq W.v (Real.log W.nq)
      (m2F ((W.nt + W.nx) / (1 + W.nx)) W.nq) < 0 := by
  obtain ⟨-, -, hx, -, hq, -⟩ := fh_window_coords W
  obtain ⟨-, -, -, -, -, -, -, -, -, hFl, -⟩ := nh_window_basic W
  have hTP := fh_window_TP W hF
  have hN := nh_window_N_neg W
  unfold fhComb
  have h1 : 4 * W.nq * (α * (1 + W.nx) ^ 2) * nhN W.nt W.nx W.nk W.nq W.v (Real.log W.nq) < 0 := by
    apply mul_neg_of_pos_of_neg _ hN
    positivity
  have h2 : 4 * W.nq * (1 + W.nx) ^ 2 * M * (m2F ((W.nt + W.nx) / (1 + W.nx)) W.nq - W.v) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos _ (by linarith)
    positivity
  nlinarith

/-- **The common order** `k < 2t + x`: otherwise the scalar reverse exclusion gives `N > 0`. -/
theorem fh_window_order (W : M2Window) : W.nk < 2 * W.nt + W.nx := by
  obtain ⟨ht, -, hx, hk1, hq, hqW, hv, hvU, -, hF, -⟩ := nh_window_basic W
  by_contra h
  push Not at h
  have hN := nh_reverse_core ht (nh_high_t W) hx hk1.le h (nh_scale_k W).le (nh_centre_gap_k W)
    (nh_window_dur_x W) hq hqW hv hvU hF
  linarith [nh_window_N_neg W]

/-- The derivative floor `t < T(x)`: `3(x + 2)³t < -2x³ - x² + 10x + 12`. -/
theorem fh_window_T (W : M2Window) :
    3 * (W.nx + 2) ^ 3 * W.nt < -2 * W.nx ^ 3 - W.nx ^ 2 + 10 * W.nx + 12 := by
  obtain ⟨-, ht2, hx, -, -, -, hv, -, hg, -, -⟩ := nh_window_basic W
  exact nh_t_lt_T (by linarith) hx hv hg

/-- **The common ratio exceeds one quarter**: for `t ≤ 1/4` the unit-shape sign `nh_low_unit`
gives `N₁ > 0`, and `N` increases with the shape, contradicting `N < 0`. -/
theorem fh_window_quarter (W : M2Window) : 1 / 4 < W.nt := by
  obtain ⟨ht, -, hx, hk1, hq, -, hv, hvU, -, hF, -⟩ := nh_window_basic W
  have ho := fh_window_order W
  by_contra h
  push Not at h
  have hT := fh_window_T W
  have hN1 := nh_low_unit ht h (by linarith) (by linarith [nh_window_dur_x W]) (by linarith) hT.le
    hq hv hF
  have hL : Real.log W.nq < W.nq - 1 := Real.log_lt_sub_one_of_pos (by linarith) hq.ne'
  have := nhN_mono_k (k := 1) (k' := W.nk) ht (by linarith) hx hq.le hvU hL hk1.le
  linarith [nh_window_N_neg W]

/-- `x < 1`, from `t < T(x)`, `t > 1/4` and `T(1) = 19/81`. -/
theorem fh_window_x_lt_one (W : M2Window) : W.nx < 1 := by
  have hT := fh_window_T W
  have ht := fh_window_quarter W
  obtain ⟨-, -, hx, -⟩ := nh_window_basic W
  by_contra h
  push Not at h
  have := nh_T_anti (xa := 1) (by norm_num) h (by linarith) hT.le
  norm_num at this
  linarith

/-- `4t + x < 2`: `T(x) < (2 - x)/4` on `(0, 1]`. -/
theorem fh_window_four (W : M2Window) : 4 * W.nt + W.nx < 2 := by
  have hT := fh_window_T W
  have hx1 := fh_window_x_lt_one W
  obtain ⟨-, -, hx, -⟩ := nh_window_basic W
  have hX : 0 < 3 * (W.nx + 2) ^ 3 := by positivity
  have e : (2 - W.nx) / 4 * (3 * (W.nx + 2) ^ 3) - (-2 * W.nx ^ 3 - W.nx ^ 2 + 10 * W.nx + 12) =
      W.nx / 4 * (8 + 4 * W.nx - 4 * W.nx ^ 2 - 3 * W.nx ^ 3) := by ring
  have hp : 0 < W.nx / 4 * (8 + 4 * W.nx - 4 * W.nx ^ 2 - 3 * W.nx ^ 3) := by
    apply mul_pos (by linarith)
    nlinarith
  have : 3 * (W.nx + 2) ^ 3 * W.nt < (2 - W.nx) / 4 * (3 * (W.nx + 2) ^ 3) := by linarith
  have : W.nt < (2 - W.nx) / 4 := by
    by_contra h; push Not at h; nlinarith
  linarith

/-- **The quantitative swap bound**: `q < W/(4t + 2x - 1)`, from the stronger secant comparison
`fh_sec_swap_q` and the incoming floor. -/
theorem fh_window_swap (W : M2Window) : W.nq < (1 + W.nx) / (4 * W.nt + 2 * W.nx - 1) := by
  obtain ⟨ht, ht2, hx, hk1, hq, hqW, hv, -, -, hF, -⟩ := nh_window_basic W
  have ho := fh_window_order W
  have h4 := fh_window_four W
  have hq4 := fh_window_quarter W
  set t := W.nt
  set x := W.nx
  set q := W.nq
  have hq0 : 0 < q := by linarith
  -- `h = 1 - 2t`, `j = 2t + x - 1`
  have hj : 0 < 2 * t + x - 1 := by linarith
  have hjh : 2 * t + x - 1 < 1 - 2 * t := by linarith
  have hsw := fh_sec_swap_q (h := 1 - 2 * t) (j := 2 * t + x - 1) (by linarith) hj hjh
  rw [show (1 - (1 - 2 * t)) / 2 = t by ring, show (1 + (1 - 2 * t)) / 2 = 1 - t by ring,
    show 1 - t + (2 * t + x - 1) = t + x by ring,
    show t + (2 * t + x - 1) = 3 * t + x - 1 by ring] at hsw
  have hFs : m2F ((t + x) / (1 + x)) q = m2Sec ((1 + x) / q - (t + x)) (t + x) (1 - t) := by
    have := nh_m2F_eq_sec (P := t + x) (C := 1 - t) (q := q) (by linarith) (by linarith) hq
    rwa [show t + x + (1 - t) = 1 + x by ring] at this
  rw [hFs, hv, nh_secN_eq hx] at hF
  have hA0 : 0 < (1 + x) / q - (t + x) := by
    rw [sub_pos, lt_div_iff₀ hq0]
    rw [lt_div_iff₀ (by linarith)] at hqW
    linarith
  -- the secant `z ↦ Sec(z, p, c)` decreases on `(0, c]`
  have hlt : 3 * t + x - 1 < (1 + x) / q - (t + x) := by
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with he | he
    · rw [he] at hF; linarith
    · have := nh_sec_start (z1 := (1 + x) / q - (t + x)) (z2 := 3 * t + x - 1) (c := 1 - t)
        (d := t + x) hA0 he (by linarith) (by linarith)
      linarith
  have hden : 0 < 4 * t + 2 * x - 1 := by linarith
  rw [lt_div_iff₀ hden]
  have : (4 * t + 2 * x - 1) < (1 + x) / q := by linarith
  rw [lt_div_iff₀ hq0] at this
  linarith

end SmoothedOctagon

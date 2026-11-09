module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LargeGap
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Casimir
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Chi
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Envelope

/-!
# Case M2, forward successor by hand: the small-gap Casimir contradiction

An actual forward window has `t > 1/3` (`fh_low_ratio`) and `0 < j < 1/30` (`fh_small_gap_j`), hence
`χ > 4/7` (`fh_chi_core`). On the first-event stationary line the squared Casimir `Γ` decreases on
`[3/4, ∞)` (`fh_cas_slope`, `fh_gam_anti`), and `3/4 ≤ w_actual < w_U`, so
`γ² = Γ(w_actual) ≥ Γ(w_U)`. At `w_U` the diagonal is positive and, by the factor elimination
(`fh_qelim`) and the incoming floor, at most `B(h₁ + v - g)`; hence `Γ(w_U) ≥ 𝒢 > 9193/50000`
(`fh_envelope`), contradicting the competitive cap `γ² < 9193/50000`.

## Main API

* `fh_Hd_wU`: `H_d(w_U)/B = log q + αq + β/q + d`.
* `fh_small_gap`: **no actual window has a forward successor**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The diagonal at the envelope norm:
`H_d(w_U) = B (h₁ + (log q + α(q - 1) + β(1/q - 1)))`. -/
theorem fh_Hd_wU {t x k q v L : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) (hq : 0 < q) :
    fhHd t x k q v L (fhwU t x k v) = (k + 2 * t * x + x ^ 2) *
      (fhh1 t x k v + (L + fhAq t x k v * (q - 1) + fhBq t x k * (1 / q - 1))) := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  unfold fhHd fhSd fhh1 fhAq fhBq fhwU
  field_simp
  ring

/-- **The envelope Casimir exceeds the cap**: on the small-gap domain, with `χ ≥ 4/7`, `t ≤ r ≤ p`,
the incoming floor and `v ∈ [3/4, min(1, V)]`, `Γ(w_U) > 9193/50000`, and `2v - eH_d(w_U)/p < 0`. -/
theorem fh_gam_wU {t x k q v : ℝ} (ht : 1 / 3 ≤ t) (ht2 : t ≤ 2 / 5) (hj0 : 0 < 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk1 : 1 ≤ k) (hk2 : k ≤ 31 / 30) (hq : 1 < q)
    (hr0 : t ≤ q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x))
    (hr1 : q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ≤ t + x)
    (hχ : 4 / 7 ≤ (t + x) * q / (1 + x)) (hv34 : 3 / 4 ≤ v) (hv1 : v ≤ 1) (hvV : v ≤ fhVq t x)
    (hFl : m2F ((t + x) / (1 + x)) q ≤ v) (hwU : 3 / 4 ≤ fhwU t x k v) :
    9193 / 50000 < fhGam t x k q v (Real.log q) (fhwU t x k v) := by
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hp : 0 < t + x := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hs2 := fh_cas_slope (k := k) ht ht2 hj0 (by linarith) hk1 hq hr0 hr1 hχ hv34 hFl hwU
  -- the diagonal at `w_U`
  have hHd := fh_Hd_wU (t := t) (x := x) (k := k) (q := q) (v := v) (L := Real.log q) (by linarith) hx (by linarith) hq0
  have hHdpos : 0 < fhHd t x k q v (Real.log q) (fhwU t x k v) := by
    have h1 : 0 < q / (1 + x) * fhHd t x k q v (Real.log q) (fhwU t x k v) / (t + x) := by linarith
    have h2 : 0 < q / (1 + x) * fhHd t x k q v (Real.log q) (fhwU t x k v) := by
      have := mul_pos h1 hp; rwa [div_mul_cancel₀ _ hp.ne'] at this
    exact pos_of_mul_pos_right h2 (by positivity)
  have hqe := fh_qelim (v := v) ht ht2 hj0.le hj1 hk1 hv1 hvV hq
  have hg : 1 - fhEta t x + fhEta t x ^ 2 = fhg t x := by
    unfold fhEta fhg; field_simp; ring
  rw [hg] at hqe
  have hFl' : m2F (fhEta t x) q ≤ v := hFl
  have hHdup : fhHd t x k q v (Real.log q) (fhwU t x k v) <
      (k + 2 * t * x + x ^ 2) * (fhh1 t x k v + v - fhg t x) := by
    rw [hHd]
    apply mul_lt_mul_of_pos_left _ hB
    linarith
  have hsq : fhHd t x k q v (Real.log q) (fhwU t x k v) ^ 2 <
      ((k + 2 * t * x + x ^ 2) * (fhh1 t x k v + v - fhg t x)) ^ 2 :=
    pow_lt_pow_left₀ hHdup hHdpos.le (by norm_num)
  have henv := fh_envelope ht ht2 hj0.le hj1 hk1 hk2 hv34 hvV
  have hkt : 0 < k - t ^ 2 := by nlinarith
  have hs : 0 < 16 * (k - t ^ 2) ^ 2 := by positivity
  unfold fhGam
  have : (k + 2 * t * x + x ^ 2) ^ 2 * (4 * v * fhwU t x k v - (fhh1 t x k v + v - fhg t x) ^ 2)
      / (16 * (k - t ^ 2) ^ 2) <
      (4 * (k + 2 * t * x + x ^ 2) ^ 2 * v * fhwU t x k v
        - fhHd t x k q v (Real.log q) (fhwU t x k v) ^ 2) / (16 * (k - t ^ 2) ^ 2) := by
    apply div_lt_div_of_pos_right _ hs
    have e : (k + 2 * t * x + x ^ 2) ^ 2 * (4 * v * fhwU t x k v - (fhh1 t x k v + v - fhg t x) ^ 2) =
        4 * (k + 2 * t * x + x ^ 2) ^ 2 * v * fhwU t x k v -
          ((k + 2 * t * x + x ^ 2) * (fhh1 t x k v + v - fhg t x)) ^ 2 := by ring
    rw [e]; linarith
  linarith

/-- **The small-gap scalar contradiction**: with `3/4 ≤ w < w_U` and `γ² = Γ(w) < 9193/50000`. -/
theorem fh_smallgap_core {t x k q v w : ℝ} (ht : 1 / 3 ≤ t) (ht2 : t ≤ 2 / 5)
    (hj0 : 0 < 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk1 : 1 ≤ k) (hk2 : k ≤ 31 / 30)
    (hq : 1 < q) (hr0 : t ≤ q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x))
    (hr1 : q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ≤ t + x)
    (hχ : 4 / 7 ≤ (t + x) * q / (1 + x)) (hv34 : 3 / 4 ≤ v) (hv1 : v ≤ 1) (hvV : v ≤ fhVq t x)
    (hFl : m2F ((t + x) / (1 + x)) q ≤ v) (hw34 : 3 / 4 ≤ w) (hwU : w < fhwU t x k v)
    (hcap : fhGam t x k q v (Real.log q) w < 9193 / 50000) : False := by
  have hx : 0 < x := by linarith
  have hp : 0 < t + x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hs1 := fh_cas_slope (k := k) ht ht2 hj0 (by linarith) hk1 hq hr0 hr1 hχ hv34 hFl hw34
  have hs2 := fh_cas_slope (k := k) ht ht2 hj0 (by linarith) hk1 hq hr0 hr1 hχ hv34 hFl
    (by linarith : 3 / 4 ≤ fhwU t x k v)
  have hanti := fh_gam_anti (L := Real.log q) hB hp hW hwU.le hs1.le hs2.le
  have hGU := fh_gam_wU ht ht2 hj0 hj1 hk1 hk2 hq hr0 hr1 hχ hv34 hv1 hvV hFl (by linarith)
  linarith

/-- **The forward successor is excluded**: no actual smaller-nonshort window has a forward
successor. -/
theorem fh_small_gap (W : M2Window) (hF : W.ForwardNext) : False := by
  have ht := fh_low_ratio W hF
  have hj1 := fh_small_gap_j W hF
  obtain ⟨-, -, hx, hk1, hq, -, hv, hvU, -, hFl, -⟩ := nh_window_basic W
  have ht2 := nh_high_t W
  have hko := fh_window_order W
  have hks := nh_scale_k W
  have hqs : W.nq * (4 * W.nt + 2 * W.nx - 1) < 1 + W.nx := by
    have := fh_window_swap W
    have hden : 0 < 4 * W.nt + 2 * W.nx - 1 := by linarith
    rwa [lt_div_iff₀ hden] at this
  have hj0 : 0 < 2 * W.nt + W.nx - 1 := by linarith
  have ht19 : W.nt ≤ 19 / 50 := by nlinarith
  have hW : 0 < 1 + W.nx := by linarith
  have hq0 : 0 < W.nq := by linarith
  -- `χ > 4/7`
  have hχ := fh_chi_core ht.le ht19 hj0.le hj1.le hk1.le hq hv hvU (nh_window_N_neg W)
  have hχ' : 4 / 7 ≤ (W.nt + W.nx) * W.nq / (1 + W.nx) := by
    rw [le_div_iff₀ hW]; linarith
  -- `t ≤ r`
  have hr0 : W.nt ≤ W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) / (1 + W.nx) - (W.nt + W.nx) := by
    obtain ⟨hT, -, -, -, -, ha, -, hd, -, -, hZ, -⟩ := fh_window_coords W
    have har := W.a_le_r
    have hrr : W.r = (W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) / (1 + W.nx) - (W.nt + W.nx)) *
        (W.a + W.c) := by
      rw [sub_mul, ← hZ, hd]; ring
    rw [ha, hrr] at har
    exact le_of_mul_le_mul_right har hT
  -- `r ≤ p`
  have hr1 : W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) / (1 + W.nx) - (W.nt + W.nx) ≤
      W.nt + W.nx := by
    have hBW : W.nk + 2 * W.nt * W.nx + W.nx ^ 2 ≤ (1 + W.nx) * (4 * W.nt + 2 * W.nx - 1) := by
      nlinarith
    have h1 : W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) ≤
        W.nq * ((1 + W.nx) * (4 * W.nt + 2 * W.nx - 1)) := mul_le_mul_of_nonneg_left hBW hq0.le
    have h2 : W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) ≤ (1 + W.nx) * (1 + W.nx) := by nlinarith
    have : W.nq * (W.nk + 2 * W.nt * W.nx + W.nx ^ 2) / (1 + W.nx) ≤ 1 + W.nx := by
      rw [div_le_iff₀ hW]; linarith
    linarith
  -- `v ≥ 3/4` and `v ≤ min(1, V)`
  have hv34 : 3 / 4 ≤ W.v := by
    have h := W.v_ge
    have hc0 : 0 < W.c := by linarith [W.a_lt_c, W.a_pos]
    have hd0 : 0 < W.d := by linarith [W.a_lt_d, W.a_pos]
    have h34 : 3 / 4 ≤ m2g W.c W.d := by
      unfold m2g; rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (W.c - W.d)]
    exact h34.trans h
  have hv1 : W.v ≤ 1 := by nlinarith
  have hvV : W.v ≤ fhVq W.nt W.nx := by rw [hv]; exact (fh_secN_lt_Vq hx (by linarith)).le
  have hcap : fhGam W.nt W.nx W.nk W.nq W.v (Real.log W.nq) W.w < 9193 / 50000 := by
    rw [← fh_window_cas W]; exact W.cas_lt
  exact fh_smallgap_core ht.le ht2.le hj0 hj1.le hk1.le (by linarith) hq hr0 hr1 hχ' hv34 hv1 hvV
    hFl (fh_window_w34 W) (fh_window_wU W) hcap

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.WindowData
public import SmoothedOctagon.Exclusion.Mixed.TurnSecant

/-!
# Case M2, reverse successor: order bounds from the actual norm floors

* `nsr_q_le_order`: on `k ≥ 2t + x`-type data, the incoming floor and the swapped secant order give
  `q ≤ W/(2t + x)`.
* `nsr_reverse_order`: **the reverse order bound** `d ≤ b*`, i.e. `k ≥ 2t + x`
  (`nsr_reverse_order_k`), for a reverse successor.
* `nsr_log_one_add_gt3`: three atanh terms for `log(1 + x)`.
* `nsr_window_dur`: **the duration bound** `d < 7c/3`, i.e. `x < 7/3 - (10/3)t`
  (`nsr_window_dur_x`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The order-face factor interval**: with
`2t + x ≥ 1`, the incoming floor `F_{p/W}(q) ≤ v = Sec(t, 1 - t, t + x)` and `1 < q < W/p` force
`q ≤ W/(2t + x)`. -/
theorem nsr_q_le_order {t x q v : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) (hx : 0 < x)
    (hk : 1 ≤ 2 * t + x) (hq : 1 < q) (hqW : q < (1 + x) / (t + x)) (hv : v = nsrSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) : q ≤ (1 + x) / (2 * t + x) := by
  have hq0 : 0 < q := by linarith
  have hFs : m2F ((t + x) / (1 + x)) q = m2Sec ((1 + x) / q - (t + x)) (t + x) (1 - t) := by
    have := nsr_m2F_eq_sec (P := t + x) (C := 1 - t) (q := q) (by linarith) (by linarith) hq
    rwa [show t + x + (1 - t) = 1 + x by ring] at this
  rw [hFs, hv, nsr_secN_eq hx] at hF
  have hswap : m2Sec t (1 - t) (t + x) ≤ m2Sec t (t + x) (1 - t) := by
    rcases eq_or_lt_of_le (show 1 - t ≤ t + x by linarith) with h | h
    · rw [h]
    · exact (nsr_sec_swap ht (by linarith) h).le
  have hA0 : 0 < (1 + x) / q - (t + x) := by
    rw [sub_pos, lt_div_iff₀ hq0]
    rw [lt_div_iff₀ (by linarith)] at hqW
    linarith
  by_contra hcon
  push Not at hcon
  have hlt : (1 + x) / q - (t + x) < t := by
    rw [div_lt_iff₀ (by linarith)] at hcon
    have : (1 + x) / q < 2 * t + x := by rw [div_lt_iff₀ hq0]; linarith
    linarith
  have := nsr_sec_start (z1 := (1 + x) / q - (t + x)) (z2 := t) (c := 1 - t) (d := t + x) hA0 hlt
    (by linarith) (by linarith)
  linarith

/-- **The reverse order bound**: a reverse successor
forces `d ≤ b* = K/(a + c) - a`. -/
theorem nsr_reverse_order (W : M2Window) (hR : W.ReverseNext) : W.d ≤ W.bStar := by
  obtain ⟨A, haA, hAd, hAdr, hw, hwle⟩ := hR
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hr : 0 < W.r := by linarith [W.a_le_r]
  have hT : 0 < W.a + W.c := by positivity
  have hK : 0 < W.a ^ 2 + 4 := by positivity
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  set q := (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) with hqdef
  have hq : 1 < q := by rw [hqdef, lt_div_iff₀ hQ]; linarith [W.factor_d]
  have hbs : W.bStar = (W.a ^ 2 + 4) / (W.a + W.c) - W.a := rfl
  by_contra hcon
  push Not at hcon
  rw [hbs] at hcon
  -- `d > b*` means `(a + c)(a + d) > K`
  have hbig : W.a ^ 2 + 4 < (W.a + W.c) * (W.a + W.d) := by
    have : (W.a ^ 2 + 4) / (W.a + W.c) < W.a + W.d := by linarith
    rw [div_lt_iff₀ hT] at this; linarith
  -- `c < b*`
  have hcb : W.c < W.d := by
    have h1 : (W.a + W.c) ^ 2 < W.a ^ 2 + 4 := by
      have := W.c_le_b; have := W.central; nlinarith
    nlinarith
  -- the incoming floor as a secant: `B₀ = (4 - dr)/(d + r) > a`
  have hFv : m2F (W.d / (W.d + W.c)) q = m2Sec ((4 - W.d * W.r) / (W.d + W.r)) W.d W.c := by
    rw [nsr_m2F_eq_sec hd hc hq]
    congr 1
    rw [hqdef]
    field_simp
    ring
  have hfloor := W.v_floor
  rw [show W.d / (W.c + W.d) = W.d / (W.d + W.c) by ring, ← hqdef, hFv, W.v_eq] at hfloor
  have hB0 : 0 < (4 - W.d * W.r) / (W.d + W.r) := div_pos (by linarith [W.star_dr]) (by positivity)
  have hswap1 := nsr_sec_swap ha W.a_lt_c.le hcb
  have haB0 : W.a < (4 - W.d * W.r) / (W.d + W.r) := by
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h'] at hfloor; linarith
    · have := nsr_sec_start hB0 h' W.a_lt_c.le hcb.le
      linarith
  have hsmall : (W.a + W.d) * (W.a + W.r) < W.a ^ 2 + 4 := by
    rw [lt_div_iff₀ (by positivity)] at haB0; nlinarith
  have hrc : W.r < W.c := by nlinarith
  -- the outgoing floor as a secant: `A₀ = (4 - cd)/(c + d) > a`
  have hFw : m2F (W.d / (W.d + W.r)) q = m2Sec ((4 - W.c * W.d) / (W.c + W.d)) W.d W.r := by
    rw [nsr_m2F_eq_sec hd hr hq]
    congr 1
    rw [hqdef]
    field_simp
    ring
  have hwf := W.w_floor
  rw [← hqdef, hFw] at hwf
  have hA0 : 0 < (4 - W.c * W.d) / (W.c + W.d) := div_pos (by linarith [W.star_cd]) (by positivity)
  have hAr : A ≤ W.r := by nlinarith
  have hw2 : W.w ≤ m2Sec W.a W.r W.d := by
    rw [hw]; exact nsr_sec_le_of_rev ha haA hAr hAd (hw ▸ hwle)
  have hrd : W.r < W.d := by linarith
  have hswap2 := nsr_sec_swap ha W.a_le_r hrd
  have haA0 : W.a < (4 - W.c * W.d) / (W.c + W.d) := by
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h'] at hwf; linarith
    · have := nsr_sec_start hA0 h' W.a_le_r hrd.le
      linarith
  rw [lt_div_iff₀ (by positivity)] at haA0
  nlinarith

/-- The reverse order bound in normalized form: `k ≥ 2t + x`. -/
theorem nsr_reverse_order_k (W : M2Window) (hR : W.ReverseNext) : 2 * W.nt + W.nx ≤ W.nk := by
  have h := nsr_reverse_order W hR
  have hT : 0 < W.a + W.c := by linarith [W.a_pos, W.a_lt_c]
  have hbs : W.bStar = (W.a ^ 2 + 4) / (W.a + W.c) - W.a := rfl
  rw [hbs] at h
  unfold M2Window.nt M2Window.nx M2Window.nk
  have e : 2 * (W.a / (W.a + W.c)) + (W.d - W.a) / (W.a + W.c) = (W.a + W.d) / (W.a + W.c) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ hT (by positivity)]
  have : W.a + W.d ≤ (W.a ^ 2 + 4) / (W.a + W.c) := by linarith
  rw [le_div_iff₀ hT] at this
  nlinarith

/-- Three atanh terms: `log(1 + x) > 2z + 2z³/3 + 2z⁵/5`, `z = x/(x + 2)`. -/
theorem nsr_log_one_add_gt3 {x : ℝ} (hx : 0 < x) :
    2 * (x / (x + 2)) + 2 * (x / (x + 2)) ^ 3 / 3 + 2 * (x / (x + 2)) ^ 5 / 5 < Real.log (1 + x) := by
  have hmono := nsr_strictMonoOn_Ici (a := 0)
    (f := fun z => Real.log (1 + z) - (2 * (z / (z + 2)) + 2 * (z / (z + 2)) ^ 3 / 3
      + 2 * (z / (z + 2)) ^ 5 / 5))
    (f' := fun z => z ^ 6 / ((z + 1) * (z + 2) ^ 6)) (fun z hz => ?_) (fun z hz => by positivity)
  · have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
    simp only [add_zero, Real.log_one] at this
    norm_num at this
    linarith
  · have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h2 : HasDerivAt (fun z : ℝ => z + 2) 1 z := by
      simpa using (hasDerivAt_id z).add_const 2
    have hz1 : (1 + z) ≠ 0 := by linarith
    have hz2 : z + 2 ≠ 0 := by linarith
    have hz2' : 2 + z ≠ 0 := by linarith
    have hz1' : z + 1 ≠ 0 := by linarith
    have hr : HasDerivAt (fun z : ℝ => z / (z + 2)) (2 / (z + 2) ^ 2) z := by
      have := (hasDerivAt_id' z).div h2 hz2
      refine this.congr_deriv ?_
      field_simp
      ring
    have := (h1.log hz1).sub (((hr.const_mul 2).add ((hr.pow 3).const_mul 2 |>.div_const 3)).add
      ((hr.pow 5).const_mul 2 |>.div_const 5))
    refine this.congr_deriv ?_
    norm_num
    field_simp
    ring

/-- `log(10/3) > 119/100`. -/
theorem nsr_log_ten_thirds : (119 / 100 : ℝ) < Real.log (10 / 3) := by
  have := nsr_log_one_add_gt3 (x := 7 / 3) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **The duration bound** `d < 7c/3`. -/
theorem nsr_window_dur (W : M2Window) : 3 * W.d < 7 * W.c := by
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hv0 := nsr_sec_zero_gt ha W.a_lt_c W.a_lt_d (W.v_eq ▸ W.v_le)
  rw [← W.v_eq] at hv0
  have hgd := W.v_ge
  -- in terms of `h = d/c`
  set h := W.d / W.c with hh
  have hh0 : 0 < h := by positivity
  have hsec : m2Sec 0 W.c W.d = 1 + 1 / (1 + h) - Real.log (1 + h) / h := by
    rw [m2Sec_of_ne hd.ne, hh]
    rw [show (W.d + W.c) / (0 + W.c) = 1 + W.d / W.c by field_simp; ring]
    field_simp
    ring
  have hg : m2g W.c W.d = 1 - h / (1 + h) ^ 2 := by
    unfold m2g; rw [hh]; field_simp; ring
  have hlog : Real.log (1 + h) < h * (1 + 2 * h) / (1 + h) ^ 2 := by
    have := lt_of_le_of_lt hgd hv0
    rw [hsec, hg] at this
    have e : 1 / (1 + h) + h / (1 + h) ^ 2 = h * (1 + 2 * h) / (1 + h) ^ 2 / h := by
      field_simp; ring
    have : Real.log (1 + h) / h < h * (1 + 2 * h) / (1 + h) ^ 2 / h := by linarith
    exact (div_lt_div_iff_of_pos_right hh0).1 this
  by_contra hcon
  push Not at hcon
  have h73 : 7 / 3 ≤ h := by rw [hh, le_div_iff₀ hc]; linarith
  -- `φ(h) = log(1 + h) - h(1 + 2h)/(1 + h)²` increases for `h > 1`
  have hmono := nsr_strictMonoOn_Ici (a := 7 / 3)
    (f := fun z => Real.log (1 + z) - z * (1 + 2 * z) / (1 + z) ^ 2)
    (f' := fun z => z * (z - 1) / (1 + z) ^ 3) (fun z hz => ?_) (fun z hz => by
      have : 0 < z - 1 := by linarith
      have : 0 < z := by linarith
      positivity)
  · have hφ : Real.log (1 + 7 / 3) - 7 / 3 * (1 + 2 * (7 / 3)) / (1 + 7 / 3) ^ 2 ≤
        Real.log (1 + h) - h * (1 + 2 * h) / (1 + h) ^ 2 :=
      hmono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h73) h73
    have := nsr_log_ten_thirds
    norm_num at hφ
    linarith
  · have hz : 0 < 1 + z := by linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h3 : HasDerivAt (fun z : ℝ => z * (1 + 2 * z)) (1 * (1 + 2 * z) + z * 2) z := by
      have hb : HasDerivAt (fun z : ℝ => 1 + 2 * z) 2 z := by
        simpa using ((hasDerivAt_id z).const_mul (2 : ℝ)).const_add 1
      exact (hasDerivAt_id' z).mul hb
    have h4 : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
      have := (h1.pow 2)
      refine this.congr_deriv ?_
      norm_num
    have := (h1.log hz.ne').sub (h3.div h4 (pow_ne_zero 2 hz.ne'))
    refine this.congr_deriv ?_
    field_simp
    ring

/-- The duration bound in normalized form: `x < 7/3 - (10/3)t`. -/
theorem nsr_window_dur_x (W : M2Window) : W.nx < 7 / 3 - 10 / 3 * W.nt := by
  have h := nsr_window_dur W
  have hT : 0 < W.a + W.c := by linarith [W.a_pos, W.a_lt_c]
  unfold M2Window.nt M2Window.nx
  rw [show (7 : ℝ) / 3 - 10 / 3 * (W.a / (W.a + W.c)) = (7 * W.c - 3 * W.a) / (3 * (W.a + W.c)) by
    field_simp; ring]
  rw [div_lt_div_iff₀ hT (by positivity)]
  nlinarith

end SmoothedOctagon

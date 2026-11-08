module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Secant
public import SmoothedOctagon.Exclusion.Mixed.Comparison

/-!
# Case M2 by hand: the centre gap `d² + 2cd > 4`

`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemmas 1 and 2. Raising the incoming norm `u` to the ceiling
`U(a/S)` and then the central margin `b` to `b* = K/T - a` strictly raises the transported norm
(Lemma 1; Route: the monotonicity in `b` is proved from `log y ≤ y - 1` instead of the derivative
formula (1)). The incoming secant is below the chord average `V_ch` (chord identity), the
envelope is increasing in `v`, and if `e = 4 - d² - 2cd ≥ 0` the cleared identity (5) puts the
envelope at `V_ch` strictly below `g_d(r₀) ≤ g_d(r) ≤ w`, `r₀ = Q/W - d`: a contradiction.

## Main API

* `nh_w_mono_u`: the transported norm is affine increasing in `u`.
* `nh_wU_lt_star`: Lemma 1, `w_U(b) < w_U(b*)`.
* `nh_sec_lt_chord`: `Sec(a, c, d) < (g_c(a) + g_c(d))/2` when `ad < c²`.
* `nh_gap_identity`: identity (5).
* `nh_centre_gap'`: Lemma 2, `d² + 2cd > 4`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The transported norm with central stationarity imposed, as a function of `u`. -/
noncomputable def nhWU (a b c d u v : ℝ) : ℝ := m2wOf a c d u v (m2h a b c u v)

/-- The transported norm is affine in `u` with slope `K(aK + SY)/(aQ²)`. -/
theorem nh_w_mono_u {a b c d u U v : ℝ} (ha : 0 < a) (hd : 0 < d) :
    nhWU a b c d U v - nhWU a b c d u v =
      (U - u) * ((a ^ 2 + 4) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d) / (a * (d ^ 2 + 4) ^ 2)) := by
  unfold nhWU m2wOf m2h m2Y
  have hK : a ^ 2 + 4 ≠ 0 := by positivity
  have hQ : d ^ 2 + 4 ≠ 0 := by positivity
  field_simp
  ring

/-- **Lemma 1** (monotonicity in `b`): with the upper incident norm, the transported norm at `b`
is strictly below the one at `b* = K/T - a`, for `2a < a + b < K/T`. -/
theorem nh_wU_lt_star {a b c d v : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (had : a < d)
    (hbs : (a + b) * (a + c) < a ^ 2 + 4) :
    nhWU a b c d (m2U (a / (a + b))) v <
      nhWU a (m2bStar a c) c d (m2U (a / (a + m2bStar a c))) v := by
  have hd : 0 < d := by linarith
  have hT : 0 < a + c := by linarith
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hS : 0 < a + b := by linarith
  set Ss := (a ^ 2 + 4) / (a + c) with hSs
  have hSS : a + b < Ss := by rw [hSs, lt_div_iff₀ hT]; linarith
  have hb' : a + m2bStar a c = Ss := by unfold m2bStar; ring
  have hY : 0 < m2Y a c d := by unfold m2Y; nlinarith
  -- the diagonal increases: `h* - h = (K/16)(2a(1/S* - 1/S) - log(ST/K))`
  have hlog : Real.log ((m2bStar a c + a) * (a + c) / (a ^ 2 + 4)) = 0 := by
    rw [show (m2bStar a c + a) * (a + c) / (a ^ 2 + 4) = 1 by
      rw [add_comm, hb', hSs]; field_simp]
    exact Real.log_one
  have hL : Real.log ((b + a) * (a + c) / (a ^ 2 + 4)) ≤ (b + a) * (a + c) / (a ^ 2 + 4) - 1 :=
    Real.log_le_sub_one_of_pos (by have : 0 < b := by linarith
                                   positivity)
  have hdiff : m2h a (m2bStar a c) c (m2U (a / (a + m2bStar a c))) v -
      m2h a b c (m2U (a / (a + b))) v =
      (a ^ 2 + 4) / 16 * (2 * a * (1 / Ss - 1 / (a + b)) -
        Real.log ((b + a) * (a + c) / (a ^ 2 + 4))) := by
    unfold m2h m2Stat
    rw [hlog, hb']
    have hbs' : m2bStar a c + a = Ss := by rw [add_comm]; exact hb'
    rw [hbs']
    generalize Real.log ((b + a) * (a + c) / (a ^ 2 + 4)) = L
    unfold m2U
    have hSs0 : Ss ≠ 0 := by positivity
    have hab0 : a + b ≠ 0 := by linarith
    have hba0 : b + a ≠ 0 := by linarith
    field_simp
    ring
  have hh : 0 < m2h a (m2bStar a c) c (m2U (a / (a + m2bStar a c))) v -
      m2h a b c (m2U (a / (a + b))) v := by
    rw [hdiff]
    apply mul_pos (by positivity)
    have hSs0 : 0 < Ss := by linarith
    have e : (b + a) * (a + c) / (a ^ 2 + 4) = (a + b) / Ss := by rw [hSs]; field_simp; ring
    rw [e] at hL ⊢
    have key : 0 < (1 - (a + b) / Ss) * (1 - 2 * a / (a + b)) := by
      apply mul_pos
      · rw [sub_pos, div_lt_one hSs0]; exact hSS
      · rw [sub_pos, div_lt_one hS]; linarith
    have e2 : (1 - (a + b) / Ss) * (1 - 2 * a / (a + b)) =
        2 * a * (1 / Ss - 1 / (a + b)) + (1 - (a + b) / Ss) := by field_simp; ring
    linarith
  -- the ceiling increases
  have hU : m2U (a / (a + b)) < m2U (a / (a + m2bStar a c)) := by
    rw [hb']
    unfold m2U
    have h1 : a / Ss < a / (a + b) := div_lt_div_of_pos_left ha hS hSS
    have h2 : a / (a + b) < 1 / 2 := by rw [div_lt_iff₀ hS]; linarith
    have h3 : 0 < a / Ss := by positivity
    nlinarith
  -- combine: `w = (K²u + 16hY + vY²)/Q²` is increasing in `u` and `h`
  unfold nhWU m2wOf
  have hQ : 0 < (d ^ 2 + 4) ^ 2 := by positivity
  apply div_lt_div_of_pos_right _ hQ
  have := mul_lt_mul_of_pos_left hU (by positivity : (0 : ℝ) < (a ^ 2 + 4) ^ 2)
  nlinarith

/-- **The chord bound**: for `0 < a < d` with `ad < c²`, the secant lies strictly below the chord
average, `Sec(a, c, d) < (g_c(a) + g_c(d))/2` (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2). -/
theorem nh_sec_lt_chord {a c d : ℝ} (ha : 0 < a) (hc : 0 < c) (had : a < d) (hlc : a * d < c ^ 2) :
    m2Sec a c d < (m2g c a + m2g c d) / 2 := by
  have hd : 0 < d := by linarith
  have hda : 0 < d - a := by linarith
  set ga := m2g c a
  set gd := m2g c d
  have hanti : StrictAntiOn (fun s => nhG c s - (ga * (s - a) + (gd - ga) * (s - a) ^ 2 / (2 * (d - a))))
      (Set.Icc a d) := by
    have hderiv : ∀ s, a ≤ s → HasDerivAt (fun s => nhG c s - (ga * (s - a) + (gd - ga) * (s - a) ^ 2 / (2 * (d - a))))
        (m2g c s - (ga + (gd - ga) * (s - a) / (d - a))) s := by
      intro s hs
      have h0 : 0 < c + s := by linarith
      have h1 : HasDerivAt (fun s : ℝ => s - a) 1 s := by simpa using (hasDerivAt_id s).sub_const a
      have := (nh_hasDerivAt_G h0).sub ((h1.const_mul ga).add (((h1.pow 2).const_mul (gd - ga)).div_const
        (2 * (d - a))))
      refine this.congr_deriv ?_
      field_simp
      ring
    apply strictAntiOn_of_deriv_neg (convex_Icc a d)
    · exact fun s hs => (hderiv s hs.1).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s hs.1.le).deriv]
      have hcs : 0 < c + s := by linarith [hs.1]
      have e : (ga + (gd - ga) * (s - a) / (d - a)) - m2g c s =
          c * (s - a) * (d - s) * (c ^ 2 * (a + d + 2 * c) + (c ^ 2 - a * d) * s) /
            ((a + c) ^ 2 * (c + d) ^ 2 * (c + s) ^ 2) := by
        simp only [ga, gd]; unfold m2g; field_simp; ring
      have : 0 < c * (s - a) * (d - s) * (c ^ 2 * (a + d + 2 * c) + (c ^ 2 - a * d) * s) /
          ((a + c) ^ 2 * (c + d) ^ 2 * (c + s) ^ 2) := by
        apply div_pos _ (by positivity)
        apply mul_pos (mul_pos (mul_pos hc (by linarith [hs.1])) (by linarith [hs.2]))
        have : 0 < (c ^ 2 - a * d) * s := mul_pos (by linarith) (by linarith [hs.1])
        positivity
      linarith
  have := hanti (Set.left_mem_Icc.2 had.le) (Set.right_mem_Icc.2 had.le) had
  simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero, sub_zero] at this
  rw [nh_sec_eq_G ha.le hc hd.le had.ne, div_lt_iff₀ hda]
  have e : (gd - ga) * (d - a) ^ 2 / (2 * (d - a)) = (gd - ga) * (d - a) / 2 := by field_simp
  rw [e] at this
  linarith

/-- **The cleared envelope identity** (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP` (5)): with `x = d - a`,
`e = 4 - d² - 2cd`, `Q²(w_{U,ch} - g_d(r₀)) = -(cx/(2aT²W²))(P₀(x) + e P_e(x))`. -/
theorem nh_gap_identity {a c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    let T := a + c
    let W := c + d
    let Q := d ^ 2 + 4
    let x := d - a
    let Vch := 1 - (a * c / T ^ 2 + c * d / W ^ 2) / 2
    let r0 := Q / W - d
    (d ^ 2 + 4) ^ 2 * (nhWU a (m2bStar a c) c d (m2U (a / (a + m2bStar a c))) Vch - m2g d r0) =
      -(c * x / (2 * a * T ^ 2 * W ^ 2)) *
        (2 * a * T ^ 5 * x + 2 * T ^ 3 * (5 * a ^ 2 + 3 * a * c + 2 * c ^ 2) * x ^ 2
          + 2 * T ^ 2 * (9 * a ^ 2 + 5 * a * c + 2 * c ^ 2) * x ^ 3
          + T * (2 * a + c) * (7 * a + c) * x ^ 4 + a * (4 * a + 3 * c) * x ^ 5
          + (4 - d ^ 2 - 2 * c * d) * (T * (2 * a * T ^ 3 + 2 * T ^ 3 * x + 4 * a * T ^ 2 * x
            + T ^ 2 * x ^ 2 + 6 * a * T * x ^ 2 + 3 * a * x ^ 3))) := by
  intro T W Q x Vch r0
  have hT : 0 < a + c := by linarith
  have hW : 0 < c + d := by linarith
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hb' : a + m2bStar a c = (a ^ 2 + 4) / (a + c) := by unfold m2bStar; ring
  have hlog : Real.log ((m2bStar a c + a) * (a + c) / (a ^ 2 + 4)) = 0 := by
    rw [show (m2bStar a c + a) * (a + c) / (a ^ 2 + 4) = 1 by
      rw [add_comm, hb']; field_simp]
    exact Real.log_one
  have hr0 : d + r0 = (d ^ 2 + 4) / (c + d) := by simp only [r0, Q, W]; ring
  simp only [Vch, x, T, W, r0, Q]
  unfold nhWU m2wOf m2h m2Stat m2Y
  rw [hlog]
  rw [show m2bStar a c + a = (a ^ 2 + 4) / (a + c) by rw [add_comm]; exact hb', hb']
  unfold m2g m2U
  rw [show d + ((d ^ 2 + 4) / (c + d) - d) = (d ^ 2 + 4) / (c + d) by ring]
  have hdr : 0 < (d ^ 2 + 4) / (c + d) := by positivity
  field_simp
  ring

/-- **Lemma 2** (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`): `d² + 2cd > 4`. -/
theorem nh_centre_gap' (W : M2Window) : 4 < W.d ^ 2 + 2 * W.c * W.d := by
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hr : 0 < W.r := by linarith [W.a_le_r]
  have hb : 0 < W.b := by linarith [W.a_lt_b]
  have hT : 0 < W.a + W.c := by positivity
  have hWp : 0 < W.c + W.d := by positivity
  have hK : 0 < W.a ^ 2 + 4 := by positivity
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  by_contra hcon
  push Not at hcon
  -- `w ≤ w_U(b) < w_U(b*)`
  have hw1 : W.w ≤ nhWU W.a W.b W.c W.d (m2U (W.a / (W.a + W.b))) W.v := by
    have e := nh_w_mono_u (a := W.a) (b := W.b) (c := W.c) (d := W.d)
      (u := W.u) (U := m2U (W.a / (W.a + W.b))) (v := W.v) ha hd
    have hwu : W.w = nhWU W.a W.b W.c W.d W.u W.v := by rw [W.w_eq, W.h_eq]; rfl
    have hu := W.u_le
    rw [m2g_eq_m2U (by positivity)] at hu
    have hY : 0 < m2Y W.a W.c W.d := by unfold m2Y; nlinarith [W.a_lt_d]
    have : 0 ≤ (m2U (W.a / (W.a + W.b)) - W.u) * ((W.a ^ 2 + 4) * (W.a * (W.a ^ 2 + 4)
        + (W.a + W.b) * m2Y W.a W.c W.d) / (W.a * (W.d ^ 2 + 4) ^ 2)) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  have hw2 := nh_wU_lt_star (v := W.v) ha W.a_lt_b hc W.a_lt_d W.central
  -- `v < V_ch` and the envelope increases with `v`
  have hch := nh_sec_lt_chord ha hc W.a_lt_d W.logconc
  rw [← W.v_eq] at hch
  set Vch := 1 - (W.a * W.c / (W.a + W.c) ^ 2 + W.c * W.d / (W.c + W.d) ^ 2) / 2 with hVch
  have hgch : (m2g W.c W.a + m2g W.c W.d) / 2 = Vch := by
    rw [hVch]; unfold m2g; field_simp; ring
  rw [hgch] at hch
  have hw3 : nhWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a / (W.a + m2bStar W.a W.c))) W.v <
      nhWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a / (W.a + m2bStar W.a W.c))) Vch := by
    have hb' : W.a + m2bStar W.a W.c = (W.a ^ 2 + 4) / (W.a + W.c) := by unfold m2bStar; ring
    have e : nhWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a / (W.a + m2bStar W.a W.c))) Vch -
        nhWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a / (W.a + m2bStar W.a W.c))) W.v =
        (Vch - W.v) * (m2Y W.a W.c W.d * ((W.a ^ 2 + 4) * (W.a + W.c) / W.a + m2Y W.a W.c W.d) /
          (W.d ^ 2 + 4) ^ 2) := by
      unfold nhWU m2wOf m2h
      rw [hb']
      field_simp
      ring
    have hY : 0 < m2Y W.a W.c W.d := by unfold m2Y; nlinarith [W.a_lt_d]
    have : 0 < (Vch - W.v) * (m2Y W.a W.c W.d * ((W.a ^ 2 + 4) * (W.a + W.c) / W.a + m2Y W.a W.c W.d) /
        (W.d ^ 2 + 4) ^ 2) := mul_pos (by linarith) (by positivity)
    linarith
  -- `g_d(r₀) ≤ g_d(r) ≤ w`, `r₀ = Q/W - d ∈ [d, r)`
  set r0 := (W.d ^ 2 + 4) / (W.c + W.d) - W.d with hr0
  have hr0d : W.d ≤ r0 := by
    rw [hr0, le_sub_iff_add_le, le_div_iff₀ hWp]; nlinarith
  have hr0r : r0 < W.r := by
    have := W.factor_d
    rw [hr0, sub_lt_iff_lt_add, div_lt_iff₀ hWp]; nlinarith
  have hg : m2g W.d r0 ≤ m2g W.d W.r := by
    have := nh_m2g_sub (B := W.d) (s1 := r0) (s2 := W.r) (by linarith) (by linarith)
    have hr0p : 0 < W.d + r0 := by linarith
    have : W.d * (W.r - r0) * (W.d ^ 2 - r0 * W.r) / ((W.d + r0) ^ 2 * (W.d + W.r) ^ 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hd.le (by linarith))
      nlinarith
    linarith
  have hwge := W.w_ge
  -- the cleared identity
  have hid := nh_gap_identity ha hc hd
  simp only at hid
  have hneg : (W.d ^ 2 + 4) ^ 2 * (nhWU W.a (m2bStar W.a W.c) W.c W.d
      (m2U (W.a / (W.a + m2bStar W.a W.c))) Vch - m2g W.d r0) < 0 := by
    rw [hVch, hr0, hid]
    have hx : 0 < W.d - W.a := by linarith [W.a_lt_d]
    have he : 0 ≤ 4 - W.d ^ 2 - 2 * W.c * W.d := by linarith
    have hA : 0 < W.c * (W.d - W.a) / (2 * W.a * (W.a + W.c) ^ 2 * (W.c + W.d) ^ 2) := by positivity
    have hB : 0 < 2 * W.a * (W.a + W.c) ^ 5 * (W.d - W.a)
        + 2 * (W.a + W.c) ^ 3 * (5 * W.a ^ 2 + 3 * W.a * W.c + 2 * W.c ^ 2) * (W.d - W.a) ^ 2
        + 2 * (W.a + W.c) ^ 2 * (9 * W.a ^ 2 + 5 * W.a * W.c + 2 * W.c ^ 2) * (W.d - W.a) ^ 3
        + (W.a + W.c) * (2 * W.a + W.c) * (7 * W.a + W.c) * (W.d - W.a) ^ 4
        + W.a * (4 * W.a + 3 * W.c) * (W.d - W.a) ^ 5
        + (4 - W.d ^ 2 - 2 * W.c * W.d) * ((W.a + W.c) * (2 * W.a * (W.a + W.c) ^ 3
          + 2 * (W.a + W.c) ^ 3 * (W.d - W.a) + 4 * W.a * (W.a + W.c) ^ 2 * (W.d - W.a)
          + (W.a + W.c) ^ 2 * (W.d - W.a) ^ 2 + 6 * W.a * (W.a + W.c) * (W.d - W.a) ^ 2
          + 3 * W.a * (W.d - W.a) ^ 3)) := by positivity
    have := mul_pos hA hB
    linarith
  have hlt : nhWU W.a (m2bStar W.a W.c) W.c W.d (m2U (W.a / (W.a + m2bStar W.a W.c))) Vch <
      m2g W.d r0 := by
    have hQ2 : 0 < (W.d ^ 2 + 4) ^ 2 := by positivity
    by_contra h
    push Not at h
    have := mul_nonneg hQ2.le (sub_nonneg.2 h)
    linarith
  linarith

end SmoothedOctagon

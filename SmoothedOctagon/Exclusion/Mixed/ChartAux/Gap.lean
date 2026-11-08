module

public import SmoothedOctagon.Exclusion.Mixed.Window

/-!
# Case M2: the first forward centre satisfies `d² + 2cd > 4`

`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemmas 1 and 2. With `K = a² + 4`, `T = a + c`, `S = a + b`,
`Q = d² + 4`, `W = c + d`, `Y = W² - T²`:

* `chwU a b c d v`: the transported norm `w_U(b)` with the upper incident norm `u = U(a/S)`.
* `ch_w_le_wU`: `w ≤ w_U(b)` when `u ≤ U(a/S)` (the `u`-coefficient `K(aK + SY)/(aQ²)` is
  positive).
* `ch_wU_lt`: `w_U(b) < w_U(b*)` for `b < b* = K/T - a` (Lemma 1, by `log x ≤ x - 1`).
* `ch_wU_v`: `w_U` is affine in `v` with slope `Y(KT/a + Y)/Q²`.
* `ch_sec_lt_chord`: `Sec(a, c, d) < V_ch = 1 - (ac/T² + cd/W²)/2` when `ad ≤ c²` (by
  `log(1 + z) > 2z/(z + 2)`).
* `ch_gap_identity`: identity (5) of Lemma 2.
* `ch_gd_mono`: `g_d` is increasing on `[d, ∞)`.
* `ch_centre_gap`: `4 < d² + 2cd` for the actual smaller-nonshort window (Lemma 2).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The transported norm with the upper incident norm `u = U(a/(a + b))` imposed. -/
noncomputable def chwU (a b c d v : ℝ) : ℝ :=
  m2wOf a c d (m2U (a / (a + b))) v (m2h a b c (m2U (a / (a + b))) v)

/-- `w ≤ w_U(b)` when `u ≤ U(a/(a + b))`. -/
theorem ch_w_le_wU {a b c d u v : ℝ} (ha : 0 < a) (hb : 0 < a + b) (hY : 0 < m2Y a c d)
    (hu : u ≤ m2U (a / (a + b))) : m2wOf a c d u v (m2h a b c u v) ≤ chwU a b c d v := by
  have hQ : 0 < d ^ 2 + 4 := by positivity
  have key : chwU a b c d v - m2wOf a c d u v (m2h a b c u v) =
      (a ^ 2 + 4) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d) / (a * (d ^ 2 + 4) ^ 2) *
        (m2U (a / (a + b)) - u) := by
    unfold chwU m2wOf m2h
    field_simp
    ring
  have hp : 0 < a * (a ^ 2 + 4) + (a + b) * m2Y a c d := add_pos (by positivity) (mul_pos hb hY)
  have : 0 ≤ (a ^ 2 + 4) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d) / (a * (d ^ 2 + 4) ^ 2) *
      (m2U (a / (a + b)) - u) :=
    mul_nonneg (div_pos (mul_pos (by positivity) hp) (by positivity)).le (by linarith)
  linarith

/-- **Lemma 1** (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP` (1)-(2)): `w_U(b) < w_U(b*)`.
Route: `log x ≤ x - 1` in place of the derivative `(w_U)_b > 0`. -/
theorem ch_wU_lt {a b c d v : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hY : 0 < m2Y a c d)
    (hcen : (a + b) * (a + c) < a ^ 2 + 4) :
    chwU a b c d v < chwU a ((a ^ 2 + 4) / (a + c) - a) c d v := by
  have hT : 0 < a + c := by linarith
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hQ : 0 < d ^ 2 + 4 := by positivity
  have hS : 0 < a + b := by linarith
  set Ss := (a ^ 2 + 4) / (a + c) with hSs
  have hSlt : a + b < Ss := by rw [hSs, lt_div_iff₀ hT]; exact hcen
  have hSs0 : 0 < Ss := by linarith
  have hL := Real.log_le_sub_one_of_pos (x := (b + a) * (a + c) / (a ^ 2 + 4))
    (div_pos (mul_pos (by linarith) hT) hK)
  have hb1 : Ss - a + a = Ss := by ring
  have hb2 : a + (Ss - a) = Ss := by ring
  have hlog1 : Real.log (Ss * (a + c) / (a ^ 2 + 4)) = 0 := by
    rw [show Ss * (a + c) / (a ^ 2 + 4) = 1 by rw [hSs]; field_simp]
    simp
  have key : chwU a (Ss - a) c d v - chwU a b c d v =
      (a ^ 2 + 4) * m2Y a c d *
          (-Real.log ((b + a) * (a + c) / (a ^ 2 + 4)) - 1 + (a + b) * (a + c) / (a ^ 2 + 4)) /
          (d ^ 2 + 4) ^ 2 +
        (Ss - (a + b)) * ((a ^ 2 + 4) ^ 2 * a * ((a + b) * Ss - a * (a + b) - a * Ss) +
          (a ^ 2 + 4) * m2Y a c d * (a + b - 2 * a) * (a + b) * Ss) /
          ((a + b) ^ 2 * Ss ^ 2 * (d ^ 2 + 4) ^ 2) := by
    unfold chwU m2wOf m2h m2Stat m2U
    simp only [hb1, hb2]
    rw [hlog1]
    generalize Real.log ((b + a) * (a + c) / (a ^ 2 + 4)) = L
    rw [hSs]
    have hba : b + a ≠ 0 := by linarith
    field_simp
    ring
  have h1 : 0 ≤ (a ^ 2 + 4) * m2Y a c d *
      (-Real.log ((b + a) * (a + c) / (a ^ 2 + 4)) - 1 + (a + b) * (a + c) / (a ^ 2 + 4)) /
      (d ^ 2 + 4) ^ 2 := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    have : (b + a) * (a + c) / (a ^ 2 + 4) = (a + b) * (a + c) / (a ^ 2 + 4) := by ring
    linarith
  have hm : 0 < (a + b) * Ss - a * (a + b) - a * Ss := by nlinarith
  have h2 : 0 < (Ss - (a + b)) * ((a ^ 2 + 4) ^ 2 * a * ((a + b) * Ss - a * (a + b) - a * Ss) +
          (a ^ 2 + 4) * m2Y a c d * (a + b - 2 * a) * (a + b) * Ss) /
          ((a + b) ^ 2 * Ss ^ 2 * (d ^ 2 + 4) ^ 2) := by
    apply div_pos _ (by positivity)
    apply mul_pos (by linarith)
    have : 0 < a + b - 2 * a := by linarith
    positivity
  linarith

/-- `w_U` is affine in `v` with slope `Y (K T/a + Y)/Q²`. -/
theorem ch_wU_v {a b c d : ℝ} (v v' : ℝ) (ha : 0 < a) :
    chwU a b c d v' - chwU a b c d v =
      m2Y a c d * ((a ^ 2 + 4) * (a + c) / a + m2Y a c d) / (d ^ 2 + 4) ^ 2 * (v' - v) := by
  have hQ : 0 < d ^ 2 + 4 := by positivity
  unfold chwU m2wOf m2h
  field_simp
  ring

/-- **The chord bound** (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2): if `0 < a < d`, `c > 0`
and `ad ≤ c²`, then `Sec(a, c, d) < 1 - (ac/T² + cd/W²)/2`. Route: `log(1 + z) > 2z/(z + 2)`
in place of integrating the pointwise chord identity. -/
theorem ch_sec_lt_chord {a c d : ℝ} (ha : 0 < a) (hc : 0 < c) (had : a < d) (hlc : a * d ≤ c ^ 2) :
    m2Sec a c d < 1 - (a * c / (a + c) ^ 2 + c * d / (c + d) ^ 2) / 2 := by
  have hT : 0 < a + c := by linarith
  have hW : 0 < c + d := by linarith
  have hda : 0 < d - a := by linarith
  have hd : 0 < d := by linarith
  have hden : 0 < a + d + 2 * c := by linarith
  have hden' : 0 < a + 2 * c + d := by linarith
  have hden'' : 0 < d + a + c * 2 := by linarith
  rw [m2Sec_of_ne had.ne]
  have hz : 0 < (d - a) / (a + c) := div_pos hda hT
  have hlog := Real.lt_log_one_add_of_pos hz
  rw [show 1 + (d - a) / (a + c) = (d + c) / (a + c) by field_simp; ring,
    show 2 * ((d - a) / (a + c)) / ((d - a) / (a + c) + 2) = 2 * (d - a) / (a + d + 2 * c) by
      field_simp; ring] at hlog
  have h1 : c / (d - a) * (2 * (d - a) / (a + d + 2 * c)) <
      c / (d - a) * Real.log ((d + c) / (a + c)) :=
    mul_lt_mul_of_pos_left hlog (div_pos hc hda)
  have h2 : c / (d - a) * (2 * (d - a) / (a + d + 2 * c)) = 2 * c / (a + d + 2 * c) := by
    field_simp
  rw [h2] at h1
  have key : 1 + c ^ 2 / ((a + c) * (d + c)) - 2 * c / (a + d + 2 * c) -
      (1 - (a * c / (a + c) ^ 2 + c * d / (c + d) ^ 2) / 2) =
      c * (a - d) ^ 2 * (a * d - c ^ 2) / (2 * (a + c) ^ 2 * (c + d) ^ 2 * (a + 2 * c + d)) := by
    field_simp
    ring
  have h3 : c * (a - d) ^ 2 * (a * d - c ^ 2) / (2 * (a + c) ^ 2 * (c + d) ^ 2 * (a + 2 * c + d))
      ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

/-- **Identity (5)** of `MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2, with `d = a + x`,
`e = 4 - d² - 2cd`, `r₀ = Q/W - d`: `w_{U,ch}(b*) - g_d(r₀) = -(c x/(2 a T² W² Q²)) (P₀ + e P_e)`. -/
theorem ch_gap_identity {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) (hx : 0 < x) :
    chwU a ((a ^ 2 + 4) / (a + c) - a) c (a + x)
        (1 - (a * c / (a + c) ^ 2 + c * (a + x) / (c + (a + x)) ^ 2) / 2) -
      m2g (a + x) (((a + x) ^ 2 + 4) / (c + (a + x)) - (a + x)) =
      -(c * x / (2 * a * (a + c) ^ 2 * (c + (a + x)) ^ 2 * ((a + x) ^ 2 + 4) ^ 2)) *
        ((2 * a * (a + c) ^ 5 * x + 2 * (a + c) ^ 3 * (5 * a ^ 2 + 3 * a * c + 2 * c ^ 2) * x ^ 2 +
          2 * (a + c) ^ 2 * (9 * a ^ 2 + 5 * a * c + 2 * c ^ 2) * x ^ 3 +
          (a + c) * (2 * a + c) * (7 * a + c) * x ^ 4 + a * (4 * a + 3 * c) * x ^ 5) +
        (4 - (a + x) ^ 2 - 2 * c * (a + x)) *
          ((a + c) * (2 * a * (a + c) ^ 3 + 2 * (a + c) ^ 3 * x + 4 * a * (a + c) ^ 2 * x +
            (a + c) ^ 2 * x ^ 2 + 6 * a * (a + c) * x ^ 2 + 3 * a * x ^ 3))) := by
  have hT : 0 < a + c := by linarith
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hW : 0 < c + (a + x) := by linarith
  have hQ : 0 < (a + x) ^ 2 + 4 := by positivity
  have hb1 : (a ^ 2 + 4) / (a + c) - a + a = (a ^ 2 + 4) / (a + c) := by ring
  have hb2 : a + ((a ^ 2 + 4) / (a + c) - a) = (a ^ 2 + 4) / (a + c) := by ring
  have hb3 : a + x + (((a + x) ^ 2 + 4) / (c + (a + x)) - (a + x)) =
      ((a + x) ^ 2 + 4) / (c + (a + x)) := by ring
  have hlog1 : Real.log ((a ^ 2 + 4) / (a + c) * (a + c) / (a ^ 2 + 4)) = 0 := by
    rw [show (a ^ 2 + 4) / (a + c) * (a + c) / (a ^ 2 + 4) = 1 by field_simp]
    simp
  unfold chwU m2wOf m2h m2Stat m2U m2g m2Y
  simp only [hb1, hb2, hb3]
  rw [hlog1]
  field_simp
  ring

/-- `g_d` is increasing on `[d, ∞)`: `g_d(r₀) ≤ g_d(r)` for `d ≤ r₀ ≤ r`. -/
theorem ch_gd_mono {d r₀ r : ℝ} (hd : 0 < d) (h0 : d ≤ r₀) (h1 : r₀ ≤ r) : m2g d r₀ ≤ m2g d r := by
  have hr0 : 0 < r₀ := by linarith
  have hr : 0 < r := by linarith
  have key : m2g d r - m2g d r₀ = d * (r - r₀) * (r * r₀ - d ^ 2) / ((d + r) ^ 2 * (d + r₀) ^ 2) := by
    unfold m2g
    field_simp
    ring
  have : 0 ≤ d * (r - r₀) * (r * r₀ - d ^ 2) / ((d + r) ^ 2 * (d + r₀) ^ 2) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg hd.le (by linarith))
    nlinarith
  linarith

/-- **Lemma 2** (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP` (3)): the first forward centre of the actual
smaller-nonshort window satisfies `d² + 2cd > 4`. -/
theorem ch_centre_gap (W : M2Window) : 4 < W.d ^ 2 + 2 * W.c * W.d := by
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hT : 0 < W.a + W.c := by linarith
  have hWd : 0 < W.c + W.d := by linarith
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  have hY : 0 < m2Y W.a W.c W.d := by
    unfold m2Y; nlinarith [W.a_lt_d]
  by_contra hcon
  push Not at hcon
  -- `r₀ = Q/W - d`, with `d ≤ r₀ < r`
  set r₀ := (W.d ^ 2 + 4) / (W.c + W.d) - W.d with hr₀
  have hr0d : W.d ≤ r₀ := by
    rw [hr₀, le_sub_iff_add_le, le_div_iff₀ hWd]; nlinarith
  have hr0r : r₀ ≤ W.r := by
    have : (W.d ^ 2 + 4) / (W.c + W.d) < W.d + W.r := by
      rw [div_lt_iff₀ hWd]; nlinarith [W.factor_d]
    rw [hr₀]; linarith
  have h1 : m2g W.d r₀ ≤ W.w := (ch_gd_mono hd hr0d hr0r).trans W.w_ge
  have h2 : W.w ≤ chwU W.a W.b W.c W.d W.v := by
    rw [W.w_eq, W.h_eq]
    refine ch_w_le_wU ha (by linarith [W.a_lt_b]) hY ?_
    rw [← m2g_eq_m2U (by linarith [W.a_lt_b])]; exact W.u_le
  have h3 := ch_wU_lt (v := W.v) ha W.a_lt_b hc hY W.central
  have hv := ch_sec_lt_chord ha hc W.a_lt_d W.logconc.le
  rw [← W.v_eq] at hv
  have h4 := ch_wU_v (b := (W.a ^ 2 + 4) / (W.a + W.c) - W.a) (c := W.c) (d := W.d) W.v
    (1 - (W.a * W.c / (W.a + W.c) ^ 2 + W.c * W.d / (W.c + W.d) ^ 2) / 2) ha
  have h4' : 0 < m2Y W.a W.c W.d * ((W.a ^ 2 + 4) * (W.a + W.c) / W.a + m2Y W.a W.c W.d) /
      (W.d ^ 2 + 4) ^ 2 * ((1 - (W.a * W.c / (W.a + W.c) ^ 2 + W.c * W.d / (W.c + W.d) ^ 2) / 2)
        - W.v) := mul_pos (by positivity) (by linarith)
  have h5 := ch_gap_identity ha hc (show 0 < W.d - W.a by linarith [W.a_lt_d])
  simp only [add_sub_cancel] at h5
  have h6 : 0 < (W.c * (W.d - W.a) / (2 * W.a * (W.a + W.c) ^ 2 * (W.c + W.d) ^ 2 *
      (W.d ^ 2 + 4) ^ 2)) *
        ((2 * W.a * (W.a + W.c) ^ 5 * (W.d - W.a) + 2 * (W.a + W.c) ^ 3 *
          (5 * W.a ^ 2 + 3 * W.a * W.c + 2 * W.c ^ 2) * (W.d - W.a) ^ 2 +
          2 * (W.a + W.c) ^ 2 * (9 * W.a ^ 2 + 5 * W.a * W.c + 2 * W.c ^ 2) * (W.d - W.a) ^ 3 +
          (W.a + W.c) * (2 * W.a + W.c) * (7 * W.a + W.c) * (W.d - W.a) ^ 4 +
          W.a * (4 * W.a + 3 * W.c) * (W.d - W.a) ^ 5) +
        (4 - W.d ^ 2 - 2 * W.c * W.d) *
          ((W.a + W.c) * (2 * W.a * (W.a + W.c) ^ 3 + 2 * (W.a + W.c) ^ 3 * (W.d - W.a) +
            4 * W.a * (W.a + W.c) ^ 2 * (W.d - W.a) +
            (W.a + W.c) ^ 2 * (W.d - W.a) ^ 2 + 6 * W.a * (W.a + W.c) * (W.d - W.a) ^ 2 +
            3 * W.a * (W.d - W.a) ^ 3))) := by
    have hx : 0 < W.d - W.a := by linarith [W.a_lt_d]
    have he : 0 ≤ 4 - W.d ^ 2 - 2 * W.c * W.d := by linarith
    positivity
  linarith
end SmoothedOctagon

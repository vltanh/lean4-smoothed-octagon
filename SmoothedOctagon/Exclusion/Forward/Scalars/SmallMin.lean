module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor

/-!
# Case F scalars: the small forward minimum

`SMALL_FORWARD_MINIMUM_HAND_PROOF`, `MIXED_GLOBAL_SMALL_FORWARD_MINIMUM` §§1-5 and
`HAND_H5_INTEGRAL_RATIONAL_BOUND`: at a forward window whose centre is a minimum of the five margins,
`a² > 4/3`, i.e. `U < 3`.

Route: the notes' argument, with three changes. The larger neighbour is lowered by a difference
comparison (`fs_res_le`) instead of the derivative (16); all three faces use one integral bound
(`fs_res_integral`, NEIGHBOR_INTEGRAL (9)) with the exact values at `h = 1` (`fs_res_one`,
`fs_res_slope`); the signs of `R₀, …, R₃` (H5 (12)) are proved by Bernstein expansions in
`μ = m/v`, `v` instead of the hand coefficient bounds.

## Main API

* `fs_res U z w h V`: the residual `αA - B - nF_{z/S}(h) - mV` with a free opposite floor `V`;
  `fs_res_canon`, `fs_res_integral`, `fs_res_one`, `fs_res_slope`, `fs_res_le`.
* `fs_Fw w q`: the central logarithmic term; `fs_Fw_nonpos_le`, `fs_Fw_hard` (`F(q) ≤ 0`).
* `fs_H5P`, `fs_H5P_pos`: the cubic of H5 (10) is positive; `fs_hardB`, `fs_hard_alg`: the rational
  envelope (H5 (3)) is negative.
* `fs_face_q1`, `fs_face_low`, `fs_face_hard`: the three comparison faces.
* `fs_U_lt_three`: `W.U < 3` for every `ff_Dim` window.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The residual with a free opposite floor -/

/-- The residual `𝓔 = αA - B - nF_{z/S}(h) - mV` with a free opposite floor `V`
(MIXED_GLOBAL_SMALL_FORWARD_MINIMUM (15)). -/
noncomputable def fs_res (U z w h V : ℝ) : ℝ :=
  ff_alpha U z h * ff_A U z w - ff_B U z h - ff_n U z h * ff_F (z / (1 + z)) h - ff_m U z w h * V

theorem fs_res_canon {U z w h V : ℝ} (hU : 0 < U) (hz : 0 < z) (hh : 0 < h) (hh1 : h ≠ 1) :
    fs_res U z w h V = fs_cf (fs_N0 U z (ff_A U z w) V (ff_q U z w))
      (fs_N1 U z (ff_A U z w) V (ff_q U z w))
      (-(z ^ 2 * (U - z) / (z ^ 2 + U))) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
      (z * (1 + z) * (U - z) / (z ^ 2 + U)) h := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hh1' : h - 1 ≠ 0 := sub_ne_zero.2 hh1
  unfold fs_res ff_alpha ff_B ff_n ff_m fs_cf fs_N0 fs_N1
  unfold ff_F
  generalize ff_A U z w = A
  generalize ff_q U z w = q
  generalize Real.log h = L
  field_simp
  ring

/-- `F_w(q) = (q - 1)/T + y(1 - 1/q) - log q` (HAND_FORWARD_NEIGHBOR_INTEGRAL (2)). -/
noncomputable def fs_Fw (w q : ℝ) : ℝ := (q - 1) / (1 + w) + w / (1 + w) * (1 - 1 / q) - Real.log q

/-- The value at `h = 1` of the canonical form (NEIGHBOR_INTEGRAL (7)). -/
theorem fs_res_one {U z w V : ℝ} (hU : 0 < U) (hz : 0 < z) (hw : 0 < w) :
    fs_N0 U z (ff_A U z w) V (ff_q U z w) + fs_N1 U z (ff_A U z w) V (ff_q U z w) +
      -(z ^ 2 * (U - z) / (z ^ 2 + U)) + z ^ 2 * (1 + z) / (z ^ 2 + U) =
      (1 + U) / (z ^ 2 + U) * fs_Fw w (ff_q U z w) -
        (1 + U) ^ 2 * (ff_q U z w - 1) / ((1 + z) * (z ^ 2 + U)) *
          (V - (1 - w / (1 + w) + (w / (1 + w)) ^ 2)) := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hT : 0 < 1 + w := by linarith
  have hK : 0 < 1 + U := by linarith
  have hq : 0 < ff_q U z w := by unfold ff_q; positivity
  unfold fs_N0 fs_N1 fs_Fw ff_A
  have e : ff_q U z w = (1 + z) * (1 + w) / (1 + U) := rfl
  generalize Real.log (ff_q U z w) = L
  rw [e]
  field_simp
  ring

/-- The slope at `h = 1` of the canonical form (NEIGHBOR_INTEGRAL (8)). -/
theorem fs_res_slope {U z w V : ℝ} (hU : 0 < U) (hz : 0 < z) (hw : 0 < w) :
    fs_N1 U z (ff_A U z w) V (ff_q U z w) + 2 * -(z ^ 2 * (U - z) / (z ^ 2 + U)) -
      z ^ 2 * (1 + z) / (z ^ 2 + U) + z + z * (1 + z) * (U - z) / (z ^ 2 + U) =
      (1 + z) * (1 + U) / (z ^ 2 + U) * (fs_Fw w (ff_q U z w) +
        z / (1 + z) * (ff_q U z w - 1) * (ff_q U z w / (1 + w) - w / (1 + w)) / ff_q U z w) -
        (1 + U) ^ 2 * ((1 + z) * ff_q U z w - 1) / ((1 + z) * (z ^ 2 + U)) *
          (V - (1 - w / (1 + w) + (w / (1 + w)) ^ 2)) := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hT : 0 < 1 + w := by linarith
  have hK : 0 < 1 + U := by linarith
  have hq : 0 < ff_q U z w := by unfold ff_q; positivity
  unfold fs_N1 fs_Fw ff_A
  have e : ff_q U z w = (1 + z) * (1 + w) / (1 + U) := rfl
  generalize Real.log (ff_q U z w) = L
  rw [e]
  field_simp
  ring

/-- **The integral bound** (NEIGHBOR_INTEGRAL (9), SMALL_FORWARD_MINIMUM_HAND_PROOF (7)):
`𝓔(h) ≤ 𝓔(1) + e𝓔'(1) + z²d e²/(2h) - z f(h)`, `d = S²/Z - 1`, `e = h - 1`. -/
theorem fs_res_integral {U z w h V : ℝ} (hz : 1 ≤ z) (hzU : z ≤ U) (hh : 1 < h) :
    fs_res U z w h V ≤
      (fs_N0 U z (ff_A U z w) V (ff_q U z w) + fs_N1 U z (ff_A U z w) V (ff_q U z w) +
        -(z ^ 2 * (U - z) / (z ^ 2 + U)) + z ^ 2 * (1 + z) / (z ^ 2 + U)) +
      (h - 1) * (fs_N1 U z (ff_A U z w) V (ff_q U z w) + 2 * -(z ^ 2 * (U - z) / (z ^ 2 + U)) -
        z ^ 2 * (1 + z) / (z ^ 2 + U) + z + z * (1 + z) * (U - z) / (z ^ 2 + U)) +
      z ^ 2 * ((1 + z) ^ 2 / (z ^ 2 + U) - 1) * (h - 1) ^ 2 / (2 * h) - z * ff_f h := by
  have hU : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  rw [fs_res_canon hU hz0 (by linarith) hh.ne']
  set c0 := fs_N0 U z (ff_A U z w) V (ff_q U z w)
  set c1 := fs_N1 U z (ff_A U z w) V (ff_q U z w)
  set c2 := -(z ^ 2 * (U - z) / (z ^ 2 + U))
  set cm := z ^ 2 * (1 + z) / (z ^ 2 + U)
  set d1 := z * (1 + z) * (U - z) / (z ^ 2 + U)
  set dd := (1 + z) ^ 2 / (z ^ 2 + U) - 1
  set G1 := c0 + c1 + c2 + cm
  set G1' := c1 + 2 * c2 - cm + z + d1
  have key := fs_cf_nonneg (c0 := G1 - G1' - z ^ 2 * dd - c0) (c1 := G1' + z ^ 2 * dd / 2 - z / 2 - c1)
    (c2 := -c2) (cm := z ^ 2 * dd / 2 + z / 2 - cm) (d0 := 0) (d1 := -d1) (h0 := 1) (h1 := h)
    one_pos hh.le (le_of_eq ?_) (le_of_eq ?_) ?_
  · have e : fs_cf (G1 - G1' - z ^ 2 * dd - c0) (G1' + z ^ 2 * dd / 2 - z / 2 - c1) (-c2)
        (z ^ 2 * dd / 2 + z / 2 - cm) 0 (-d1) h =
        G1 + (h - 1) * G1' + z ^ 2 * dd * (h - 1) ^ 2 / (2 * h) - z * ff_f h -
          fs_cf c0 c1 c2 cm z d1 h := by
      unfold fs_cf ff_f
      have : h ≠ 0 := by linarith
      field_simp
      ring
    linarith
  · simp only [fs_cf, Real.log_one]; ring
  · simp only [fs_cf', Real.log_one]; ring
  · intro s hs
    have hs1 : 1 ≤ s := hs.1
    have e : 2 * -c2 * s ^ 3 + 2 * (z ^ 2 * dd / 2 + z / 2 - cm) + -d1 * s ^ 2 - 0 * s =
        z * (U - z) * (s - 1) * (2 * z * (s ^ 2 + s + 1) - (1 + z) * (s + 1)) / (z ^ 2 + U) := by
      simp only [c2, cm, d1, dd]
      field_simp
      ring
    rw [e]
    apply div_nonneg _ hZ.le
    have h1 : (1 + z) * (s + 1) ≤ 2 * z * (s ^ 2 + s + 1) := by nlinarith
    have : 0 ≤ z * (U - z) * (s - 1) := mul_nonneg (mul_nonneg hz0.le (by linarith)) (by linarith)
    nlinarith

/-! ### The central logarithmic term (SMALL_FORWARD_MINIMUM_HAND_PROOF §2) -/

theorem fs_hasDerivAt_Fw (w : ℝ) {q : ℝ} (hq : 0 < q) (hw : 0 < 1 + w) :
    HasDerivAt (fs_Fw w) ((q - 1) * (q - w) / ((1 + w) * q ^ 2)) q := by
  show HasDerivAt (fun q ↦ (q - 1) / (1 + w) + w / (1 + w) * (1 - 1 / q) - Real.log q) _ q
  have h1 : HasDerivAt (fun q : ℝ ↦ (q - 1) / (1 + w)) (1 / (1 + w)) q :=
    ((hasDerivAt_id' q).sub_const 1).div_const (1 + w)
  have h2 : HasDerivAt (fun q : ℝ ↦ 1 / q) ((0 * q - 1 * 1) / q ^ 2) q :=
    (hasDerivAt_const q (1 : ℝ)).div (hasDerivAt_id' q) hq.ne'
  have h := ((h1.add ((h2.const_sub 1).const_mul (w / (1 + w)))).sub (Real.hasDerivAt_log hq.ne'))
  convert h using 1
  field_simp
  ring

/-- `F_z(q) ≤ 0` for `1 ≤ q ≤ z` (`F' = (q - 1)(q - z)/(Sq²) ≤ 0`, `F(1) = 0`). -/
theorem fs_Fw_nonpos_le {z q : ℝ} (hz : 1 ≤ z) (hq : 1 ≤ q) (hqz : q ≤ z) : fs_Fw z q ≤ 0 := by
  have key := ff_le_of_deriv (f := fun s ↦ -fs_Fw z s)
    (f' := fun s ↦ -((s - 1) * (s - z) / ((1 + z) * s ^ 2))) hq (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have : fs_Fw z 1 = 0 := by simp [fs_Fw]
    simp only [this] at key; linarith
  · exact (fs_hasDerivAt_Fw z (by linarith [hs.1]) (by linarith)).neg
  · have hs1 : 1 ≤ s := hs.1
    have : (s - 1) * (s - z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [hs.2])
    have : 0 < (1 + z) * s ^ 2 := by positivity
    rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le

/-- `F_z` increases on `[z, Q]`. -/
theorem fs_Fw_mono {z q Q : ℝ} (hz : 1 ≤ z) (hzq : z ≤ q) (hqQ : q ≤ Q) : fs_Fw z q ≤ fs_Fw z Q := by
  refine ff_le_of_deriv (f := fs_Fw z) (f' := fun s ↦ (s - 1) * (s - z) / ((1 + z) * s ^ 2)) hqQ
    (fun s hs ↦ fs_hasDerivAt_Fw z (by linarith [hs.1]) (by linarith)) (fun s hs ↦ ?_)
  have hs : z ≤ s := le_trans hzq hs.1
  have : 0 ≤ (s - 1) * (s - z) := mul_nonneg (by linarith) (by linarith)
  have : 0 < (1 + z) * s ^ 2 := by have : 0 < s := by linarith
                                   positivity
  exact div_nonneg (by linarith) this.le

/-- `F_z(S²/4) ≤ 0` for `1 ≤ z ≤ 3`. -/
theorem fs_Fw_quarter {z : ℝ} (hz : 1 ≤ z) (hz3 : z ≤ 3) : fs_Fw z ((1 + z) ^ 2 / 4) ≤ 0 := by
  have hS : 0 < 1 + z := by linarith
  have e : fs_Fw z ((1 + z) ^ 2 / 4) = (1 + z) / 4 + 1 - 2 / (1 + z) - 4 / (1 + z) ^ 2 +
      4 / (1 + z) ^ 3 - 2 * Real.log ((1 + z) / 2) := by
    unfold fs_Fw
    rw [show (1 + z) ^ 2 / 4 = ((1 + z) / 2) ^ 2 by ring, Real.log_pow]
    field_simp
    ring
  rw [e]
  have key := ff_le_of_deriv
    (f := fun S ↦ -(S / 4 + 1 - 2 / S - 4 / S ^ 2 + 4 / S ^ 3 - 2 * Real.log (S / 2)))
    (f' := fun S ↦ -((S - 6) * (S - 2) ^ 2 * (S + 2) / (4 * S ^ 4))) (lo := 2) (hi := 1 + z)
    (by linarith) (fun S hS' ↦ ?_) (fun S hS' ↦ ?_)
  · norm_num at key
    linarith
  · have hS0 : 0 < S := by linarith [hS'.1]
    have hl : HasDerivAt (fun S : ℝ ↦ Real.log (S / 2)) (1 / 2 / (S / 2)) S :=
      ((hasDerivAt_id' S).div_const 2).log (by positivity)
    have hd : ∀ (n : ℕ) (c : ℝ), HasDerivAt (fun S : ℝ ↦ c / S ^ n)
        ((0 * S ^ n - c * (n * S ^ (n - 1))) / (S ^ n) ^ 2) S := fun n c ↦
      (hasDerivAt_const S c).div (hasDerivAt_pow n S) (pow_ne_zero n hS0.ne')
    have h1 : HasDerivAt (fun S : ℝ ↦ 2 / S) ((0 * S - 2 * 1) / S ^ 2) S :=
      (hasDerivAt_const S (2 : ℝ)).div (hasDerivAt_id' S) hS0.ne'
    have h := (((((((hasDerivAt_id' S).div_const 4).add_const 1).sub h1).sub (hd 2 4)).add
      (hd 3 4)).sub (hl.const_mul 2)).neg
    convert h using 1
    push_cast
    field_simp
    ring
  · have hS2 : 2 ≤ S := hS'.1
    have hS4 : S ≤ 4 := by linarith [hS'.2]
    have : (S - 6) * (S - 2) ^ 2 * (S + 2) ≤ 0 := by
      have : 0 ≤ (S - 2) ^ 2 * (S + 2) := by positivity
      nlinarith
    have : 0 < 4 * S ^ 4 := by positivity
    rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le

/-- `F_z(S) ≤ 0` for `z ≥ 3`. -/
theorem fs_Fw_S {z : ℝ} (hz : 3 ≤ z) : fs_Fw z (1 + z) ≤ 0 := by
  have hS : 0 < 1 + z := by linarith
  have e : fs_Fw z (1 + z) = (1 + z - 1) / (1 + z) + ((1 + z - 1) / (1 + z)) ^ 2 - Real.log (1 + z) := by
    unfold fs_Fw; field_simp; ring
  rw [e]
  have key := ff_le_of_deriv (f := fun S ↦ -((S - 1) / S + ((S - 1) / S) ^ 2 - Real.log S))
    (f' := fun S ↦ (S - 1) * (S - 2) / S ^ 3) (lo := 4) (hi := 1 + z)
    (by linarith) (fun S hS' ↦ ?_) (fun S hS' ↦ ?_)
  · have h4 : (4 - 1) / 4 + ((4 - 1) / 4) ^ 2 - Real.log 4 < (0 : ℝ) := by
      have := Real.log_two_gt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      linarith
    linarith
  · have hS0 : 0 < S := by linarith [hS'.1]
    have hq : HasDerivAt (fun S : ℝ ↦ (S - 1) / S) ((1 * S - (S - 1) * 1) / S ^ 2) S :=
      ((hasDerivAt_id' S).sub_const 1).div (hasDerivAt_id' S) hS0.ne'
    have h := ((hq.add (hq.pow 2)).sub (Real.hasDerivAt_log hS0.ne')).neg
    convert h using 1
    push_cast
    field_simp
    ring
  · have : 4 ≤ S := hS'.1
    have : 0 < S := by linarith
    have : 0 ≤ (S - 1) * (S - 2) := mul_nonneg (by linarith) (by linarith)
    positivity

/-- **`F(q) ≤ 0` on the hard face** (SMALL_FORWARD_MINIMUM_HAND_PROOF (4)): for `U ≥ 3`, `1 ≤ z < U`. -/
theorem fs_Fw_hard {U z : ℝ} (hU : 3 ≤ U) (hzU : z < U) (hz : 1 ≤ z) :
    fs_Fw z ((1 + z) * (1 + z) / (1 + U)) ≤ 0 := by
  have hK : 0 < 1 + U := by linarith
  have hS : 0 < 1 + z := by linarith
  set q := (1 + z) * (1 + z) / (1 + U) with hq
  have hq1 : 0 < q := by positivity
  have hq4 : q ≤ (1 + z) ^ 2 / 4 := by
    rw [hq, div_le_div_iff₀ hK (by norm_num)]; nlinarith
  have hqS : q ≤ 1 + z := by
    rw [hq, div_le_iff₀ hK]; nlinarith
  by_cases hqz : q ≤ z
  · by_cases hq1' : 1 ≤ q
    · exact fs_Fw_nonpos_le hz hq1' hqz
    · -- `q < 1`: `F` decreasing from `q` to `1`
      push Not at hq1'
      have key := ff_le_of_deriv (f := fs_Fw z) (f' := fun s ↦ (s - 1) * (s - z) / ((1 + z) * s ^ 2))
        hq1'.le (fun s hs ↦ fs_hasDerivAt_Fw z (by linarith [hs.1]) (by linarith)) (fun s hs ↦ ?_)
      · have : fs_Fw z 1 = 0 := by simp [fs_Fw]
        linarith
      · have hs0 : 0 < s := by linarith [hs.1]
        have : 0 ≤ (s - 1) * (s - z) := mul_nonneg_of_nonpos_of_nonpos (by linarith [hs.2])
          (by linarith [hs.2])
        positivity
  · push Not at hqz
    rcases le_total z 3 with hz3 | hz3
    · exact le_trans (fs_Fw_mono hz hqz.le hq4) (fs_Fw_quarter hz hz3)
    · exact le_trans (fs_Fw_mono hz hqz.le hqS) (fs_Fw_S hz3)

/-! ### The cubic `P` (H5 (10)-(19)) -/

theorem fs_H5_R3 {m v : ℝ} (hm : 0 ≤ m) (hmv : m ≤ v) (hv1 : v ≤ 1) :
    0 ≤ -(3) * m ^ (2:ℕ) * v - (3) * m ^ (2:ℕ) - (3) * m * v ^ (2:ℕ) + (6) * m + (6) * v := by
  have b1 : 0 ≤ m := hm
  have b2 : 0 ≤ v - m := by linarith
  have b3 : 0 ≤ v := by linarith
  have b4 : 0 ≤ 1 - v := by linarith
  have key : v ^ 1 * (-(3) * m ^ (2:ℕ) * v - (3) * m ^ (2:ℕ) - (3) * m * v ^ (2:ℕ) + (6) * m + (6) * v) =
      (6) * (v - m) ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (12) * (v - m) ^ (2:ℕ) * v * (1 - v) +
      (6) * (v - m) ^ (2:ℕ) * v ^ (2:ℕ) +
      (18) * m * (v - m) * (1 - v) ^ (2:ℕ) +
      (36) * m * (v - m) * v * (1 - v) +
      (15) * m * (v - m) * v ^ (2:ℕ) +
      (12) * m ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (21) * m ^ (2:ℕ) * v * (1 - v) +
      (3) * m ^ (2:ℕ) * v ^ (2:ℕ) := by ring
  have h : 0 ≤ v ^ 1 * (-(3) * m ^ (2:ℕ) * v - (3) * m ^ (2:ℕ) - (3) * m * v ^ (2:ℕ) + (6) * m + (6) * v) := by rw [key]; clear key; positivity
  rcases eq_or_lt_of_le b3 with hv0 | hv0
  · have hm0 : m = 0 := by linarith
    subst hm0; rw [← hv0]; norm_num
  · exact nonneg_of_mul_nonneg_right (by linarith [h]) (pow_pos hv0 1)

theorem fs_H5_R2 {m v : ℝ} (hm : 0 ≤ m) (hmv : m ≤ v) (hv1 : v ≤ 1) :
    0 ≤ m ^ (4:ℕ) * v + (4) * m ^ (4:ℕ) - (3) * m ^ (3:ℕ) * v ^ (2:ℕ) - (13) * m ^ (3:ℕ) * v - (28) * m ^ (3:ℕ) + (3) * m ^ (2:ℕ) * v ^ (2:ℕ) - (14) * m ^ (2:ℕ) * v + (28) * m ^ (2:ℕ) - m * v ^ (3:ℕ) - (30) * m * v ^ (2:ℕ) + (24) * m * v + (24) * m + (2) * v ^ (3:ℕ) + (24) * v := by
  have b1 : 0 ≤ m := hm
  have b2 : 0 ≤ v - m := by linarith
  have b3 : 0 ≤ v := by linarith
  have b4 : 0 ≤ 1 - v := by linarith
  have key : v ^ 3 * (m ^ (4:ℕ) * v + (4) * m ^ (4:ℕ) - (3) * m ^ (3:ℕ) * v ^ (2:ℕ) - (13) * m ^ (3:ℕ) * v - (28) * m ^ (3:ℕ) + (3) * m ^ (2:ℕ) * v ^ (2:ℕ) - (14) * m ^ (2:ℕ) * v + (28) * m ^ (2:ℕ) - m * v ^ (3:ℕ) - (30) * m * v ^ (2:ℕ) + (24) * m * v + (24) * m + (2) * v ^ (3:ℕ) + (24) * v) =
      (24) * (v - m) ^ (4:ℕ) * (1 - v) ^ (4:ℕ) +
      (96) * (v - m) ^ (4:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (146) * (v - m) ^ (4:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (100) * (v - m) ^ (4:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (26) * (v - m) ^ (4:ℕ) * v ^ (4:ℕ) +
      (120) * m * (v - m) ^ (3:ℕ) * (1 - v) ^ (4:ℕ) +
      (504) * m * (v - m) ^ (3:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (770) * m * (v - m) ^ (3:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (507) * m * (v - m) ^ (3:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (121) * m * (v - m) ^ (3:ℕ) * v ^ (4:ℕ) +
      (216) * m ^ (2:ℕ) * (v - m) ^ (2:ℕ) * (1 - v) ^ (4:ℕ) +
      (964) * m ^ (2:ℕ) * (v - m) ^ (2:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (1504) * m ^ (2:ℕ) * (v - m) ^ (2:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (980) * m ^ (2:ℕ) * (v - m) ^ (2:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (224) * m ^ (2:ℕ) * (v - m) ^ (2:ℕ) * v ^ (4:ℕ) +
      (168) * m ^ (3:ℕ) * (v - m) * (1 - v) ^ (4:ℕ) +
      (800) * m ^ (3:ℕ) * (v - m) * v * (1 - v) ^ (3:ℕ) +
      (1254) * m ^ (3:ℕ) * (v - m) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (770) * m ^ (3:ℕ) * (v - m) * v ^ (3:ℕ) * (1 - v) +
      (145) * m ^ (3:ℕ) * (v - m) * v ^ (4:ℕ) +
      (48) * m ^ (4:ℕ) * (1 - v) ^ (4:ℕ) +
      (244) * m ^ (4:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (374) * m ^ (4:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (201) * m ^ (4:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (21) * m ^ (4:ℕ) * v ^ (4:ℕ) := by ring
  have h : 0 ≤ v ^ 3 * (m ^ (4:ℕ) * v + (4) * m ^ (4:ℕ) - (3) * m ^ (3:ℕ) * v ^ (2:ℕ) - (13) * m ^ (3:ℕ) * v - (28) * m ^ (3:ℕ) + (3) * m ^ (2:ℕ) * v ^ (2:ℕ) - (14) * m ^ (2:ℕ) * v + (28) * m ^ (2:ℕ) - m * v ^ (3:ℕ) - (30) * m * v ^ (2:ℕ) + (24) * m * v + (24) * m + (2) * v ^ (3:ℕ) + (24) * v) := by rw [key]; clear key; positivity
  rcases eq_or_lt_of_le b3 with hv0 | hv0
  · have hm0 : m = 0 := by linarith
    subst hm0; rw [← hv0]; norm_num
  · exact nonneg_of_mul_nonneg_right (by linarith [h]) (pow_pos hv0 3)

theorem fs_H5_R1 {m v : ℝ} (hm : 0 ≤ m) (hmv : m ≤ v) (hv1 : v ≤ 1) :
    0 ≤ -m ^ (6:ℕ) + (7) * m ^ (5:ℕ) * v + (14) * m ^ (5:ℕ) - (3) * m ^ (4:ℕ) * v ^ (2:ℕ) - (46) * m ^ (4:ℕ) * v - (40) * m ^ (4:ℕ) - (2) * m ^ (3:ℕ) * v ^ (3:ℕ) - (12) * m ^ (3:ℕ) * v ^ (2:ℕ) + (40) * m ^ (3:ℕ) * v - (48) * m ^ (3:ℕ) + (8) * m ^ (2:ℕ) * v ^ (3:ℕ) + (12) * m ^ (2:ℕ) * v ^ (2:ℕ) - (96) * m ^ (2:ℕ) * v + (160) * m ^ (2:ℕ) - (16) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (144) * m * v + (16) * v ^ (3:ℕ) := by
  have b1 : 0 ≤ m := hm
  have b2 : 0 ≤ v - m := by linarith
  have b3 : 0 ≤ v := by linarith
  have b4 : 0 ≤ 1 - v := by linarith
  have key : v ^ 4 * (-m ^ (6:ℕ) + (7) * m ^ (5:ℕ) * v + (14) * m ^ (5:ℕ) - (3) * m ^ (4:ℕ) * v ^ (2:ℕ) - (46) * m ^ (4:ℕ) * v - (40) * m ^ (4:ℕ) - (2) * m ^ (3:ℕ) * v ^ (3:ℕ) - (12) * m ^ (3:ℕ) * v ^ (2:ℕ) + (40) * m ^ (3:ℕ) * v - (48) * m ^ (3:ℕ) + (8) * m ^ (2:ℕ) * v ^ (3:ℕ) + (12) * m ^ (2:ℕ) * v ^ (2:ℕ) - (96) * m ^ (2:ℕ) * v + (160) * m ^ (2:ℕ) - (16) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (144) * m * v + (16) * v ^ (3:ℕ)) =
      (16) * (v - m) ^ (6:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (48) * (v - m) ^ (6:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (48) * (v - m) ^ (6:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (16) * (v - m) ^ (6:ℕ) * v ^ (4:ℕ) +
      (144) * m * (v - m) ^ (5:ℕ) * (1 - v) ^ (4:ℕ) +
      (576) * m * (v - m) ^ (5:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (848) * m * (v - m) ^ (5:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (544) * m * (v - m) ^ (5:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (128) * m * (v - m) ^ (5:ℕ) * v ^ (4:ℕ) +
      (880) * m ^ (2:ℕ) * (v - m) ^ (4:ℕ) * (1 - v) ^ (4:ℕ) +
      (3184) * m ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (4204) * m ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (2384) * m ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (484) * m ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (4:ℕ) +
      (2080) * m ^ (3:ℕ) * (v - m) ^ (3:ℕ) * (1 - v) ^ (4:ℕ) +
      (7248) * m ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (9192) * m ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (4980) * m ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (954) * m ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (4:ℕ) +
      (2400) * m ^ (4:ℕ) * (v - m) ^ (2:ℕ) * (1 - v) ^ (4:ℕ) +
      (8160) * m ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (10072) * m ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (5230) * m ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (909) * m ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (4:ℕ) +
      (1360) * m ^ (5:ℕ) * (v - m) * (1 - v) ^ (4:ℕ) +
      (4528) * m ^ (5:ℕ) * (v - m) * v * (1 - v) ^ (3:ℕ) +
      (5432) * m ^ (5:ℕ) * (v - m) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (2638) * m ^ (5:ℕ) * (v - m) * v ^ (3:ℕ) * (1 - v) +
      (369) * m ^ (5:ℕ) * (v - m) * v ^ (4:ℕ) +
      (304) * m ^ (6:ℕ) * (1 - v) ^ (4:ℕ) +
      (992) * m ^ (6:ℕ) * v * (1 - v) ^ (3:ℕ) +
      (1148) * m ^ (6:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (2:ℕ) +
      (500) * m ^ (6:ℕ) * v ^ (3:ℕ) * (1 - v) +
      (41) * m ^ (6:ℕ) * v ^ (4:ℕ) := by ring
  have h : 0 ≤ v ^ 4 * (-m ^ (6:ℕ) + (7) * m ^ (5:ℕ) * v + (14) * m ^ (5:ℕ) - (3) * m ^ (4:ℕ) * v ^ (2:ℕ) - (46) * m ^ (4:ℕ) * v - (40) * m ^ (4:ℕ) - (2) * m ^ (3:ℕ) * v ^ (3:ℕ) - (12) * m ^ (3:ℕ) * v ^ (2:ℕ) + (40) * m ^ (3:ℕ) * v - (48) * m ^ (3:ℕ) + (8) * m ^ (2:ℕ) * v ^ (3:ℕ) + (12) * m ^ (2:ℕ) * v ^ (2:ℕ) - (96) * m ^ (2:ℕ) * v + (160) * m ^ (2:ℕ) - (16) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (144) * m * v + (16) * v ^ (3:ℕ)) := by rw [key]; clear key; positivity
  rcases eq_or_lt_of_le b3 with hv0 | hv0
  · have hm0 : m = 0 := by linarith
    subst hm0; rw [← hv0]; norm_num
  · exact nonneg_of_mul_nonneg_right (by linarith [h]) (pow_pos hv0 4)

theorem fs_H5_R0 {m v : ℝ} (hm : 0 ≤ m) (hmv : m ≤ v) (hv1 : v ≤ 1) (hv : 0 < v) :
    0 < (6) * m ^ (6:ℕ) * v - (4) * m ^ (6:ℕ) - m ^ (5:ℕ) * v ^ (3:ℕ) - (32) * m ^ (5:ℕ) * v + (56) * m ^ (5:ℕ) + (6) * m ^ (4:ℕ) * v ^ (3:ℕ) - (12) * m ^ (4:ℕ) * v ^ (2:ℕ) + (40) * m ^ (4:ℕ) * v - (224) * m ^ (4:ℕ) - (20) * m ^ (3:ℕ) * v ^ (3:ℕ) - (112) * m ^ (3:ℕ) * v + (256) * m ^ (3:ℕ) + (40) * m ^ (2:ℕ) * v ^ (3:ℕ) + (128) * m ^ (2:ℕ) * v - (48) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (32) * v ^ (3:ℕ) := by
  have b3 : 0 ≤ v := hv.le
  have b4 : 0 ≤ 1 - v := by linarith
  have h : 0 ≤ v ^ 3 * ((6) * m ^ (6:ℕ) * v - (4) * m ^ (6:ℕ) - m ^ (5:ℕ) * v ^ (3:ℕ) - (32) * m ^ (5:ℕ) * v + (56) * m ^ (5:ℕ) + (6) * m ^ (4:ℕ) * v ^ (3:ℕ) - (12) * m ^ (4:ℕ) * v ^ (2:ℕ) + (40) * m ^ (4:ℕ) * v - (224) * m ^ (4:ℕ) - (20) * m ^ (3:ℕ) * v ^ (3:ℕ) - (112) * m ^ (3:ℕ) * v + (256) * m ^ (3:ℕ) + (40) * m ^ (2:ℕ) * v ^ (3:ℕ) + (128) * m ^ (2:ℕ) * v - (48) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (32) * v ^ (3:ℕ)) - 3 * v ^ 6 := by
    rcases le_total (2 * m) v with hs | hs
    · have b1 : 0 ≤ m := hm
      have b2 : 0 ≤ 1 / 2 * v - m := by linarith
      have key : v ^ 3 * ((6) * m ^ (6:ℕ) * v - (4) * m ^ (6:ℕ) - m ^ (5:ℕ) * v ^ (3:ℕ) - (32) * m ^ (5:ℕ) * v + (56) * m ^ (5:ℕ) + (6) * m ^ (4:ℕ) * v ^ (3:ℕ) - (12) * m ^ (4:ℕ) * v ^ (2:ℕ) + (40) * m ^ (4:ℕ) * v - (224) * m ^ (4:ℕ) - (20) * m ^ (3:ℕ) * v ^ (3:ℕ) - (112) * m ^ (3:ℕ) * v + (256) * m ^ (3:ℕ) + (40) * m ^ (2:ℕ) * v ^ (3:ℕ) + (128) * m ^ (2:ℕ) * v - (48) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (32) * v ^ (3:ℕ)) - 3 * v ^ 6 =
          (1856) * (1 / 2 * v - m) ^ (6:ℕ) * (1 - v) ^ (5:ℕ) +
      (9280) * (1 / 2 * v - m) ^ (6:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (18560) * (1 / 2 * v - m) ^ (6:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (18560) * (1 / 2 * v - m) ^ (6:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (9280) * (1 / 2 * v - m) ^ (6:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (1856) * (1 / 2 * v - m) ^ (6:ℕ) * v ^ (5:ℕ) +
      (8064) * m * (1 / 2 * v - m) ^ (5:ℕ) * (1 - v) ^ (5:ℕ) +
      (38784) * m * (1 / 2 * v - m) ^ (5:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (74496) * m * (1 / 2 * v - m) ^ (5:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (71424) * m * (1 / 2 * v - m) ^ (5:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (34176) * m * (1 / 2 * v - m) ^ (5:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (6528) * m * (1 / 2 * v - m) ^ (5:ℕ) * v ^ (5:ℕ) +
      (14528) * m ^ (2:ℕ) * (1 / 2 * v - m) ^ (4:ℕ) * (1 - v) ^ (5:ℕ) +
      (64960) * m ^ (2:ℕ) * (1 / 2 * v - m) ^ (4:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (115200) * m ^ (2:ℕ) * (1 / 2 * v - m) ^ (4:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (101120) * m ^ (2:ℕ) * (1 / 2 * v - m) ^ (4:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (43840) * m ^ (2:ℕ) * (1 / 2 * v - m) ^ (4:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (7488) * m ^ (2:ℕ) * (1 / 2 * v - m) ^ (4:ℕ) * v ^ (5:ℕ) +
      (16640) * m ^ (3:ℕ) * (1 / 2 * v - m) ^ (3:ℕ) * (1 - v) ^ (5:ℕ) +
      (66944) * m ^ (3:ℕ) * (1 / 2 * v - m) ^ (3:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (103936) * m ^ (3:ℕ) * (1 / 2 * v - m) ^ (3:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (76384) * m ^ (3:ℕ) * (1 / 2 * v - m) ^ (3:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (25536) * m ^ (3:ℕ) * (1 / 2 * v - m) ^ (3:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (2784) * m ^ (3:ℕ) * (1 / 2 * v - m) ^ (3:ℕ) * v ^ (5:ℕ) +
      (15552) * m ^ (4:ℕ) * (1 / 2 * v - m) ^ (2:ℕ) * (1 - v) ^ (5:ℕ) +
      (58816) * m ^ (4:ℕ) * (1 / 2 * v - m) ^ (2:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (83744) * m ^ (4:ℕ) * (1 / 2 * v - m) ^ (2:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (53328) * m ^ (4:ℕ) * (1 / 2 * v - m) ^ (2:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (12952) * m ^ (4:ℕ) * (1 / 2 * v - m) ^ (2:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (104) * m ^ (4:ℕ) * (1 / 2 * v - m) ^ (2:ℕ) * v ^ (5:ℕ) +
      (10112) * m ^ (5:ℕ) * (1 / 2 * v - m) * (1 - v) ^ (5:ℕ) +
      (38400) * m ^ (5:ℕ) * (1 / 2 * v - m) * v * (1 - v) ^ (4:ℕ) +
      (55472) * m ^ (5:ℕ) * (1 / 2 * v - m) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (36496) * m ^ (5:ℕ) * (1 / 2 * v - m) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (9664) * m ^ (5:ℕ) * (1 / 2 * v - m) * v ^ (4:ℕ) * (1 - v) +
      (350) * m ^ (5:ℕ) * (1 / 2 * v - m) * v ^ (5:ℕ) +
      (2880) * m ^ (6:ℕ) * (1 - v) ^ (5:ℕ) +
      (11072) * m ^ (6:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (16400) * m ^ (6:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (11292) * m ^ (6:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (3302) * m ^ (6:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (216) * m ^ (6:ℕ) * v ^ (5:ℕ) := by ring
      rw [key]; clear key; positivity
    · have b1 : 0 ≤ m - 1 / 2 * v := by linarith
      have b2 : 0 ≤ v - m := by linarith
      have key : v ^ 3 * ((6) * m ^ (6:ℕ) * v - (4) * m ^ (6:ℕ) - m ^ (5:ℕ) * v ^ (3:ℕ) - (32) * m ^ (5:ℕ) * v + (56) * m ^ (5:ℕ) + (6) * m ^ (4:ℕ) * v ^ (3:ℕ) - (12) * m ^ (4:ℕ) * v ^ (2:ℕ) + (40) * m ^ (4:ℕ) * v - (224) * m ^ (4:ℕ) - (20) * m ^ (3:ℕ) * v ^ (3:ℕ) - (112) * m ^ (3:ℕ) * v + (256) * m ^ (3:ℕ) + (40) * m ^ (2:ℕ) * v ^ (3:ℕ) + (128) * m ^ (2:ℕ) * v - (48) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (32) * v ^ (3:ℕ)) - 3 * v ^ 6 =
          (2880) * (v - m) ^ (6:ℕ) * (1 - v) ^ (5:ℕ) +
      (11072) * (v - m) ^ (6:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (16400) * (v - m) ^ (6:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (11292) * (v - m) ^ (6:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (3302) * (v - m) ^ (6:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (216) * (v - m) ^ (6:ℕ) * v ^ (5:ℕ) +
      (24448) * (m - 1 / 2 * v) * (v - m) ^ (5:ℕ) * (1 - v) ^ (5:ℕ) +
      (94464) * (m - 1 / 2 * v) * (v - m) ^ (5:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (141328) * (m - 1 / 2 * v) * (v - m) ^ (5:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (99008) * (m - 1 / 2 * v) * (v - m) ^ (5:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (29960) * (m - 1 / 2 * v) * (v - m) ^ (5:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (2242) * (m - 1 / 2 * v) * (v - m) ^ (5:ℕ) * v ^ (5:ℕ) +
      (87232) * (m - 1 / 2 * v) ^ (2:ℕ) * (v - m) ^ (4:ℕ) * (1 - v) ^ (5:ℕ) +
      (339136) * (m - 1 / 2 * v) ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (513024) * (m - 1 / 2 * v) ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (365888) * (m - 1 / 2 * v) ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (114432) * (m - 1 / 2 * v) ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (9564) * (m - 1 / 2 * v) ^ (2:ℕ) * (v - m) ^ (4:ℕ) * v ^ (5:ℕ) +
      (164096) * (m - 1 / 2 * v) ^ (3:ℕ) * (v - m) ^ (3:ℕ) * (1 - v) ^ (5:ℕ) +
      (639104) * (m - 1 / 2 * v) ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (971136) * (m - 1 / 2 * v) ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (697120) * (m - 1 / 2 * v) ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (219840) * (m - 1 / 2 * v) ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (18608) * (m - 1 / 2 * v) ^ (3:ℕ) * (v - m) ^ (3:ℕ) * v ^ (5:ℕ) +
      (170176) * (m - 1 / 2 * v) ^ (4:ℕ) * (v - m) ^ (2:ℕ) * (1 - v) ^ (5:ℕ) +
      (660160) * (m - 1 / 2 * v) ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (999680) * (m - 1 / 2 * v) ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (713088) * (m - 1 / 2 * v) ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (220832) * (m - 1 / 2 * v) ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (17120) * (m - 1 / 2 * v) ^ (4:ℕ) * (v - m) ^ (2:ℕ) * v ^ (5:ℕ) +
      (92032) * (m - 1 / 2 * v) ^ (5:ℕ) * (v - m) * (1 - v) ^ (5:ℕ) +
      (353664) * (m - 1 / 2 * v) ^ (5:ℕ) * (v - m) * v * (1 - v) ^ (4:ℕ) +
      (529920) * (m - 1 / 2 * v) ^ (5:ℕ) * (v - m) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (371328) * (m - 1 / 2 * v) ^ (5:ℕ) * (v - m) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (110080) * (m - 1 / 2 * v) ^ (5:ℕ) * (v - m) * v ^ (4:ℕ) * (1 - v) +
      (6816) * (m - 1 / 2 * v) ^ (5:ℕ) * (v - m) * v ^ (5:ℕ) +
      (20288) * (m - 1 / 2 * v) ^ (6:ℕ) * (1 - v) ^ (5:ℕ) +
      (76864) * (m - 1 / 2 * v) ^ (6:ℕ) * v * (1 - v) ^ (4:ℕ) +
      (113280) * (m - 1 / 2 * v) ^ (6:ℕ) * v ^ (2:ℕ) * (1 - v) ^ (3:ℕ) +
      (77184) * (m - 1 / 2 * v) ^ (6:ℕ) * v ^ (3:ℕ) * (1 - v) ^ (2:ℕ) +
      (21312) * (m - 1 / 2 * v) ^ (6:ℕ) * v ^ (4:ℕ) * (1 - v) +
      (768) * (m - 1 / 2 * v) ^ (6:ℕ) * v ^ (5:ℕ) := by ring
      rw [key]; clear key; positivity
  have h3 : 0 < 3 * v ^ 6 := by positivity
  have h4 : 0 < v ^ 3 * ((6) * m ^ (6:ℕ) * v - (4) * m ^ (6:ℕ) - m ^ (5:ℕ) * v ^ (3:ℕ) - (32) * m ^ (5:ℕ) * v + (56) * m ^ (5:ℕ) + (6) * m ^ (4:ℕ) * v ^ (3:ℕ) - (12) * m ^ (4:ℕ) * v ^ (2:ℕ) + (40) * m ^ (4:ℕ) * v - (224) * m ^ (4:ℕ) - (20) * m ^ (3:ℕ) * v ^ (3:ℕ) - (112) * m ^ (3:ℕ) * v + (256) * m ^ (3:ℕ) + (40) * m ^ (2:ℕ) * v ^ (3:ℕ) + (128) * m ^ (2:ℕ) * v - (48) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (32) * v ^ (3:ℕ)) := by linarith
  exact pos_of_mul_pos_right h4 (pow_pos hv 3).le

/-- The cubic `P` of HAND_H5_INTEGRAL_RATIONAL_BOUND (10), with `l = λ`. -/
noncomputable def fs_H5P (z l v : ℝ) : ℝ :=
  (z + l) ^ 2 * v ^ 3 - 3 * z * (1 - l) * (1 + z) * (z + l) * v ^ 2 +
    ((1 + l) * (1 - l) * (1 + z) * z * (3 * (z - 1) + (1 - l)) - 6 * (z + l) * (z - l) * (1 - z * l)) * v +
    (1 + l) * (1 - l) * (1 + z) * (3 * (z - 1) + (1 - l)) * (z - l)

/-- **`P > 0`** (H5_INTEGRAL_RATIONAL_BOUND §§3-4): `(2 - m)³P = R₀ + R₁p + R₂p² + R₃p³`,
`m = 1 - λ`, `p = (2 - m)z - (2 + m) = U - 3`. -/
theorem fs_H5P_pos {z l v : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hvm : 1 - l ≤ v) (hv1 : v ≤ 1)
    (hv0 : 0 < v) (hp : 0 ≤ (1 + l) * z - (3 - l)) : 0 < fs_H5P z l v := by
  obtain ⟨m, rfl⟩ : ∃ m, l = 1 - m := ⟨1 - l, by ring⟩
  have hm0 : 0 ≤ m := by linarith
  have hmv : m ≤ v := by linarith
  have h0 := fs_H5_R0 hm0 hmv hv1 hv0
  have h1 := fs_H5_R1 hm0 hmv hv1
  have h2 := fs_H5_R2 hm0 hmv hv1
  have h3 := fs_H5_R3 hm0 hmv hv1
  have key : (2 - m) ^ 3 * fs_H5P z (1 - m) v =
      ((6) * m ^ (6:ℕ) * v - (4) * m ^ (6:ℕ) - m ^ (5:ℕ) * v ^ (3:ℕ) - (32) * m ^ (5:ℕ) * v + (56) * m ^ (5:ℕ) + (6) * m ^ (4:ℕ) * v ^ (3:ℕ) - (12) * m ^ (4:ℕ) * v ^ (2:ℕ) + (40) * m ^ (4:ℕ) * v - (224) * m ^ (4:ℕ) - (20) * m ^ (3:ℕ) * v ^ (3:ℕ) - (112) * m ^ (3:ℕ) * v + (256) * m ^ (3:ℕ) + (40) * m ^ (2:ℕ) * v ^ (3:ℕ) + (128) * m ^ (2:ℕ) * v - (48) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (32) * v ^ (3:ℕ)) + (-m ^ (6:ℕ) + (7) * m ^ (5:ℕ) * v + (14) * m ^ (5:ℕ) - (3) * m ^ (4:ℕ) * v ^ (2:ℕ) - (46) * m ^ (4:ℕ) * v - (40) * m ^ (4:ℕ) - (2) * m ^ (3:ℕ) * v ^ (3:ℕ) - (12) * m ^ (3:ℕ) * v ^ (2:ℕ) + (40) * m ^ (3:ℕ) * v - (48) * m ^ (3:ℕ) + (8) * m ^ (2:ℕ) * v ^ (3:ℕ) + (12) * m ^ (2:ℕ) * v ^ (2:ℕ) - (96) * m ^ (2:ℕ) * v + (160) * m ^ (2:ℕ) - (16) * m * v ^ (3:ℕ) - (96) * m * v ^ (2:ℕ) + (144) * m * v + (16) * v ^ (3:ℕ)) * ((2 - m) * z - (2 + m)) +
      (m ^ (4:ℕ) * v + (4) * m ^ (4:ℕ) - (3) * m ^ (3:ℕ) * v ^ (2:ℕ) - (13) * m ^ (3:ℕ) * v - (28) * m ^ (3:ℕ) + (3) * m ^ (2:ℕ) * v ^ (2:ℕ) - (14) * m ^ (2:ℕ) * v + (28) * m ^ (2:ℕ) - m * v ^ (3:ℕ) - (30) * m * v ^ (2:ℕ) + (24) * m * v + (24) * m + (2) * v ^ (3:ℕ) + (24) * v) * ((2 - m) * z - (2 + m)) ^ 2 +
      (-(3) * m ^ (2:ℕ) * v - (3) * m ^ (2:ℕ) - (3) * m * v ^ (2:ℕ) + (6) * m + (6) * v) * ((2 - m) * z - (2 + m)) ^ 3 := by
    unfold fs_H5P; ring
  have hp' : 0 ≤ (2 - m) * z - (2 + m) := by linarith
  have hpos : 0 < (2 - m) ^ 3 * fs_H5P z (1 - m) v := by
    rw [key]
    have := mul_nonneg h1 hp'
    have := mul_nonneg h2 (pow_nonneg hp' 2)
    have := mul_nonneg h3 (pow_nonneg hp' 3)
    linarith
  exact pos_of_mul_pos_right hpos (by have : 0 < 2 - m := by linarith
                                      positivity)

/-! ### The hard face: the rational envelope (HAND_H5_INTEGRAL_RATIONAL_BOUND) -/

/-- The rational envelope `𝓑` of H5_INTEGRAL_RATIONAL_BOUND (3), in the quantities `S, Z, K, q, x, d`. -/
noncomputable def fs_hardB (S Z K q x d h z : ℝ) : ℝ :=
  (h - 1) * (S * K / Z) * x * (q - 1) * (q / S - x) / q -
    K ^ 2 / (S * Z) * (q - 1 + (h - 1) * (S * q - 1)) *
      (x * (x - 1 / 2) * d + x * d ^ 2 / (3 * (d + 2))) +
    z ^ 2 * d * (h - 1) ^ 2 / (2 * h) - z * (h - 1) ^ 3 / (3 * h * (h + 1))

/-- **The H5 integral bound is negative** (H5_INTEGRAL_RATIONAL_BOUND, Theorem), in the coordinates
`m = 1 - λ = (2z + 1 - U)/S`: `Z = S(S - m)`, `K = S(2 - m)`, `q = S/(2 - m)`, `d = m/(S - m)`. -/
theorem fs_hard_alg {z m h : ℝ} (hz : 1 ≤ z) (hm0 : 0 < m) (hm1 : m < 1)
    (hp : 3 ≤ 2 * z + 1 - m * (1 + z)) (hhl : (1 + z) / (1 + z - m) ≤ h) (hhu : h ≤ (1 + z) / z)
    (hh1 : 1 < h) (hq : 1 ≤ (1 + z) / (2 - m)) :
    fs_hardB (1 + z) ((1 + z) * (1 + z - m)) ((1 + z) * (2 - m)) ((1 + z) / (2 - m)) (z / (1 + z))
      (m / (1 + z - m)) h z < 0 := by
  have hS : 0 < 1 + z := by linarith
  have hSm : 0 < 1 + z - m := by linarith
  have h2m : 0 < 2 - m := by linarith
  have h2Sm : 0 < 2 * (1 + z) - m := by linarith
  have hh0 : 0 < h := by linarith
  have hz0 : 0 < z := by linarith
  -- the floor weakening `Δ₀ ≥ Δ̄`
  have hD : z * m * (3 * (z - 1) + m) / (6 * (1 + z) ^ 2 * (1 + z - m)) ≤
      z / (1 + z) * (z / (1 + z) - 1 / 2) * (m / (1 + z - m)) +
        z / (1 + z) * (m / (1 + z - m)) ^ 2 / (3 * (m / (1 + z - m) + 2)) := by
    have e : z / (1 + z) * (z / (1 + z) - 1 / 2) * (m / (1 + z - m)) +
        z / (1 + z) * (m / (1 + z - m)) ^ 2 / (3 * (m / (1 + z - m) + 2)) -
        z * m * (3 * (z - 1) + m) / (6 * (1 + z) ^ 2 * (1 + z - m)) =
        z * m ^ 3 / (6 * (1 + z) ^ 2 * (1 + z - m) * (2 * (1 + z) - m)) := by
      have e2 : m / (1 + z - m) + 2 = (2 * (1 + z) - m) / (1 + z - m) := by field_simp; ring
      rw [e2]
      generalize hg : 2 * (1 + z) - m = g at *
      generalize hk : 1 + z - m = k at *
      field_simp
      subst hg hk
      ring
    have : 0 ≤ z * m ^ 3 / (6 * (1 + z) ^ 2 * (1 + z - m) * (2 * (1 + z) - m)) := by positivity
    linarith
  have hcoef : 0 ≤ ((1 + z) * (2 - m)) ^ 2 / ((1 + z) * ((1 + z) * (1 + z - m))) *
      ((1 + z) / (2 - m) - 1 + (h - 1) * ((1 + z) * ((1 + z) / (2 - m)) - 1)) := by
    apply mul_nonneg (by positivity)
    have : 1 ≤ (1 + z) * ((1 + z) / (2 - m)) := by nlinarith
    nlinarith
  -- the Padé weakening
  have hpade : z * (h - 1) * ((h - 1) / h) ^ 2 / 6 ≤ z * (h - 1) ^ 3 / (3 * h * (h + 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have e : z * (h - 1) * ((h - 1) / h) ^ 2 * (3 * h * (h + 1)) = z * (h - 1) ^ 3 * (3 * (h + 1) / h) := by
      field_simp
    rw [e]
    have : 3 * (h + 1) / h ≤ 6 := by rw [div_le_iff₀ hh0]; linarith
    have : 0 ≤ z * (h - 1) ^ 3 := by have : 0 ≤ h - 1 := by linarith
                                     positivity
    nlinarith
  -- the cubic
  have hP := fs_H5P_pos (z := z) (l := 1 - m) (v := (1 + z) * (h - 1) / h) (by linarith) (by linarith)
    (by rw [le_div_iff₀ hh0]; rw [div_le_iff₀ hSm] at hhl; nlinarith)
    (by rw [div_le_one hh0]; rw [le_div_iff₀ hz0] at hhu; nlinarith)
    (by have : 0 < h - 1 := by linarith
        positivity) (by nlinarith)
  have key : fs_hardB (1 + z) ((1 + z) * (1 + z - m)) ((1 + z) * (2 - m)) ((1 + z) / (2 - m))
      (z / (1 + z)) (m / (1 + z - m)) h z ≤
      (h - 1) * ((1 + z) * ((1 + z) * (2 - m)) / ((1 + z) * (1 + z - m))) * (z / (1 + z)) *
        ((1 + z) / (2 - m) - 1) * ((1 + z) / (2 - m) / (1 + z) - z / (1 + z)) / ((1 + z) / (2 - m)) -
      ((1 + z) * (2 - m)) ^ 2 / ((1 + z) * ((1 + z) * (1 + z - m))) *
        ((1 + z) / (2 - m) - 1 + (h - 1) * ((1 + z) * ((1 + z) / (2 - m)) - 1)) *
        (z * m * (3 * (z - 1) + m) / (6 * (1 + z) ^ 2 * (1 + z - m))) +
      z ^ 2 * (m / (1 + z - m)) * (h - 1) ^ 2 / (2 * h) - z * (h - 1) * ((h - 1) / h) ^ 2 / 6 := by
    unfold fs_hardB
    have := mul_le_mul_of_nonneg_left hD hcoef
    linarith
  have e : (h - 1) * ((1 + z) * ((1 + z) * (2 - m)) / ((1 + z) * (1 + z - m))) * (z / (1 + z)) *
        ((1 + z) / (2 - m) - 1) * ((1 + z) / (2 - m) / (1 + z) - z / (1 + z)) / ((1 + z) / (2 - m)) -
      ((1 + z) * (2 - m)) ^ 2 / ((1 + z) * ((1 + z) * (1 + z - m))) *
        ((1 + z) / (2 - m) - 1 + (h - 1) * ((1 + z) * ((1 + z) / (2 - m)) - 1)) *
        (z * m * (3 * (z - 1) + m) / (6 * (1 + z) ^ 2 * (1 + z - m))) +
      z ^ 2 * (m / (1 + z - m)) * (h - 1) ^ 2 / (2 * h) - z * (h - 1) * ((h - 1) / h) ^ 2 / 6 =
      -(z * h * fs_H5P z (1 - m) ((1 + z) * (h - 1) / h) /
        (6 * (1 + z) * ((1 + z) * (1 + z - m)) ^ 2)) := by
    unfold fs_H5P
    field_simp
    ring
  rw [e] at key
  have : 0 < z * h * fs_H5P z (1 - m) ((1 + z) * (h - 1) / h) /
      (6 * (1 + z) * ((1 + z) * (1 + z - m)) ^ 2) := by positivity
  linarith

/-! ### The three comparison faces -/

/-- `Δ = F_x(I) - (1 - x + x²) ≥ Δ₀ = x(x - 1/2)d + xd²/(3(d + 2))`, `d = I - 1`
(NEIGHBOR_INTEGRAL (6), from the Padé bound). -/
theorem fs_Delta_ge {x I : ℝ} (hx : 0 ≤ x) (hI : 1 < I) :
    x * (x - 1 / 2) * (I - 1) + x * (I - 1) ^ 2 / (3 * ((I - 1) + 2)) ≤
      ff_F x I - (1 - x + x ^ 2) := by
  have hp := fs_f_ge_pade hI.le
  unfold ff_f at hp
  have hI0 : 0 < I := by linarith
  have hI1 : 0 < I - 1 := by linarith
  have hl : Real.log I ≤ (I - I⁻¹) / 2 - (I - 1) ^ 3 / (3 * I * (I + 1)) := by linarith
  have hc : 0 ≤ x * I / (I - 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hl hc
  have e1 : x * I / (I - 1) * Real.log I = x * I * Real.log I / (I - 1) := by ring
  have e2 : x * I / (I - 1) * ((I - I⁻¹) / 2 - (I - 1) ^ 3 / (3 * I * (I + 1))) =
      x * (I + 1) / 2 - x * (I - 1) ^ 2 / (3 * (I + 1)) := by
    field_simp; ring
  have e3 : (I - 1) + 2 = I + 1 := by ring
  rw [e3]
  unfold ff_F
  have : x * (x - 1 / 2) * (I - 1) + x * (I - 1) ^ 2 / (3 * (I + 1)) =
      1 + x ^ 2 * I - (x * (I + 1) / 2 - x * (I - 1) ^ 2 / (3 * (I + 1))) - (1 - x + x ^ 2) := by ring
  linarith

/-- **The hard face** (SMALL_FORWARD_MINIMUM_HAND_PROOF): `w = z`, `U ≥ 3`, `S² ≥ K`, `H = S²/Z > 1`. -/
theorem fs_face_hard {U z h : ℝ} (hU : 3 ≤ U) (hUz : U < 2 * z + 1) (hzU : z < U) (hz : 1 ≤ z)
    (hq : 1 + U ≤ (1 + z) ^ 2) (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h) (hhu : h ≤ (1 + z) / z)
    (hh1 : 1 < h) : fs_res U z z h (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) < 0 := by
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hh0 : 0 < h := by linarith
  have hInt := fs_res_integral (w := z) (V := ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) hz
    hzU.le hh1
  rw [fs_res_one hU0 hz0 hz0, fs_res_slope hU0 hz0 hz0] at hInt
  have hqd : ff_q U z z = (1 + z) * (1 + z) / (1 + U) := rfl
  have hF : fs_Fw z (ff_q U z z) ≤ 0 := by rw [hqd]; exact fs_Fw_hard hU hzU hz
  have hI1 : 1 < (1 + z) ^ 2 / (z ^ 2 + U) := by rw [lt_div_iff₀ hZ]; nlinarith
  have hΔ := fs_Delta_ge (x := z / (1 + z)) (by positivity) hI1
  have hpade := fs_f_ge_pade hh1.le
  have hq1 : 1 ≤ ff_q U z z := by rw [hqd, le_div_iff₀ hK]; nlinarith
  have hcF : 0 ≤ (1 + U) / (z ^ 2 + U) * (1 + (1 + z) * (h - 1)) := by
    have : 0 ≤ h - 1 := by linarith
    positivity
  have hcΔ : 0 ≤ (1 + U) ^ 2 / ((1 + z) * (z ^ 2 + U)) *
      (ff_q U z z - 1 + (h - 1) * ((1 + z) * ff_q U z z - 1)) := by
    apply mul_nonneg (by positivity)
    have : 0 ≤ h - 1 := by linarith
    have : 0 ≤ (1 + z) * ff_q U z z - 1 := by nlinarith
    nlinarith
  have t1 := mul_nonpos_of_nonneg_of_nonpos hcF hF
  have t2 := mul_nonneg hcΔ (sub_nonneg.2 hΔ)
  have t3 := mul_nonneg hz0.le (sub_nonneg.2 hpade)
  have hB : fs_res U z z h (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) ≤
      fs_hardB (1 + z) (z ^ 2 + U) (1 + U) (ff_q U z z) (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U) - 1)
        h z := by
    refine le_trans hInt (le_of_sub_nonneg ?_)
    have e : fs_hardB (1 + z) (z ^ 2 + U) (1 + U) (ff_q U z z) (z / (1 + z))
        ((1 + z) ^ 2 / (z ^ 2 + U) - 1) h z -
        (((1 + U) / (z ^ 2 + U) * fs_Fw z (ff_q U z z) -
          (1 + U) ^ 2 * (ff_q U z z - 1) / ((1 + z) * (z ^ 2 + U)) *
            (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U)) - (1 - z / (1 + z) + (z / (1 + z)) ^ 2))) +
        (h - 1) * ((1 + z) * (1 + U) / (z ^ 2 + U) * (fs_Fw z (ff_q U z z) +
          z / (1 + z) * (ff_q U z z - 1) * (ff_q U z z / (1 + z) - z / (1 + z)) / ff_q U z z) -
          (1 + U) ^ 2 * ((1 + z) * ff_q U z z - 1) / ((1 + z) * (z ^ 2 + U)) *
            (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U)) - (1 - z / (1 + z) + (z / (1 + z)) ^ 2))) +
        z ^ 2 * ((1 + z) ^ 2 / (z ^ 2 + U) - 1) * (h - 1) ^ 2 / (2 * h) - z * ff_f h) =
        -((1 + U) / (z ^ 2 + U) * (1 + (1 + z) * (h - 1)) * fs_Fw z (ff_q U z z)) +
        (1 + U) ^ 2 / ((1 + z) * (z ^ 2 + U)) *
          (ff_q U z z - 1 + (h - 1) * ((1 + z) * ff_q U z z - 1)) *
          (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U)) - (1 - z / (1 + z) + (z / (1 + z)) ^ 2) -
            (z / (1 + z) * (z / (1 + z) - 1 / 2) * ((1 + z) ^ 2 / (z ^ 2 + U) - 1) +
              z / (1 + z) * ((1 + z) ^ 2 / (z ^ 2 + U) - 1) ^ 2 /
                (3 * (((1 + z) ^ 2 / (z ^ 2 + U) - 1) + 2)))) +
        z * (ff_f h - (h - 1) ^ 3 / (3 * h * (h + 1))) := by
      unfold fs_hardB
      ring
    rw [e]
    linarith
  refine lt_of_le_of_lt hB ?_
  -- the coordinates `m = (2z + 1 - U)/S`
  obtain ⟨m, hm⟩ : ∃ m, m = (2 * z + 1 - U) / (1 + z) := ⟨_, rfl⟩
  have hUm : U = 2 * z + 1 - m * (1 + z) := by rw [hm]; field_simp; ring
  have hm0 : 0 < m := by rw [hm]; apply div_pos _ hS; linarith
  have hm1 : m < 1 := by rw [hm, div_lt_one hS]; linarith
  have e1 : z ^ 2 + U = (1 + z) * (1 + z - m) := by rw [hUm]; ring
  have e2 : 1 + U = (1 + z) * (2 - m) := by rw [hUm]; ring
  have hSm : 0 < 1 + z - m := by linarith
  have h2m : 0 < 2 - m := by linarith
  have e3 : ff_q U z z = (1 + z) / (2 - m) := by rw [hqd, e2]; field_simp
  have e4 : (1 + z) ^ 2 / (z ^ 2 + U) - 1 = m / (1 + z - m) := by rw [e1]; field_simp; ring
  rw [e4, e3, e1, e2]
  refine fs_hard_alg hz hm0 hm1 (by linarith) ?_ hhu hh1 ?_
  · calc (1 + z) / (1 + z - m) = (1 + z) ^ 2 / (z ^ 2 + U) := by rw [e1]; field_simp
      _ ≤ h := hhl
  · rw [← e3]; exact hq1

/-- **The low face** (MIXED_GLOBAL_SMALL_FORWARD_MINIMUM §5): `w = z`, `S² ≥ K`, `H = S²/Z ≤ 1`. -/
theorem fs_face_low {U z h : ℝ} (hzU : z < U) (hz : 1 ≤ z) (hq : 1 + U ≤ (1 + z) ^ 2)
    (hlow : 2 * z + 1 ≤ U) (hh1 : 1 < h) :
    fs_res U z z h (1 - z / (1 + z) + (z / (1 + z)) ^ 2) < 0 := by
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hInt := fs_res_integral (w := z) (V := 1 - z / (1 + z) + (z / (1 + z)) ^ 2) hz hzU.le hh1
  rw [fs_res_one hU0 hz0 hz0, fs_res_slope hU0 hz0 hz0] at hInt
  have hqd : ff_q U z z = (1 + z) * (1 + z) / (1 + U) := rfl
  have hq1 : 1 ≤ ff_q U z z := by rw [hqd, le_div_iff₀ hK]; nlinarith
  have hqz : ff_q U z z ≤ z := by rw [hqd, div_le_iff₀ hK]; nlinarith
  have hF := fs_Fw_nonpos_le hz hq1 hqz
  have hq0 : 0 < ff_q U z z := by linarith
  have hslope : z / (1 + z) * (ff_q U z z - 1) * (ff_q U z z / (1 + z) - z / (1 + z)) /
      ff_q U z z ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hq0.le
    apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (by linarith))
    rw [sub_nonpos]; exact div_le_div_of_nonneg_right hqz hS.le
  have hd : (1 + z) ^ 2 / (z ^ 2 + U) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hZ]; nlinarith
  have hpade := fs_f_ge_pade hh1.le
  have hpos : 0 < (h - 1) ^ 3 / (3 * h * (h + 1)) := by
    have : 0 < h - 1 := by linarith
    have : 0 < h := by linarith
    positivity
  have t1 : (h - 1) * ((1 + z) * (1 + U) / (z ^ 2 + U) * (fs_Fw z (ff_q U z z) +
      z / (1 + z) * (ff_q U z z - 1) * (ff_q U z z / (1 + z) - z / (1 + z)) / ff_q U z z)) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    linarith
  have t2 : (1 + U) / (z ^ 2 + U) * fs_Fw z (ff_q U z z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hF
  have t3 : z ^ 2 * ((1 + z) ^ 2 / (z ^ 2 + U) - 1) * (h - 1) ^ 2 / (2 * h) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd)
      (by positivity)
  have t4 := mul_le_mul_of_nonneg_left hpade hz0.le
  have e0 : (1 - z / (1 + z) + (z / (1 + z)) ^ 2) - (1 - z / (1 + z) + (z / (1 + z)) ^ 2) = 0 := by ring
  simp only [e0, mul_zero, sub_zero] at hInt
  nlinarith [mul_pos hz0 hpos]

/-- **The zero-central-factor face** (MIXED_GLOBAL_SMALL_FORWARD_MINIMUM §4): `q = 1`,
`w = K/S - 1`, opposite floor `1 - y + y²`. -/
theorem fs_face_q1 {U z h : ℝ} (hzU : z < U) (hz : 1 ≤ z) (hq : (1 + z) ^ 2 ≤ 1 + U) (hh1 : 1 < h) :
    fs_res U z ((1 + U) / (1 + z) - 1) h
      (1 - ((1 + U) / (1 + z) - 1) / (1 + ((1 + U) / (1 + z) - 1)) +
        (((1 + U) / (1 + z) - 1) / (1 + ((1 + U) / (1 + z) - 1))) ^ 2) < 0 := by
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hw : 0 < (1 + U) / (1 + z) - 1 := by
    rw [sub_pos, lt_div_iff₀ hS]; nlinarith
  have hInt := fs_res_integral (w := (1 + U) / (1 + z) - 1)
    (V := 1 - ((1 + U) / (1 + z) - 1) / (1 + ((1 + U) / (1 + z) - 1)) +
        (((1 + U) / (1 + z) - 1) / (1 + ((1 + U) / (1 + z) - 1))) ^ 2) hz hzU.le hh1
  rw [fs_res_one hU0 hz0 hw, fs_res_slope hU0 hz0 hw] at hInt
  have hq1 : ff_q U z ((1 + U) / (1 + z) - 1) = 1 := by
    unfold ff_q; field_simp; ring
  have hF : fs_Fw ((1 + U) / (1 + z) - 1) 1 = 0 := by simp [fs_Fw]
  rw [hq1, hF] at hInt
  have hd : (1 + z) ^ 2 / (z ^ 2 + U) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hZ]; nlinarith
  have hpade := fs_f_ge_pade hh1.le
  have hpos : 0 < (h - 1) ^ 3 / (3 * h * (h + 1)) := by
    have : 0 < h - 1 := by linarith
    have : 0 < h := by linarith
    positivity
  have t3 : z ^ 2 * ((1 + z) ^ 2 / (z ^ 2 + U) - 1) * (h - 1) ^ 2 / (2 * h) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd)
      (by positivity)
  have t4 := mul_le_mul_of_nonneg_left hpade hz0.le
  simp only [sub_self, mul_zero, zero_mul, zero_div, add_zero, zero_add, mul_one, div_one] at hInt
  nlinarith [mul_pos hz0 hpos]

/-! ### Lowering the larger neighbour and the whole-window statement -/

/-- **Lowering the larger neighbour** (MIXED_GLOBAL_SMALL_FORWARD_MINIMUM §3 (16), difference form):
with `B(w) = 1 - y + y² ≤ V` and `V' ≤ V`, `𝓔(w, V) ≤ 𝓔(w', V')` for `1 ≤ w' ≤ w` and `q(w') ≥ 1`. -/
theorem fs_res_le {U z w w' h V V' : ℝ} (hU : 0 < U) (hz : 0 < z) (hw' : 1 ≤ w') (hww : w' ≤ w)
    (hq : 1 ≤ ff_q U z w') (hh : 1 ≤ h) (hVB : 1 - w / (1 + w) + (w / (1 + w)) ^ 2 ≤ V)
    (hVV : V' ≤ V) : fs_res U z w h V ≤ fs_res U z w' h V' := by
  have hw : 1 ≤ w := le_trans hw' hww
  have hA := fs_A_sub_le hU hz hw' hww
  have hms := fs_m_sub (w := w) (w' := w') (h := h) hU hz
  have hα : 0 ≤ ff_alpha U z h := (ff_alpha_pos hU hz hh).le
  have hm' : 0 ≤ ff_m U z w' h := by
    unfold ff_m
    apply mul_nonneg (by positivity)
    have : 0 ≤ ff_q U z w' * (1 + z) - 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1) this]
  have hB : 1 - w / (1 + w) + (w / (1 + w)) ^ 2 = 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 := by
    have : (1 + w) ≠ 0 := by linarith
    field_simp; ring
  have key : fs_res U z w h V - fs_res U z w' h V' =
      ff_alpha U z h * (ff_A U z w - ff_A U z w') - ff_alpha U z h * (w - w') * V -
        ff_m U z w' h * (V - V') := by
    unfold fs_res
    have : ff_m U z w h = ff_m U z w' h + ff_alpha U z h * (w - w') := by linarith
    rw [this]; ring
  have t1 := mul_le_mul_of_nonneg_left hA hα
  have t2 : ff_alpha U z h * ((w - w') * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2)) ≤
      ff_alpha U z h * ((w - w') * V) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hα
  have t3 : 0 ≤ ff_m U z w' h * (V - V') := mul_nonneg hm' (by linarith)
  nlinarith

/-- `1 - y + y²` increases for `y ≥ 1/2`. -/
theorem fs_B_mono {y y' : ℝ} (hy' : 1 / 2 ≤ y') (hyy : y' ≤ y) :
    1 - y' + y' ^ 2 ≤ 1 - y + y ^ 2 := by nlinarith

/-- **The small forward minimum** with `z ≤ w`. -/
theorem fs_U_lt_three_le (W : ff_Dim) (hzw : W.z ≤ W.w) : W.U < 3 := by
  by_contra hU3
  push Not at hU3
  have hz := W.one_le_z
  have hw := W.one_le_w
  have hzU := W.z_lt
  have hwU := W.w_lt
  have hU0 : 0 < W.U := by linarith
  have hz0 : 0 < W.z := by linarith
  have hS : 0 < 1 + W.z := by linarith
  have hT : 0 < 1 + W.w := by linarith
  have hK : 0 < 1 + W.U := by linarith
  have hZ : 0 < W.z ^ 2 + W.U := by positivity
  have hWW : 0 < W.w ^ 2 + W.U := by positivity
  set h := ff_hd W.U W.z W.P with hhdef
  set k := ff_hd W.U W.w W.D with hkdef
  have hh1 : 1 < h := W.one_lt_h
  have hk1 : 1 < k := W.one_lt_k
  have hhl : (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) ≤ h := by
    rw [hhdef]; unfold ff_hd
    apply div_le_div_of_nonneg_right _ hZ.le
    nlinarith [W.one_le_P]
  have hhu : h ≤ (1 + W.z) / W.z := by
    rw [hhdef]; unfold ff_hd
    rw [div_le_div_iff₀ hZ hz0]
    nlinarith [W.Pz_lt]
  have hkl : (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) ≤ k := by
    rw [hkdef]; unfold ff_hd
    apply div_le_div_of_nonneg_right _ hWW.le
    nlinarith [W.one_le_D]
  have hq : 1 < ff_q W.U W.z W.w := W.one_lt_q
  have hn : 0 ≤ ff_n W.U W.z h := by
    unfold ff_n
    apply div_nonneg _ hZ.le
    apply mul_nonneg (mul_nonneg (by positivity) (by linarith)); linarith
  have hm : 0 ≤ ff_m W.U W.z W.w h := by
    unfold ff_m
    apply mul_nonneg (by positivity)
    have : 0 ≤ ff_q W.U W.z W.w * (1 + W.z) - 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1) this]
  have hy : 1 / 2 ≤ W.w / (1 + W.w) := by rw [le_div_iff₀ hT]; linarith
  have hx : 1 / 2 ≤ W.z / (1 + W.z) := by rw [le_div_iff₀ hS]; linarith
  have hxy : W.z / (1 + W.z) ≤ W.w / (1 + W.w) := by
    rw [div_le_div_iff₀ hS hT]; nlinarith
  have hv := W.floorR
  -- the residual is nonnegative for every admissible opposite floor `V ≤ v`
  have hres : ∀ V, V ≤ W.v → 0 ≤ fs_res W.U W.z W.w h V := by
    intro V hV
    have hrow := W.rowL
    have hu := W.floorL
    unfold fs_res
    have := mul_le_mul_of_nonneg_left hu hn
    have := mul_le_mul_of_nonneg_left hV hm
    linarith
  have hBw : 1 - W.w / (1 + W.w) + (W.w / (1 + W.w)) ^ 2 ≤ W.v :=
    le_trans (fs_F_ge hy hk1) hv
  have hII : (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) ≤ (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) := by
    rw [div_le_div_iff₀ hZ hWW]
    have : (1 + W.w) ^ 2 * (W.z ^ 2 + W.U) - (1 + W.z) ^ 2 * (W.w ^ 2 + W.U) =
        (W.w - W.z) * (W.U * (W.w + W.z + 2) - 2 * W.w * W.z - W.w - W.z) := by ring
    have h2 : 0 ≤ W.U * (W.w + W.z + 2) - 2 * W.w * W.z - W.w - W.z := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hzw) h2]
  rcases lt_or_ge ((1 + W.z) ^ 2) (1 + W.U) with hSK | hSK
  · -- the zero-central-factor face
    set w' := (1 + W.U) / (1 + W.z) - 1 with hw'
    have hw'z : W.z ≤ w' := by
      rw [hw', le_sub_iff_add_le, le_div_iff₀ hS]; nlinarith
    have hw'w : w' ≤ W.w := by
      rw [hw', sub_le_iff_le_add, div_le_iff₀ hS]
      have := hq; unfold ff_q at this; rw [lt_div_iff₀ hK] at this; nlinarith
    have hq' : 1 ≤ ff_q W.U W.z w' := by
      rw [hw']; unfold ff_q; rw [le_div_iff₀ hK]; field_simp; linarith
    have hT' : 0 < 1 + w' := by linarith
    have hy' : 1 / 2 ≤ w' / (1 + w') := by rw [le_div_iff₀ hT']; linarith
    have hyy : w' / (1 + w') ≤ W.w / (1 + W.w) := by
      rw [div_le_div_iff₀ hT' hT]; nlinarith
    have h0 := hres _ hBw
    have hle := fs_res_le (V' := 1 - w' / (1 + w') + (w' / (1 + w')) ^ 2) hU0 hz0
      (by linarith) hw'w hq' hh1.le le_rfl (fs_B_mono hy' hyy)
    have hneg := fs_face_q1 hzU hz hSK.le hh1
    linarith
  · rcases le_or_gt (2 * W.z + 1) W.U with hlow | hhard
    · -- the low face
      have hqz : 1 ≤ ff_q W.U W.z W.z := by unfold ff_q; rw [le_div_iff₀ hK]; linarith only [hSK]
      have h0 := hres _ hBw
      have hle := fs_res_le (V' := 1 - W.z / (1 + W.z) + (W.z / (1 + W.z)) ^ 2) hU0 hz0 hz hzw hqz
        hh1.le le_rfl (fs_B_mono hx hxy)
      have hneg := fs_face_low hzU hz hSK hlow hh1
      linarith
    · -- the hard face
      have hqz : 1 ≤ ff_q W.U W.z W.z := by unfold ff_q; rw [le_div_iff₀ hK]; linarith only [hSK]
      have hIz : 1 < (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) := by rw [lt_div_iff₀ hZ]; linarith only [hhard]
      have hIw : 1 < (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) := lt_of_lt_of_le hIz hII
      have hV : ff_F (W.w / (1 + W.w)) ((1 + W.w) ^ 2 / (W.w ^ 2 + W.U)) ≤ W.v :=
        le_trans (fs_F_mono_r hy hIw hkl) hv
      have h0 := hres _ hV
      have hVV : ff_F (W.z / (1 + W.z)) ((1 + W.z) ^ 2 / (W.z ^ 2 + W.U)) ≤
          ff_F (W.w / (1 + W.w)) ((1 + W.w) ^ 2 / (W.w ^ 2 + W.U)) :=
        le_trans (fs_F_mono_r hx hIz hII) (fs_F_mono_x hx hxy hIw)
      have hle := fs_res_le hU0 hz0 hz hzw hqz hh1.le (fs_F_ge hy hIw) hVV
      have hneg := fs_face_hard hU3 hhard hzU hz hSK hhl hhu hh1
      linarith

/-- **The small forward minimum** (SMALL_FORWARD_MINIMUM_HAND_PROOF; MIXED_GLOBAL_SMALL_FORWARD_MINIMUM
§§1-5): at a forward window whose centre is a minimum of the five margins, `U < 3`. -/
theorem fs_U_lt_three (W : ff_Dim) : W.U < 3 := by
  rcases le_total W.z W.w with h | h
  · exact fs_U_lt_three_le W h
  · exact fs_U_lt_three_le W.swap h

end SmoothedOctagon

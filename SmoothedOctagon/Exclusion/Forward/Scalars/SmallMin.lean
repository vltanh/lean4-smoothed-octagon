module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor

/-!
# Case F scalars: the small forward minimum

At a forward window whose centre is a minimum of the five margins, `a² > 4/3`, i.e. `U < 3`.

Suppose `U ≥ 3`. The left row makes the residual `𝓔 = αA - B - nF_{z/S}(h) - mV` nonnegative for
every admissible opposite floor `V ≤ v`. The larger neighbour is lowered by a difference comparison
(`fs_res_le`) to one of three comparison faces: `q = 1` when `S² ≤ K`; `w = z` with `U ≥ 2z + 1`
(the low face); `w = z` with `U < 2z + 1` (the hard face). On each face `𝓔 < 0`. All three faces use
one integral bound (`fs_res_integral`) with the exact values at `h = 1` (`fs_res_one`,
`fs_res_slope`). On the hard face the rational envelope is negative by AM--GM. The physical order gives
a strict lower bound for its linear term; a reciprocal square-root comparison and a
completed square supply the remaining shape margin.

## Main API

* `fs_res U z w h V`: the residual `αA - B - nF_{z/S}(h) - mV` with a free opposite floor `V`;
  `fs_res_canon`, `fs_res_integral`, `fs_res_one`, `fs_res_slope`, `fs_res_le`.
* `fs_Fw w q`: the central logarithmic term; `fs_Fw_nonpos_le`, `fs_Fw_hard` (`F(q) ≤ 0`).
* `fs_H5P`, `fs_H5P_pos`: the cubic `P` is positive; `fs_hardB`, `fs_hard_alg`: the rational
  envelope of the hard face is negative.
* `fs_face_q1`, `fs_face_low`, `fs_face_hard`: the three comparison faces.
* `fs_U_lt_three`: `W.U < 3` for every `ff_Dim` window.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The residual with a free opposite floor -/

/-- The residual `𝓔 = αA - B - nF_{z/S}(h) - mV` with a free opposite floor `V`. -/
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

/-- The central logarithmic term `F_w(q) = (q - 1)/T + y(1 - 1/q) - log q`. -/
noncomputable def fs_Fw (w q : ℝ) : ℝ := (q - 1) / (1 + w) + w / (1 + w) * (1 - 1 / q) - Real.log q

/-- The value at `h = 1` of the canonical form. -/
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

/-- The slope at `h = 1` of the canonical form. -/
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

/-- **The integral bound**: `𝓔(h) ≤ 𝓔(1) + e𝓔'(1) + z²d e²/(2h) - z f(h)`, `d = S²/Z - 1`,
`e = h - 1`, by the second-order comparison of canonical functions (`fs_cf_nonneg`). -/
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

/-! ### The central logarithmic term -/

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

/-- **`F(q) ≤ 0` on the hard face**: for `U ≥ 3`, `1 ≤ z < U`. -/
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

/-! ### Positivity by AM--GM -/

/-- The cubic `P` in `v` that controls the rational envelope of the hard face, with `l = λ`. -/
noncomputable def fs_H5P (z l v : ℝ) : ℝ :=
  (z + l) ^ 2 * v ^ 3 - 3 * z * (1 - l) * (1 + z) * (z + l) * v ^ 2 +
    ((1 + l) * (1 - l) * (1 + z) * z * (3 * (z - 1) + (1 - l)) - 6 * (z + l) * (z - l) * (1 - z * l)) * v +
    (1 + l) * (1 - l) * (1 + z) * (3 * (z - 1) + (1 - l)) * (z - l)

private noncomputable def fsH5C (z μ : ℝ) : ℝ :=
  (2 - μ) * μ * (1 + z) * z * (3 * (z - 1) + μ) -
    6 * (z + 1 - μ) * (z - (1 - μ)) * (1 - z * (1 - μ))

private noncomputable def fsH5D (z μ : ℝ) : ℝ :=
  (2 - μ) * μ * (1 + z) * (3 * (z - 1) + μ) * (z - (1 - μ))

/-- The order constraint gives a strict lower bound for the linear coefficient. -/
private theorem fs_H5C_lower {z μ : ℝ} (hm0 : 0 < μ) (hm1 : μ < 1)
    (hp : 2 + μ ≤ (2 - μ) * z) :
    (4 - 3 * μ) * μ ^ 2 * (1 + z) ^ 2 < fsH5C z μ := by
  have h2 : 0 < 2 - μ := by linarith
  have hz : 1 < z := by
    by_contra h
    have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt h) h2.le
    linarith
  have hz0 : 0 < z := by linarith
  have hS : 0 < 1 + z := by linarith
  have hell : 0 < z + 1 - μ := by linarith
  have hzl : 0 < z - (1 - μ) := by linarith
  have hgap : 0 ≤ (2 - μ) * (3 * (z - 1) + μ) - μ * (8 - μ) := by
    nlinarith only [hp]
  have hloss : 0 ≤ μ ^ 2 - (2 - μ) * (1 - z * (1 - μ)) := by
    have := mul_nonneg (show 0 ≤ 1 - μ by linarith) (show 0 ≤ (2 - μ) * z - (2 + μ) by linarith)
    nlinarith only [this]
  let T := 4 * μ * (2 - μ) + 2 * (1 - μ ^ 2) * (z ^ 2 - 1) +
    5 * μ * (2 - μ) * (z - 1)
  have hT : 0 < T := by
    have : 0 ≤ 1 - μ ^ 2 := by nlinarith only [hm0, hm1]
    have : 0 ≤ z ^ 2 - 1 := by nlinarith only [hz]
    dsimp [T]
    positivity
  have h1 : 0 ≤ (2 - μ) * μ * (1 + z) * z *
      ((2 - μ) * (3 * (z - 1) + μ) - μ * (8 - μ)) := by positivity
  have h2p : 0 ≤ 6 * (z + 1 - μ) * (z - (1 - μ)) *
      (μ ^ 2 - (2 - μ) * (1 - z * (1 - μ))) := by positivity
  have e : (2 - μ) * (fsH5C z μ - (4 - 3 * μ) * μ ^ 2 * (1 + z) ^ 2) =
      μ ^ 2 * T +
        (2 - μ) * μ * (1 + z) * z * ((2 - μ) * (3 * (z - 1) + μ) - μ * (8 - μ)) +
        6 * (z + 1 - μ) * (z - (1 - μ)) * (μ ^ 2 - (2 - μ) * (1 - z * (1 - μ))) := by
    dsimp [fsH5C, T]
    ring
  have hprod : 0 < (2 - μ) * (fsH5C z μ - (4 - 3 * μ) * μ ^ 2 * (1 + z) ^ 2) := by
    rw [e]
    have := mul_pos (sq_pos_of_pos hm0) hT
    linarith only [this, h1, h2p]
  have := pos_of_mul_pos_right hprod h2.le
  linarith only [this]

/-- A reciprocal square-root comparison supplies the AM--GM margin. -/
private theorem fs_H5_sqrt_lower {μ : ℝ} (hm0 : 0 < μ) (hm1 : μ < 1) :
    2 - μ + μ * (1 - μ) / 4 ≤ Real.sqrt (4 - 3 * μ) := by
  have harg : 0 ≤ 4 - 3 * μ := by linarith
  have hs0 := Real.sqrt_nonneg (4 - 3 * μ)
  have hs := Real.sq_sqrt harg
  have hp : 0 ≤ μ * (1 - μ) := mul_nonneg hm0.le (by linarith)
  have hs2 : Real.sqrt (4 - 3 * μ) ≤ 2 := by nlinarith only [hs0, hs, hm0]
  have hbase : 2 - μ ≤ Real.sqrt (4 - 3 * μ) := by nlinarith only [hs0, hs, hp, hm1]
  have he : (Real.sqrt (4 - 3 * μ) - (2 - μ)) *
      (Real.sqrt (4 - 3 * μ) + 2 - μ) = μ * (1 - μ) := by nlinarith only [hs]
  have hprod := mul_nonneg (sub_nonneg.mpr hbase)
    (show 0 ≤ 4 - (Real.sqrt (4 - 3 * μ) + 2 - μ) by linarith)
  nlinarith only [he, hprod]

/-- AM--GM and a completed square give positivity on the full physical shape range. -/
private theorem fs_H5P_amgm {z μ v : ℝ} (hm0 : 0 < μ) (hm1 : μ < 1)
    (hv0 : 0 < v) (hv1 : v ≤ 1) (hp : 2 + μ ≤ (2 - μ) * z) :
    0 < fs_H5P z (1 - μ) v := by
  have h2 : 0 < 2 - μ := by linarith
  have hz : 1 < z := by
    by_contra h
    have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt h) h2.le
    linarith
  have hz0 : 0 < z := by linarith
  let S := 1 + z
  let ell := z + 1 - μ
  let C := fsH5C z μ
  let D := fsH5D z μ
  let r := μ * S * ell
  let Q := (μ + z - 2) * (μ + 3 * z - 5)
  have hS : 0 < S := by dsimp [S]; linarith
  have hell : 1 ≤ ell := by dsimp [ell]; linarith
  have hell0 : 0 < ell := by linarith
  have hzl : 0 < z - (1 - μ) := by linarith
  have h3z : 0 < 3 * (z - 1) + μ := by linarith
  have hD : 0 < D := by dsimp [D, fsH5D]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hC : (4 - 3 * μ) * μ ^ 2 * S ^ 2 < C := fs_H5C_lower hm0 hm1 hp
  have heq : fs_H5P z (1 - μ) v = ell ^ 2 * v ^ 3 - 3 * z * r * v ^ 2 + C * v + D := by
    dsimp [fs_H5P, ell, r, S, C, D, fsH5C, fsH5D]
    ring
  have hv2 : 0 ≤ 1 - v ^ 2 := by nlinarith only [hv0, hv1]
  have hgood : 0 ≤ μ * ell / 2 + Q → 0 < fs_H5P z (1 - μ) v := by
    intro hg
    let root := Real.sqrt (4 - 3 * μ)
    have hs : root ^ 2 = 4 - 3 * μ := Real.sq_sqrt (by linarith)
    have hroot := fs_H5_sqrt_lower hm0 hm1
    have hmargin : 0 ≤ 2 * r * root + D - 3 * z * r := by
      have ha : 0 ≤ 2 * r * (root - (2 - μ) - μ * (1 - μ) / 4) :=
        mul_nonneg (by positivity) (by dsimp [root]; linarith only [hroot])
      have hb : 0 ≤ μ * S * (1 - μ) * (μ * ell / 2 + Q) :=
        mul_nonneg (by positivity) hg
      have e : 2 * r * root + D - 3 * z * r =
          2 * r * (root - (2 - μ) - μ * (1 - μ) / 4) +
            μ * S * (1 - μ) * (μ * ell / 2 + Q) := by
        dsimp [r, D, fsH5D, Q, ell, S]
        ring
      rw [e]
      linarith only [ha, hb]
    have e : fs_H5P z (1 - μ) v =
        v * (ell * v - μ * S * root) ^ 2 +
          (C - (4 - 3 * μ) * μ ^ 2 * S ^ 2) * v + D * (1 - v ^ 2) +
            v ^ 2 * (2 * r * root + D - 3 * z * r) := by
      rw [heq]
      dsimp [r]
      linear_combination -(μ * S) ^ 2 * v * hs
    rw [e]
    have h1 : 0 ≤ v * (ell * v - μ * S * root) ^ 2 := by positivity
    have h2p : 0 < (C - (4 - 3 * μ) * μ ^ 2 * S ^ 2) * v :=
      mul_pos (by linarith only [hC]) hv0
    have h3 : 0 ≤ D * (1 - v ^ 2) := mul_nonneg hD.le hv2
    have h4 : 0 ≤ v ^ 2 * (2 * r * root + D - 3 * z * r) :=
      mul_nonneg (sq_nonneg v) hmargin
    linarith only [h1, h2p, h3, h4]
  by_cases hm16 : 1 / 6 ≤ μ
  · apply hgood
    have hQ : -1 / 12 ≤ Q := by
      have hmSq : (1 - 2 * μ) ^ 2 ≤ 1 := by nlinarith only [hm0, hm1]
      have e : Q = 3 * (μ + z - 2 + (1 - 2 * μ) / 6) ^ 2 - (1 - 2 * μ) ^ 2 / 12 := by
        dsimp [Q]
        ring
      rw [e]
      nlinarith only [hmSq, sq_nonneg (μ + z - 2 + (1 - 2 * μ) / 6)]
    have hmul := mul_nonneg hm0.le (sub_nonneg.mpr hell)
    linarith only [hQ, hmul, hm16]
  push Not at hm16
  by_cases hQ : 0 ≤ Q
  · exact hgood (by positivity)
  push Not at hQ
  have hzlo : (5 - μ) / 3 < z := by
    by_contra h
    have h1 : μ + z - 2 ≤ 0 := by linarith
    have h2q : μ + 3 * z - 5 ≤ 0 := by linarith
    have := mul_nonneg_of_nonpos_of_nonpos h1 h2q
    change 0 ≤ Q at this
    linarith only [this, hQ]
  have hzhi : z < 2 - μ := by
    by_contra h
    have h1 : 0 ≤ μ + z - 2 := by linarith
    have h2q : 0 ≤ μ + 3 * z - 5 := by linarith
    have := mul_nonneg h1 h2q
    change 0 ≤ Q at this
    linarith only [this, hQ]
  have hz32 : 3 / 2 < z := by linarith
  have hz2 : z < 2 := by linarith
  have hS3 : S < 3 := by dsimp [S]; linarith
  have hzlam : 1 < z * (1 - μ) := by
    have h := mul_lt_mul_of_pos_left (show (5 / 6 : ℝ) < 1 - μ by linarith) hz0
    nlinarith only [h, hz32]
  have hCfirst : (2 - μ) * μ * S * z * (3 * (z - 1) + μ) < C := by
    have hterm : 0 < 6 * ell * (z - (1 - μ)) * (z * (1 - μ) - 1) := by positivity
    dsimp [C, fsH5C, ell, S] at *
    nlinarith only [hterm]
  have hcoef : 9 / 4 < (2 - μ) * (3 * (z - 1) + μ) := by
    have hterm : 0 < (2 - μ) * (3 * (z - 1) + μ - 3 / 2) :=
      mul_pos h2 (by linarith only [hz32, hm0])
    nlinarith only [hterm, hm16]
  let b := z * μ * S
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by
    have hzm : z * μ < 1 / 3 := by
      have h := mul_lt_mul_of_pos_left hm16 hz0
      nlinarith only [h, hz2]
    have h := mul_lt_mul_of_pos_left hS3 (show 0 < z * μ by positivity)
    dsimp [b]
    nlinarith only [h, hzm]
  have hCb : 9 / 4 * b < C := by
    have h := mul_lt_mul_of_pos_right hcoef hb0
    dsimp [b, S] at *
    nlinarith only [h, hCfirst]
  have hbb : b ^ 2 ≤ b := by nlinarith only [hb0, hb1]
  have hCstrong : 9 / 4 * b ^ 2 < C := by linarith only [hbb, hCb]
  have e : fs_H5P z (1 - μ) v =
      v * (ell * v - 3 / 2 * b) ^ 2 + (C - 9 / 4 * b ^ 2) * v + D := by
    rw [heq]
    dsimp [b, r]
    ring
  rw [e]
  have h1 : 0 ≤ v * (ell * v - 3 / 2 * b) ^ 2 := by positivity
  have h2p : 0 < (C - 9 / 4 * b ^ 2) * v := mul_pos (by linarith only [hCstrong]) hv0
  linarith only [h1, h2p, hD]

/-- **`P > 0`** by AM--GM: the physical order bounds the linear term below,
and a completed square controls the remaining shape comparison. The argument holds
for every `0 < v ≤ 1`, including the original physical range `1 - λ ≤ v`. -/
theorem fs_H5P_pos {z l v : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (_hvm : 1 - l ≤ v) (hv1 : v ≤ 1)
    (hv0 : 0 < v) (hp : 0 ≤ (1 + l) * z - (3 - l)) : 0 < fs_H5P z l v := by
  have h := fs_H5P_amgm (μ := 1 - l) (z := z) (v := v) (by linarith) (by linarith) hv0 hv1 (by nlinarith only [hp])
  simpa only [sub_sub_cancel] using h

/-! ### The hard face: the rational envelope -/

/-- The rational envelope `𝓑` of the integral bound on the hard face (logarithms replaced by Padé
bounds), in the quantities `S, Z, K, q, x, d`. -/
noncomputable def fs_hardB (S Z K q x d h z : ℝ) : ℝ :=
  (h - 1) * (S * K / Z) * x * (q - 1) * (q / S - x) / q -
    K ^ 2 / (S * Z) * (q - 1 + (h - 1) * (S * q - 1)) *
      (x * (x - 1 / 2) * d + x * d ^ 2 / (3 * (d + 2))) +
    z ^ 2 * d * (h - 1) ^ 2 / (2 * h) - z * (h - 1) ^ 3 / (3 * h * (h + 1))

/-- **The rational envelope is negative**, in the coordinates `m = 1 - λ = (2z + 1 - U)/S`:
`Z = S(S - m)`, `K = S(2 - m)`, `q = S/(2 - m)`, `d = m/(S - m)`. -/
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
(from the Padé bound). -/
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

/-- **The hard face** `w = z`, `U ≥ 3`, `S² ≥ K`, `H = S²/Z > 1`: the residual is negative. -/
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

/-- **The low face** `w = z`, `S² ≥ K`, `H = S²/Z ≤ 1`: the residual is negative. -/
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

/-- **The zero-central-factor face** `q = 1`, `w = K/S - 1`, opposite floor `1 - y + y²`: the
residual is negative. -/
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

/-- **Lowering the larger neighbour**, in difference form: with `B(w) = 1 - y + y² ≤ V` and
`V' ≤ V`, `𝓔(w, V) ≤ 𝓔(w', V')` for `1 ≤ w' ≤ w` and `q(w') ≥ 1`. -/
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

/-- **The small forward minimum**: at a forward window whose centre is a minimum of the five
margins, `U < 3`. -/
theorem fs_U_lt_three (W : ff_Dim) : W.U < 3 := by
  rcases le_total W.z W.w with h | h
  · exact fs_U_lt_three_le W h
  · exact fs_U_lt_three_le W.swap h

end SmoothedOctagon

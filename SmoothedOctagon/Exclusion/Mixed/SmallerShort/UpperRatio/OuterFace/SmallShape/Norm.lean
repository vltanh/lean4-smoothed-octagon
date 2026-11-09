module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LargeShape
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LowerTerminal.Defs

/-!
# Smaller-short window, upper ratio: the smaller-shape norm and the lower-shape beta comparison

For the outer face with `α ≤ 3/2`: the incoming ceiling `u_s` decreases in `β`; both tests
increase in the norm (`u`-coefficient `H_u > 0`); on the lower shape `α = a_f(x)` the transport
satisfies `E_L < 1/3`, `w < 3/4`, and the tests with the moving norm `u_s` increase in `c`.

The reciprocal convexity of `OuterFace/Reciprocal` is applied with the fixed norm
`ū = u_s(x, x + c(a_f - 1))`, which dominates `u_s` on `a_f ≤ α ≤ 3/2` and is below `u_v`
(`ur_ubar_le`).

## Main API

* `urkx`, `ur_Us_eq`: `u_s = 3/4 + 1/1200 + k/(β - 1)`.
* `ur_ubar_le`: `u_s(x, x + c(a_f - 1)) ≤ u_v` for `c ≥ 5/8`.
* `urHu`, `ur_Ht_u`, `ur_Hu_pos`: the norm coefficient of `urHt` and its sign.
* `ur_af_ELw`: `E_L < 1/3` and `w < 3/4` on the lower shape.
* `ur_beta_H0`, `ur_beta_H1`: the tests with norm `u_s` increase in `c` on the lower shape.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The smaller-shape ceiling -/

/-- `k(x) = 17(x - 1)³/(240S²) - (x - 1)/1200`. -/
noncomputable def urkx (x : ℝ) : ℝ := 17 * (x - 1) ^ 3 / (240 * (1 + x) ^ 2) - (x - 1) / 1200

theorem ur_Us_eq {x b : ℝ} (hb : b - 1 ≠ 0) : ssUs x b = 3 / 4 + 1 / 1200 + urkx x / (b - 1) := by
  unfold ssUs urkx
  field_simp
  ring

theorem ur_kx_bounds {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) :
    0 < urkx x ∧ urkx x ≤ 119 / 13872 * (x - 1) ^ 2 := by
  have hS : 0 < 240 * (1 + x) ^ 2 := by positivity
  unfold urkx
  constructor
  · have : (x - 1) / 1200 < 17 * (x - 1) ^ 3 / (240 * (1 + x) ^ 2) := by
      rw [lt_div_iff₀ hS]; nlinarith [mul_pos (by linarith : (0 : ℝ) < x - 1)
        (by nlinarith : (0 : ℝ) < 85 * (x - 1) ^ 2 - (1 + x) ^ 2)]
    linarith
  · have h1 : 17 * (x - 1) ^ 3 / (240 * (1 + x) ^ 2) ≤ 119 / 13872 * (x - 1) ^ 2 := by
      rw [div_le_iff₀ hS]
      nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ x - 1) 2)
        (by nlinarith : (0 : ℝ) ≤ 119 * 240 * (1 + x) ^ 2 - 13872 * 17 * (x - 1))]
    have : 0 ≤ (x - 1) / 1200 := by linarith
    linarith

/-- `u_s` decreases in `β`, with the Lipschitz bound `u_s(b) - u_s(b') ≤ (119/13872)(b' - b)`. -/
theorem ur_Us_lip {x b b' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hb : x ≤ b) (hbb : b ≤ b') :
    ssUs x b' ≤ ssUs x b ∧ ssUs x b - ssUs x b' ≤ 119 / 13872 * (b' - b) := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < b' - 1 := by linarith
  obtain ⟨hk, hk'⟩ := ur_kx_bounds hx hx2
  rw [ur_Us_eq h1.ne', ur_Us_eq h2.ne']
  have e : urkx x / (b - 1) - urkx x / (b' - 1) = urkx x * (b' - b) / ((b - 1) * (b' - 1)) := by
    field_simp; ring
  have hx1 : (x - 1) ^ 2 ≤ (b - 1) * (b' - 1) := by nlinarith
  constructor
  · have : 0 ≤ urkx x * (b' - b) / ((b - 1) * (b' - 1)) := by
      have : 0 ≤ b' - b := by linarith
      positivity
    linarith
  · have : urkx x * (b' - b) / ((b - 1) * (b' - 1)) ≤ 119 / 13872 * (b' - b) := by
      rw [div_le_iff₀ (by positivity)]
      have hbb' : 0 ≤ b' - b := by linarith
      have := mul_le_mul_of_nonneg_right hk' hbb'
      have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ 119 / 13872 * (b' - b))
      nlinarith
    linarith

/-- `ū = u_s(x, x + c(a_f - 1)) ≤ u_v` (`c ≥ 5/8`; at `c = 5/8` the cleared difference has
positive coefficients in `h = x - 2`: `7860h⁴ + 239845h³ + 554347h² + 421323h + 103377`). -/
theorem ur_ubar_le {x c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c) :
    ssUs x (x + c * ((36 * x + 25) / 84 - 1)) ≤ ssVbar x := by
  have ha : 0 ≤ (36 * x + 25) / 84 - 1 := by linarith
  have h1 := (ur_Us_lip hx hx2 (b := x + 5 / 8 * ((36 * x + 25) / 84 - 1))
    (b' := x + c * ((36 * x + 25) / 84 - 1)) (by nlinarith) (by nlinarith)).1
  refine h1.trans ?_
  have hd : 0 < 240 * (x + 1) ^ 2 * (35 * x + 13) * (852 * x - 967) := by
    have : 0 < 852 * x - 967 := by linarith
    positivity
  have key : ssVbar x - ssUs x (x + 5 / 8 * ((36 * x + 25) / 84 - 1)) =
      (7860 * (x - 2) ^ 4 + 239845 * (x - 2) ^ 3 + 554347 * (x - 2) ^ 2 + 421323 * (x - 2) +
        103377) / (240 * (x + 1) ^ 2 * (35 * x + 13) * (852 * x - 967)) := by
    have h8 : 852 * x - 967 ≠ 0 := by linarith
    have h8' : x * 852 - 967 ≠ 0 := by linarith
    have h8'' : -967 + x * 852 ≠ 0 := by linarith
    have hV : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
    rw [show x + 5 / 8 * ((36 * x + 25) / 84 - 1) = (852 * x - 295) / 672 by ring]
    have hb1 : (852 * x - 295) / 672 - 1 ≠ 0 := ne_of_gt (by linarith)
    have hb2 : x * 852 - 295 - 672 ≠ 0 := ne_of_gt (by linarith)
    unfold ssVbar ssUs
    field_simp
    ring
  have : 0 ≤ ssVbar x - ssUs x (x + 5 / 8 * ((36 * x + 25) / 84 - 1)) := by
    rw [key]
    have : 0 ≤ x - 2 := by linarith
    positivity
  linarith

/-! ### The norm coefficient -/

/-- `H_u = Z + j/7 - mt/49`, `j = S(6 + r²) - 2D_r`, `t = D_r(S(6 + r²) - D_r)`. -/
noncomputable def urHu (m x c r : ℝ) : ℝ :=
  urZr x c r + ((1 + x) * (6 + r ^ 2) - 2 * urDr x c r) / 7 -
    m * (urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r)) / 49

/-- Norm affinity of the test. -/
theorem ur_Ht_u (m x c u u' r : ℝ) :
    urHt m x c u' r - urHt m x c u r = (u' - u) * urHu m x c r := by
  unfold urHt urHu urELr urWr urJ2 ssE0
  ring

/-- `0 < H_u < 13/2` for `2/3 ≤ r ≤ 5/6` and a multiplier `0 < m ≤ 13/4`. -/
theorem ur_Hu_pos {m x c r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hr : 2 / 3 ≤ r) (hr2 : r ≤ 5 / 6) (hm : 0 < m) (hm2 : m ≤ 13 / 4) :
    0 < urHu m x c r ∧ urHu m x c r < 13 / 2 := by
  have hD : 53 / 72 ≤ urDr x c r ∧ urDr x c r ≤ 154 / 81 := by
    unfold urDr urd1 urd2
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hc),
      mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hc2), mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hr2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hr)) (sub_nonneg.2 hc),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hr2)) (sub_nonneg.2 hc2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hr)) (sub_nonneg.2 hr),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hr2)) (sub_nonneg.2 hr2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hr),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hr)) (sub_nonneg.2 hr2)]
  have hN : 19 < (1 + x) * (6 + r ^ 2) ∧ (1 + x) * (6 + r ^ 2) < 23 := by
    constructor <;> nlinarith
  have hZ : 5 / 2 < urZr x c r ∧ urZr x c r < 19 / 6 := by
    unfold urZr; constructor <;> nlinarith
  obtain ⟨hD1, hD2⟩ := hD
  obtain ⟨hN1, hN2⟩ := hN
  have ht : 0 < urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r) := by
    apply mul_pos <;> linarith
  have ht' : urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r) < 50 := by nlinarith
  unfold urHu
  constructor
  · have : m * (urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r)) ≤ 13 / 4 * 50 := by
      nlinarith
    linarith
  · have : 0 < m * (urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r)) := mul_pos hm ht
    linarith

/-! ### The lower shape `α = a_f` -/

/-- `r_f = 1/a_f = 84/(36x + 25)` lies in `[2/3, 5/6]`, and `x r_f - 1 ≥ 3/4`. -/
theorem ur_rf {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) :
    420 / 557 ≤ 84 / (36 * x + 25) ∧ 84 / (36 * x + 25) ≤ 84 / 103 ∧
      3 / 4 ≤ x * (84 / (36 * x + 25)) - 1 := by
  have hA : 0 < 36 * x + 25 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hA]; linarith
  · rw [div_le_div_iff₀ hA (by norm_num)]; linarith
  · rw [mul_div_assoc', le_sub_iff_add_le, le_div_iff₀ hA]; linarith

/-- `D_r` bounds on the smaller rectangle. -/
theorem ur_Dr_box {x c r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hr : 2 / 3 ≤ r) (hr2 : r ≤ 5 / 6) :
    53 / 72 ≤ urDr x c r ∧ urDr x c r ≤ 154 / 81 := by
  unfold urDr urd1 urd2
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hc),
    mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hc2), mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hr2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hr)) (sub_nonneg.2 hc),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hr2)) (sub_nonneg.2 hc2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hr)) (sub_nonneg.2 hr),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hr2)) (sub_nonneg.2 hr2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hr),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hr)) (sub_nonneg.2 hr2)]

/-- `E_L < 1/3` at `c = 5/8`, `u = 3/4` on the lower shape. -/
theorem ur_af_k7 {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) :
    0 < 1 / 3 - urELr x (5 / 8) (3 / 4) (84 / (36 * x + 25)) := by
  have hS : 0 < 1 + x := by linarith
  have hA : 0 < 36 * x + 25 := by linarith
  have k7 : 168 * (1 + x) * (36 * x + 25) ^ 2 *
      (1 / 3 - urELr x (5 / 8) (3 / 4) (84 / (36 * x + 25))) =
      -46656 * (x - 2) ^ 4 - 137376 * (x - 2) ^ 3 + 182520 * (x - 2) ^ 2 + 492047 * (x - 2) +
        90213 := by
    unfold urELr urDr urd1 urd2 urJ2 ssE0; field_simp; ring
  have hh' : x - 2 ≤ 2 / 5 := by linarith
  have h3 : (x - 2) ^ 3 ≤ (2 / 5) ^ 3 := pow_le_pow_left₀ (by linarith) hh' 3
  have h4 : (x - 2) ^ 4 ≤ (2 / 5) ^ 4 := pow_le_pow_left₀ (by linarith) hh' 4
  have : 0 < -46656 * (x - 2) ^ 4 - 137376 * (x - 2) ^ 3 + 182520 * (x - 2) ^ 2 +
      492047 * (x - 2) + 90213 := by
    have : 0 ≤ x - 2 := by linarith
    linarith [sq_nonneg (x - 2)]
  rw [← k7] at this
  exact pos_of_mul_pos_right this (by positivity)

/-- `w < 3/4` at `c = 5/8`, `u = 3/4` on the lower shape. -/
theorem ur_af_k8 {x : ℝ} (hx : 13 / 6 ≤ x) (_hx2 : x ≤ 12 / 5) :
    0 < 3 / 4 - urWr x (5 / 8) (3 / 4) (84 / (36 * x + 25)) / 49 := by
  have hS : 0 < 1 + x := by linarith
  have hA : 0 < 36 * x + 25 := by linarith
  have k8 : 4 * (784 * (1 + x) * (36 * x + 25) ^ 4 *
      (3 / 4 - urWr x (5 / 8) (3 / 4) (84 / (36 * x + 25)) / 49)) =
      1110786048 * (x - 2) ^ 6 + 10265688576 * (x - 2) ^ 5 + 39296105856 * (x - 2) ^ 4 +
        83068492464 * (x - 2) ^ 3 + 97377690816 * (x - 2) ^ 2 + 48493013565 * (x - 2) -
        135636633 := by
    unfold urWr urDr urd1 urd2 ssE0; field_simp; ring
  have : 0 < 1110786048 * (x - 2) ^ 6 + 10265688576 * (x - 2) ^ 5 + 39296105856 * (x - 2) ^ 4 +
      83068492464 * (x - 2) ^ 3 + 97377690816 * (x - 2) ^ 2 + 48493013565 * (x - 2) -
      135636633 := by
    have : 0 ≤ x - 2 := by linarith
    have : 0 ≤ 1110786048 * (x - 2) ^ 6 + 10265688576 * (x - 2) ^ 5 +
        39296105856 * (x - 2) ^ 4 + 83068492464 * (x - 2) ^ 3 + 97377690816 * (x - 2) ^ 2 := by
      positivity
    linarith
  rw [← k8] at this
  have := pos_of_mul_pos_right this (by norm_num : (0 : ℝ) ≤ 4)
  exact pos_of_mul_pos_right this (by positivity)

/-- `E_L < 1/3` and `w < 3/4` on the lower shape, from their values at `c = 5/8`, `u = 3/4` and
the bounds on `D_r`. -/
theorem ur_af_ELw {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (_hu2 : u ≤ 4 / 5) :
    urELr x c u (84 / (36 * x + 25)) < 1 / 3 ∧ urWr x c u (84 / (36 * x + 25)) / 49 < 3 / 4 := by
  obtain ⟨hr1, hr2, hxr⟩ := ur_rf hx hx2
  have e7 := ur_af_k7 hx hx2
  have e8 := ur_af_k8 hx hx2
  set r := 84 / (36 * x + 25) with hr
  have hr1' : 2 / 3 ≤ r := by linarith
  have hr2' : r ≤ 5 / 6 := by linarith
  have hS : 0 < 1 + x := by linarith
  obtain ⟨hDc, hDc'⟩ := ur_Dr_box hx hx2 hc hc2 hr1' hr2'
  obtain ⟨hD5, hD5'⟩ := ur_Dr_box hx hx2 (le_refl (5 / 8 : ℝ)) (by norm_num) hr1' hr2'
  have hDcc : urDr x c r - urDr x (5 / 8) r = (c - 5 / 8) * (2 * (1 - r) * (1 - x * r)) := by
    unfold urDr urd1 urd2; ring
  have hDle : urDr x c r ≤ urDr x (5 / 8) r := by
    have : (c - 5 / 8) * (2 * (1 - r) * (1 - x * r)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
    linarith
  have hN : 19 < (1 + x) * (6 + r ^ 2) := by nlinarith
  constructor
  · have e : urELr x c u r - urELr x (5 / 8) (3 / 4) r =
        (u - 3 / 4) * (2 * urDr x c r - (1 + x) * (6 + r ^ 2)) / 7 +
          3 / 2 * (urDr x c r - urDr x (5 / 8) r) / 7 := by
      unfold urELr urJ2 ssE0; ring
    have : (u - 3 / 4) * (2 * urDr x c r - (1 + x) * (6 + r ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  · have e : urWr x c u r - urWr x (5 / 8) (3 / 4) r =
        -((u - 3 / 4) * (urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r))) +
          (urDr x c r - urDr x (5 / 8) r) * (3 / 4 * (urDr x c r + urDr x (5 / 8) r) -
            ((6 + r ^ 2) * ssE0 x (3 / 4) + (2 * (1 + x) - 1) * r ^ 2)) := by
      unfold urWr ssE0; ring
    have hY : (6 + r ^ 2) * ssE0 x (3 / 4) + (2 * (1 + x) - 1) * r ^ 2 < 203 / 240 := by
      unfold ssE0
      have h1 : 1 / (1 + x) ≤ 6 / 19 := by rw [div_le_iff₀ hS]; linarith
      have h2 : r ^ 2 ≤ 25 / 36 := by nlinarith
      nlinarith
    have h1 : 0 ≤ (u - 3 / 4) * (urDr x c r * ((1 + x) * (6 + r ^ 2) - urDr x c r)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have h2 : (urDr x c r - urDr x (5 / 8) r) * (3 / 4 * (urDr x c r + urDr x (5 / 8) r) -
        ((6 + r ^ 2) * ssE0 x (3 / 4) + (2 * (1 + x) - 1) * r ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have : urWr x c u r ≤ urWr x (5 / 8) (3 / 4) r := by linarith
    linarith

/-! ### The beta comparison on the lower shape -/

theorem ur_hd_Zc (x r c : ℝ) : HasDerivAt (fun s => urZr x s r) (1 - r) c := by
  convert ur_hd_lin (1 - r) (1 + x * r) c using 1
  funext s; unfold urZr; ring

theorem ur_hd_Drc (x r c : ℝ) :
    HasDerivAt (fun s => urDr x s r) (2 * (1 - r) * (1 - x * r)) c := by
  convert ur_hd_lin (2 * (1 - r) * (1 - x * r)) (1 + 2 * x * r + (1 + 2 * x - 2 * x ^ 2) * r ^ 2) c
    using 1
  funext s; unfold urDr urd1 urd2; ring

/-- The `c`-derivative of a test with multiplier `m(Z)` at fixed `x`, `u`, `r`. -/
theorem ur_hd_Htc {x u r c m' : ℝ} {m : ℝ → ℝ} (hm : HasDerivAt m m' (urZr x c r))
    (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => urHt (m (urZr x s r)) x s u r)
      ((1 - r) * ((u - 1) - 1 / urZr x c r ^ 2 + 1 / urZr x c r +
        m' * (urWr x c u r / 49 - 3 / 4)) +
        2 * (1 - r) * (1 - x * r) * (m (urZr x c r) * urELr x c u r - 2 * u) / 7) c := by
  have hZc := ur_hd_Zc x r c
  have hD := ur_hd_Drc x r c
  have hW : HasDerivAt (fun s => urWr x s u r) (2 * (1 - r) * (1 - x * r) *
      (2 * u * urDr x c r - ((6 + r ^ 2) * ssE0 x u + (2 * (1 + x) - 1) * r ^ 2))) c := by
    have := ((hD.mul hD).const_mul u).sub (hD.mul_const ((6 + r ^ 2) * ssE0 x u +
      (2 * (1 + x) - 1) * r ^ 2))
    convert this.const_add ((6 + r ^ 2) ^ 2 - (6 + r ^ 2) * (1 + x) * r ^ 2 + (1 + x) ^ 2 * r ^ 4)
      using 1
    · funext s; unfold urWr; simp only [Pi.mul_apply, Pi.sub_apply]; ring
    · ring
  have hEL : HasDerivAt (fun s => urELr x s u r) (2 * u * (2 * (1 - r) * (1 - x * r)) / 7) c := by
    have := ((hD.const_mul (2 * u)).sub_const (6 * ssE0 x u + urJ2 x u * r ^ 2)).div_const 7
    convert this using 1
    · funext s; unfold urELr; ring
  have hinv : HasDerivAt (fun s => 1 / urZr x s r) (-(1 - r) / urZr x c r ^ 2) c := by
    have := hZc.inv hZ.ne'
    convert this using 1
    · funext s; simp
  have hlog : HasDerivAt (fun s => log (2 * urZr x s r / 7)) ((1 - r) / urZr x c r) c := by
    have := ((hZc.const_mul 2).div_const 7).log (by positivity)
    convert this using 1
    field_simp
  have hmZ := hm.comp c hZc
  have := (((((hZc.const_mul (u - 1)).const_add (6 / 7)).add hinv).sub hEL).add
    (hmZ.mul ((hW.div_const 49).sub_const (3 / 4)))).add hlog
  convert this using 1
  · funext s; simp [urHt, Function.comp]
  · simp only [Function.comp]
    unfold urELr urJ2
    field_simp
    ring

/-- The `c`-slope lower bound on the lower shape: with a multiplier `0 < m ≤ 11/4`, `m' ≤ 0`,
the fixed-norm slope is at least `(1 - r_f)·463/5000`. -/
theorem ur_Htc_lb {x c u m m' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hm : 0 < m) (hm2 : m ≤ 11 / 4)
    (hm' : m' ≤ 0) :
    (1 - 84 / (36 * x + 25)) * (463 / 5000) ≤
      (1 - 84 / (36 * x + 25)) * ((u - 1) - 1 / urZr x c (84 / (36 * x + 25)) ^ 2 +
        1 / urZr x c (84 / (36 * x + 25)) +
        m' * (urWr x c u (84 / (36 * x + 25)) / 49 - 3 / 4)) +
      2 * (1 - 84 / (36 * x + 25)) * (1 - x * (84 / (36 * x + 25))) *
        (m * urELr x c u (84 / (36 * x + 25)) - 2 * u) / 7 := by
  obtain ⟨hr1, hr2, hxr⟩ := ur_rf hx hx2
  obtain ⟨hEL, hw⟩ := ur_af_ELw hx hx2 hc hc2 hu hu2
  set r := 84 / (36 * x + 25) with hr
  have hA : 0 < 36 * x + 25 := by linarith
  have hZ : 14 / 5 ≤ urZr x c r ∧ urZr x c r ≤ 25 / 8 := by
    have e : urZr x c r = (36 * c * x - 59 * c + 120 * x + 25) / (36 * x + 25) := by
      rw [hr]; unfold urZr; field_simp; ring
    rw [e, le_div_iff₀ hA, div_le_iff₀ hA]
    constructor <;> nlinarith
  set p := 1 / urZr x c r with hp
  have hp1 : 8 / 25 ≤ p := by rw [hp, le_div_iff₀ (by linarith)]; linarith
  have hp2 : p ≤ 5 / 14 := by rw [hp, div_le_iff₀ (by linarith)]; linarith
  have hpp : 1 / urZr x c r ^ 2 = p ^ 2 := by rw [hp]; field_simp
  rw [hpp]
  have h1 : 136 / 625 ≤ p - p ^ 2 := by nlinarith
  have h2 : 0 ≤ m' * (urWr x c u r / 49 - 3 / 4) := mul_nonneg_of_nonpos_of_nonpos hm' (by linarith)
  have h3 : m * urELr x c u r ≤ 11 / 12 := by
    rcases le_total (urELr x c u r) 0 with h | h
    · nlinarith
    · nlinarith
  have h4 : 1 / 8 ≤ 2 / 7 * (x * r - 1) * (2 * u - m * urELr x c u r) := by nlinarith
  have hr1' : 0 ≤ 1 - r := by linarith
  have e : 2 * (1 - r) * (1 - x * r) * (m * urELr x c u r - 2 * u) / 7 =
      (1 - r) * (2 / 7 * (x * r - 1) * (2 * u - m * urELr x c u r)) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (show 463 / 5000 ≤ (u - 1) - p ^ 2 + p +
    m' * (urWr x c u r / 49 - 3 / 4) + 2 / 7 * (x * r - 1) * (2 * u - m * urELr x c u r) by
      linarith) hr1'
  linarith

/-- **The beta comparison**: on the lower shape the test with multiplier `M(Z)` and the moving
norm `u_s` increases in `c`. At fixed norm the `c`-slope is at least `κ = (1 - r_f)·463/5000`;
moving the norm costs at most `(13/2)(119/13872)` per unit of `β` (`H_u < 13/2` and the Lipschitz
bound of `u_s`), and `β` moves by `a_f - 1` per unit of `c`, with
`(13/2)(119/13872)(a_f - 1) ≤ κ`. -/
theorem ur_beta_gen {M M' : ℝ → ℝ} {x c c' : ℝ} (hM : ∀ z, 0 < z → HasDerivAt M (M' z) z)
    (hMb : ∀ z, 14 / 5 ≤ z → z ≤ 25 / 8 → 0 < M z ∧ M z ≤ 11 / 4 ∧ M' z ≤ 0)
    (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c) (hcc : c ≤ c') (hc' : c' ≤ 7 / 8) :
    urHt (M (urZr x c (84 / (36 * x + 25)))) x c
        (ssUs x (x + c * ((36 * x + 25) / 84 - 1))) (84 / (36 * x + 25)) ≤
      urHt (M (urZr x c' (84 / (36 * x + 25)))) x c'
        (ssUs x (x + c' * ((36 * x + 25) / 84 - 1))) (84 / (36 * x + 25)) := by
  obtain ⟨hr1, hr2, hxr⟩ := ur_rf hx hx2
  have hA : 0 < 36 * x + 25 := by linarith
  have haf : 0 ≤ (36 * x + 25) / 84 - 1 := by linarith
  have hZbox : ∀ s, 5 / 8 ≤ s → s ≤ 7 / 8 → 14 / 5 ≤ urZr x s (84 / (36 * x + 25)) ∧
      urZr x s (84 / (36 * x + 25)) ≤ 25 / 8 := fun s h1 h2 => by
    have e : urZr x s (84 / (36 * x + 25)) = (36 * s * x - 59 * s + 120 * x + 25) / (36 * x + 25) := by
      unfold urZr; field_simp; ring
    rw [e, le_div_iff₀ hA, div_le_iff₀ hA]
    constructor <;> nlinarith
  set r := 84 / (36 * x + 25) with hr
  set b := x + c * ((36 * x + 25) / 84 - 1) with hb
  set b' := x + c' * ((36 * x + 25) / 84 - 1) with hb'
  have hbx : x ≤ b := by rw [hb]; nlinarith
  have hbb : b ≤ b' := by rw [hb, hb']; nlinarith
  obtain ⟨hu'le, hlip⟩ := ur_Us_lip hx hx2 hbx hbb
  -- the norm `u' = u_s(b')` lies in `[3/4, 4/5]`
  have hu'0 : 3 / 4 ≤ ssUs x b' := by
    have hb1 : 0 < b' - 1 := by linarith
    rw [ur_Us_eq hb1.ne']
    have := (ur_kx_bounds hx hx2).1
    have : 0 ≤ urkx x / (b' - 1) := by positivity
    linarith
  have hu'1 : ssUs x b' ≤ 4 / 5 :=
    (ur_ubar_le hx hx2 (hc.trans hcc)).trans (ur_Vbar_le hx hx2).2.le
  set κ := (1 - r) * (463 / 5000) with hκ
  -- step 1: the fixed-norm slope
  have step1 : urHt (M (urZr x c r)) x c (ssUs x b') r - κ * c ≤
      urHt (M (urZr x c' r)) x c' (ssUs x b') r - κ * c' := by
    apply ss_le_of_deriv (f := fun s => urHt (M (urZr x s r)) x s (ssUs x b') r - κ * s) hcc
    · intro z hz
      have hz1 : 5 / 8 ≤ z := hc.trans hz.1
      have hz2 : z ≤ 7 / 8 := hz.2.trans hc'
      have hZz := hZbox z hz1 hz2
      have hZ0 : 0 < urZr x z r := by linarith [hZz.1]
      exact (ur_hd_Htc (u := ssUs x b') (hM _ hZ0) hZ0).sub ((hasDerivAt_id z).const_mul κ)
    · intro z hz
      have hz1 : 5 / 8 ≤ z := hc.trans hz.1.le
      have hz2 : z ≤ 7 / 8 := hz.2.le.trans hc'
      obtain ⟨hm0, hm1, hm'⟩ := hMb _ (hZbox z hz1 hz2).1 (hZbox z hz1 hz2).2
      have := ur_Htc_lb hx hx2 hz1 hz2 hu'0 hu'1 hm0 hm1 hm'
      simp only [mul_one]
      rw [← hr] at this
      linarith
  -- step 2: the norm motion
  have hZc := hZbox c hc (hcc.trans hc')
  obtain ⟨hm0, hm1, -⟩ := hMb _ hZc.1 hZc.2
  obtain ⟨-, hHu⟩ := ur_Hu_pos (m := M (urZr x c r)) (r := r) hx hx2 hc (hcc.trans hc')
    (by linarith) (by linarith) hm0 (by linarith)
  have step2 := ur_Ht_u (M (urZr x c r)) x c (ssUs x b') (ssUs x b) r
  have hdu : 0 ≤ ssUs x b - ssUs x b' := by linarith
  have h2 : (ssUs x b - ssUs x b') * urHu (M (urZr x c r)) x c r ≤
      (ssUs x b - ssUs x b') * (13 / 2) := mul_le_mul_of_nonneg_left hHu.le hdu
  -- step 3: compare
  have hbd : b' - b = (c' - c) * ((36 * x + 25) / 84 - 1) := by rw [hb, hb']; ring
  have h3 : 13 / 2 * (119 / 13872) * ((c' - c) * ((36 * x + 25) / 84 - 1)) ≤ κ * (c' - c) := by
    have e : (36 * x + 25) / 84 - 1 = (1 - r) * ((36 * x + 25) / 84) := by
      rw [hr]; field_simp
    rw [e, hκ]
    have hcc' : 0 ≤ c' - c := by linarith
    have h1r : 0 ≤ 1 - r := by linarith
    have : (36 * x + 25) / 84 ≤ 557 / 420 := by rw [div_le_iff₀ (by norm_num)]; linarith
    nlinarith [mul_nonneg hcc' h1r]
  nlinarith

/-- The beta comparison for `H₀` (multiplier `4 - Z/2`). -/
theorem ur_beta_H0 {x c c' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hcc : c ≤ c') (hc' : c' ≤ 7 / 8) :
    urH0 x c (ssUs x (x + c * ((36 * x + 25) / 84 - 1))) (84 / (36 * x + 25)) ≤
      urH0 x c' (ssUs x (x + c' * ((36 * x + 25) / 84 - 1))) (84 / (36 * x + 25)) :=
  ur_beta_gen (M := fun z => 4 - z / 2) (M' := fun _ => -(1 / 2))
    (fun z _ => by simpa using ((hasDerivAt_id z).div_const 2).const_sub 4)
    (fun z h1 h2 => ⟨by linarith, by linarith, by norm_num⟩) hx hx2 hc hcc hc'

/-- The beta comparison for `H₁` (multiplier `7/Z + 1/4`). -/
theorem ur_beta_H1 {x c c' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hcc : c ≤ c') (hc' : c' ≤ 7 / 8) :
    urH1 x c (ssUs x (x + c * ((36 * x + 25) / 84 - 1))) (84 / (36 * x + 25)) ≤
      urH1 x c' (ssUs x (x + c' * ((36 * x + 25) / 84 - 1))) (84 / (36 * x + 25)) :=
  ur_beta_gen (M := fun z => 7 / z + 1 / 4) (M' := fun z => -(7 / z ^ 2))
    (fun z hz => by
      have := ((hasDerivAt_inv hz.ne').const_mul 7).add_const (1 / 4)
      convert this using 1
      · funext s; simp [div_eq_mul_inv]
      · ring)
    (fun z h1 h2 => ⟨by positivity, by
      rw [← sub_nonneg]
      have : 7 / z ≤ 5 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith, by have : 0 < z ^ 2 := by positivity
                   have : 0 < 7 / z ^ 2 := by positivity
                   linarith⟩) hx hx2 hc hcc hc'

end SmoothedOctagon

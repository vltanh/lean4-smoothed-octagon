module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Shapes

/-!
# The division coefficient on small shapes

At the largest norm, write the division coefficient as a quartic in the
reciprocal shape `r = 1 / α`. Its linear and quadratic terms increase
together on `r ≥ 5/6`; its remaining nonconstant terms increase separately.
The value at `r = 5/6` increases with the ratio `x ≥ 3/2`. These two
comparisons reduce the lower bound to the corner `(x, α) = (3/2, 6/5)`.
-/

@[expose] public section
namespace SmoothedOctagon

/-- The numerator of `1225(x + 1) w₀(x, 1/r, 19/25)`. -/
noncomputable def lroW0Numerator (x r : ℝ) : ℝ :=
  -36 * x ^ 2 + 847 * x + 1033 +
    r * (4 * x * (18 * x ^ 2 + 17 * x - 76) +
    r * (x * (148 * x ^ 2 + 74 * x - 207) + 42 +
    r * (2 * x * (32 * x ^ 2 + 51 * x - 6) +
    r * (x * (13 * x ^ 2 + 32 * x - 6)))))

theorem lro_w0_reciprocal {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lrow0 x a (19 / 25) = lroW0Numerator x (1 / a) / (1225 * (x + 1)) := by
  have hS : x + 1 ≠ 0 := by linarith
  simp only [lrow0, lroM, lroJ, lroK, ssE0, lroD0, lroW0Numerator]
  field_simp
  ring

/-- Pairing the linear and quadratic increments gives the reciprocal-shape comparison. -/
theorem lro_w0_numerator_ge_base {x r : ℝ} (hx : 3 / 2 ≤ x) (hr : 5 / 6 ≤ r) :
    lroW0Numerator x (5 / 6) ≤ lroW0Numerator x r := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 9 / 4 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 3 / 2)]
  let c1 := 4 * x * (18 * x ^ 2 + 17 * x - 76)
  let c2 := x * (148 * x ^ 2 + 74 * x - 207) + 42
  let c3 := 2 * x * (32 * x ^ 2 + 51 * x - 6)
  let c4 := x * (13 * x ^ 2 + 32 * x - 6)
  have h2 : 0 ≤ c2 := by
    have : 0 ≤ 148 * x ^ 2 + 74 * x - 207 := by linarith
    dsimp [c2]
    positivity
  have h3 : 0 ≤ c3 := by
    have : 0 ≤ 32 * x ^ 2 + 51 * x - 6 := by linarith
    dsimp [c3]
    positivity
  have h4 : 0 ≤ c4 := by
    have : 0 ≤ 13 * x ^ 2 + 32 * x - 6 := by linarith
    dsimp [c4]
    positivity
  have h12 : 0 ≤ c1 + (5 / 3) * c2 := by
    have hq : 0 ≤ 956 * x ^ 2 + 574 * x - 1947 := by linarith
    have he : c1 + (5 / 3) * c2 =
        x / 3 * (956 * x ^ 2 + 574 * x - 1947) + 70 := by
      dsimp [c1, c2]
      ring
    rw [he]
    positivity
  have hpair : 0 ≤ (r - 5 / 6) * (c1 + c2 * (r + 5 / 6)) := by
    have hp := mul_nonneg h2 (sub_nonneg.mpr hr)
    exact mul_nonneg (sub_nonneg.mpr hr) (by nlinarith only [hp, h12])
  have hp3 := mul_nonneg h3 (sub_nonneg.mpr
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 6) hr 3))
  have hp4 := mul_nonneg h4 (sub_nonneg.mpr
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 6) hr 4))
  have he : lroW0Numerator x r - lroW0Numerator x (5 / 6) =
      (r - 5 / 6) * (c1 + c2 * (r + 5 / 6)) +
      c3 * (r ^ 3 - (5 / 6) ^ 3) + c4 * (r ^ 4 - (5 / 6) ^ 4) := by
    dsimp [lroW0Numerator, c1, c2, c3, c4]
    ring
  exact sub_nonneg.mp (he ▸ add_nonneg (add_nonneg hpair hp3) hp4)

/-- At the largest shape, the ratio comparison reduces to a positive quadratic. -/
theorem lro_w0_base_ge_corner {x : ℝ} (hx : 3 / 2 ≤ x) :
    633019 / 705600 ≤ lroW0Numerator x (5 / 6) / (1225 * (x + 1)) := by
  have hx0 : 0 ≤ x := by linarith
  have hS : x + 1 ≠ 0 := by linarith
  have he : lroW0Numerator x (5 / 6) / (1225 * (x + 1)) - 633019 / 705600 =
      (2 * x - 3) * (534170 * x ^ 2 + 1181023 * x + 63633) /
        (6350400 * (x + 1)) := by
    unfold lroW0Numerator
    field_simp
    ring
  have hp : 0 ≤ (2 * x - 3) * (534170 * x ^ 2 + 1181023 * x + 63633) /
      (6350400 * (x + 1)) := by
    have : 0 ≤ 2 * x - 3 := by linarith
    positivity
  linarith only [he, hp]

/-- The small-shape division coefficient has the round lower bound `8/9`. -/
theorem lro_small_shape_w0 {x a u : ℝ} (hx : 3 / 2 ≤ x) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hu : u ≤ 19 / 25) : 8 / 9 < lrow0 x a u := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hr : 5 / 6 ≤ 1 / a := (le_div_iff₀ ha0).mpr (by linarith)
  have hnum := lro_w0_numerator_ge_base hx hr
  have hbase := lro_w0_base_ge_corner hx
  have hS : 0 < 1225 * (x + 1) := by positivity
  have htop : 8 / 9 < lrow0 x a (19 / 25) := by
    rw [lro_w0_reciprocal hx0 ha0]
    have hd := div_le_div_of_nonneg_right hnum hS.le
    have hc : (8 / 9 : ℝ) < 633019 / 705600 := by norm_num
    exact hc.trans_le (hbase.trans hd)
  obtain ⟨hD0, hD1⟩ := lro_KS_D0 ha1 (by linarith : a ≤ x)
  have hm := lro_w0_diff' (u := u) (u' := 19 / 25) hx0 ha0
  have hp : 0 ≤ (19 / 25 - u) * lroD0 x a * (lroK a * (1 + x) - lroD0 x a) /
      (49 * a ^ 4) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) hD0.le)
      (sub_nonneg.mpr hD1.le)) (by positivity)
  linarith only [hm, hp, htop]

end SmoothedOctagon

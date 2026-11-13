module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Shapes

/-!
# The residue on the outer ratio interval

At the pole of the reciprocal-shape denominator, the transport polynomial
factors as `(v - 1)((2x + 1)v + 1)`. The quartic decreases with the norm.
At the upper norm, four round coefficient bounds reduce its lower bound
to a sum of squares. This proves the residue sign throughout the rectangle.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioResidue

noncomputable def transport (x v : ℝ) : ℝ := (v - 1) * ((2 * x + 1) * v + 1)

/-- The transport quartic evaluated at the pole `r = -v`. -/
noncomputable def poleValue (x v u : ℝ) : ℝ :=
  36 + (12 - 6 * (x + 1)) * v ^ 2 + ((x + 1) ^ 2 - (x + 1) + 1) * v ^ 4 +
    u * transport x v ^ 2 - transport x v * (6 * ssE0 x u + lrJ2 x u * v ^ 2)

theorem residue_eq {x C u : ℝ} (he : 0 < x - C) :
    lrQ1 x C u = (119 / 4 - poleValue x ((1 + C) / (x - C)) u) / 96 := by
  let v := (1 + C) / (x - C)
  have hd : lrd0 C - lrd1 x C * v + lrd2 x C * v ^ 2 = transport x v := by
    dsimp [v, lrd0, lrd1, lrd2, transport]
    field_simp
    ring
  have hw : lrW0 x C u - lrW1 x C u * v + lrW2 x C u * v ^ 2 -
      lrW3 x C u * v ^ 3 + lrW4 x C u * v ^ 4 = poleValue x v u := by
    have hid : lrW0 x C u - lrW1 x C u * v + lrW2 x C u * v ^ 2 -
        lrW3 x C u * v ^ 3 + lrW4 x C u * v ^ 4 =
        36 + (12 - 6 * (x + 1)) * v ^ 2 + ((x + 1) ^ 2 - (x + 1) + 1) * v ^ 4 +
        u * (lrd0 C - lrd1 x C * v + lrd2 x C * v ^ 2) ^ 2 -
        (lrd0 C - lrd1 x C * v + lrd2 x C * v ^ 2) *
          (6 * ssE0 x u + lrJ2 x u * v ^ 2) := by
      unfold lrW0 lrW1 lrW2 lrW3 lrW4
      ring
    rw [hid, hd]
    rfl
  have hq : lrQ1 x C u = (119 / 4 -
      (lrW0 x C u - lrW1 x C u * v + lrW2 x C u * v ^ 2 -
        lrW3 x C u * v ^ 3 + lrW4 x C u * v ^ 4)) / 96 := by
    dsimp [v, lrQ1, lrq0, lrq1, lrq2, lrq3]
    field_simp
    ring
  exact hq.trans (by rw [hw])

theorem norm_difference {x v u u' : ℝ} (hx : 0 < x) :
    poleValue x v u - poleValue x v u' =
      (u - u') * (transport x v * (x * (v - 1) ^ 2 - 7 * (x + 1))) := by
  have hS : x + 1 ≠ 0 := by linarith
  unfold poleValue transport lrJ2 ssE0
  field_simp
  ring

theorem ge_upper_norm {x v u : ℝ} (hx : 3 / 2 ≤ x) (hv0 : 1 ≤ v) (hv1 : v ≤ 3)
    (hu : u ≤ 19 / 25) : poleValue x v (19 / 25) ≤ poleValue x v u := by
  have hD : 0 ≤ transport x v := by
    unfold transport
    exact mul_nonneg (by linarith) (by positivity)
  have hq : (v - 1) ^ 2 ≤ 4 := by nlinarith
  have ht : x * (v - 1) ^ 2 - 7 * (x + 1) ≤ 0 := by nlinarith
  have hs := mul_nonpos_of_nonneg_of_nonpos hD ht
  have hp := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hu) hs
  have hd := norm_difference (v := v) (u := u) (u' := 19 / 25) (by linarith : 0 < x)
  linarith only [hd, hp]

noncomputable def c0 (x : ℝ) : ℝ := (x + 1) * (4 * x ^ 2 - 20 * x + 53) / 4
noncomputable def c1 (x : ℝ) : ℝ := 14 * (x + 1) * (2 * x - 3) * (3 * x - 2) / 25
noncomputable def c2 (x : ℝ) : ℝ := (34 * x ^ 3 - 40 * x ^ 2 - 207 * x + 42) / 25
noncomputable def c3 (x : ℝ) : ℝ := -2 * x * (2 * x - 3) * (3 * x - 2) / 25
noncomputable def c4 (x : ℝ) : ℝ := x * (13 * x ^ 2 + 32 * x - 6) / 25

theorem pole_expansion {x q : ℝ} (hx : 0 < x) :
    (x + 1) * (poleValue x (1 + q) (19 / 25) - 119 / 4) =
      c0 x + c1 x * q + c2 x * q ^ 2 + c3 x * q ^ 3 + c4 x * q ^ 4 := by
  have hS : x + 1 ≠ 0 := by linarith
  unfold poleValue transport lrJ2 ssE0 c0 c1 c2 c3 c4
  field_simp
  ring

theorem c0_bound {x : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) : 18 ≤ c0 x := by
  have hp := mul_nonneg (show 0 ≤ 2 - x by linarith) (show 0 ≤ 3 - x by linarith)
  have hq : 29 / 4 ≤ (4 * x ^ 2 - 20 * x + 53) / 4 := by nlinarith only [hp]
  have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ x + 1 by linarith)
  unfold c0
  nlinarith only [hx, hm]

theorem c1_nonneg {x : ℝ} (hx : 3 / 2 ≤ x) : 0 ≤ c1 x := by
  have h1 : 0 ≤ 2 * x - 3 := by linarith
  have h2 : 0 ≤ 3 * x - 2 := by linarith
  unfold c1
  positivity

theorem c2_bound {x : ℝ} (hx : 3 / 2 ≤ x) : -11 ≤ c2 x := by
  have ht : 0 ≤ x - 3 / 2 := by linarith
  have hid : 25 * (c2 x + 11) =
      34 * (x - 3 / 2) ^ 3 + 13 * (x - 3 / 2) ^ 2 + (5 / 2) * (x - 3 / 2) +
        100 * (x - 2) ^ 2 + 25 / 4 := by unfold c2; ring
  have hp : 0 ≤ 34 * (x - 3 / 2) ^ 3 + 13 * (x - 3 / 2) ^ 2 +
      (5 / 2) * (x - 3 / 2) + 100 * (x - 2) ^ 2 + 25 / 4 := by positivity
  linarith only [hid, hp]

theorem c3_bound {x : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) : -1 ≤ c3 x := by
  have hp : (2 * x - 3) * (3 * x - 2) ≤ 4 :=
    (mul_le_mul (show 2 * x - 3 ≤ 1 by linarith) (show 3 * x - 2 ≤ 4 by linarith)
      (by linarith) (by norm_num)).trans_eq (by norm_num)
  have hn : 0 ≤ (2 * x - 3) * (3 * x - 2) := mul_nonneg (by linarith) (by linarith)
  have hm := mul_nonneg (show 0 ≤ 4 - 2 * x by linarith) hn
  unfold c3
  nlinarith only [hp, hm]

theorem c4_bound {x : ℝ} (hx : 3 / 2 ≤ x) : 4 ≤ c4 x := by
  have hq : 285 / 4 ≤ 13 * x ^ 2 + 32 * x - 6 := by
    nlinarith [sq_nonneg (x - 3 / 2)]
  have hm := mul_le_mul hx hq (by norm_num : (0 : ℝ) ≤ 285 / 4) (by linarith : 0 ≤ x)
  unfold c4
  nlinarith only [hm]

/-- The rounded quartic is a sum of squares with constant term four. -/
theorem quartic_bound (q : ℝ) : 4 ≤ 18 - 11 * q ^ 2 - q ^ 3 + 4 * q ^ 4 := by
  have hid : 18 - 11 * q ^ 2 - q ^ 3 + 4 * q ^ 4 =
      4 + (7 / 2) * (q ^ 2 - 2) ^ 2 + (5 / 2) * q ^ 2 +
        (1 / 2) * q ^ 2 * (q - 1) ^ 2 := by ring
  nlinarith only [hid, sq_nonneg (q ^ 2 - 2), sq_nonneg q,
    mul_nonneg (sq_nonneg q) (sq_nonneg (q - 1))]

theorem pole_value_gt {x v u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2)
    (hv0 : 1 ≤ v) (hv1 : v ≤ 3) (hu : u ≤ 19 / 25) : 119 / 4 < poleValue x v u := by
  have hq : 0 ≤ v - 1 := by linarith
  have h0 := c0_bound hx hx2
  have h1 := mul_nonneg (c1_nonneg hx) hq
  have h2 := mul_nonneg (show 0 ≤ c2 x + 11 by linarith [c2_bound hx]) (sq_nonneg (v - 1))
  have h3 := mul_nonneg (show 0 ≤ c3 x + 1 by linarith [c3_bound hx hx2])
    (show 0 ≤ (v - 1) ^ 3 by positivity)
  have h4 := mul_nonneg (show 0 ≤ c4 x - 4 by linarith [c4_bound hx])
    (show 0 ≤ (v - 1) ^ 4 by positivity)
  have hs := quartic_bound (v - 1)
  have he := pole_expansion (q := v - 1) (by linarith : 0 < x)
  rw [show 1 + (v - 1) = v by ring] at he
  have hp : 0 < (x + 1) * (poleValue x v (19 / 25) - 119 / 4) := by
    nlinarith only [he, h0, h1, h2, h3, h4, hs]
  have hb : 119 / 4 < poleValue x v (19 / 25) := by nlinarith only [hp, hx]
  exact hb.trans_le (ge_upper_norm hx hv0 hv1 hu)

end LowerRatioResidue

/-- The outer residue is negative on the enlarged displacement interval. -/
theorem lro_residue_neg {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 4 / 5) (hu : u ≤ 19 / 25) : lrQ1 x C u < 0 := by
  have he : 0 < x - C := by linarith
  have hv0 : 1 ≤ (1 + C) / (x - C) := (le_div_iff₀ he).mpr (by linarith)
  have hv1 : (1 + C) / (x - C) ≤ 3 := (div_le_iff₀ he).mpr (by linarith)
  have hp := LowerRatioResidue.pole_value_gt hx hx2 hv0 hv1 hu
  rw [LowerRatioResidue.residue_eq he]
  exact div_neg_of_neg_of_pos (by linarith only [hp]) (by norm_num)

end SmoothedOctagon

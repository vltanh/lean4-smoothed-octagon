module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestZeroSigns

/-!
# Smaller-short window, lower ratio, outer face, small shapes: the test `F₀`

On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`, `x ≤ β ≤ x + (10/13)(α - 1)`,
`u_f ≤ u ≤ u_ℓ(x, β)`:

* norm concavity at the actual point reduces `u` to the two curves `u_f(x)`, `u_ℓ(x, β)`;
* `β ↦ F₀` decreases with slope `≤ -7/5120` at a fixed norm (`lro_F0_bmono`), and along the ceiling
  `u_ℓ(x, β)` as well: `(F₀)_u ≥ -1/6` on the capped strip (`(F₀)_u` is affine
  decreasing in `u` and concave in `β`) and `0 ≤ -(u_ℓ)_β ≤ 15/1992`; so `C = 10/13`;
* at `C = 10/13`, `α ↦ F₀` increases at a fixed norm: in the reciprocal shape
  `g′(r) ≤ P′(r) + ce/Z² - (399/400)ce/Z ≤ -1/400` (`ℓ′(y) ≥ (1 - (5/23)⁴)/y`, and
  `P′ = Σ i pᵢ r^{i-1}` decreases in `u ≥ 3/4`); along the ceiling the norm motion costs at most
  `(1/4)(15/1992)(10/13)` per unit of `α` since `(F₀)_u ≤ Γ_u ≤ 1/4`; so
  `α = α_*(x)`, `1` on `x ≤ 5/3`, `(45x + 22)/97` on `x ≥ 5/3`;
* the four terminal curves are positive.

The shape derivative is bounded through the reciprocal-shape form at the single slope
`C = 10/13` (two-variable signs in `(x, r)`), and the terminal curves are cleared and bounded
termwise.

## Main API

* `lro_F0_uquad`, `lro_B_F0u_ge`, `lro_B_F0u_le`, `lro_F0_bmono_ul`, `lro_B_amono`,
  `lro_B_amono_ul`, `lro_B_F0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real



/-! ### The norm derivative of `F₀` -/

/-- `F₀` is a concave quadratic in `u` with derivative `Γ_u - cR_u`. -/
theorem lro_F0_uquad {x a b u1 u2 : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lroF0 x a b u1 - lroF0 x a b u2 = (u1 - u2) * (lroGu x a u2 - 7 / 96 * lroR2u x a b) -
      (u1 - u2) ^ 2 * (1 + x) ^ 2 * lroK a ^ 2 / (576 * a ^ 4) := by
  have hK : lroK a ≠ 0 := by unfold lroK; positivity
  simp only [lroF0, lroR2, lrow, lroEL, lroG, lroGu, lroR2u, lrowu, lroE]
  field_simp
  ring

theorem lro_Gu_diff {x a u u' : ℝ} (_hx : 0 < x) (_ha : 0 < a) :
    lroGu x a u - lroGu x a u' = (u' - u) * (2 * (1 + x) ^ 2 * lroK a ^ 2 / (576 * a ^ 4)) := by
  simp only [lroGu, lroE]
  ring

/-- `(F₀)_u ≥ -1/6` on the capped strip: `(F₀)_u` is concave in `β` and at least `-1/6` at
`β = x` and `β = αx` (at `u = 19/25`, where it is smallest). -/
theorem lro_B_F0u_ge {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hcap : x * (x + 2) ≤ 6 * a ^ 2) (hxb : x ≤ b) (hbx : b ≤ a * x) (hu : u ≤ 19 / 25) :
    -(1 / 6) ≤ lroGu x a u - 7 / 96 * lroR2u x a b := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hG := lro_Gu_diff (u := u) (u' := 19 / 25) hx0 ha0
  have hG0 : 0 ≤ (19 / 25 - u) * (2 * (1 + x) ^ 2 * lroK a ^ 2 / (576 * a ^ 4)) :=
    mul_nonneg (by linarith) (by positivity)
  have hK : 6 * a ^ 2 + 1 ≠ 0 := by positivity
  have ha0' : a ≠ 0 := ha0.ne'
  have hid : ∀ s, (a * x - x) * (lroGu x a (19 / 25) - 7 / 96 * lroR2u x a s) -
      (a * x - s) * (lroGu x a (19 / 25) - 7 / 96 * lroR2u x a x) -
        (s - x) * (lroGu x a (19 / 25) - 7 / 96 * lroR2u x a (a * x)) =
      (x - a) ^ 2 / (84 * a ^ 4) * (s - x) * (a * x - s) * (a * x - x) := by
    intro s
    simp only [lroR2u, lrowu, lrod, ssDg]
    generalize lroGu x a (19 / 25) = G
    generalize lroL a = L
    field_simp
    ring
  have hm := lr_conc3 (f := fun s => lroGu x a (19 / 25) - 7 / 96 * lroR2u x a s) hxb hbx
    (by positivity) hid
  have hS : 1 + x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hend1 : -(1 / 6) ≤ lroGu x a (19 / 25) - 7 / 96 * lroR2u x a x := by
    rcases le_total x (7 / 4) with h74 | h74
    · have hP0 : 0 ≤ lrPhX1 (x - 3 / 2) (a - 1) / a ^ 4 :=
        div_nonneg (lrPhX1_pos (t := x - 3 / 2) (s := a - 1) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : lroGu x a (19 / 25) - 7 / 96 * lroR2u x a (x) + 1 / 6 =
          lrPhX1 (x - 3 / 2) (a - 1) / a ^ 4 := by
        simp only [lroGu, lroR2u, lrowu, lrod, lroL, lrov, lroE, lroK, ssDg, lrPhX1]
        field_simp
        ring
      linarith
    · have h47 : 4 * x / 7 ≤ a := by
        have : (4 * x / 7) ^ 2 ≤ a ^ 2 := by nlinarith
        nlinarith [sq_nonneg (a - 4 * x / 7)]
      have hP0 : 0 ≤ lrPhX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 :=
        div_nonneg (lrPhX2_pos (t := x - 7 / 4) (s := a - 4 * x / 7) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : lroGu x a (19 / 25) - 7 / 96 * lroR2u x a (x) + 1 / 6 =
          lrPhX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 := by
        simp only [lroGu, lroR2u, lrowu, lrod, lroL, lrov, lroE, lroK, ssDg, lrPhX2]
        field_simp
        ring
      linarith
  have hend2 : -(1 / 6) ≤ lroGu x a (19 / 25) - 7 / 96 * lroR2u x a (a * x) := by
    rcases le_total x (7 / 4) with h74 | h74
    · have hP0 : 0 ≤ lrPhAX1 (x - 3 / 2) (a - 1) / a ^ 4 :=
        div_nonneg (lrPhAX1_pos (t := x - 3 / 2) (s := a - 1) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : lroGu x a (19 / 25) - 7 / 96 * lroR2u x a (a * x) + 1 / 6 =
          lrPhAX1 (x - 3 / 2) (a - 1) / a ^ 4 := by
        simp only [lroGu, lroR2u, lrowu, lrod, lroL, lrov, lroE, lroK, ssDg, lrPhAX1]
        field_simp
        ring
      linarith
    · have h47 : 4 * x / 7 ≤ a := by
        have : (4 * x / 7) ^ 2 ≤ a ^ 2 := by nlinarith
        nlinarith [sq_nonneg (a - 4 * x / 7)]
      have hP0 : 0 ≤ lrPhAX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 :=
        div_nonneg (lrPhAX2_pos (t := x - 7 / 4) (s := a - 4 * x / 7) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : lroGu x a (19 / 25) - 7 / 96 * lroR2u x a (a * x) + 1 / 6 =
          lrPhAX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 := by
        simp only [lroGu, lroR2u, lrowu, lrod, lroL, lrov, lroE, lroK, ssDg, lrPhAX2]
        field_simp
        ring
      linarith
  have := le_trans (le_min hend1 hend2) hm
  linarith

/-- `(F₀)_u ≤ 1/4` on the strip for `u ≥ 3/4`: `Γ_u ≤ Γ_u(3/4) ≤ 1/4` and `(R₂)_u ≥ 0`. -/
theorem lro_B_F0u_le {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hxb : x ≤ b) (hu : 3 / 4 ≤ u) : lroGu x a u - 7 / 96 * lroR2u x a b ≤ 1 / 4 := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hG := lro_Gu_diff (u := u) (u' := 3 / 4) hx0 ha0
  have hG0 : (3 / 4 - u) * (2 * (1 + x) ^ 2 * lroK a ^ 2 / (576 * a ^ 4)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hG34 : lroGu x a (3 / 4) ≤ 1 / 4 := by
    have hid : 1 / 4 - lroGu x a (3 / 4) = lrPGu (x - 3 / 2) (a - 1) / a ^ 4 := by
      simp only [lroGu, lrov, lroE, lroK, lrPGu]
      field_simp
      ring
    have := lrPGu_pos (t := x - 3 / 2) (s := a - 1) (by linarith) (by linarith) (by linarith)
      (by linarith)
    have : 0 ≤ lrPGu (x - 3 / 2) (a - 1) / a ^ 4 := div_nonneg this (by positivity)
    linarith
  -- `R_u ≥ B/α - 1/2 ≥ 0` from `δ ≤ 1/2`
  have hR : 0 ≤ lroR2u x a b := by
    have e : lroR2u x a b = 2 * lrod x a b ^ 2 - 2 * lrod x a b * (lroL a * (1 + x) + 1) +
        (a + b) / a + lroL a * (1 + x) := by
      unfold lroR2u lrowu; ring
    have hd : lrod x a b ≤ 1 / 2 := by
      unfold lrod
      rw [div_le_iff₀ (by positivity)]
      unfold ssDg
      nlinarith [mul_nonneg (sub_nonneg.2 ha1) (by linarith : (0 : ℝ) ≤ 5 / 2 * (a + 1) - 2 * x),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3 / 2) (by linarith : (0 : ℝ) ≤ x - 1 / 2),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - a) (by linarith : (0 : ℝ) ≤ b - x)]
    have hL : 0 ≤ lroL a * (1 + x) := by unfold lroL lroK; positivity
    have hB : 1 ≤ (a + b) / a := by rw [le_div_iff₀ ha0]; linarith
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - lrod x a b)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - lrod x a b + lroL a * (1 + x))]
  linarith

end SmoothedOctagon

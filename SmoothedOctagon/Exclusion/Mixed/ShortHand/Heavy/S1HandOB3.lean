module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB2

/-!
# Gate S1 by hand, outer face, branch B: the test `F₀`

On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`, `x ≤ β ≤ x + (10/13)(α - 1)`,
`u_f ≤ u ≤ u_ℓ(x, β)`:

* norm concavity at the actual point reduces `u` to the two curves `u_f(x)`, `u_ℓ(x, β)`;
* `β ↦ F₀` decreases with slope `≤ -7/5120` at a fixed norm (`hl1o_F0_bmono`), and along the ceiling
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

* `hl1o_F0_uquad`, `hl1o_B_F0u_ge`, `hl1o_B_F0u_le`, `hl1o_F0_bmono_ul`, `hl1o_B_amono`,
  `hl1o_B_amono_ul`, `hl1o_B_F0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real



/-! ### The norm derivative of `F₀` -/

/-- `F₀` is a concave quadratic in `u` with derivative `Γ_u - cR_u`. -/
theorem hl1o_F0_uquad {x a b u1 u2 : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hh1oF0 x a b u1 - hh1oF0 x a b u2 = (u1 - u2) * (hh1oGu x a u2 - 7 / 96 * hh1oR2u x a b) -
      (u1 - u2) ^ 2 * (1 + x) ^ 2 * hh1oK a ^ 2 / (576 * a ^ 4) := by
  have hK : hh1oK a ≠ 0 := by unfold hh1oK; positivity
  simp only [hh1oF0, hh1oR2, hh1ow, hh1oEL, hh1oG, hh1oGu, hh1oR2u, hh1owu, hh1oE]
  field_simp
  ring

theorem hl1o_Gu_diff {x a u u' : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hh1oGu x a u - hh1oGu x a u' = (u' - u) * (2 * (1 + x) ^ 2 * hh1oK a ^ 2 / (576 * a ^ 4)) := by
  simp only [hh1oGu, hh1oE]
  ring

/-- `(F₀)_u ≥ -1/6` on the capped strip: `(F₀)_u` is concave in `β` and at least `-1/6` at
`β = x` and `β = αx` (at `u = 19/25`, where it is smallest). -/
theorem hl1o_B_F0u_ge {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hcap : x * (x + 2) ≤ 6 * a ^ 2) (hxb : x ≤ b) (hbx : b ≤ a * x) (hu : u ≤ 19 / 25) :
    -(1 / 6) ≤ hh1oGu x a u - 7 / 96 * hh1oR2u x a b := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hG := hl1o_Gu_diff (u := u) (u' := 19 / 25) hx0 ha0
  have hG0 : 0 ≤ (19 / 25 - u) * (2 * (1 + x) ^ 2 * hh1oK a ^ 2 / (576 * a ^ 4)) :=
    mul_nonneg (by linarith) (by positivity)
  have hK : 6 * a ^ 2 + 1 ≠ 0 := by positivity
  have ha0' : a ≠ 0 := ha0.ne'
  have hid : ∀ s, (a * x - x) * (hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a s) -
      (a * x - s) * (hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a x) -
        (s - x) * (hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a (a * x)) =
      (x - a) ^ 2 / (84 * a ^ 4) * (s - x) * (a * x - s) * (a * x - x) := by
    intro s
    simp only [hh1oR2u, hh1owu, hh1od, hsDg]
    generalize hh1oGu x a (19 / 25) = G
    generalize hh1oL a = L
    field_simp
    ring
  have hm := hl1_conc3 (f := fun s => hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a s) hxb hbx
    (by positivity) hid
  have hS : 1 + x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hend1 : -(1 / 6) ≤ hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a x := by
    rcases le_total x (7 / 4) with h74 | h74
    · have hP0 : 0 ≤ hl1PhX1 (x - 3 / 2) (a - 1) / a ^ 4 :=
        div_nonneg (hl1PhX1_pos (t := x - 3 / 2) (s := a - 1) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a (x) + 1 / 6 =
          hl1PhX1 (x - 3 / 2) (a - 1) / a ^ 4 := by
        simp only [hh1oGu, hh1oR2u, hh1owu, hh1od, hh1oL, hh1ov, hh1oE, hh1oK, hsDg, hl1PhX1]
        field_simp
        ring
      linarith
    · have h47 : 4 * x / 7 ≤ a := by
        have : (4 * x / 7) ^ 2 ≤ a ^ 2 := by nlinarith
        nlinarith [sq_nonneg (a - 4 * x / 7)]
      have hP0 : 0 ≤ hl1PhX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 :=
        div_nonneg (hl1PhX2_pos (t := x - 7 / 4) (s := a - 4 * x / 7) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a (x) + 1 / 6 =
          hl1PhX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 := by
        simp only [hh1oGu, hh1oR2u, hh1owu, hh1od, hh1oL, hh1ov, hh1oE, hh1oK, hsDg, hl1PhX2]
        field_simp
        ring
      linarith
  have hend2 : -(1 / 6) ≤ hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a (a * x) := by
    rcases le_total x (7 / 4) with h74 | h74
    · have hP0 : 0 ≤ hl1PhAX1 (x - 3 / 2) (a - 1) / a ^ 4 :=
        div_nonneg (hl1PhAX1_pos (t := x - 3 / 2) (s := a - 1) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a (a * x) + 1 / 6 =
          hl1PhAX1 (x - 3 / 2) (a - 1) / a ^ 4 := by
        simp only [hh1oGu, hh1oR2u, hh1owu, hh1od, hh1oL, hh1ov, hh1oE, hh1oK, hsDg, hl1PhAX1]
        field_simp
        ring
      linarith
    · have h47 : 4 * x / 7 ≤ a := by
        have : (4 * x / 7) ^ 2 ≤ a ^ 2 := by nlinarith
        nlinarith [sq_nonneg (a - 4 * x / 7)]
      have hP0 : 0 ≤ hl1PhAX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 :=
        div_nonneg (hl1PhAX2_pos (t := x - 7 / 4) (s := a - 4 * x / 7) (by linarith) (by linarith) (by linarith)
          (by linarith)) (by positivity)
      have hid2 : hh1oGu x a (19 / 25) - 7 / 96 * hh1oR2u x a (a * x) + 1 / 6 =
          hl1PhAX2 (x - 7 / 4) (a - 4 * x / 7) / a ^ 4 := by
        simp only [hh1oGu, hh1oR2u, hh1owu, hh1od, hh1oL, hh1ov, hh1oE, hh1oK, hsDg, hl1PhAX2]
        field_simp
        ring
      linarith
  have := le_trans (le_min hend1 hend2) hm
  linarith

/-- `(F₀)_u ≤ 1/4` on the strip for `u ≥ 3/4`: `Γ_u ≤ Γ_u(3/4) ≤ 1/4` and `(R₂)_u ≥ 0`. -/
theorem hl1o_B_F0u_le {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hxb : x ≤ b) (hu : 3 / 4 ≤ u) : hh1oGu x a u - 7 / 96 * hh1oR2u x a b ≤ 1 / 4 := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hG := hl1o_Gu_diff (u := u) (u' := 3 / 4) hx0 ha0
  have hG0 : (3 / 4 - u) * (2 * (1 + x) ^ 2 * hh1oK a ^ 2 / (576 * a ^ 4)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hG34 : hh1oGu x a (3 / 4) ≤ 1 / 4 := by
    have hid : 1 / 4 - hh1oGu x a (3 / 4) = hl1PGu (x - 3 / 2) (a - 1) / a ^ 4 := by
      simp only [hh1oGu, hh1ov, hh1oE, hh1oK, hl1PGu]
      field_simp
      ring
    have := hl1PGu_pos (t := x - 3 / 2) (s := a - 1) (by linarith) (by linarith) (by linarith)
      (by linarith)
    have : 0 ≤ hl1PGu (x - 3 / 2) (a - 1) / a ^ 4 := div_nonneg this (by positivity)
    linarith
  -- `R_u ≥ B/α - 1/2 ≥ 0` from `δ ≤ 1/2`
  have hR : 0 ≤ hh1oR2u x a b := by
    have e : hh1oR2u x a b = 2 * hh1od x a b ^ 2 - 2 * hh1od x a b * (hh1oL a * (1 + x) + 1) +
        (a + b) / a + hh1oL a * (1 + x) := by
      unfold hh1oR2u hh1owu; ring
    have hd : hh1od x a b ≤ 1 / 2 := by
      unfold hh1od
      rw [div_le_iff₀ (by positivity)]
      unfold hsDg
      nlinarith [mul_nonneg (sub_nonneg.2 ha1) (by linarith : (0 : ℝ) ≤ 5 / 2 * (a + 1) - 2 * x),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3 / 2) (by linarith : (0 : ℝ) ≤ x - 1 / 2),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - a) (by linarith : (0 : ℝ) ≤ b - x)]
    have hL : 0 ≤ hh1oL a * (1 + x) := by unfold hh1oL hh1oK; positivity
    have hB : 1 ≤ (a + b) / a := by rw [le_div_iff₀ ha0]; linarith
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - hh1od x a b)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - hh1od x a b + hh1oL a * (1 + x))]
  linarith

end SmoothedOctagon

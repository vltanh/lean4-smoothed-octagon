module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOCurv

/-!
# Gate S3, the outer face by hand: the upper shape `α = x`

Hand proof of the leaf `hs3_outer_face`, seventh part: `SHORT_DISPLACEMENT_OUTER_TERMINALS.md` §4
with `SHORT_DISPLACEMENT_OUTER_TERMINAL_ALGEBRA.md` §4. At `r = 1/x`, the lower slope
`C ≥ 8x/(9x + 8)` gives `ū - 3/4 ≤ 238/30381 < 1/125` (the note's (10)); with `A_n > 1` the norm is
raised to `379/500` and the logarithm constant to `16/9`. The resulting bound `H_n(x, C)` is
`ψ(Z) + const` with `ψ(z) = -121z/500 + 1/z - 56/(5z + 14)` decreasing (`f(z) < 121/500`, (11)), so the
lower slope is extremal; `H_n` increases in `n` (`w(379/500) > 3/4`, (12)); and
`H_{7/2}(x, 8x/(9x + 8)) = W(h)/(63000x³S(9x + 8)(13x + 4)(32x + 19)) < 0` ((13)).

## Main API

* `hl3o_up`: `G(x, C, n, 1/x) < 0` for `8x/(9x + 8) ≤ C ≤ 5/6`, `5/2 ≤ n ≤ 7/2`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The upper-face bound `H_n(x, C)`: norm `379/500`, logarithm constant `16/9`. -/
noncomputable def hl3oHup (x C n : ℝ) : ℝ :=
  hl3oP x C n (1 / x) + 1 / 125 * hl3oA x C n (1 / x) + hl3oPhi x C (1 / x) + 153 / 180000

/-- `ψ(z) = -121z/500 + 1/z - 56/(5z + 14)`. -/
noncomputable def hl3oψ (z : ℝ) : ℝ := -(121 / 500) * z + (1 / z - 56 / (5 * z + 14))

theorem hl3_hd_ψ {z : ℝ} (hz : 0 < z) : HasDerivAt hl3oψ (-(121 / 500) + hl3of z) z := by
  have h5 : 5 * z + 14 ≠ 0 := by positivity
  have := ((hasDerivAt_id z).const_mul (-(121 / 500))).add
    (((hasDerivAt_const z (1 : ℝ)).fun_div (hasDerivAt_id z) hz.ne').sub
      ((hasDerivAt_const z (56 : ℝ)).fun_div (((hasDerivAt_id z).const_mul 5).add_const 14) h5))
  unfold hl3oψ hl3of
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

section Up

variable {x C n : ℝ}

/-- `ū - 3/4 = V(1/x) = c(C + 2)/(C + 1) < 1/125` for `C ≥ 8x/(9x + 8)` (the note's (10)). -/
theorem hl3o_V_up (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 8 * x / (9 * x + 8) ≤ C) :
    hl3oV x C (1 / x) ≤ 1 / 125 := by
  have hx0 : 0 < x := by linarith
  have hC0 : 8 / 13 ≤ C := by
    have : 8 / 13 ≤ 8 * x / (9 * x + 8) := by rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  have hc : hl3oc x ≤ 49 / 10127 := by
    unfold hl3oc
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx2) (by linarith : (0 : ℝ) ≤ 8412 * x - 4380)]
  have e : hl3oV x C (1 / x) = hl3oc x * (C + 2) / (C + 1) := by
    unfold hl3oV
    have h1 : C + (x - C - 1) * (1 / x) = (C + 1) * (x - 1) / x := by field_simp; ring
    rw [h1]
    have : x - 1 ≠ 0 := by linarith
    have : C + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e, div_le_iff₀ (by linarith)]
  have hc0 : 0 ≤ hl3oc x := by unfold hl3oc; positivity
  nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ C + 2)]

/-- The norm-and-weight part of `H_n` is affine in `C` with slope `-(121/500)(1 - 1/x)`. -/
theorem hl3o_Hup_affine (hx : 0 < x) (C₁ C₂ : ℝ) :
    (hl3oP x C₂ n (1 / x) + 1 / 125 * hl3oA x C₂ n (1 / x)) -
      (hl3oP x C₁ n (1 / x) + 1 / 125 * hl3oA x C₁ n (1 / x)) =
      -(121 / 500) * ((1 - 1 / x) * (C₂ - C₁)) := by
  unfold hl3oP hl3oA hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2 hl3oAc3 hl3oAc4
    hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1 hl3oγ2 hl3oγ3 hl3oγ4
    hl3oδ0 hl3oδ1 hl3oδ2
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The `n`-slope of `H_n` is `w(379/500) - 3/4 = (w₁₉(h) + S³(6x - 1)/5)/(4900x³)` (the note's (12)). -/
theorem hl3o_Hup_n (hx : 0 < x) :
    hl3oHup x C (7 / 2) - hl3oHup x C n = (7 / 2 - n) *
      ((144 * (x - 2) ^ 4 + 1585 * (x - 2) ^ 3 + 5414 * (x - 2) ^ 2 + 7516 * (x - 2) + 3728 +
        (x + 1) ^ 3 * (6 * x - 1) / 5) / (4900 * x ^ 3)) := by
  unfold hl3oHup hl3oP hl3oA hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2
    hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1 hl3oγ2
    hl3oγ3 hl3oγ4 hl3oδ0 hl3oδ1 hl3oδ2
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `H_{7/2}(x, 8x/(9x + 8)) = W(h)/(63000x³S(9x + 8)(13x + 4)(32x + 19))` (the note's (13)). -/
theorem hl3o_W_id (hx : 0 < x) :
    hl3oHup x (8 * x / (9 * x + 8)) (7 / 2) *
      (63000 * x ^ 3 * (x + 1) * (9 * x + 8) * (13 * x + 4) * (32 * x + 19)) =
      -24463296 * (x - 2) ^ 8 - 412280226 * (x - 2) ^ 7 - 2909495636 * (x - 2) ^ 6 -
        11176434083 * (x - 2) ^ 5 - 25317396372 * (x - 2) ^ 4 - 33983546668 * (x - 2) ^ 3 -
        25312811671 * (x - 2) ^ 2 - 8458571328 * (x - 2) - 404024580 := by
  have h98 : 9 * x + 8 ≠ 0 := by positivity
  have hZ : 1 + 8 * x / (9 * x + 8) + (x - 8 * x / (9 * x + 8)) * (1 / x) =
      2 * (13 * x + 4) / (9 * x + 8) := by field_simp; ring
  unfold hl3oHup hl3oPhi
  rw [hZ]
  have hK : 5 * (2 * (13 * x + 4) / (9 * x + 8)) + 14 = 8 * (32 * x + 19) / (9 * x + 8) := by
    field_simp; ring
  rw [hK]
  unfold hl3oP hl3oA hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2
    hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1 hl3oγ2
    hl3oγ3 hl3oγ4 hl3oδ0 hl3oδ1 hl3oδ2
  have : x + 1 ≠ 0 := by linarith
  have : 13 * x + 4 ≠ 0 := by positivity
  have : 32 * x + 19 ≠ 0 := by positivity
  field_simp
  ring

/-- **The upper shape** (`SHORT_DISPLACEMENT_OUTER_TERMINALS` §4): `R_n(x, x, C) < 0`. -/
theorem hl3o_up (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 8 * x / (9 * x + 8) ≤ C) (hC' : C ≤ 5 / 6)
    (hn : 5 / 2 ≤ n) (hn' : n ≤ 7 / 2) : hl3oG x C n (1 / x) < 0 := by
  have hx0 : 0 < x := by linarith
  have hC0 : 8 / 13 ≤ 8 * x / (9 * x + 8) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hr1 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  -- raise the norm
  obtain ⟨hA1, -, -⟩ := hl3o_A_bds hx hx2 (by linarith) hC' hn hn' le_rfl (by linarith)
  have hV := hl3o_V_up hx hx2 hC
  have h1 : hl3oG x C n (1 / x) < hl3oHup x C n := by
    unfold hl3oG hl3oHup
    have := mul_le_mul_of_nonneg_right hV (by linarith : (0 : ℝ) ≤ hl3oA x C n (1 / x))
    linarith
  -- the lower slope is extremal: `H_n = ψ(Z) + const`
  have h2 : hl3oHup x C n ≤ hl3oHup x (8 * x / (9 * x + 8)) n := by
    set C₁ := 8 * x / (9 * x + 8) with hC₁
    have hZ : ∀ c, 1 + c + (x - c) * (1 / x) = 2 + (1 - 1 / x) * c := by
      intro c; field_simp; ring
    have hZ1 : 23 / 10 ≤ 2 + (1 - 1 / x) * C₁ := by
      have : (1 - 1 / x) * (3 / 5) ≤ (1 - 1 / x) * C₁ :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hZ12 : 2 + (1 - 1 / x) * C₁ ≤ 2 + (1 - 1 / x) * C := by
      have := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 - 1 / x)
      linarith
    have hψ := ss_le_of_deriv (f := fun z => -hl3oψ z) (f' := fun z => -(-(121 / 500) + hl3of z)) hZ12
      (fun z hz => (hl3_hd_ψ (by linarith [hz.1])).neg)
      (fun z hz => by linarith [hl3of_lt (z := z) (by linarith [hz.1])])
    have ha := hl3o_Hup_affine (n := n) hx0 C₁ C
    unfold hl3oHup hl3oPhi
    rw [hZ C, hZ C₁]
    unfold hl3oψ at hψ
    linarith
  -- `H_n` increases in `n`
  have h3 : hl3oHup x (8 * x / (9 * x + 8)) n ≤ hl3oHup x (8 * x / (9 * x + 8)) (7 / 2) := by
    have e := hl3o_Hup_n (C := 8 * x / (9 * x + 8)) (n := n) hx0
    have hh : 0 ≤ x - 2 := by linarith
    have : 0 ≤ (7 / 2 - n) *
        ((144 * (x - 2) ^ 4 + 1585 * (x - 2) ^ 3 + 5414 * (x - 2) ^ 2 + 7516 * (x - 2) + 3728 +
          (x + 1) ^ 3 * (6 * x - 1) / 5) / (4900 * x ^ 3)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ 6 * x - 1 := by linarith
      positivity
    linarith
  -- the terminal value
  have h4 : hl3oHup x (8 * x / (9 * x + 8)) (7 / 2) < 0 := by
    have hh : 0 ≤ x - 2 := by linarith
    have hW : -24463296 * (x - 2) ^ 8 - 412280226 * (x - 2) ^ 7 - 2909495636 * (x - 2) ^ 6 -
        11176434083 * (x - 2) ^ 5 - 25317396372 * (x - 2) ^ 4 - 33983546668 * (x - 2) ^ 3 -
        25312811671 * (x - 2) ^ 2 - 8458571328 * (x - 2) - 404024580 < 0 := by
      have : 0 ≤ 24463296 * (x - 2) ^ 8 + 412280226 * (x - 2) ^ 7 + 2909495636 * (x - 2) ^ 6 +
        11176434083 * (x - 2) ^ 5 + 25317396372 * (x - 2) ^ 4 + 33983546668 * (x - 2) ^ 3 +
        25312811671 * (x - 2) ^ 2 + 8458571328 * (x - 2) := by positivity
      linarith
    rw [← hl3o_W_id hx0] at hW
    exact neg_of_mul_neg_left hW (by positivity)
  linarith

end Up

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.Convexity

/-!
# Smaller-short window, displacement, outer face: the upper shape `α = x`

The outer face sign `dsp_outer_face_proof`, seventh part. At `r = 1/x`, the lower slope
`C ≥ 8x/(9x + 8)` gives `ū - 3/4 ≤ 238/30381 < 1/125`; with `A_n > 1` the norm is
raised to `379/500` and the logarithm constant to `16/9`. The resulting bound `H_n(x, C)` is
`ψ(Z) + const` with `ψ(z) = -121z/500 + 1/z - 56/(5z + 14)` decreasing (`f(z) < 121/500`), so the
lower slope is extremal; `H_n` increases in `n` (`w(379/500) > 3/4`); and
`H_{7/2}(x, 8x/(9x + 8)) = W(h)/(63000x³S(9x + 8)(13x + 4)(32x + 19)) < 0`.

## Main API

* `dspo_up`: `G(x, C, n, 1/x) < 0` for `8x/(9x + 8) ≤ C ≤ 5/6`, `5/2 ≤ n ≤ 7/2`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The upper-face bound `H_n(x, C)`: norm `379/500`, logarithm constant `16/9`. -/
noncomputable def dspoHup (x C n : ℝ) : ℝ :=
  dspoP x C n (1 / x) + 1 / 125 * dspoA x C n (1 / x) + dspoPhi x C (1 / x) + 153 / 180000

/-- `ψ(z) = -121z/500 + 1/z - 56/(5z + 14)`. -/
noncomputable def dspoψ (z : ℝ) : ℝ := -(121 / 500) * z + (1 / z - 56 / (5 * z + 14))

theorem dsp_hd_ψ {z : ℝ} (hz : 0 < z) : HasDerivAt dspoψ (-(121 / 500) + dspof z) z := by
  have h5 : 5 * z + 14 ≠ 0 := by positivity
  have := ((hasDerivAt_id z).const_mul (-(121 / 500))).add
    (((hasDerivAt_const z (1 : ℝ)).fun_div (hasDerivAt_id z) hz.ne').sub
      ((hasDerivAt_const z (56 : ℝ)).fun_div (((hasDerivAt_id z).const_mul 5).add_const 14) h5))
  unfold dspoψ dspof
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

section Up

variable {x C n : ℝ}

/-- `ū - 3/4 = V(1/x) = c(C + 2)/(C + 1) < 1/125` for `C ≥ 8x/(9x + 8)`. -/
theorem dspo_V_up (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 8 * x / (9 * x + 8) ≤ C) :
    dspoV x C (1 / x) ≤ 1 / 125 := by
  have hx0 : 0 < x := by linarith
  have hC0 : 8 / 13 ≤ C := by
    have : 8 / 13 ≤ 8 * x / (9 * x + 8) := by rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  have hc : dspoc x ≤ 49 / 10127 := by
    unfold dspoc
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx2) (by linarith : (0 : ℝ) ≤ 8412 * x - 4380)]
  have e : dspoV x C (1 / x) = dspoc x * (C + 2) / (C + 1) := by
    unfold dspoV
    have h1 : C + (x - C - 1) * (1 / x) = (C + 1) * (x - 1) / x := by field_simp; ring
    rw [h1]
    have : x - 1 ≠ 0 := by linarith
    have : C + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e, div_le_iff₀ (by linarith)]
  have hc0 : 0 ≤ dspoc x := by unfold dspoc; positivity
  nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ C + 2)]

/-- The norm-and-weight part of `H_n` is affine in `C` with slope `-(121/500)(1 - 1/x)`. -/
theorem dspo_Hup_affine (hx : 0 < x) (C₁ C₂ : ℝ) :
    (dspoP x C₂ n (1 / x) + 1 / 125 * dspoA x C₂ n (1 / x)) -
      (dspoP x C₁ n (1 / x) + 1 / 125 * dspoA x C₁ n (1 / x)) =
      -(121 / 500) * ((1 - 1 / x) * (C₂ - C₁)) := by
  unfold dspoP dspoA dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4
    dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2 dspoγ0 dspoγ1 dspoγ2 dspoγ3 dspoγ4
    dspoδ0 dspoδ1 dspoδ2
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The `n`-slope of `H_n` is `w(379/500) - 3/4 = (w₁₉(h) + S³(6x - 1)/5)/(4900x³)`. -/
theorem dspo_Hup_n (hx : 0 < x) :
    dspoHup x C (7 / 2) - dspoHup x C n = (7 / 2 - n) *
      ((144 * (x - 2) ^ 4 + 1585 * (x - 2) ^ 3 + 5414 * (x - 2) ^ 2 + 7516 * (x - 2) + 3728 +
        (x + 1) ^ 3 * (6 * x - 1) / 5) / (4900 * x ^ 3)) := by
  unfold dspoHup dspoP dspoA dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0 dspoAc1 dspoAc2
    dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2 dspoγ0 dspoγ1 dspoγ2
    dspoγ3 dspoγ4 dspoδ0 dspoδ1 dspoδ2
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `H_{7/2}(x, 8x/(9x + 8)) = W(h)/(63000x³S(9x + 8)(13x + 4)(32x + 19))`. -/
theorem dspo_W_id (hx : 0 < x) :
    dspoHup x (8 * x / (9 * x + 8)) (7 / 2) *
      (63000 * x ^ 3 * (x + 1) * (9 * x + 8) * (13 * x + 4) * (32 * x + 19)) =
      -24463296 * (x - 2) ^ 8 - 412280226 * (x - 2) ^ 7 - 2909495636 * (x - 2) ^ 6 -
        11176434083 * (x - 2) ^ 5 - 25317396372 * (x - 2) ^ 4 - 33983546668 * (x - 2) ^ 3 -
        25312811671 * (x - 2) ^ 2 - 8458571328 * (x - 2) - 404024580 := by
  have h98 : 9 * x + 8 ≠ 0 := by positivity
  have hZ : 1 + 8 * x / (9 * x + 8) + (x - 8 * x / (9 * x + 8)) * (1 / x) =
      2 * (13 * x + 4) / (9 * x + 8) := by field_simp; ring
  unfold dspoHup dspoPhi
  rw [hZ]
  have hK : 5 * (2 * (13 * x + 4) / (9 * x + 8)) + 14 = 8 * (32 * x + 19) / (9 * x + 8) := by
    field_simp; ring
  rw [hK]
  unfold dspoP dspoA dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0 dspoAc1 dspoAc2
    dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2 dspoγ0 dspoγ1 dspoγ2
    dspoγ3 dspoγ4 dspoδ0 dspoδ1 dspoδ2
  have : x + 1 ≠ 0 := by linarith
  have : 13 * x + 4 ≠ 0 := by positivity
  have : 32 * x + 19 ≠ 0 := by positivity
  field_simp
  ring

/-- **The upper shape**: `R_n(x, x, C) < 0`. -/
theorem dspo_up (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 8 * x / (9 * x + 8) ≤ C) (hC' : C ≤ 5 / 6)
    (hn : 5 / 2 ≤ n) (hn' : n ≤ 7 / 2) : dspoG x C n (1 / x) < 0 := by
  have hx0 : 0 < x := by linarith
  have hC0 : 8 / 13 ≤ 8 * x / (9 * x + 8) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hr1 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  -- raise the norm
  obtain ⟨hA1, -, -⟩ := dspo_A_bds hx hx2 (by linarith) hC' hn hn' le_rfl (by linarith)
  have hV := dspo_V_up hx hx2 hC
  have h1 : dspoG x C n (1 / x) < dspoHup x C n := by
    unfold dspoG dspoHup
    have := mul_le_mul_of_nonneg_right hV (by linarith : (0 : ℝ) ≤ dspoA x C n (1 / x))
    linarith
  -- the lower slope is extremal: `H_n = ψ(Z) + const`
  have h2 : dspoHup x C n ≤ dspoHup x (8 * x / (9 * x + 8)) n := by
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
    have hψ := ss_le_of_deriv (f := fun z => -dspoψ z) (f' := fun z => -(-(121 / 500) + dspof z)) hZ12
      (fun z hz => (dsp_hd_ψ (by linarith [hz.1])).neg)
      (fun z hz => by linarith [dspof_lt (z := z) (by linarith [hz.1])])
    have ha := dspo_Hup_affine (n := n) hx0 C₁ C
    unfold dspoHup dspoPhi
    rw [hZ C, hZ C₁]
    unfold dspoψ at hψ
    linarith
  -- `H_n` increases in `n`
  have h3 : dspoHup x (8 * x / (9 * x + 8)) n ≤ dspoHup x (8 * x / (9 * x + 8)) (7 / 2) := by
    have e := dspo_Hup_n (C := 8 * x / (9 * x + 8)) (n := n) hx0
    have hh : 0 ≤ x - 2 := by linarith
    have : 0 ≤ (7 / 2 - n) *
        ((144 * (x - 2) ^ 4 + 1585 * (x - 2) ^ 3 + 5414 * (x - 2) ^ 2 + 7516 * (x - 2) + 3728 +
          (x + 1) ^ 3 * (6 * x - 1) / 5) / (4900 * x ^ 3)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ 6 * x - 1 := by linarith
      positivity
    linarith
  -- the terminal value
  have h4 : dspoHup x (8 * x / (9 * x + 8)) (7 / 2) < 0 := by
    have hh : 0 ≤ x - 2 := by linarith
    have hW : -24463296 * (x - 2) ^ 8 - 412280226 * (x - 2) ^ 7 - 2909495636 * (x - 2) ^ 6 -
        11176434083 * (x - 2) ^ 5 - 25317396372 * (x - 2) ^ 4 - 33983546668 * (x - 2) ^ 3 -
        25312811671 * (x - 2) ^ 2 - 8458571328 * (x - 2) - 404024580 < 0 := by
      have : 0 ≤ 24463296 * (x - 2) ^ 8 + 412280226 * (x - 2) ^ 7 + 2909495636 * (x - 2) ^ 6 +
        11176434083 * (x - 2) ^ 5 + 25317396372 * (x - 2) ^ 4 + 33983546668 * (x - 2) ^ 3 +
        25312811671 * (x - 2) ^ 2 + 8458571328 * (x - 2) := by positivity
      linarith
    rw [← dspo_W_id hx0] at hW
    exact neg_of_mul_neg_left hW (by positivity)
  linarith

end Up

end SmoothedOctagon

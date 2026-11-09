module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.Reciprocal.Defs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.Reciprocal.Polynomials

/-!
# Smaller-short window, upper ratio: reciprocal-shape convexity of the outer tests

On the rectangle `13/6 ≤ x ≤ 12/5`, `5/8 ≤ c ≤ 7/8`, `1/x ≤ r ≤ 5/6`, `3/4 ≤ u ≤ 4/5`, both
outer tests satisfy `(H_j)_rr > 1/2`. For `H₀`: the third derivative is positive by the
coefficient bounds `ur_comp`, `ur_Wb`, and `(H₀)_rr(1/x) > 1/2` by the identities A. For `H₁`:
the residue `L = e⁴R` (`R = W(ξ)/7 - 17/4`, `ξ = -d/e`) is positive by the identities B,
`Z⁴(H₁)_rrr` increases and is positive at `r = 1/x` by D, and `(H₁)_rr(1/x) > 1/2` by C. The
identities A-D write the relevant cleared quantity, which is affine in `u`, as the combination
`(16 - 20u)P_{·,0} + (20u - 15)P_{·,1}` (up to constant factors) of the eight bivariate
polynomials `P_{A,0}`, …, `P_{D,1}` of `Reciprocal/Polynomials`, each positive on the box.

## Main API

* `ur_comp`, `ur_Wb`: bounds on the components and on the quartic coefficients of `W`.
* `ur_H0d2_gt`, `ur_H1d2_gt`: `(H_j)_rr > 1/2` on the rectangle.
* `ur_H0_le_max`, `ur_H1_le_max`: each test is at most the larger endpoint value on any
  subinterval of `[1/x, 5/6]`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- Norm affinity: a value affine in `u` that is positive at `u = 3/4` and `u = 4/5`. -/
theorem ur_affine_pos {u P Q a b : ℝ} (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hP : 0 < P)
    (hQ : 0 < Q) (ha : 0 < a) (hb : 0 < b) : 0 < (16 - 20 * u) * P / a + (20 * u - 15) * Q / b := by
  rcases le_total u (31 / 40) with h | h
  · have h1 : 0 < (16 - 20 * u) * P / a := div_pos (mul_pos (by linarith) hP) ha
    have h2 : 0 ≤ (20 * u - 15) * Q / b := div_nonneg (mul_nonneg (by linarith) hQ.le) hb.le
    linarith
  · have h1 : 0 ≤ (16 - 20 * u) * P / a := div_nonneg (mul_nonneg (by linarith) hP.le) ha.le
    have h2 : 0 < (20 * u - 15) * Q / b := div_pos (mul_pos (by linarith) hQ) hb
    linarith

/-- Bounds on the components `x - c`, `d₁`, `d₂`, `E₀`, `J₂` on the rectangle. -/
theorem ur_comp {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    5 / 4 < x - c ∧ x - c < 9 / 5 ∧ -5 / 4 < urd1 x c ∧ urd1 x c ≤ 11 / 20 ∧
      -3 < urd2 x c ∧ urd2 x c ≤ -19 / 72 ∧ -3 / 5 < ssE0 x u ∧ ssE0 x u < 0 ∧
      14 / 3 < urJ2 x u ∧ urJ2 x u < 6 := by
  have hS : 0 < 1 + x := by linarith
  have hi1 : 5 / 17 ≤ 1 / (1 + x) := by rw [le_div_iff₀ hS]; linarith
  have hi2 : 1 / (1 + x) ≤ 6 / 19 := by rw [div_le_iff₀ hS]; linarith
  have h1c : 0 ≤ 1 - c := by linarith
  have hx1 := mul_le_mul_of_nonneg_right hx h1c
  have hx3 := mul_le_mul_of_nonneg_right hx2 h1c
  have hcx : 1 + c - x ≤ 0 := by linarith
  have hx4 := mul_le_mul_of_nonpos_right hx hcx
  have hx5 := mul_le_mul_of_nonpos_right hx2 hcx
  have hu1 : u - 1 ≤ 0 := by linarith
  have hS1 := mul_le_mul_of_nonpos_right (show 19 / 6 ≤ 1 + x by linarith) hu1
  have hS2 := mul_le_mul_of_nonpos_right (show 1 + x ≤ 17 / 5 by linarith) hu1
  unfold urd1 urd2 urJ2 ssE0
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Bounds on the quartic coefficients of `W`: `-50 < W₂ < -16`, `W₃ > -6`, `W₄ > 7`. -/
theorem ur_Wb {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    -50 < urW2 x c u ∧ urW2 x c u < -16 ∧ -6 < urW3 x c u ∧ 7 < urW4 x c u := by
  obtain ⟨-, -, hd1, hd1', hd2, hd2', hE, hE', hJ, hJ'⟩ := ur_comp hx hx2 hc hc2 hu hu2
  unfold urW2 urW3 urW4
  generalize urd1 x c = d1 at *
  generalize urd2 x c = d2 at *
  generalize urJ2 x u = J at *
  generalize ssE0 x u = E at *
  have hd1sq : d1 ^ 2 < 25 / 16 := by nlinarith
  have hud1 : u * d1 ^ 2 ≤ 4 / 5 * (25 / 16) :=
    mul_le_mul hu2 hd1sq.le (sq_nonneg _) (by norm_num)
  have hud2 : 0 ≤ u * ((1 + 2 * c) * (-d2)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hud2' : u * ((1 + 2 * c) * (-d2)) ≤ 4 / 5 * (11 / 4 * 3) :=
    mul_le_mul hu2 (mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num))
      (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hdE : 0 ≤ (-d2) * (-E) := mul_nonneg (by linarith) (by linarith)
  have hdE' : (-d2) * (-E) ≤ 3 * (3 / 5) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hcJ : (9 / 4) * (14 / 3) ≤ (1 + 2 * c) * J :=
    mul_le_mul (by linarith) hJ.le (by norm_num) (by linarith)
  have hcJ' : (1 + 2 * c) * J ≤ 11 / 4 * 6 :=
    mul_le_mul (by linarith) hJ'.le (by linarith) (by norm_num)
  have hP : -(2 * (4 / 5) * 3 + 6) < 2 * u * d2 - J := by nlinarith
  have hP' : 2 * u * d2 - J < 0 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rcases le_total 0 d1 with h | h
    · have : d1 * (2 * u * d2 - J) ≥ 11 / 20 * (2 * u * d2 - J) := by nlinarith
      linarith
    · nlinarith
  · have hS : 283 / 36 ≤ (1 + x) ^ 2 - (1 + x) + 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u) (sq_nonneg d2), mul_pos (by linarith : 0 < J)
      (by linarith : 0 < -d2)]

/-- `5/12 ≤ 1/x ≤ r`, `Z ≥ 2` and the edge value `7/3 ≤ Z(1/x) ≤ 8/3`. -/
theorem ur_Zb {x c r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hr : 1 / x ≤ r) :
    5 / 12 ≤ r ∧ 2 ≤ urZr x c r ∧ 7 / 3 ≤ urZr x c (1 / x) ∧ urZr x c (1 / x) ≤ 8 / 3 ∧
      urZr x c (1 / x) ≤ urZr x c r := by
  have hx0 : 0 < x := by linarith
  have h1 : 5 / 12 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  have h2 : 1 / x ≤ 6 / 13 := by rw [div_le_iff₀ hx0]; linarith
  have hZb : urZr x c (1 / x) = 2 + c * (1 - 1 / x) := by unfold urZr; field_simp; ring
  have hmono : urZr x c (1 / x) ≤ urZr x c r := by
    unfold urZr; nlinarith
  refine ⟨h1.trans hr, ?_, ?_, ?_, hmono⟩
  · refine le_trans ?_ hmono
    rw [hZb]; nlinarith
  · rw [hZb]; nlinarith
  · rw [hZb]; nlinarith

/-! ### The first test -/

/-- `(H₀)_rrr > 0`, from the coefficient bounds. -/
theorem ur_H0d3_pos {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (hr2 : r ≤ 5 / 6) :
    0 < urH0d3 x c u r := by
  obtain ⟨he, he', -⟩ := ur_comp hx hx2 hc hc2 hu hu2
  obtain ⟨hW2, hW2', hW3, hW4⟩ := ur_Wb hx hx2 hc hc2 hu hu2
  obtain ⟨hr5, hZ2, -⟩ := ur_Zb hx hx2 hc hc2 hr
  have hZ0 : 0 < urZr x c r := by linarith
  have e1 : urH0d3 x c u r = ((3 * (7 - c) - 12 * (x - c) * r) * urW3 x c u -
      3 * (x - c) * urW2 x c u + (12 * (7 - c) * r - 30 * (x - c) * r ^ 2) * urW4 x c u) / 49 +
      2 * (x - c) ^ 3 * ((urZr x c r - 3) / urZr x c r ^ 4) := by
    unfold urH0d3 urWd2 urWd3
    field_simp
    unfold urZr
    ring
  rw [e1]
  have hq : -(1 / 16) ≤ (urZr x c r - 3) / urZr x c r ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num) hZ2 4]
  have he3 : (x - c) ^ 3 < (9 / 5) ^ 3 := pow_lt_pow_left₀ he' (by linarith) (by norm_num)
  have hpole : -(729 / 1000) < 2 * (x - c) ^ 3 * ((urZr x c r - 3) / urZr x c r ^ 4) := by
    nlinarith [pow_pos (by linarith : 0 < x - c) 3]
  have hP1 : 0 < 3 * (7 - c) - 12 * (x - c) * r := by nlinarith
  have hP1' : 3 * (7 - c) - 12 * (x - c) * r < 13 := by nlinarith
  have hP2 : 21 < 12 * (7 - c) * r - 30 * (x - c) * r ^ 2 := by nlinarith
  have t1 : -78 < (3 * (7 - c) - 12 * (x - c) * r) * urW3 x c u := by nlinarith
  have t2 : 60 < -(3 * (x - c) * urW2 x c u) := by nlinarith
  have t3 : 147 < (12 * (7 - c) * r - 30 * (x - c) * r ^ 2) * urW4 x c u := by nlinarith
  linarith

/-- `(H₀)_rr(1/x) > 1/2` (identities A). -/
theorem ur_H0d2_edge {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    1 / 2 < urH0d2 x c u (1 / x) := by
  obtain ⟨he, he', -⟩ := ur_comp hx hx2 hc hc2 hu hu2
  obtain ⟨-, -, hZb, hZb', -⟩ := ur_Zb hx hx2 hc hc2 le_rfl
  have hx0 : 0 < x := by linarith
  have key : 392 * x ^ 2 * (1 + x) * ((-urELd2 x c u - (x - c) * urWd1 x c u (1 / x) / 49 +
      (4 - urZr x c (1 / x) / 2) * urWd2 x c u (1 / x) / 49) - 5 / 8) =
      (16 - 20 * u) * urPA0 (x - 2) (c - 5 / 8) / 64 +
        (20 * u - 15) * urPA1 (x - 2) (c - 5 / 8) / 20 := by
    unfold urELd2 urWd1 urWd2 urW1 urW2 urW3 urW4 urd1 urd2 urJ2 ssE0 urZr urPA0 urPA1
    field_simp
    ring
  have hA0 := ur_PA0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hA1 := ur_PA1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hpos : 0 < 392 * x ^ 2 * (1 + x) := by positivity
  have hQ : 0 < (-urELd2 x c u - (x - c) * urWd1 x c u (1 / x) / 49 +
      (4 - urZr x c (1 / x) / 2) * urWd2 x c u (1 / x) / 49) - 5 / 8 := by
    have : 0 < 392 * x ^ 2 * (1 + x) * ((-urELd2 x c u - (x - c) * urWd1 x c u (1 / x) / 49 +
        (4 - urZr x c (1 / x) / 2) * urWd2 x c u (1 / x) / 49) - 5 / 8) := by
      rw [key]; exact ur_affine_pos hu hu2 hA0 hA1 (by norm_num) (by norm_num)
    exact pos_of_mul_pos_right this hpos.le
  have hq : (urZr x c (1 / x) - 2) / urZr x c (1 / x) ^ 3 ≤ 1 / 27 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (urZr x c (1 / x) - 3)) (by linarith :
      (0 : ℝ) ≤ urZr x c (1 / x) + 6)]
  have he2 : (x - c) ^ 2 < 81 / 25 := by nlinarith
  have hpole : -(1 / 8) < 2 * (x - c) ^ 2 / urZr x c (1 / x) ^ 3 -
      (x - c) ^ 2 / urZr x c (1 / x) ^ 2 := by
    have e : 2 * (x - c) ^ 2 / urZr x c (1 / x) ^ 3 - (x - c) ^ 2 / urZr x c (1 / x) ^ 2 =
        -((x - c) ^ 2 * ((urZr x c (1 / x) - 2) / urZr x c (1 / x) ^ 3)) := by
      field_simp; ring
    rw [e]
    have hq0 : 0 ≤ (urZr x c (1 / x) - 2) / urZr x c (1 / x) ^ 3 :=
      div_nonneg (by linarith) (by positivity)
    nlinarith [mul_le_mul he2.le hq (by positivity) (by norm_num)]
  unfold urH0d2
  linarith

/-- `(H₀)_rr > 1/2` on the rectangle: it increases from its value at `r = 1/x`. -/
theorem ur_H0d2_gt {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (hr2 : r ≤ 5 / 6) :
    1 / 2 < urH0d2 x c u r :=
  lt_of_lt_of_le (ur_H0d2_edge hx hx2 hc hc2 hu hu2)
    (ss_le_of_deriv hr (fun s hs => ur_hd_H0d2 (by linarith [(ur_Zb hx hx2 hc hc2 hs.1).2.1]))
      (fun s hs => (ur_H0d3_pos hx hx2 hc hc2 hu hu2 hs.1.le (hs.2.le.trans hr2)).le))

/-! ### The second test -/

/-- `ξ = -d/e`. -/
noncomputable def urXi (x c : ℝ) : ℝ := -(1 + c) / (x - c)

/-- The residue `R = W(ξ)/7 - 17/4` at the pole `ξ = -d/e` of `1/Z`. -/
noncomputable def urRr (x c u : ℝ) : ℝ := urWr x c u (urXi x c) / 7 - 17 / 4

/-- `L = e⁴R`. -/
noncomputable def urLr (x c u : ℝ) : ℝ := (x - c) ^ 4 * urRr x c u

/-- `(H₁)_rrr = A(r) - 6e³R/Z⁴ + 2e³/Z³`. -/
theorem ur_H1d3_eq {x c u r : ℝ} (he : x - c ≠ 0) (hZ : urZr x c r ≠ 0) :
    urH1d3 x c u r = 3 * urW3 x c u / 98 + 6 * urW4 x c u * r / 49 +
      6 * urW4 x c u / (7 * (x - c)) - 6 * (x - c) ^ 3 * urRr x c u / urZr x c r ^ 4 +
      2 * (x - c) ^ 3 / urZr x c r ^ 3 := by
  unfold urH1d3 urRr urWd1 urWd2 urWd3 urXi
  rw [urWr_eq, urWr_eq]
  unfold urZr at *
  generalize urW0 x c u = W0
  generalize urW1 x c u = W1
  generalize urW2 x c u = W2
  generalize urW3 x c u = W3
  generalize urW4 x c u = W4
  field_simp
  ring

/-- `(H₁)_rr` in divided form. -/
theorem ur_H1d2_eq {x c u r : ℝ} (he : x - c ≠ 0) (hZ : urZr x c r ≠ 0) :
    urH1d2 x c u r = -urELd2 x c u + urWd2 x c u r / 196 + 6 * urW4 x c u * r / (7 * (x - c)) +
      2 * urW3 x c u / (7 * (x - c)) - 2 * (1 + c) * urW4 x c u / (7 * (x - c) ^ 2) +
      2 * (x - c) ^ 2 * urRr x c u / urZr x c r ^ 3 - (x - c) ^ 2 / urZr x c r ^ 2 := by
  unfold urH1d2 urRr urWd1 urWd2 urXi
  rw [urWr_eq, urWr_eq]
  unfold urZr at *
  generalize urW0 x c u = W0
  generalize urW1 x c u = W1
  generalize urW2 x c u = W2
  generalize urW3 x c u = W3
  generalize urW4 x c u = W4
  field_simp
  ring

/-- `L > 0` (identities B). -/
theorem ur_L_pos {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) : 0 < urLr x c u := by
  have he : x - c ≠ 0 := by linarith
  have hS : 0 < 1 + x := by linarith
  have key : 28 * (1 + x) * urLr x c u = (16 - 20 * u) * urPB0 (x - 2) (c - 5 / 8) / 4096 +
      (20 * u - 15) * urPB1 (x - 2) (c - 5 / 8) / 20480 := by
    unfold urLr urRr urXi urWr urDr urd1 urd2 ssE0 urPB0 urPB1
    field_simp
    ring
  have hB0 := ur_PB0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hB1 := ur_PB1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have : 0 < 28 * (1 + x) * urLr x c u := by
    rw [key]; exact ur_affine_pos hu hu2 hB0 hB1 (by norm_num) (by norm_num)
  exact pos_of_mul_pos_right this (by positivity)

/-- `(H₁)_rrr > 0` (identities D). -/
theorem ur_H1d3_pos {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (_hr2 : r ≤ 5 / 6) :
    0 < urH1d3 x c u r := by
  obtain ⟨he, he', -⟩ := ur_comp hx hx2 hc hc2 hu hu2
  obtain ⟨-, -, hW3, hW4⟩ := ur_Wb hx hx2 hc hc2 hu hu2
  obtain ⟨hr5, hZ2, hZb, -, hZZ⟩ := ur_Zb hx hx2 hc hc2 hr
  have he0 : 0 < x - c := by linarith
  have hZ0 : 0 < urZr x c r := by linarith
  have hS : 0 < 1 + x := by linarith
  have keyD : 324 * (1 + x) * (urW4 x c u * (7 / 3) ^ 4 - 7 * urLr x c u -
      3 * (x - c) / 14 * (7 / 3) ^ 4) = (16 - 20 * u) * urPD0 (x - 2) (c - 5 / 8) / 4096 +
      (20 * u - 15) * urPD1 (x - 2) (c - 5 / 8) / 20480 := by
    unfold urLr urRr urXi urWr urW4 urDr urd1 urd2 urJ2 ssE0 urPD0 urPD1
    field_simp
    ring
  have hD0 := ur_PD0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hD1 := ur_PD1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hD : 0 < urW4 x c u * (7 / 3) ^ 4 - 7 * urLr x c u - 3 * (x - c) / 14 * (7 / 3) ^ 4 := by
    have : 0 < 324 * (1 + x) * (urW4 x c u * (7 / 3) ^ 4 - 7 * urLr x c u -
        3 * (x - c) / 14 * (7 / 3) ^ 4) := by
      rw [keyD]; exact ur_affine_pos hu hu2 hD0 hD1 (by norm_num) (by norm_num)
    exact pos_of_mul_pos_right this (by positivity)
  -- `A(r) ≥ 6W₄/(7e) - 9/49 > 0`
  have hA : 6 * urW4 x c u / (7 * (x - c)) - 9 / 49 ≤
      3 * urW3 x c u / 98 + 6 * urW4 x c u * r / 49 + 6 * urW4 x c u / (7 * (x - c)) := by
    have : 0 ≤ 6 * urW4 x c u * r / 49 := by
      have : 0 ≤ r := by linarith
      positivity
    linarith
  have hA0 : 0 < 6 * urW4 x c u / (7 * (x - c)) - 9 / 49 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]
    nlinarith
  have hZ4 : (7 / 3) ^ 4 ≤ urZr x c r ^ 4 := pow_le_pow_left₀ (by norm_num) (hZb.trans hZZ) 4
  have hg : 0 < (3 * urW3 x c u / 98 + 6 * urW4 x c u * r / 49 +
      6 * urW4 x c u / (7 * (x - c))) * urZr x c r ^ 4 - 6 * (x - c) ^ 3 * urRr x c u +
      2 * (x - c) ^ 3 * urZr x c r := by
    have h1 := mul_le_mul hA hZ4 (by positivity) (hA0.le.trans hA)
    have e : (6 * urW4 x c u / (7 * (x - c)) - 9 / 49) * (7 / 3) ^ 4 -
        6 * (x - c) ^ 3 * urRr x c u = 6 / (7 * (x - c)) * (urW4 x c u * (7 / 3) ^ 4 -
        7 * urLr x c u - 3 * (x - c) / 14 * (7 / 3) ^ 4) := by
      unfold urLr; field_simp; ring
    have h2 : 0 < 6 / (7 * (x - c)) * (urW4 x c u * (7 / 3) ^ 4 - 7 * urLr x c u -
        3 * (x - c) / 14 * (7 / 3) ^ 4) := mul_pos (by positivity) hD
    have h3 : 0 < 2 * (x - c) ^ 3 * urZr x c r := by positivity
    linarith
  rw [ur_H1d3_eq he0.ne' hZ0.ne']
  have e : 3 * urW3 x c u / 98 + 6 * urW4 x c u * r / 49 + 6 * urW4 x c u / (7 * (x - c)) -
      6 * (x - c) ^ 3 * urRr x c u / urZr x c r ^ 4 + 2 * (x - c) ^ 3 / urZr x c r ^ 3 =
      ((3 * urW3 x c u / 98 + 6 * urW4 x c u * r / 49 + 6 * urW4 x c u / (7 * (x - c))) *
        urZr x c r ^ 4 - 6 * (x - c) ^ 3 * urRr x c u + 2 * (x - c) ^ 3 * urZr x c r) /
        urZr x c r ^ 4 := by
    field_simp
  rw [e]
  positivity

/-- The identity C for `107520e²S𝒞`. -/
theorem ur_keyC {x c u : ℝ} (hx0 : x ≠ 0) (he0 : x - c ≠ 0) (hS : 1 + x ≠ 0) :
    107520 * (x - c) ^ 2 * (1 + x) * (-urELd2 x c u - 2 / 3 +
      6 * urW4 x c u / (7 * (x - c) * x) + 2 * urW3 x c u / (7 * (x - c)) -
      2 * (1 + c) * urW4 x c u / (7 * (x - c) ^ 2) + 27 * urLr x c u / (256 * (x - c) ^ 2) -
      3 / 5 - 1 / 2) = (16 - 20 * u) * urPC0 (x - 2) (c - 5 / 8) / 4096 +
      (20 * u - 15) * urPC1 (x - 2) (c - 5 / 8) / 4096 := by
    unfold urELd2 urLr urRr urXi urWr urW3 urW4 urDr urd1 urd2 urJ2 ssE0 urPC0 urPC1
    field_simp
    ring

/-- `(H₁)_rr(1/x) > 1/2` (identities C). -/
theorem ur_H1d2_edge {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    1 / 2 < urH1d2 x c u (1 / x) := by
  obtain ⟨he, he', -⟩ := ur_comp hx hx2 hc hc2 hu hu2
  obtain ⟨hW2, -, hW3, hW4⟩ := ur_Wb hx hx2 hc hc2 hu hu2
  obtain ⟨hr5, -, hZb, hZb', -⟩ := ur_Zb hx hx2 hc hc2 le_rfl
  have hx0 : 0 < x := by linarith
  have he0 : 0 < x - c := by linarith
  have hS : 0 < 1 + x := by linarith
  have hL := ur_L_pos hx hx2 hc hc2 hu hu2
  have keyC := ur_keyC (x := x) (c := c) (u := u) hx0.ne' he0.ne' hS.ne'
  have hC0 := ur_PC0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hC1 := ur_PC1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hC : 0 < -urELd2 x c u - 2 / 3 + 6 * urW4 x c u / (7 * (x - c) * x) +
      2 * urW3 x c u / (7 * (x - c)) - 2 * (1 + c) * urW4 x c u / (7 * (x - c) ^ 2) +
      27 * urLr x c u / (256 * (x - c) ^ 2) - 3 / 5 - 1 / 2 := by
    have : 0 < 107520 * (x - c) ^ 2 * (1 + x) * (-urELd2 x c u - 2 / 3 +
        6 * urW4 x c u / (7 * (x - c) * x) + 2 * urW3 x c u / (7 * (x - c)) -
        2 * (1 + c) * urW4 x c u / (7 * (x - c) ^ 2) + 27 * urLr x c u / (256 * (x - c) ^ 2) -
        3 / 5 - 1 / 2) := by
      rw [keyC]; exact ur_affine_pos hu hu2 hC0 hC1 (by norm_num) (by norm_num)
    exact pos_of_mul_pos_right this (by positivity)
  -- the three comparisons in the divided form
  have hWd2 : -(2 / 3) < urWd2 x c u (1 / x) / 196 := by
    unfold urWd2
    have h6 : 1 / x ≤ 6 / 13 := by rw [div_le_iff₀ hx0]; linarith
    have h1 : -6 * (6 / 13) ≤ urW3 x c u * (1 / x) := by
      rcases le_total 0 (urW3 x c u) with h | h
      · have : 0 ≤ urW3 x c u * (1 / x) := by positivity
        linarith
      · nlinarith
    have h2 : 0 ≤ urW4 x c u * (1 / x) ^ 2 := by
      have : 0 ≤ urW4 x c u := by linarith
      positivity
    linarith
  have hR : 27 * urLr x c u / (256 * (x - c) ^ 2) ≤
      2 * (x - c) ^ 2 * urRr x c u / urZr x c (1 / x) ^ 3 := by
    have e : 2 * (x - c) ^ 2 * urRr x c u / urZr x c (1 / x) ^ 3 =
        2 * urLr x c u / ((x - c) ^ 2 * urZr x c (1 / x) ^ 3) := by
      unfold urLr; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hZ3 : urZr x c (1 / x) ^ 3 ≤ (8 / 3) ^ 3 := pow_le_pow_left₀ (by linarith) hZb' 3
    have : 0 < urLr x c u * (x - c) ^ 2 := by positivity
    nlinarith
  have hE : -(3 / 5) < -((x - c) ^ 2 / urZr x c (1 / x) ^ 2) := by
    rw [neg_lt_neg_iff, div_lt_iff₀ (by positivity)]
    have : (7 / 3) ^ 2 ≤ urZr x c (1 / x) ^ 2 := pow_le_pow_left₀ (by norm_num) hZb 2
    nlinarith
  rw [ur_H1d2_eq he0.ne' (ne_of_gt (by linarith))]
  have e6 : 6 * urW4 x c u * (1 / x) / (7 * (x - c)) = 6 * urW4 x c u / (7 * (x - c) * x) := by
    field_simp
  rw [e6]
  linarith

/-- `(H₁)_rr > 1/2` on the rectangle: it increases from its value at `r = 1/x`. -/
theorem ur_H1d2_gt {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (hr2 : r ≤ 5 / 6) :
    1 / 2 < urH1d2 x c u r :=
  lt_of_lt_of_le (ur_H1d2_edge hx hx2 hc hc2 hu hu2)
    (ss_le_of_deriv hr (fun s hs => ur_hd_H1d2 (by linarith [(ur_Zb hx hx2 hc hc2 hs.1).2.1]))
      (fun s hs => (ur_H1d3_pos hx hx2 hc hc2 hu hu2 hs.1.le (hs.2.le.trans hr2)).le))

/-! ### Convexity -/

/-- `H₀` is at most its larger endpoint value on `[r₀, r₁] ⊆ [1/x, 5/6]`. -/
theorem ur_H0_le_max {x c u r0 r r1 : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (h0 : 1 / x ≤ r0) (h01 : r0 ≤ r)
    (h1 : r ≤ r1) (h15 : r1 ≤ 5 / 6) :
    urH0 x c u r ≤ max (urH0 x c u r0) (urH0 x c u r1) :=
  ur_le_max_of_deriv2 h01 h1
    (fun s hs => ur_hd_H0 (by linarith [(ur_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => ur_hd_H0d1 (by linarith [(ur_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => by linarith [ur_H0d2_gt hx hx2 hc hc2 hu hu2 (h0.trans hs.1) (hs.2.trans h15)])

/-- `H₁` is at most its larger endpoint value on `[r₀, r₁] ⊆ [1/x, 5/6]`. -/
theorem ur_H1_le_max {x c u r0 r r1 : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (h0 : 1 / x ≤ r0) (h01 : r0 ≤ r)
    (h1 : r ≤ r1) (h15 : r1 ≤ 5 / 6) :
    urH1 x c u r ≤ max (urH1 x c u r0) (urH1 x c u r1) :=
  ur_le_max_of_deriv2 h01 h1
    (fun s hs => ur_hd_H1 (by linarith [(ur_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => ur_hd_H1d1 (by linarith [(ur_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => by linarith [ur_H1d2_gt hx hx2 hc hc2 hu hu2 (h0.trans hs.1) (hs.2.trans h15)])

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecipDefs
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecipPoly

/-!
# S2 hand signs: reciprocal-shape convexity of the outer tests

`archive/lighter-proofs/SHORT_RATIO_OUTER_RECIPROCAL.md` (1): on the rectangle
`13/6 ≤ x ≤ 12/5`, `5/8 ≤ c ≤ 7/8`, `1/x ≤ r ≤ 5/6`, `3/4 ≤ u ≤ 4/5`, both outer tests satisfy
`(H_j)_rr > 1/2`. For `H₀`: the third derivative is positive by the coefficient bounds (8)-(11),
and `(H₀)_rr(1/x) > 1/2` by the identities A (§2 (12)). For `H₁`: the residue `L = e⁴R`
(`R = W(ξ)/7 - 17/4`, `ξ = -d/e`) is positive by the identities B, `Z⁴(H₁)_rrr` increases and is
positive at `r = 1/x` by D (§3 (15)-(17)), and `(H₁)_rr(1/x) > 1/2` by C (§3 (18)-(19)). The
eight polynomials are those of the algebra companion (`S2HandRecipPoly`); each identity below is
the normalization listed there, affine in `u`.

## Main API

* `hl2_comp`, `hl2_Wb`: the bounds (8)-(9).
* `hl2_H0d2_gt`, `hl2_H1d2_gt`: `(H_j)_rr > 1/2` on the rectangle.
* `hl2_H0_le_max`, `hl2_H1_le_max`: each test is at most the larger endpoint value on any
  subinterval of `[1/x, 5/6]`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- Norm affinity: a value affine in `u` that is positive at `u = 3/4` and `u = 4/5`. -/
theorem hl2_affine_pos {u P Q a b : ℝ} (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hP : 0 < P)
    (hQ : 0 < Q) (ha : 0 < a) (hb : 0 < b) : 0 < (16 - 20 * u) * P / a + (20 * u - 15) * Q / b := by
  rcases le_total u (31 / 40) with h | h
  · have h1 : 0 < (16 - 20 * u) * P / a := div_pos (mul_pos (by linarith) hP) ha
    have h2 : 0 ≤ (20 * u - 15) * Q / b := div_nonneg (mul_nonneg (by linarith) hQ.le) hb.le
    linarith
  · have h1 : 0 ≤ (16 - 20 * u) * P / a := div_nonneg (mul_nonneg (by linarith) hP.le) ha.le
    have h2 : 0 < (20 * u - 15) * Q / b := div_pos (mul_pos (by linarith) hQ) hb
    linarith

/-- The bounds `SHORT_RATIO_OUTER_RECIPROCAL` (8). -/
theorem hl2_comp {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    5 / 4 < x - c ∧ x - c < 9 / 5 ∧ -5 / 4 < hl2d1 x c ∧ hl2d1 x c ≤ 11 / 20 ∧
      -3 < hl2d2 x c ∧ hl2d2 x c ≤ -19 / 72 ∧ -3 / 5 < hsE0 x u ∧ hsE0 x u < 0 ∧
      14 / 3 < hl2J2 x u ∧ hl2J2 x u < 6 := by
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
  unfold hl2d1 hl2d2 hl2J2 hsE0
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The coefficient bounds `SHORT_RATIO_OUTER_RECIPROCAL` (9). -/
theorem hl2_Wb {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    -50 < hl2W2 x c u ∧ hl2W2 x c u < -16 ∧ -6 < hl2W3 x c u ∧ 7 < hl2W4 x c u := by
  obtain ⟨-, -, hd1, hd1', hd2, hd2', hE, hE', hJ, hJ'⟩ := hl2_comp hx hx2 hc hc2 hu hu2
  unfold hl2W2 hl2W3 hl2W4
  generalize hl2d1 x c = d1 at *
  generalize hl2d2 x c = d2 at *
  generalize hl2J2 x u = J at *
  generalize hsE0 x u = E at *
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
theorem hl2_Zb {x c r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hr : 1 / x ≤ r) :
    5 / 12 ≤ r ∧ 2 ≤ hl2Zr x c r ∧ 7 / 3 ≤ hl2Zr x c (1 / x) ∧ hl2Zr x c (1 / x) ≤ 8 / 3 ∧
      hl2Zr x c (1 / x) ≤ hl2Zr x c r := by
  have hx0 : 0 < x := by linarith
  have h1 : 5 / 12 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  have h2 : 1 / x ≤ 6 / 13 := by rw [div_le_iff₀ hx0]; linarith
  have hZb : hl2Zr x c (1 / x) = 2 + c * (1 - 1 / x) := by unfold hl2Zr; field_simp; ring
  have hmono : hl2Zr x c (1 / x) ≤ hl2Zr x c r := by
    unfold hl2Zr; nlinarith
  refine ⟨h1.trans hr, ?_, ?_, ?_, hmono⟩
  · refine le_trans ?_ hmono
    rw [hZb]; nlinarith
  · rw [hZb]; nlinarith
  · rw [hZb]; nlinarith

/-! ### The first test -/

/-- `(H₀)_rrr > 0` (`SHORT_RATIO_OUTER_RECIPROCAL` (10)-(11)). -/
theorem hl2_H0d3_pos {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (hr2 : r ≤ 5 / 6) :
    0 < hl2H0d3 x c u r := by
  obtain ⟨he, he', -⟩ := hl2_comp hx hx2 hc hc2 hu hu2
  obtain ⟨hW2, hW2', hW3, hW4⟩ := hl2_Wb hx hx2 hc hc2 hu hu2
  obtain ⟨hr5, hZ2, -⟩ := hl2_Zb hx hx2 hc hc2 hr
  have hZ0 : 0 < hl2Zr x c r := by linarith
  have e1 : hl2H0d3 x c u r = ((3 * (7 - c) - 12 * (x - c) * r) * hl2W3 x c u -
      3 * (x - c) * hl2W2 x c u + (12 * (7 - c) * r - 30 * (x - c) * r ^ 2) * hl2W4 x c u) / 49 +
      2 * (x - c) ^ 3 * ((hl2Zr x c r - 3) / hl2Zr x c r ^ 4) := by
    unfold hl2H0d3 hl2Wd2 hl2Wd3
    field_simp
    unfold hl2Zr
    ring
  rw [e1]
  have hq : -(1 / 16) ≤ (hl2Zr x c r - 3) / hl2Zr x c r ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num) hZ2 4]
  have he3 : (x - c) ^ 3 < (9 / 5) ^ 3 := pow_lt_pow_left₀ he' (by linarith) (by norm_num)
  have hpole : -(729 / 1000) < 2 * (x - c) ^ 3 * ((hl2Zr x c r - 3) / hl2Zr x c r ^ 4) := by
    nlinarith [pow_pos (by linarith : 0 < x - c) 3]
  have hP1 : 0 < 3 * (7 - c) - 12 * (x - c) * r := by nlinarith
  have hP1' : 3 * (7 - c) - 12 * (x - c) * r < 13 := by nlinarith
  have hP2 : 21 < 12 * (7 - c) * r - 30 * (x - c) * r ^ 2 := by nlinarith
  have t1 : -78 < (3 * (7 - c) - 12 * (x - c) * r) * hl2W3 x c u := by nlinarith
  have t2 : 60 < -(3 * (x - c) * hl2W2 x c u) := by nlinarith
  have t3 : 147 < (12 * (7 - c) * r - 30 * (x - c) * r ^ 2) * hl2W4 x c u := by nlinarith
  linarith

/-- `(H₀)_rr(1/x) > 1/2` (`SHORT_RATIO_OUTER_RECIPROCAL` (12); identities A). -/
theorem hl2_H0d2_edge {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    1 / 2 < hl2H0d2 x c u (1 / x) := by
  obtain ⟨he, he', -⟩ := hl2_comp hx hx2 hc hc2 hu hu2
  obtain ⟨-, -, hZb, hZb', -⟩ := hl2_Zb hx hx2 hc hc2 le_rfl
  have hx0 : 0 < x := by linarith
  have key : 392 * x ^ 2 * (1 + x) * ((-hl2ELd2 x c u - (x - c) * hl2Wd1 x c u (1 / x) / 49 +
      (4 - hl2Zr x c (1 / x) / 2) * hl2Wd2 x c u (1 / x) / 49) - 5 / 8) =
      (16 - 20 * u) * hl2PA0 (x - 2) (c - 5 / 8) / 64 +
        (20 * u - 15) * hl2PA1 (x - 2) (c - 5 / 8) / 20 := by
    unfold hl2ELd2 hl2Wd1 hl2Wd2 hl2W1 hl2W2 hl2W3 hl2W4 hl2d1 hl2d2 hl2J2 hsE0 hl2Zr hl2PA0 hl2PA1
    field_simp
    ring
  have hA0 := hl2_PA0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hA1 := hl2_PA1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hpos : 0 < 392 * x ^ 2 * (1 + x) := by positivity
  have hQ : 0 < (-hl2ELd2 x c u - (x - c) * hl2Wd1 x c u (1 / x) / 49 +
      (4 - hl2Zr x c (1 / x) / 2) * hl2Wd2 x c u (1 / x) / 49) - 5 / 8 := by
    have : 0 < 392 * x ^ 2 * (1 + x) * ((-hl2ELd2 x c u - (x - c) * hl2Wd1 x c u (1 / x) / 49 +
        (4 - hl2Zr x c (1 / x) / 2) * hl2Wd2 x c u (1 / x) / 49) - 5 / 8) := by
      rw [key]; exact hl2_affine_pos hu hu2 hA0 hA1 (by norm_num) (by norm_num)
    exact pos_of_mul_pos_right this hpos.le
  have hq : (hl2Zr x c (1 / x) - 2) / hl2Zr x c (1 / x) ^ 3 ≤ 1 / 27 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (hl2Zr x c (1 / x) - 3)) (by linarith :
      (0 : ℝ) ≤ hl2Zr x c (1 / x) + 6)]
  have he2 : (x - c) ^ 2 < 81 / 25 := by nlinarith
  have hpole : -(1 / 8) < 2 * (x - c) ^ 2 / hl2Zr x c (1 / x) ^ 3 -
      (x - c) ^ 2 / hl2Zr x c (1 / x) ^ 2 := by
    have e : 2 * (x - c) ^ 2 / hl2Zr x c (1 / x) ^ 3 - (x - c) ^ 2 / hl2Zr x c (1 / x) ^ 2 =
        -((x - c) ^ 2 * ((hl2Zr x c (1 / x) - 2) / hl2Zr x c (1 / x) ^ 3)) := by
      field_simp; ring
    rw [e]
    have hq0 : 0 ≤ (hl2Zr x c (1 / x) - 2) / hl2Zr x c (1 / x) ^ 3 :=
      div_nonneg (by linarith) (by positivity)
    nlinarith [mul_le_mul he2.le hq (by positivity) (by norm_num)]
  unfold hl2H0d2
  linarith

/-- `(H₀)_rr > 1/2` on the rectangle (`SHORT_RATIO_OUTER_RECIPROCAL` (1), `j = 0`). -/
theorem hl2_H0d2_gt {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (hr2 : r ≤ 5 / 6) :
    1 / 2 < hl2H0d2 x c u r :=
  lt_of_lt_of_le (hl2_H0d2_edge hx hx2 hc hc2 hu hu2)
    (ss_le_of_deriv hr (fun s hs => hl2_hd_H0d2 (by linarith [(hl2_Zb hx hx2 hc hc2 hs.1).2.1]))
      (fun s hs => (hl2_H0d3_pos hx hx2 hc hc2 hu hu2 hs.1.le (hs.2.le.trans hr2)).le))

/-! ### The second test -/

/-- `ξ = -d/e`. -/
noncomputable def hl2Xi (x c : ℝ) : ℝ := -(1 + c) / (x - c)

/-- The residue `R = W(ξ)/7 - 17/4` (`SHORT_RATIO_OUTER_RECIPROCAL` (13)). -/
noncomputable def hl2Rr (x c u : ℝ) : ℝ := hl2Wr x c u (hl2Xi x c) / 7 - 17 / 4

/-- `L = e⁴R`. -/
noncomputable def hl2Lr (x c u : ℝ) : ℝ := (x - c) ^ 4 * hl2Rr x c u

/-- `(H₁)_rrr = A(r) - 6e³R/Z⁴ + 2e³/Z³` (`SHORT_RATIO_OUTER_RECIPROCAL` (15)). -/
theorem hl2_H1d3_eq {x c u r : ℝ} (he : x - c ≠ 0) (hZ : hl2Zr x c r ≠ 0) :
    hl2H1d3 x c u r = 3 * hl2W3 x c u / 98 + 6 * hl2W4 x c u * r / 49 +
      6 * hl2W4 x c u / (7 * (x - c)) - 6 * (x - c) ^ 3 * hl2Rr x c u / hl2Zr x c r ^ 4 +
      2 * (x - c) ^ 3 / hl2Zr x c r ^ 3 := by
  unfold hl2H1d3 hl2Rr hl2Wd1 hl2Wd2 hl2Wd3 hl2Xi
  rw [hl2Wr_eq, hl2Wr_eq]
  unfold hl2Zr at *
  generalize hl2W0 x c u = W0
  generalize hl2W1 x c u = W1
  generalize hl2W2 x c u = W2
  generalize hl2W3 x c u = W3
  generalize hl2W4 x c u = W4
  field_simp
  ring

/-- `(H₁)_rr` in divided form (`SHORT_RATIO_OUTER_RECIPROCAL` (18)). -/
theorem hl2_H1d2_eq {x c u r : ℝ} (he : x - c ≠ 0) (hZ : hl2Zr x c r ≠ 0) :
    hl2H1d2 x c u r = -hl2ELd2 x c u + hl2Wd2 x c u r / 196 + 6 * hl2W4 x c u * r / (7 * (x - c)) +
      2 * hl2W3 x c u / (7 * (x - c)) - 2 * (1 + c) * hl2W4 x c u / (7 * (x - c) ^ 2) +
      2 * (x - c) ^ 2 * hl2Rr x c u / hl2Zr x c r ^ 3 - (x - c) ^ 2 / hl2Zr x c r ^ 2 := by
  unfold hl2H1d2 hl2Rr hl2Wd1 hl2Wd2 hl2Xi
  rw [hl2Wr_eq, hl2Wr_eq]
  unfold hl2Zr at *
  generalize hl2W0 x c u = W0
  generalize hl2W1 x c u = W1
  generalize hl2W2 x c u = W2
  generalize hl2W3 x c u = W3
  generalize hl2W4 x c u = W4
  field_simp
  ring

/-- `L > 0` (`SHORT_RATIO_OUTER_RECIPROCAL` (14); identities B). -/
theorem hl2_L_pos {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) : 0 < hl2Lr x c u := by
  have he : x - c ≠ 0 := by linarith
  have hS : 0 < 1 + x := by linarith
  have key : 28 * (1 + x) * hl2Lr x c u = (16 - 20 * u) * hl2PB0 (x - 2) (c - 5 / 8) / 4096 +
      (20 * u - 15) * hl2PB1 (x - 2) (c - 5 / 8) / 20480 := by
    unfold hl2Lr hl2Rr hl2Xi hl2Wr hl2Dr hl2d1 hl2d2 hsE0 hl2PB0 hl2PB1
    field_simp
    ring
  have hB0 := hl2_PB0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hB1 := hl2_PB1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have : 0 < 28 * (1 + x) * hl2Lr x c u := by
    rw [key]; exact hl2_affine_pos hu hu2 hB0 hB1 (by norm_num) (by norm_num)
  exact pos_of_mul_pos_right this (by positivity)

/-- `(H₁)_rrr > 0` (`SHORT_RATIO_OUTER_RECIPROCAL` (15)-(17); identities D). -/
theorem hl2_H1d3_pos {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (_hr2 : r ≤ 5 / 6) :
    0 < hl2H1d3 x c u r := by
  obtain ⟨he, he', -⟩ := hl2_comp hx hx2 hc hc2 hu hu2
  obtain ⟨-, -, hW3, hW4⟩ := hl2_Wb hx hx2 hc hc2 hu hu2
  obtain ⟨hr5, hZ2, hZb, -, hZZ⟩ := hl2_Zb hx hx2 hc hc2 hr
  have he0 : 0 < x - c := by linarith
  have hZ0 : 0 < hl2Zr x c r := by linarith
  have hS : 0 < 1 + x := by linarith
  have keyD : 324 * (1 + x) * (hl2W4 x c u * (7 / 3) ^ 4 - 7 * hl2Lr x c u -
      3 * (x - c) / 14 * (7 / 3) ^ 4) = (16 - 20 * u) * hl2PD0 (x - 2) (c - 5 / 8) / 4096 +
      (20 * u - 15) * hl2PD1 (x - 2) (c - 5 / 8) / 20480 := by
    unfold hl2Lr hl2Rr hl2Xi hl2Wr hl2W4 hl2Dr hl2d1 hl2d2 hl2J2 hsE0 hl2PD0 hl2PD1
    field_simp
    ring
  have hD0 := hl2_PD0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hD1 := hl2_PD1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hD : 0 < hl2W4 x c u * (7 / 3) ^ 4 - 7 * hl2Lr x c u - 3 * (x - c) / 14 * (7 / 3) ^ 4 := by
    have : 0 < 324 * (1 + x) * (hl2W4 x c u * (7 / 3) ^ 4 - 7 * hl2Lr x c u -
        3 * (x - c) / 14 * (7 / 3) ^ 4) := by
      rw [keyD]; exact hl2_affine_pos hu hu2 hD0 hD1 (by norm_num) (by norm_num)
    exact pos_of_mul_pos_right this (by positivity)
  -- `A(r) ≥ 6W₄/(7e) - 9/49 > 0`
  have hA : 6 * hl2W4 x c u / (7 * (x - c)) - 9 / 49 ≤
      3 * hl2W3 x c u / 98 + 6 * hl2W4 x c u * r / 49 + 6 * hl2W4 x c u / (7 * (x - c)) := by
    have : 0 ≤ 6 * hl2W4 x c u * r / 49 := by
      have : 0 ≤ r := by linarith
      positivity
    linarith
  have hA0 : 0 < 6 * hl2W4 x c u / (7 * (x - c)) - 9 / 49 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]
    nlinarith
  have hZ4 : (7 / 3) ^ 4 ≤ hl2Zr x c r ^ 4 := pow_le_pow_left₀ (by norm_num) (hZb.trans hZZ) 4
  have hg : 0 < (3 * hl2W3 x c u / 98 + 6 * hl2W4 x c u * r / 49 +
      6 * hl2W4 x c u / (7 * (x - c))) * hl2Zr x c r ^ 4 - 6 * (x - c) ^ 3 * hl2Rr x c u +
      2 * (x - c) ^ 3 * hl2Zr x c r := by
    have h1 := mul_le_mul hA hZ4 (by positivity) (hA0.le.trans hA)
    have e : (6 * hl2W4 x c u / (7 * (x - c)) - 9 / 49) * (7 / 3) ^ 4 -
        6 * (x - c) ^ 3 * hl2Rr x c u = 6 / (7 * (x - c)) * (hl2W4 x c u * (7 / 3) ^ 4 -
        7 * hl2Lr x c u - 3 * (x - c) / 14 * (7 / 3) ^ 4) := by
      unfold hl2Lr; field_simp; ring
    have h2 : 0 < 6 / (7 * (x - c)) * (hl2W4 x c u * (7 / 3) ^ 4 - 7 * hl2Lr x c u -
        3 * (x - c) / 14 * (7 / 3) ^ 4) := mul_pos (by positivity) hD
    have h3 : 0 < 2 * (x - c) ^ 3 * hl2Zr x c r := by positivity
    linarith
  rw [hl2_H1d3_eq he0.ne' hZ0.ne']
  have e : 3 * hl2W3 x c u / 98 + 6 * hl2W4 x c u * r / 49 + 6 * hl2W4 x c u / (7 * (x - c)) -
      6 * (x - c) ^ 3 * hl2Rr x c u / hl2Zr x c r ^ 4 + 2 * (x - c) ^ 3 / hl2Zr x c r ^ 3 =
      ((3 * hl2W3 x c u / 98 + 6 * hl2W4 x c u * r / 49 + 6 * hl2W4 x c u / (7 * (x - c))) *
        hl2Zr x c r ^ 4 - 6 * (x - c) ^ 3 * hl2Rr x c u + 2 * (x - c) ^ 3 * hl2Zr x c r) /
        hl2Zr x c r ^ 4 := by
    field_simp
  rw [e]
  positivity

/-- The identity C (`SHORT_RATIO_OUTER_RECIPROCAL_ALGEBRA`: `107520e²S𝒞`). -/
theorem hl2_keyC {x c u : ℝ} (hx0 : x ≠ 0) (he0 : x - c ≠ 0) (hS : 1 + x ≠ 0) :
    107520 * (x - c) ^ 2 * (1 + x) * (-hl2ELd2 x c u - 2 / 3 +
      6 * hl2W4 x c u / (7 * (x - c) * x) + 2 * hl2W3 x c u / (7 * (x - c)) -
      2 * (1 + c) * hl2W4 x c u / (7 * (x - c) ^ 2) + 27 * hl2Lr x c u / (256 * (x - c) ^ 2) -
      3 / 5 - 1 / 2) = (16 - 20 * u) * hl2PC0 (x - 2) (c - 5 / 8) / 4096 +
      (20 * u - 15) * hl2PC1 (x - 2) (c - 5 / 8) / 4096 := by
    unfold hl2ELd2 hl2Lr hl2Rr hl2Xi hl2Wr hl2W3 hl2W4 hl2Dr hl2d1 hl2d2 hl2J2 hsE0 hl2PC0 hl2PC1
    field_simp
    ring

/-- `(H₁)_rr(1/x) > 1/2` (`SHORT_RATIO_OUTER_RECIPROCAL` (18)-(19); identities C). -/
theorem hl2_H1d2_edge {x c u : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) :
    1 / 2 < hl2H1d2 x c u (1 / x) := by
  obtain ⟨he, he', -⟩ := hl2_comp hx hx2 hc hc2 hu hu2
  obtain ⟨hW2, -, hW3, hW4⟩ := hl2_Wb hx hx2 hc hc2 hu hu2
  obtain ⟨hr5, -, hZb, hZb', -⟩ := hl2_Zb hx hx2 hc hc2 le_rfl
  have hx0 : 0 < x := by linarith
  have he0 : 0 < x - c := by linarith
  have hS : 0 < 1 + x := by linarith
  have hL := hl2_L_pos hx hx2 hc hc2 hu hu2
  have keyC := hl2_keyC (x := x) (c := c) (u := u) hx0.ne' he0.ne' hS.ne'
  have hC0 := hl2_PC0_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hC1 := hl2_PC1_pos (h := x - 2) (t := c - 5 / 8) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hC : 0 < -hl2ELd2 x c u - 2 / 3 + 6 * hl2W4 x c u / (7 * (x - c) * x) +
      2 * hl2W3 x c u / (7 * (x - c)) - 2 * (1 + c) * hl2W4 x c u / (7 * (x - c) ^ 2) +
      27 * hl2Lr x c u / (256 * (x - c) ^ 2) - 3 / 5 - 1 / 2 := by
    have : 0 < 107520 * (x - c) ^ 2 * (1 + x) * (-hl2ELd2 x c u - 2 / 3 +
        6 * hl2W4 x c u / (7 * (x - c) * x) + 2 * hl2W3 x c u / (7 * (x - c)) -
        2 * (1 + c) * hl2W4 x c u / (7 * (x - c) ^ 2) + 27 * hl2Lr x c u / (256 * (x - c) ^ 2) -
        3 / 5 - 1 / 2) := by
      rw [keyC]; exact hl2_affine_pos hu hu2 hC0 hC1 (by norm_num) (by norm_num)
    exact pos_of_mul_pos_right this (by positivity)
  -- the three comparisons of (18)-(19)
  have hWd2 : -(2 / 3) < hl2Wd2 x c u (1 / x) / 196 := by
    unfold hl2Wd2
    have h6 : 1 / x ≤ 6 / 13 := by rw [div_le_iff₀ hx0]; linarith
    have h1 : -6 * (6 / 13) ≤ hl2W3 x c u * (1 / x) := by
      rcases le_total 0 (hl2W3 x c u) with h | h
      · have : 0 ≤ hl2W3 x c u * (1 / x) := by positivity
        linarith
      · nlinarith
    have h2 : 0 ≤ hl2W4 x c u * (1 / x) ^ 2 := by
      have : 0 ≤ hl2W4 x c u := by linarith
      positivity
    linarith
  have hR : 27 * hl2Lr x c u / (256 * (x - c) ^ 2) ≤
      2 * (x - c) ^ 2 * hl2Rr x c u / hl2Zr x c (1 / x) ^ 3 := by
    have e : 2 * (x - c) ^ 2 * hl2Rr x c u / hl2Zr x c (1 / x) ^ 3 =
        2 * hl2Lr x c u / ((x - c) ^ 2 * hl2Zr x c (1 / x) ^ 3) := by
      unfold hl2Lr; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hZ3 : hl2Zr x c (1 / x) ^ 3 ≤ (8 / 3) ^ 3 := pow_le_pow_left₀ (by linarith) hZb' 3
    have : 0 < hl2Lr x c u * (x - c) ^ 2 := by positivity
    nlinarith
  have hE : -(3 / 5) < -((x - c) ^ 2 / hl2Zr x c (1 / x) ^ 2) := by
    rw [neg_lt_neg_iff, div_lt_iff₀ (by positivity)]
    have : (7 / 3) ^ 2 ≤ hl2Zr x c (1 / x) ^ 2 := pow_le_pow_left₀ (by norm_num) hZb 2
    nlinarith
  rw [hl2_H1d2_eq he0.ne' (ne_of_gt (by linarith))]
  have e6 : 6 * hl2W4 x c u * (1 / x) / (7 * (x - c)) = 6 * hl2W4 x c u / (7 * (x - c) * x) := by
    field_simp
  rw [e6]
  linarith

/-- `(H₁)_rr > 1/2` on the rectangle (`SHORT_RATIO_OUTER_RECIPROCAL` (1), `j = 1`). -/
theorem hl2_H1d2_gt {x c u r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (hr : 1 / x ≤ r) (hr2 : r ≤ 5 / 6) :
    1 / 2 < hl2H1d2 x c u r :=
  lt_of_lt_of_le (hl2_H1d2_edge hx hx2 hc hc2 hu hu2)
    (ss_le_of_deriv hr (fun s hs => hl2_hd_H1d2 (by linarith [(hl2_Zb hx hx2 hc hc2 hs.1).2.1]))
      (fun s hs => (hl2_H1d3_pos hx hx2 hc hc2 hu hu2 hs.1.le (hs.2.le.trans hr2)).le))

/-! ### Convexity -/

/-- `H₀` is at most its larger endpoint value on `[r₀, r₁] ⊆ [1/x, 5/6]`. -/
theorem hl2_H0_le_max {x c u r0 r r1 : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (h0 : 1 / x ≤ r0) (h01 : r0 ≤ r)
    (h1 : r ≤ r1) (h15 : r1 ≤ 5 / 6) :
    hl2H0 x c u r ≤ max (hl2H0 x c u r0) (hl2H0 x c u r1) :=
  hl2_le_max_of_deriv2 h01 h1
    (fun s hs => hl2_hd_H0 (by linarith [(hl2_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => hl2_hd_H0d1 (by linarith [(hl2_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => by linarith [hl2_H0d2_gt hx hx2 hc hc2 hu hu2 (h0.trans hs.1) (hs.2.trans h15)])

/-- `H₁` is at most its larger endpoint value on `[r₀, r₁] ⊆ [1/x, 5/6]`. -/
theorem hl2_H1_le_max {x c u r0 r r1 : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hu : 3 / 4 ≤ u) (hu2 : u ≤ 4 / 5) (h0 : 1 / x ≤ r0) (h01 : r0 ≤ r)
    (h1 : r ≤ r1) (h15 : r1 ≤ 5 / 6) :
    hl2H1 x c u r ≤ max (hl2H1 x c u r0) (hl2H1 x c u r1) :=
  hl2_le_max_of_deriv2 h01 h1
    (fun s hs => hl2_hd_H1 (by linarith [(hl2_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => hl2_hd_H1d1 (by linarith [(hl2_Zb hx hx2 hc hc2 (h0.trans hs.1)).2.1]))
    (fun s hs => by linarith [hl2_H1d2_gt hx hx2 hc hc2 hu hu2 (h0.trans hs.1) (hs.2.trans h15)])

end SmoothedOctagon

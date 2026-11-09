module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.CentralFace.ShapeDerivative

/-!
# Smaller-short window, displacement, central face: the sign of the shape derivative

The central face sign `dsp_central_alpha_proof`, second part. On the actual
comparison path `a_min(x) ≤ a`, `6a² ≤ x(x + 2)`, `2 ≤ x ≤ 13/6`, both shape derivatives
`H_i = dspcH x a n_i N_i` (`CentralFace/ShapeDerivative`) are negative: the grouped term is at most
`(8/5)𝓡(q)`, `𝓡(q) = (16363/330)q² - (87103/6000)q + 1 < 0`, and with the first-term bound
`dspc_T1`, the pairing and norm bounds `dspc_EL_bd`, `dspc_w_bd` and the `Bu_b` term, `H_i` is
below a convex quadratic in `q`, negative on `[63/500, 1/7]` (`dspc_core`).
Hence both tests decrease from `a_min(x)` to `a`, and the endpoint signs `dsp_central_endpoint`
close the face.

The lower bounds `n_i ≥ 19/6` are proved by the exact divided differences of the cleared
multiplier conditions between `a` and `a₊ = 13(3x + 2)/90` (with the endpoint polynomials
`P₀(h)`, `P₁(h)`), and the polynomial `Q_w(h, r)` (`dspcQw`) is bounded through `4H₀H₂ > H₁²`.

## Main API

* `dspc_H_neg`: `H_i < 0` on the comparison path.
* `dsp_central_alpha_proof`: `F₀, F₁ < 0` at `(x, a, b(x, a), ū(x, b(x, a)), q_c(x, a))` for
  `a_min(x) ≤ a`, `6a² ≤ x(x + 2)`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- Powers of `0 ≤ h ≤ 1/6`. -/
theorem dsp_hpow {h : ℝ} (h0 : 0 ≤ h) (h6 : h ≤ 1 / 6) :
    h ^ 2 ≤ 1 / 36 ∧ h ^ 3 ≤ 1 / 216 ∧ h ^ 4 ≤ 1 / 1296 ∧ h ^ 5 ≤ 1 / 7776 ∧ h ^ 6 ≤ 1 / 46656 ∧
      h ^ 7 ≤ 1 / 279936 ∧ h ^ 8 ≤ 1 / 1679616 := by
  have k : ∀ n : ℕ, h ^ n ≤ (1 / 6) ^ n := fun n => pow_le_pow_left₀ h0 h6 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := k 2; norm_num at this ⊢; linarith
  · have := k 3; norm_num at this ⊢; linarith
  · have := k 4; norm_num at this ⊢; linarith
  · have := k 5; norm_num at this ⊢; linarith
  · have := k 6; norm_num at this ⊢; linarith
  · have := k 7; norm_num at this ⊢; linarith
  · have := k 8; norm_num at this ⊢; linarith

section Bounds

variable {x a : ℝ}

/-! ### The comparison domain -/

/-- `a ≥ (x + 23)/22 ≥ 108/95`, `a ≤ a₊ = 13(3x + 2)/90 < 5/4`. -/
theorem dspc_dom (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    (x + 23) / 22 ≤ a ∧ 108 / 95 ≤ a ∧ a ≤ 13 * (3 * x + 2) / 90 ∧ a < 5 / 4 := by
  unfold dspamin at ham
  have hap : a < 13 * (3 * x + 2) / 90 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (a + 13 * (3 * x + 2) / 90)]
  refine ⟨by linarith, by linarith, hap.le, by linarith⟩

theorem dspc_B_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) : 3 / 4 ≤ dspcB x ∧ dspcB x ≤ 4 / 5 := by
  unfold dspcB
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

/-- `x - B = x(15x + 11)/(15x + 36)`. -/
theorem dspc_xB (hx : 0 < x) : x - dspcB x = x * (15 * x + 11) / (15 * x + 36) := by
  unfold dspcB
  field_simp
  ring

/-- `a + b = (40ax + 36a + 15x² + 11x)/(15x + 36)`. -/
theorem dspc_ab (hx : 0 < x) :
    a + dspb x a = (40 * a * x + 36 * a + 15 * x ^ 2 + 11 * x) / (15 * x + 36) := by
  unfold dspb
  have : 15 * x + 36 ≠ 0 := by linarith
  field_simp
  ring

/-- The boundary point: `20x/19 ≤ b ≤ 2a` and `11a/6 ≤ b` (so `1/p ≥ 17/6`). -/
theorem dspc_b_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    20 * x / 19 ≤ dspb x a ∧ dspb x a ≤ 2 * a ∧ 11 * a / 6 ≤ dspb x a := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  unfold dspamin at ham
  have h36 : 0 < 15 * x + 36 := by linarith
  have e : dspb x a * (15 * x + 36) = x * (15 * x + 36) + 25 * x * (a - 1) := by
    unfold dspb; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num)]
    have : x * (15 * x + 36) ≤ 25 * x * (a - 1) * 19 := by nlinarith
    nlinarith
  · have : 15 * x ^ 2 + 11 * x ≤ a * (5 * x + 72) := by nlinarith
    nlinarith
  · -- `a(5x + 132) ≤ 2x(15x + 11)`, from the central cap `6a² ≤ x(x + 2)`
    have hc : a * (5 * x + 132) ≤ 2 * x * (15 * x + 11) := by
      have hsq : (a * (5 * x + 132)) ^ 2 ≤ (2 * x * (15 * x + 11)) ^ 2 := by
        have e10 : 6 * (2 * x * (15 * x + 11)) ^ 2 - (5 * x + 132) ^ 2 * (x * (x + 2)) =
            x * (5375 * (x - 2) ^ 3 + 38800 * (x - 2) ^ 2 + 73540 * (x - 2) + 32) := by ring
        have hpos : 0 ≤ x * (5375 * (x - 2) ^ 3 + 38800 * (x - 2) ^ 2 + 73540 * (x - 2) + 32) := by
          have : 0 ≤ x - 2 := by linarith
          positivity
        nlinarith [mul_le_mul_of_nonneg_left h6 (sq_nonneg (5 * x + 132))]
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    nlinarith

/-- `p = a/(a + b) ∈ [1/3, 1/2)`, `1/p ≥ 17/6`. -/
theorem dspc_p_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    1 / 3 ≤ dspcp x a ∧ dspcp x a < 1 / 2 ∧ 17 / 6 ≤ 1 / dspcp x a := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hb1, hb2, hb3⟩ := dspc_b_bds hx hx2 ham h6
  have hb : x ≤ dspb x a := by
    have : x ≤ 20 * x / 19 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  unfold dspcp ssRA
  have hab : 0 < a + dspb x a := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hab]; linarith
  · rw [div_lt_iff₀ hab]; linarith
  · rw [one_div_div, le_div_iff₀ (by linarith)]; linarith

/-- `q = a²/K ∈ [63/500, 1/7]`, from `a ≥ (x + 23)/22` and the central cap. -/
theorem dspc_q_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : 63 / 500 ≤ ssQc x a ∧ ssQc x a ≤ 1 / 7 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  unfold ssQc
  have hK : 0 < x * (x + 2) + a ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hK]
    have h1 : ((x + 23) / 22) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) h23 2
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  · rw [div_le_iff₀ hK]; linarith

/-- `y = 2q/p = 2a(a + b)/K ∈ [3/4, 6/7]`. -/
theorem dspc_y_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : 3 / 4 ≤ dspcy x a ∧ dspcy x a ≤ 6 / 7 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hb1, hb2, hb3⟩ := dspc_b_bds hx hx2 ham h6
  have hK : 0 < x * (x + 2) + a ^ 2 := by positivity
  have ha0 : 0 < a := by linarith
  have hab : 0 < a + dspb x a := by linarith
  have e : dspcy x a = 2 * a * (a + dspb x a) / (x * (x + 2) + a ^ 2) := by
    unfold dspcy dspcp ssRA ssQc
    field_simp
  rw [e]
  have hb20 : 20 * x / 19 * 19 = 20 * x := by ring
  constructor
  · rw [le_div_iff₀ hK]
    have : 20 * x / 19 * a ≤ dspb x a * a := mul_le_mul_of_nonneg_right hb1 ha0.le
    nlinarith [mul_nonneg (sub_nonneg.2 h108) (sub_nonneg.2 hx),
      mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), mul_nonneg (sub_nonneg.2 h108) (sub_nonneg.2 h108)]
  · rw [div_le_iff₀ hK]
    nlinarith [mul_le_mul_of_nonneg_left hb2 ha0.le]

/-- `n₀ ≥ 19/6`: `(103 - 35a)K - 144a(a + b) ≥ 0`, by the divided difference to
`a₊ = 13(3x + 2)/90` and `P₀(h) > 0`. -/
theorem dspc_n0_lo (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : 19 / 6 ≤ dspcn0 x a := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hB1, hB2⟩ := dspc_B_bds hx hx2
  have hK : 0 < x * (x + 2) + a ^ 2 := by positivity
  have ha0 : 0 < a := by linarith
  set ap := 13 * (3 * x + 2) / 90 with hapd
  set B := dspcB x with hBd
  -- the cleared condition at `a₊`
  have hG0p : 0 ≤ (103 - 35 * ap) * (x * (x + 2) + ap ^ 2) - 144 * ap * (ap + (x + B * (ap - 1))) := by
    have e : ((103 - 35 * ap) * (x * (x + 2) + ap ^ 2) - 144 * ap * (ap + (x + B * (ap - 1)))) *
        (145800 * (5 * x + 12)) = 125999488 - 633236320 * (x - 2) - 655622604 * (x - 2) ^ 2 -
          179084736 * (x - 2) ^ 3 - 13132665 * (x - 2) ^ 4 := by
      rw [hBd, hapd]; unfold dspcB; field_simp; ring
    have hh0 : 0 ≤ x - 2 := by linarith
    obtain ⟨p2, p3, p4, -⟩ := dsp_hpow hh0 (by linarith)
    have : 0 ≤ 125999488 - 633236320 * (x - 2) - 655622604 * (x - 2) ^ 2 -
          179084736 * (x - 2) ^ 3 - 13132665 * (x - 2) ^ 4 := by linarith
    rw [← e] at this
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hM : 0 ≤ (ap - a) * (144 * B * (a + ap - 1) + 35 * (a ^ 2 + a * ap + ap ^ 2) + 41 * (a + ap) +
      35 * x ^ 2 + 214 * x) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hG0 : 0 ≤ (103 - 35 * a) * (x * (x + 2) + a ^ 2) - 144 * a * (a + (x + B * (a - 1))) := by
    nlinarith
  -- back to `n₀`
  have hab : 0 < a + (x + B * (a - 1)) := by nlinarith
  have hyK : dspcy x a * (x * (x + 2) + a ^ 2) = 2 * a * (a + (x + B * (a - 1))) := by
    unfold dspcy dspcp ssRA ssQc
    rw [dspc_b_eq, ← hBd]
    field_simp
  have hy : 72 * dspcy x a ≤ 103 - 35 * a := by nlinarith
  have hk : 0 < 5 * a - 1 := by linarith
  have : 7 / 6 ≤ 4 * (4 - 3 * dspcy x a) / (5 * a - 1) := by
    rw [le_div_iff₀ hk]; linarith
  unfold dspcn0
  linarith

/-- `n₁ ≥ 19/6`: `6K(5a - 1) + 24a(a + b) - 19(5a - 1)a(a + b) ≥ 0`, by the
divided difference to `a₊` and `P₁(h) > 0`. -/
theorem dspc_n1_lo (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : 19 / 6 ≤ dspcn1 x a := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hB1, hB2⟩ := dspc_B_bds hx hx2
  have hK : 0 < x * (x + 2) + a ^ 2 := by positivity
  have ha0 : 0 < a := by linarith
  set ap := 13 * (3 * x + 2) / 90 with hapd
  set B := dspcB x with hBd
  have hap1 : 108 / 95 ≤ ap := by rw [hapd]; linarith
  have hap2 : ap ≤ 5 / 4 := by rw [hapd]; linarith
  have hG1p : 0 ≤ 6 * (x * (x + 2) + ap ^ 2) * (5 * ap - 1) + 24 * ap * (ap + (x + B * (ap - 1))) -
      19 * (5 * ap - 1) * ap * (ap + (x + B * (ap - 1))) := by
    have e : (6 * (x * (x + 2) + ap ^ 2) * (5 * ap - 1) + 24 * ap * (ap + (x + B * (ap - 1))) -
        19 * (5 * ap - 1) * ap * (ap + (x + B * (ap - 1)))) * (218700 * (5 * x + 12)) =
          72261472 - 304916812 * (x - 2) - 443055600 * (x - 2) ^ 2 -
          187091181 * (x - 2) ^ 3 - 25163190 * (x - 2) ^ 4 := by
      rw [hBd, hapd]; unfold dspcB; field_simp; ring
    have hh0 : 0 ≤ x - 2 := by linarith
    obtain ⟨p2, p3, p4, -⟩ := dsp_hpow hh0 (by linarith)
    have : 0 ≤ 72261472 - 304916812 * (x - 2) - 443055600 * (x - 2) ^ 2 -
          187091181 * (x - 2) ^ 3 - 25163190 * (x - 2) ^ 4 := by linarith
    rw [← e] at this
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hM : 0 ≤ (ap - a) * (95 * B * (a ^ 2 + a * ap + ap ^ 2) - 138 * B * (a + ap) + 43 * B +
      65 * (a ^ 2 + a * ap + ap ^ 2) + 95 * x * (a + ap) - 37 * (a + ap) - 30 * x ^ 2 - 103 * x) := by
    apply mul_nonneg (by linarith)
    have hB0 : 0 ≤ B := by linarith
    have h1 : 0 ≤ 95 * (a ^ 2 + a * ap + ap ^ 2) - 138 * (a + ap) + 43 := by nlinarith
    nlinarith [mul_nonneg hB0 h1, mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 h108),
      mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hap1)]
  have hG1 : 0 ≤ 6 * (x * (x + 2) + a ^ 2) * (5 * a - 1) + 24 * a * (a + (x + B * (a - 1))) -
      19 * (5 * a - 1) * a * (a + (x + B * (a - 1))) := by
    nlinarith
  have hab : 0 < a + (x + B * (a - 1)) := by nlinarith
  set m := a * (a + (x + B * (a - 1))) with hmd
  have hm : 0 < m := by positivity
  have hTm : dspcp x a / ssQc x a * m = x * (x + 2) + a ^ 2 := by
    unfold dspcp ssRA ssQc
    rw [dspc_b_eq, ← hBd, hmd]
    field_simp
  have hk : 0 < 5 * a - 1 := by linarith
  have htk : 4 / (5 * a - 1) * (5 * a - 1) = 4 := by field_simp
  unfold dspcn1
  by_contra hc
  rw [not_le] at hc
  have h1 := mul_lt_mul_of_pos_right hc (by positivity : (0 : ℝ) < 6 * (5 * a - 1) * m)
  have e1 : dspcp x a / ssQc x a * (5 * a - 1) * m = (x * (x + 2) + a ^ 2) * (5 * a - 1) := by
    rw [mul_right_comm, hTm]
  have e2 : 4 / (5 * a - 1) * (5 * a - 1) * m = 4 * m := by rw [htk]
  nlinarith

/-- `n₀, n₁ ≤ 53/15`, from `y ≥ 3/4` and `k ≥ 89/19`. -/
theorem dspc_n_hi (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : dspcn0 x a ≤ 53 / 15 ∧ dspcn1 x a ≤ 53 / 15 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hy1, hy2⟩ := dspc_y_bds hx hx2 ham h6
  have hk : 89 / 19 ≤ 5 * a - 1 := by linarith
  have hk0 : 0 < 5 * a - 1 := by linarith
  have hp0 := dspc_p_pos (x := x) (a := a) (by linarith) (by linarith)
  have hq0 := dspc_q_pos (x := x) (a := a) (by linarith) (by linarith)
  have hik : 1 / (5 * a - 1) ≤ 19 / 89 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]; linarith
  constructor
  · unfold dspcn0
    have : 4 * (4 - 3 * dspcy x a) / (5 * a - 1) = 4 * (4 - 3 * dspcy x a) * (1 / (5 * a - 1)) := by
      ring
    rw [this]
    have h1 : 0 ≤ 4 * (4 - 3 * dspcy x a) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hik h1]
  · unfold dspcn1
    have eT : dspcp x a / ssQc x a = 2 / dspcy x a := by
      unfold dspcy; field_simp
    rw [eT]
    have hT : 2 / dspcy x a ≤ 8 / 3 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have : 4 / (5 * a - 1) = 4 * (1 / (5 * a - 1)) := by ring
    rw [this]
    linarith

/-- `A ≥ 25/11`: `66aj(A - 25/11) = 127h - 220h² + 85hr + 44r`, `h = x - 2`, `r = 8a - 9`,
`j = 5x + 12`. -/
theorem dspc_A_lo (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : 25 / 11 ≤ dspcA x a := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  have ha0 : 0 < a := by linarith
  have e : (dspcA x a - 25 / 11) * (66 * a * (5 * x + 12)) = 127 * (x - 2) - 220 * (x - 2) ^ 2 +
      85 * (x - 2) * (8 * a - 9) + 44 * (8 * a - 9) := by
    unfold dspcA dspcB
    have : 15 * x + 36 ≠ 0 := by linarith
    field_simp
    ring
  have hr : 0 ≤ 8 * a - 9 := by linarith
  have hh : 0 ≤ x - 2 := by linarith
  have : 0 ≤ (dspcA x a - 25 / 11) * (66 * a * (5 * x + 12)) := by
    rw [e]; nlinarith [mul_nonneg hh hr]
  have := nonneg_of_mul_nonneg_left this (by positivity)
  linarith

/-- `0 < z < 6/5`: `2560aKZ(6/5 - z) = Q_z(h, r)`, `Z = 3j(a + b)`. -/
theorem dspc_z_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) : 0 < dspcz x a ∧ dspcz x a < 6 / 5 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hb1, hb2, hb3⟩ := dspc_b_bds hx hx2 ham h6
  obtain ⟨hB1, hB2⟩ := dspc_B_bds hx hx2
  have ha0 : 0 < a := by linarith
  have hK : 0 < x * (x + 2) + a ^ 2 := by positivity
  have hab : 0 < a + dspb x a := by linarith
  have hb20 : x ≤ dspb x a := by
    have : x ≤ 20 * x / 19 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  constructor
  · unfold dspcz dspcL dspcK
    have h1 : (x - dspcB x) / (a * (a + dspb x a)) < 1 / a := by
      rw [div_lt_div_iff₀ (by positivity) ha0]; nlinarith
    have h2 : 2 * a / (x * (x + 2) + a ^ 2) < 1 / a := by
      rw [div_lt_div_iff₀ hK ha0]; nlinarith
    have : 2 / a = 1 / a + 1 / a := by ring
    linarith
  · have e : (6 / 5 - dspcz x a) * (2560 * a * (x * (x + 2) + a ^ 2) *
        (40 * a * x + 36 * a + 15 * x ^ 2 + 11 * x)) =
        (30 * (x - 2) + 87) * (8 * a - 9) ^ 4 +
        (90 * (x - 2) ^ 2 + 1506 * (x - 2) + 3624) * (8 * a - 9) ^ 3 +
        (1920 * (x - 2) ^ 3 + 20118 * (x - 2) ^ 2 + 77690 * (x - 2) + 103390) * (8 * a - 9) ^ 2 +
        (5760 * (x - 2) ^ 4 + 70784 * (x - 2) ^ 3 + 353566 * (x - 2) ^ 2 + 876742 * (x - 2) +
          892064) * (8 * a - 9) +
        13440 * (x - 2) ^ 4 + 69376 * (x - 2) ^ 3 + 10466 * (x - 2) ^ 2 - 214768 * (x - 2) + 45715 := by
      have hZ : 0 < 40 * a * x + 36 * a + 15 * x ^ 2 + 11 * x := by positivity
      unfold dspcz dspcL dspcK
      rw [dspc_ab (by linarith), dspc_xB (by linarith)]
      have : 15 * x + 36 ≠ 0 := by linarith
      have : 40 * a * x + 36 * a + 15 * x ^ 2 + 11 * x ≠ 0 := hZ.ne'
      field_simp
      ring
    have hQ : 0 < (30 * (x - 2) + 87) * (8 * a - 9) ^ 4 +
        (90 * (x - 2) ^ 2 + 1506 * (x - 2) + 3624) * (8 * a - 9) ^ 3 +
        (1920 * (x - 2) ^ 3 + 20118 * (x - 2) ^ 2 + 77690 * (x - 2) + 103390) * (8 * a - 9) ^ 2 +
        (5760 * (x - 2) ^ 4 + 70784 * (x - 2) ^ 3 + 353566 * (x - 2) ^ 2 + 876742 * (x - 2) +
          892064) * (8 * a - 9) +
        13440 * (x - 2) ^ 4 + 69376 * (x - 2) ^ 3 + 10466 * (x - 2) ^ 2 - 214768 * (x - 2) + 45715 := by
      have hh : 0 ≤ x - 2 := by linarith
      have hr : 0 ≤ 8 * a - 9 := by linarith
      have : 0 ≤ (30 * (x - 2) + 87) * (8 * a - 9) ^ 4 +
        (90 * (x - 2) ^ 2 + 1506 * (x - 2) + 3624) * (8 * a - 9) ^ 3 +
        (1920 * (x - 2) ^ 3 + 20118 * (x - 2) ^ 2 + 77690 * (x - 2) + 103390) * (8 * a - 9) ^ 2 +
        (5760 * (x - 2) ^ 4 + 70784 * (x - 2) ^ 3 + 353566 * (x - 2) ^ 2 + 876742 * (x - 2) +
          892064) * (8 * a - 9) + 13440 * (x - 2) ^ 4 + 69376 * (x - 2) ^ 3 + 10466 * (x - 2) ^ 2 := by
        positivity
      linarith
    rw [← e] at hQ
    have := pos_of_mul_pos_left hQ (by positivity)
    linarith

/-- `-N₀ ≤ 4` and `-N₁ ≤ 21/5`, both `N_i < 0`. -/
theorem dspc_N_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    dspcN0 x a < 0 ∧ -dspcN0 x a ≤ 21 / 5 ∧ dspcN1 x a < 0 ∧ -dspcN1 x a ≤ 21 / 5 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hy1, hy2⟩ := dspc_y_bds hx hx2 ham h6
  obtain ⟨hz1, hz2⟩ := dspc_z_bds hx hx2 ham h6
  have hk0 : 0 < 5 * a - 1 := by linarith
  have hik0 : 0 < 1 / (5 * a - 1) := by positivity
  have hik : 1 / (5 * a - 1) ≤ 19 / 89 := by
    rw [div_le_div_iff₀ hk0 (by norm_num)]; linarith
  have hik2 : (1 / (5 * a - 1)) ^ 2 ≤ (19 / 89) ^ 2 := pow_le_pow_left₀ hik0.le hik 2
  have hp0 := dspc_p_pos (x := x) (a := a) (by linarith) (by linarith)
  have hq0 := dspc_q_pos (x := x) (a := a) (by linarith) (by linarith)
  have eT : dspcp x a / ssQc x a = 2 / dspcy x a := by
    unfold dspcy; field_simp
  have hT : 2 / dspcy x a ≤ 8 / 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hT0 : 0 < 2 / dspcy x a := by
    apply div_pos (by norm_num); linarith
  have e0 : dspcN0 x a = -12 * (dspcy x a * dspcz x a) * (1 / (5 * a - 1)) -
      20 * (4 - 3 * dspcy x a) * (1 / (5 * a - 1)) ^ 2 := by
    unfold dspcN0; field_simp
  have e1 : dspcN1 x a = -(2 / dspcy x a) * dspcz x a - 20 * (1 / (5 * a - 1)) ^ 2 := by
    unfold dspcN1; rw [eT]; field_simp
  have hyz : dspcy x a * dspcz x a ≤ 6 / 7 * (6 / 5) :=
    mul_le_mul hy2 hz2.le hz1.le (by norm_num)
  have hyz0 : 0 < dspcy x a * dspcz x a := mul_pos (by linarith) hz1
  have h4y : 0 ≤ 4 - 3 * dspcy x a := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]
    have : 0 < dspcy x a * dspcz x a * (1 / (5 * a - 1)) := by positivity
    nlinarith [mul_nonneg h4y (sq_nonneg (1 / (5 * a - 1)))]
  · rw [e0]
    have h1 : dspcy x a * dspcz x a * (1 / (5 * a - 1)) ≤ 6 / 7 * (6 / 5) * (19 / 89) :=
      mul_le_mul hyz hik hik0.le (by norm_num)
    have h2 : (4 - 3 * dspcy x a) * (1 / (5 * a - 1)) ^ 2 ≤ (4 - 3 * (3 / 4)) * (19 / 89) ^ 2 :=
      mul_le_mul (by linarith) hik2 (by positivity) (by norm_num)
    -- the affine function of `y` increases; `y ≤ 6/7`
    nlinarith
  · rw [e1]
    have : 0 < 2 / dspcy x a * dspcz x a := mul_pos hT0 hz1
    nlinarith [sq_nonneg (1 / (5 * a - 1))]
  · rw [e1]
    have h1 : 2 / dspcy x a * dspcz x a ≤ 8 / 3 * (6 / 5) := mul_le_mul hT hz2.le hz1.le (by norm_num)
    nlinarith

/-! ### The incoming ceiling -/

/-- `1/5808 ≤ g = V_G - 3/4 ≤ 1/100` on `[2, 13/6]`. -/
theorem dspc_g_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    1 / 5808 ≤ ssVG x - 3 / 4 ∧ ssVG x - 3 / 4 ≤ 1 / 100 := by
  unfold ssVG
  rw [add_sub_cancel_left]
  have hd : 0 < 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by positivity
  constructor
  · rw [div_le_div_iff₀ (by norm_num) hd]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx), mul_nonneg (sub_nonneg.2 hx)
      (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx))]
  · rw [div_le_div_iff₀ hd (by norm_num)]
    have h1 := mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)
    nlinarith [mul_nonneg h1 (sub_nonneg.2 hx), mul_nonneg h1 (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx))]

/-- `ū(x, b) = 3/4 + 1/5808 + (x - 1)(g - 1/5808)/(b - 1)`. -/
theorem dspc_ucb_eq {b : ℝ} (hb : 1 < b) :
    ssUCB x b = 3 / 4 + 1 / 5808 + (x - 1) * (ssVG x - 3 / 4 - 1 / 5808) / (b - 1) := by
  unfold ssUCB
  have : b - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `b ≤ b₊ = x + B(a₊ - 1)`, `b₊ - 1 = (465x² + 58x - 648)/(18(15x + 36))`. -/
theorem dspc_bp (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    dspb x a - 1 ≤ (465 * x ^ 2 + 58 * x - 648) / (18 * (15 * x + 36)) := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  have e : x + dspcB x * (13 * (3 * x + 2) / 90 - 1) - 1 =
      (465 * x ^ 2 + 58 * x - 648) / (18 * (15 * x + 36)) := by
    unfold dspcB
    have : 15 * x + 36 ≠ 0 := by linarith
    field_simp
    ring
  rw [← e, dspc_b_eq]
  have := (dspc_B_bds hx hx2).1
  nlinarith

/-- `u_0 = 757/1000 + h/150 ≤ u ≤ 19/25` and `-u_b ≥ 3/500`. -/
theorem dspc_u_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    757 / 1000 + (x - 2) / 150 ≤ dspcu x a ∧ dspcu x a ≤ 19 / 25 ∧ dspcub x a ≤ -(3 / 500) := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hb1, hb2, hb3⟩ := dspc_b_bds hx hx2 ham h6
  obtain ⟨hg1, hg2⟩ := dspc_g_bds hx hx2
  have hbp := dspc_bp hx hx2 ham h6
  have hbx : x ≤ dspb x a := by
    have : x ≤ 20 * x / 19 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hb1' : 0 < dspb x a - 1 := by linarith
  set Q := 465 * x ^ 2 + 58 * x - 648 with hQ
  have hQ0 : 0 < Q := by rw [hQ]; nlinarith
  set R := 13 * x ^ 2 + 14 * x + 3 with hR
  have hR0 : 0 < R := by rw [hR]; positivity
  set G := ssVG x - 3 / 4 with hG
  have hG' : G = (x - 1) ^ 2 * (71 * x ^ 2 + 48 * x + 1) / (96 * x * (x + 1) * R) := by
    rw [hG, hR]; unfold ssVG; ring
  have hc : 0 ≤ (x - 1) * (G - 1 / 5808) := mul_nonneg (by linarith) (by linarith)
  have hh0 : 0 ≤ x - 2 := by linarith
  obtain ⟨p2, p3, p4, p5, p6, p7, p8⟩ := dsp_hpow hh0 (by linarith)
  have hx0 : 0 < x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- lower the ceiling to `b₊`, then the one-variable identity with `P_u`
    unfold dspcu
    rw [dspc_ucb_eq (by linarith)]
    have h1 : (x - 1) * (G - 1 / 5808) / (Q / (18 * (15 * x + 36))) ≤
        (x - 1) * (G - 1 / 5808) / (dspb x a - 1) :=
      div_le_div_of_nonneg_left hc hb1' hbp
    have e : 3 / 4 + 1 / 5808 + (x - 1) * (G - 1 / 5808) / (Q / (18 * (15 * x + 36))) -
        (757 / 1000 + (x - 2) / 150) =
        (70764042 + 544147561 * (x - 2) + 703021883 * (x - 2) ^ 2 - 544043387 * (x - 2) ^ 3 -
          1587453649 * (x - 2) ^ 4 - 1086331448 * (x - 2) ^ 5 - 300939850 * (x - 2) ^ 6 -
          29257800 * (x - 2) ^ 7) / (726000 * x * (1 + x) * R * Q) := by
      rw [hG']
      have : 15 * x + 36 ≠ 0 := by linarith
      have : Q ≠ 0 := hQ0.ne'
      have : R ≠ 0 := hR0.ne'
      have : x + 1 ≠ 0 := by linarith
      have : 1 + x ≠ 0 := by linarith
      have : x ≠ 0 := by linarith
      field_simp
      rw [hQ, hR]
      ring
    have hP : 0 ≤ 70764042 + 544147561 * (x - 2) + 703021883 * (x - 2) ^ 2 - 544043387 * (x - 2) ^ 3 -
          1587453649 * (x - 2) ^ 4 - 1086331448 * (x - 2) ^ 5 - 300939850 * (x - 2) ^ 6 -
          29257800 * (x - 2) ^ 7 := by
      have := sq_nonneg (x - 2)
      linarith
    have := div_nonneg hP (by positivity : (0 : ℝ) ≤ 726000 * x * (1 + x) * R * Q)
    linarith
  · -- `u - 3/4 ≤ 1/100`: `(x - 1)g + (b - x)/5808 ≤ (b - 1)/100`
    unfold dspcu ssUCB
    rw [← hG]
    have : ((x - 1) * G + (dspb x a - x) / 5808) / (dspb x a - 1) ≤ 1 / 100 := by
      rw [div_le_iff₀ hb1']
      nlinarith
    linarith
  · -- `-u_b` decreases in `b`; the one-variable identity with `P_b`
    unfold dspcub
    rw [← hG]
    have h1 : (x - 1) * (G - 1 / 5808) / (Q / (18 * (15 * x + 36))) ^ 2 ≤
        (x - 1) * (G - 1 / 5808) / (dspb x a - 1) ^ 2 :=
      div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_left₀ hb1'.le hbp 2)
    have e : (x - 1) * (G - 1 / 5808) / (Q / (18 * (15 * x + 36))) ^ 2 - 3 / 500 =
        3 * (8496963156 + 2200521664 * (x - 2) - 100718737143 * (x - 2) ^ 2 -
          269487341827 * (x - 2) ^ 3 - 312488173018 * (x - 2) ^ 4 - 189579248676 * (x - 2) ^ 5 -
          62001148349 * (x - 2) ^ 6 - 10298395365 * (x - 2) ^ 7 - 680243850 * (x - 2) ^ 8) /
          (121000 * x * (1 + x) * R * Q ^ 2) := by
      rw [hG']
      have : 15 * x + 36 ≠ 0 := by linarith
      have : Q ≠ 0 := hQ0.ne'
      have : R ≠ 0 := hR0.ne'
      have : x + 1 ≠ 0 := by linarith
      have : 1 + x ≠ 0 := by linarith
      have : x ≠ 0 := by linarith
      field_simp
      rw [hQ, hR]
      ring
    have hP : 0 ≤ 8496963156 + 2200521664 * (x - 2) - 100718737143 * (x - 2) ^ 2 -
          269487341827 * (x - 2) ^ 3 - 312488173018 * (x - 2) ^ 4 - 189579248676 * (x - 2) ^ 5 -
          62001148349 * (x - 2) ^ 6 - 10298395365 * (x - 2) ^ 7 - 680243850 * (x - 2) ^ 8 := by
      linarith
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hP)
      (by positivity : (0 : ℝ) ≤ 121000 * x * (1 + x) * R * Q ^ 2)
    have e2 : (x - 1) * (1 / 5808 - G) / (dspb x a - 1) ^ 2 =
        -((x - 1) * (G - 1 / 5808) / (dspb x a - 1) ^ 2) := by ring
    rw [e2]
    linarith

/-! ### The transport coefficients -/

/-- `0 < d ≤ 3/10` and `20/7 ≤ λS ≤ 19/6`. -/
theorem dspc_d_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    0 < dspcd x a ∧ dspcd x a ≤ 3 / 10 ∧ 20 / 7 ≤ dspclam x a * (1 + x) ∧
      dspclam x a * (1 + x) ≤ 19 / 6 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hb1, hb2, hb3⟩ := dspc_b_bds hx hx2 ham h6
  have hK : 0 < dspcK x a := dspc_K_pos (by linarith)
  have hK' : dspcK x a = x * (x + 2) + a ^ 2 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dspcd
    apply div_pos _ hK
    unfold ssDg
    have h1 : dspb x a * (x - a) ≤ 2 * a * (x - a) := mul_le_mul_of_nonneg_right hb2 (by linarith)
    nlinarith
  · -- `30jK(3/10 - d) = P_d(x, a) ≥ P_d(x, a₊) = n(h)/8100`
    have e : (3 / 10 - dspcd x a) * (30 * (5 * x + 12) * dspcK x a) =
        -605 * a ^ 2 * x - 252 * a ^ 2 + 200 * a * x ^ 2 - 220 * a * x + 345 * x ^ 3 + 118 * x ^ 2 -
          654 * x - 360 := by
      unfold dspcd ssDg dspb
      have : 15 * x + 36 ≠ 0 := by linarith
      have : dspcK x a ≠ 0 := hK.ne'
      field_simp
      rw [hK']
      ring
    set ap := 13 * (3 * x + 2) / 90 with hapd
    have hPd : 0 ≤ -605 * ap ^ 2 * x - 252 * ap ^ 2 + 200 * ap * x ^ 2 - 220 * ap * x + 345 * x ^ 3 +
        118 * x ^ 2 - 654 * x - 360 := by
      have e2 : -605 * ap ^ 2 * x - 252 * ap ^ 2 + 200 * ap * x ^ 2 - 220 * ap * x + 345 * x ^ 3 +
          118 * x ^ 2 - 654 * x - 360 = (2576295 * (x - 2) ^ 3 + 14499138 * (x - 2) ^ 2 +
            20348776 * (x - 2) + 225008) / 8100 := by
        rw [hapd]; ring
      rw [e2]
      have : 0 ≤ x - 2 := by linarith
      positivity
    have hdd : 0 ≤ (ap - a) * ((605 * x + 252) * (a + ap) - 200 * x ^ 2 + 220 * x) := by
      apply mul_nonneg (by linarith)
      have : ap ≥ 108 / 95 := by rw [hapd]; linarith
      nlinarith
    have : 0 ≤ (3 / 10 - dspcd x a) * (30 * (5 * x + 12) * dspcK x a) := by rw [e]; nlinarith
    have := nonneg_of_mul_nonneg_left this (by positivity)
    linarith
  · unfold dspclam
    rw [div_mul_eq_mul_div, le_div_iff₀ hK, hK']
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)]
  · unfold dspclam
    rw [div_mul_eq_mul_div, div_le_iff₀ hK, hK']
    have h1 : ((x + 23) / 22) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) h23 2
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]

/-- **The pairing bound** `E_L ≤ 5q - 83/200`. -/
theorem dspc_EL_bd (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) ≤ 5 * ssQc x a - 83 / 200 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hd0, hd1, hl1, hl2⟩ := dspc_d_bds hx hx2 ham h6
  obtain ⟨hu0, hu1, hub⟩ := dspc_u_bds hx hx2 ham h6
  have hK : 0 < dspcK x a := dspc_K_pos (by linarith)
  have hK' : dspcK x a = x * (x + 2) + a ^ 2 := rfl
  -- lower the norm to `u_ℓ = 3/4 + 13/2000`: `(E_L)_u = 2d - λS < 0`
  have hlow : dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) ≤
      dspcEL x (dspclam x a) (dspcd x a) (1513 / 2000) := by
    have e : dspcEL x (dspclam x a) (dspcd x a) (dspcu x a) -
        dspcEL x (dspclam x a) (dspcd x a) (1513 / 2000) =
        (dspcu x a - 1513 / 2000) * (2 * dspcd x a - dspclam x a * (1 + x)) := by
      unfold dspcEL dspcE; ring
    have : (dspcu x a - 1513 / 2000) * (2 * dspcd x a - dspclam x a * (1 + x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  -- `6000jK(5q - 83/200 - E_L) = P_E(x, a)`
  have e : (5 * ssQc x a - 83 / 200 - dspcEL x (dspclam x a) (dspcd x a) (1513 / 2000)) *
      (6000 * (5 * x + 12) * dspcK x a) =
      -59140 * a ^ 2 * x + 221184 * a ^ 2 + 60520 * a * x ^ 2 - 66572 * a * x - 7305 * x ^ 4 +
        38883 * x ^ 3 - 63499 * x ^ 2 - 106923 * x + 17532 := by
    unfold dspcEL dspcE dspclam dspcd ssDg dspb ssQc
    rw [← hK']
    have : 15 * x + 36 ≠ 0 := by linarith
    have : dspcK x a ≠ 0 := hK.ne'
    have : 1 + x ≠ 0 := by linarith
    field_simp
    rw [hK']
    ring
  have hPE : 0 ≤ -59140 * a ^ 2 * x + 221184 * a ^ 2 + 60520 * a * x ^ 2 - 66572 * a * x -
      7305 * x ^ 4 + 38883 * x ^ 3 - 63499 * x ^ 2 - 106923 * x + 17532 := by
    -- increasing in `a`; at `a = 25/22` it is `(3/121)N(h)` with `N ≥ 22000 - 203000h + 2400000h²`
    have hdd : 0 ≤ (a - 25 / 22) * ((221184 - 59140 * x) * (a + 25 / 22) + 60520 * x ^ 2 - 66572 * x) := by
      apply mul_nonneg (by linarith)
      nlinarith
    have hh : 0 ≤ x - 2 := by linarith
    obtain ⟨p2, p3, p4, -⟩ := dsp_hpow hh (by linarith)
    have hN : 0 ≤ 22000 - 203000 * (x - 2) + 2400000 * (x - 2) ^ 2 := by
      nlinarith [sq_nonneg ((x - 2) - 203000 / 4800000)]
    have h3 : (x - 2) ^ 3 ≤ (x - 2) ^ 2 / 6 := by
      have := mul_le_mul_of_nonneg_left (show x - 2 ≤ 1 / 6 by linarith) (sq_nonneg (x - 2))
      nlinarith
    have h4 : (x - 2) ^ 4 ≤ (x - 2) ^ 2 / 36 := by
      have := mul_le_mul_of_nonneg_left p2 (sq_nonneg (x - 2))
      nlinarith
    nlinarith
  have := nonneg_of_mul_nonneg_left (e ▸ hPE) (by positivity)
  linarith

/-- The polynomial `Q_w(h, r)` that controls the norm bound `dspc_w_bd`. -/
noncomputable def dspcQw (h r : ℝ) : ℝ :=
  (3278275 * h ^ 2 + 16992820 * h + 22245004) * r ^ 4 +
    (-15808000 * h ^ 3 + 31803500 * h ^ 2 + 466210640 * h + 728151984) * r ^ 3 +
    (14976000 * h ^ 5 + 60016000 * h ^ 4 - 691610880 * h ^ 3 - 2567450318 * h ^ 2 + 816470712 * h +
      6535942600) * r ^ 2 +
    (-36864000 * h ^ 6 + 135628800 * h ^ 5 + 1618338560 * h ^ 4 - 5043517440 * h ^ 3 -
      37422983124 * h ^ 2 - 43214024624 * h + 7365531312) * r +
    (-442368000 * h ^ 7 - 5902848000 * h ^ 6 - 28361948160 * h ^ 5 - 60905292416 * h ^ 4 -
      71564445952 * h ^ 3 - 86648243805 * h ^ 2 - 76691490124 * h + 16148237836)

/-- `Q_w(h, r) > 0` for `0 ≤ h ≤ 1/6`, `r ≥ 0`: `H₀ > 5·10⁸`,
`H₁ > -9·10⁸`, `H₂ > 64·10⁸`, `H₃, H₄ > 0`, and `4H₀H₂ > H₁²`. -/
theorem dspc_Qw_pos {h r : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hr : 0 ≤ r) : 0 < dspcQw h r := by
  obtain ⟨p2, p3, p4, p5, p6, p7, -⟩ := dsp_hpow hh hh6
  have q2 := sq_nonneg h
  have q3 := pow_nonneg hh 3
  have q4 := pow_nonneg hh 4
  have q5 := pow_nonneg hh 5
  have h4 : 0 ≤ 3278275 * h ^ 2 + 16992820 * h + 22245004 := by positivity
  have h3 : 0 ≤ -15808000 * h ^ 3 + 31803500 * h ^ 2 + 466210640 * h + 728151984 := by linarith
  have h2 : 6400000000 ≤ 14976000 * h ^ 5 + 60016000 * h ^ 4 - 691610880 * h ^ 3 -
      2567450318 * h ^ 2 + 816470712 * h + 6535942600 := by linarith
  have h1 : -900000000 ≤ -36864000 * h ^ 6 + 135628800 * h ^ 5 + 1618338560 * h ^ 4 -
      5043517440 * h ^ 3 - 37422983124 * h ^ 2 - 43214024624 * h + 7365531312 := by linarith
  have h0 : 500000000 ≤ -442368000 * h ^ 7 - 5902848000 * h ^ 6 - 28361948160 * h ^ 5 -
      60905292416 * h ^ 4 - 71564445952 * h ^ 3 - 86648243805 * h ^ 2 - 76691490124 * h +
      16148237836 := by linarith
  unfold dspcQw
  generalize 3278275 * h ^ 2 + 16992820 * h + 22245004 = H4 at h4 ⊢
  generalize -15808000 * h ^ 3 + 31803500 * h ^ 2 + 466210640 * h + 728151984 = H3 at h3 ⊢
  generalize 14976000 * h ^ 5 + 60016000 * h ^ 4 - 691610880 * h ^ 3 - 2567450318 * h ^ 2 +
    816470712 * h + 6535942600 = H2 at h2 ⊢
  generalize -36864000 * h ^ 6 + 135628800 * h ^ 5 + 1618338560 * h ^ 4 - 5043517440 * h ^ 3 -
    37422983124 * h ^ 2 - 43214024624 * h + 7365531312 = H1 at h1 ⊢
  generalize -442368000 * h ^ 7 - 5902848000 * h ^ 6 - 28361948160 * h ^ 5 - 60905292416 * h ^ 4 -
    71564445952 * h ^ 3 - 86648243805 * h ^ 2 - 76691490124 * h + 16148237836 = H0 at h0 ⊢
  have hq : 0 < H2 * r ^ 2 + H1 * r + H0 := by
    rcases le_or_gt 0 H1 with hH1 | hH1
    · positivity
    · have : 4 * H2 * (H2 * r ^ 2 + H1 * r + H0) = (2 * H2 * r + H1) ^ 2 + (4 * H0 * H2 - H1 ^ 2) := by
        ring
      have : H1 ^ 2 ≤ 900000000 ^ 2 := by nlinarith
      nlinarith [sq_nonneg (2 * H2 * r + H1), mul_le_mul h0 h2 (by norm_num) (by linarith)]
  have : 0 ≤ H4 * r ^ 4 + H3 * r ^ 3 := by positivity
  linarith

/-- **The norm bound** `w ≥ w_b = 901/1000 - 6q/5`, through `Q_w(h, r) > 0`. -/
theorem dspc_w_bd (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    901 / 1000 - 6 * ssQc x a / 5 ≤ dspcW x (dspclam x a) (dspcd x a) (dspcu x a) := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hd0, hd1, hl1, hl2⟩ := dspc_d_bds hx hx2 ham h6
  obtain ⟨hu0, hu1, hub⟩ := dspc_u_bds hx hx2 ham h6
  have hK : 0 < dspcK x a := dspc_K_pos (by linarith)
  have hK' : dspcK x a = x * (x + 2) + a ^ 2 := rfl
  -- raise the norm to `19/25`: `w_u = d(d - λS) < 0`
  have hhigh : dspcW x (dspclam x a) (dspcd x a) (19 / 25) ≤
      dspcW x (dspclam x a) (dspcd x a) (dspcu x a) := by
    have e : dspcW x (dspclam x a) (dspcd x a) (dspcu x a) -
        dspcW x (dspclam x a) (dspcd x a) (19 / 25) =
        (19 / 25 - dspcu x a) * (dspcd x a * (dspclam x a * (1 + x) - dspcd x a)) := by
      unfold dspcW dspcE; ring
    have : 0 ≤ (19 / 25 - dspcu x a) * (dspcd x a * (dspclam x a * (1 + x) - dspcd x a)) :=
      mul_nonneg (by linarith) (mul_nonneg hd0.le (by linarith))
    linarith
  have e : (dspcW x (dspclam x a) (dspcd x a) (19 / 25) - (901 / 1000 - 6 * ssQc x a / 5)) *
      (1000 * (5 * x + 12) ^ 2 * dspcK x a ^ 2 * 36864) = dspcQw (x - 2) (8 * a - 9) := by
    unfold dspcW dspcE dspcv dspclam dspcd ssDg dspb ssQc dspcQw
    rw [← hK']
    have : 15 * x + 36 ≠ 0 := by linarith
    have : dspcK x a ≠ 0 := hK.ne'
    have : 1 + x ≠ 0 := by linarith
    field_simp
    rw [hK']
    ring
  have hQ := dspc_Qw_pos (h := x - 2) (r := 8 * a - 9) (by linarith) (by linarith) (by linarith)
  rw [← e] at hQ
  have := pos_of_mul_pos_left hQ (by positivity)
  linarith

/-! ### The first term and the `Bu_b` term -/

/-- `(x - B)(1 - p + p² - u)/a² < 1/48`. -/
theorem dspc_T1 (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    (x - dspcB x) / a ^ 2 * (1 - dspcp x a + dspcp x a ^ 2 - dspcu x a) < 1 / 48 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hp1, hp2, hp3⟩ := dspc_p_bds hx hx2 ham h6
  obtain ⟨hu0, hu1, hub⟩ := dspc_u_bds hx hx2 ham h6
  have ha0 : 0 < a := by linarith
  set c := 187 / 9000 - (x - 2) / 150 with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hm : 1 - dspcp x a + dspcp x a ^ 2 - dspcu x a ≤ c := by
    have : (dspcp x a - 1 / 3) * (dspcp x a - 2 / 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    rw [hc]; nlinarith
  have hxB : x - dspcB x = x * (15 * x + 11) / (15 * x + 36) := dspc_xB (by linarith)
  have hxB0 : 0 ≤ (x - dspcB x) / a ^ 2 := by rw [hxB]; positivity
  have hbd : (x - dspcB x) / a ^ 2 ≤ 484 * x * (15 * x + 11) / ((15 * x + 36) * (x + 23) ^ 2) := by
    rw [hxB, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((x + 23) / 22) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) h23 2
    have h2 : 0 ≤ x * (15 * x + 11) * (15 * x + 36) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have h12 : 484 * x * (15 * x + 11) / ((15 * x + 36) * (x + 23) ^ 2) * c < 1 / 48 := by
    have e : 1 / 48 - 484 * x * (15 * x + 11) / ((15 * x + 36) * (x + 23) ^ 2) * c =
        (876825 * (x - 2) ^ 3 + 1714440 * (x - 2) ^ 2 - 3336451 * (x - 2) + 625438) /
          (54000 * (x + 23) ^ 2 * (5 * x + 12)) := by
      rw [hc]
      have : 15 * x + 36 ≠ 0 := by linarith
      have : x + 23 ≠ 0 := by linarith
      have : 5 * x + 12 ≠ 0 := by linarith
      field_simp
      ring
    have : 0 < (876825 * (x - 2) ^ 3 + 1714440 * (x - 2) ^ 2 - 3336451 * (x - 2) + 625438) /
          (54000 * (x + 23) ^ 2 * (5 * x + 12)) := by
      apply div_pos _ (by positivity)
      have : 0 ≤ x - 2 := by linarith
      have : 0 ≤ 876825 * (x - 2) ^ 3 + 1714440 * (x - 2) ^ 2 := by positivity
      linarith
    linarith
  calc (x - dspcB x) / a ^ 2 * (1 - dspcp x a + dspcp x a ^ 2 - dspcu x a)
      ≤ (x - dspcB x) / a ^ 2 * c := mul_le_mul_of_nonneg_left hm hxB0
    _ ≤ 484 * x * (15 * x + 11) / ((15 * x + 36) * (x + 23) ^ 2) * c :=
      mul_le_mul_of_nonneg_right hbd hc0
    _ < 1 / 48 := h12

/-- The `Bu_b` term is below `-1/100`: its coefficient
`1/p + λS - 2d + nd(d - λS)` is at least `9/4` for `0 ≤ n ≤ 53/15`. -/
theorem dspc_T3 (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) {n : ℝ} (hn' : n ≤ 53 / 15) :
    dspcB x * dspcub x a * (1 / dspcp x a + dspclam x a * (1 + x) - 2 * dspcd x a +
      n * dspcd x a * (dspcd x a - dspclam x a * (1 + x))) ≤ -(1 / 100) := by
  obtain ⟨hp1, hp2, hp3⟩ := dspc_p_bds hx hx2 ham h6
  obtain ⟨hu0, hu1, hub⟩ := dspc_u_bds hx hx2 ham h6
  obtain ⟨hd0, hd1, hl1, hl2⟩ := dspc_d_bds hx hx2 ham h6
  obtain ⟨hB1, hB2⟩ := dspc_B_bds hx hx2
  set d := dspcd x a
  set l := dspclam x a * (1 + x)
  have hcoef : 9 / 4 ≤ 1 / dspcp x a + l - 2 * d + n * d * (d - l) := by
    have h1 : 53 / 15 * d * (d - l) ≤ n * d * (d - l) := by
      have : 0 ≤ (53 / 15 - n) * (d * (l - d)) := mul_nonneg (by linarith) (mul_nonneg hd0.le (by linarith))
      nlinarith
    rcases le_or_gt (53 / 15 * d) 1 with hmd | hmd
    · have : (1 - 53 / 15 * d) * (20 / 7) ≤ (1 - 53 / 15 * d) * l :=
        mul_le_mul_of_nonneg_left hl1 (by linarith)
      nlinarith
    · have : (1 - 53 / 15 * d) * l ≥ (1 - 53 / 15 * d) * (19 / 6) :=
        mul_le_mul_of_nonpos_left hl2 (by linarith)
      nlinarith
  have hBu : dspcB x * dspcub x a ≤ -(9 / 2000) := by nlinarith
  nlinarith

/-! ### The final comparison -/

/-- **The quadratic comparison**, in abstract variables: from the bounds above, the shape
derivative is below a convex quadratic in `q` that is negative on `[63/500, 1/7]`. -/
theorem dspc_core {a q A u EL w n N L T1 T3 : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 5 / 4)
    (hL : L * a = 2 * q) (hq : 63 / 500 ≤ q) (hq' : q ≤ 1 / 7) (hA : 25 / 11 ≤ A) (hu : 3 / 4 ≤ u)
    (hEL : EL ≤ 5 * q - 83 / 200) (hw : 901 / 1000 - 6 * q / 5 ≤ w) (hn : 19 / 6 ≤ n)
    (hn' : n ≤ 53 / 15) (hN : N ≤ 0) (hN' : -N ≤ 21 / 5) (hT1 : T1 < 1 / 48)
    (hT3 : T3 ≤ -(1 / 100)) :
    T1 + 2 * (1 - q) ^ 2 / a + L * A * (n * EL - 2 * u) + L * (EL - 2 * n * w) + T3 +
      N * (w - 3 / 4) < 0 := by
  have ha0 : 0 < a := by linarith
  set X := (1 - q) ^ 2 + q * (A * (n * EL - 2 * u) + EL - 2 * n * w) with hX
  have e : 2 * (1 - q) ^ 2 / a + L * A * (n * EL - 2 * u) + L * (EL - 2 * n * w) = 2 * X / a := by
    have hL' : L = 2 * q / a := by field_simp; linarith
    rw [hL', hX]; field_simp; ring
  -- the bracket is at most `𝓡(q)`
  have hnEL : n * EL - 2 * u < 0 := by
    have : n * EL ≤ n * (3 / 10) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  set Xq := 25 / 11 * (5 * q - 83 / 200) - 2 * (901 / 1000 - 6 * q / 5) with hXq
  have hXq0 : Xq < 0 := by rw [hXq]; linarith
  have h1 : q * (A * (n * EL - 2 * u)) ≤ q * (25 / 11 * (n * EL - 2 * u)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h2 : n * (25 / 11 * EL - 2 * w) ≤ n * Xq := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [hXq]; linarith
  have h3 : n * Xq ≤ 19 / 6 * Xq := by nlinarith
  have hXR : X ≤ 16363 / 330 * q ^ 2 - 87103 / 6000 * q + 1 := by
    have h4 : q * (n * (25 / 11 * EL - 2 * w)) ≤ q * (19 / 6 * Xq) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h5 : q * (-(50 / 11) * u + EL) ≤ q * (-(75 / 22) + (5 * q - 83 / 200)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hX]
    rw [hXq] at h4
    nlinarith
  have hqq := mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hq')
  have hR : 16363 / 330 * q ^ 2 - 87103 / 6000 * q + 1 < 0 := by linarith
  have hXa : 2 * X / a ≤ 8 / 5 * (16363 / 330 * q ^ 2 - 87103 / 6000 * q + 1) := by
    rw [div_le_iff₀ ha0]
    have := mul_nonneg_of_nonpos_of_nonpos hR.le (by linarith : a - 5 / 4 ≤ 0)
    linarith
  have hNw : N * (w - 3 / 4) ≤ 21 / 5 * (3 / 4 - (901 / 1000 - 6 * q / 5)) := by
    have h6 : N * (w - 3 / 4) ≤ N * (901 / 1000 - 6 * q / 5 - 3 / 4) :=
      mul_le_mul_of_nonpos_left (by linarith) hN
    have h7 : -N * (3 / 4 - (901 / 1000 - 6 * q / 5)) ≤ 21 / 5 * (3 / 4 - (901 / 1000 - 6 * q / 5)) :=
      mul_le_mul_of_nonneg_right hN' (by linarith)
    linarith
  have hfin : 1 / 48 - 1 / 100 + 8 / 5 * (16363 / 330 * q ^ 2 - 87103 / 6000 * q + 1) +
      21 / 5 * (3 / 4 - (901 / 1000 - 6 * q / 5)) < 0 := by linarith
  linarith

/-- **Both shape derivatives are negative** on the comparison path. -/
theorem dspc_H_neg (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ham : dspamin x ≤ a)
    (h6 : 6 * a ^ 2 ≤ x * (x + 2)) :
    dspcH x a (dspcn0 x a) (dspcN0 x a) < 0 ∧ dspcH x a (dspcn1 x a) (dspcN1 x a) < 0 := by
  obtain ⟨h23, h108, hap, h54⟩ := dspc_dom hx hx2 ham h6
  obtain ⟨hq1, hq2⟩ := dspc_q_bds hx hx2 ham h6
  obtain ⟨hu0, hu1, hub⟩ := dspc_u_bds hx hx2 ham h6
  obtain ⟨hN0, hN0', hN1, hN1'⟩ := dspc_N_bds hx hx2 ham h6
  obtain ⟨hn0, hn1⟩ := dspc_n_hi hx hx2 ham h6
  have hn0' := dspc_n0_lo hx hx2 ham h6
  have hn1' := dspc_n1_lo hx hx2 ham h6
  have hA := dspc_A_lo hx hx2 ham h6
  have hEL := dspc_EL_bd hx hx2 ham h6
  have hw := dspc_w_bd hx hx2 ham h6
  have hT1 := dspc_T1 hx hx2 ham h6
  have hL : dspcL x a * a = 2 * ssQc x a := by
    unfold dspcL ssQc dspcK
    have : 0 < x * (x + 2) + a ^ 2 := by positivity
    field_simp
  have hu : 3 / 4 ≤ dspcu x a := by linarith
  constructor
  · exact dspc_core (by linarith) h54.le hL hq1 hq2 hA hu hEL hw hn0' hn0 hN0.le hN0' hT1
      (dspc_T3 hx hx2 ham h6 hn0)
  · exact dspc_core (by linarith) h54.le hL hq1 hq2 hA hu hEL hw hn1' hn1 hN1.le hN1' hT1
      (dspc_T3 hx hx2 ham h6 hn1)

end Bounds

/-! ### The central face sign -/

/-- A function with nonpositive derivative on `[a, b]` does not increase. -/
theorem dsp_le_of_deriv_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z) (hn : ∀ z ∈ Ioo a b, f' z ≤ 0) : f b ≤ f a := by
  have := ss_le_of_deriv (f := fun t => -f t) (f' := fun t => -f' t) hab
    (fun z hz => (hd z hz).neg) (fun z hz => by linarith [hn z hz])
  linarith

/-- **`dsp_central_alpha_proof`**: on the comparison path `a_min(x) ≤ α`, `6α² ≤ x(x + 2)`,
both central tests are negative at `β = b(x, α)`, `q = q_c`, `u = ū(x, b)`. Both decrease from
`a_min(x)` (`dspc_H_neg`), where `b = 20x/19` and `dsp_central_endpoint` applies. -/
theorem dsp_central_alpha_proof {x al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : dspamin x ≤ al)
    (h6 : 6 * al ^ 2 ≤ x * (x + 2)) :
    dspF0 x (dspb x al) al (ssUCB x (dspb x al)) (ssQc x al) < 0 ∧
      dspF1 x (dspb x al) al (ssUCB x (dspb x al)) (ssQc x al) < 0 := by
  have ham1 : 1 < dspamin x := by unfold dspamin; linarith
  have hdom : ∀ s ∈ Icc (dspamin x) al, dspamin x ≤ s ∧ 6 * s ^ 2 ≤ x * (x + 2) := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    have : s ^ 2 ≤ al ^ 2 := pow_le_pow_left₀ (by linarith [hs.1]) hs.2 2
    linarith
  have hb : dspb x (dspamin x) = 20 * x / 19 := by
    unfold dspb dspamin
    have : 15 * x + 36 ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨hE0, hE1⟩ := dsp_central_endpoint hx hx2
  rw [← hb] at hE0 hE1
  constructor
  · have := dsp_le_of_deriv_nonpos (f := fun s => dspF0 x (dspb x s) s (ssUCB x (dspb x s)) (ssQc x s))
      (f' := fun s => dspcH x s (dspcn0 x s) (dspcN0 x s)) hal
      (fun s hs => dspc_hasDerivAt_F0 (by linarith) (by linarith [hs.1]))
      (fun s hs => (dspc_H_neg hx hx2 (hdom s (Ioo_subset_Icc_self hs)).1
        (hdom s (Ioo_subset_Icc_self hs)).2).1.le)
    exact this.trans_lt hE0
  · have := dsp_le_of_deriv_nonpos (f := fun s => dspF1 x (dspb x s) s (ssUCB x (dspb x s)) (ssQc x s))
      (f' := fun s => dspcH x s (dspcn1 x s) (dspcN1 x s)) hal
      (fun s hs => dspc_hasDerivAt_F1 (by linarith) (by linarith [hs.1]))
      (fun s hs => (dspc_H_neg hx hx2 (hdom s (Ioo_subset_Icc_self hs)).1
        (hdom s (Ioo_subset_Icc_self hs)).2).2.le)
    exact this.trans_lt hE1

end SmoothedOctagon

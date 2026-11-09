module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.NormBeta

/-!
# Smaller-short window, lower ratio, central face: the beta reduction

`(r₀)_β ≥ 1/40 + 1/1000` (`lrc_R2b_ge`) and, at `u = 19/25`,
`(r₁)_β ≥ 1/40 + 1/1000` (`lrc_R1b_ge`). With `ε(y) ≤ 1/625` for the cubic majorant,
`(F₀)_u ∈ [-1/5, 0]` and `0 ≤ -(u_ℓ)_β ≤ 15/1992`, the first test decreases in `β` along the
ceiling `u_ℓ(x, β)` and the second decreases in `β` at `u = 19/25` (`lrc_F0_bstep`,
`lrc_F1_bstep`).

## Main API

* `lr_phi27`, `lrc_R2b_ge`, `lrc_R1b_ge`, `lrc_F1_bstep`, `lrc_F0_bstep`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `t ↦ t/(α + t)² + t/(27α²)` increases (`B³ - 27α²(β - α) = (β - 2α)²(β + 7α)`). -/
theorem lr_phi27 {a t1 t2 : ℝ} (ha : 0 < a) (ht1 : 0 ≤ t1) (h : t1 ≤ t2) :
    t1 / (a + t1) ^ 2 - t2 / (a + t2) ^ 2 ≤ (t2 - t1) / (27 * a ^ 2) := by
  have key := ss_le_of_deriv (f := fun t => t / (a + t) ^ 2 + t / (27 * a ^ 2))
    (f' := fun t => (a - t) / (a + t) ^ 3 + 1 / (27 * a ^ 2)) h
    (fun t ht => by
      have hp : 0 < a + t := by linarith [ht.1]
      have h1 := (hasDerivAt_id' t).fun_div (((hasDerivAt_id' t).const_add a).fun_pow 2)
        (pow_ne_zero 2 hp.ne')
      have h2 := (hasDerivAt_id' t).div_const (27 * a ^ 2)
      convert h1.add h2 using 1
      push_cast
      field_simp
      ring)
    (fun t ht => by
      have hp : 0 < a + t := by linarith [ht.1]
      have e : (a - t) / (a + t) ^ 3 + 1 / (27 * a ^ 2) =
          (t - 2 * a) ^ 2 * (t + 7 * a) / (27 * a ^ 2 * (a + t) ^ 3) := by field_simp; ring
      rw [e]
      have : 0 ≤ t + 7 * a := by linarith [ht.1]
      positivity)
  have e : (t2 - t1) / (27 * a ^ 2) = t2 / (27 * a ^ 2) - t1 / (27 * a ^ 2) := by ring
  linarith

/-- `(r₀)_β ≥ 1/40 + 1/1000` on the strip for `u ≥ 3/4`. -/
theorem lrc_R2b_ge {x a b u : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 7 / 6)
    (hb0 : x ≤ b) (hb1 : b ≤ x + 10 / 13 * (a - 1)) (hu : 3 / 4 ≤ u) :
    1 / 40 + 1 / 1000 ≤ lrcR2b x a b u := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hKp : 0 < lrcK x a := by unfold lrcK; positivity
  have hK : lrcK x a ≠ 0 := hKp.ne'
  obtain ⟨hD0, hD1, -, h18⟩ := lrc_dom hx hx2 ha1 ha2 hb0 hb1
  have hbd : lrcR2b x a b u - lrcR2b x a x u =
      4 * u * (2 * (a - x) / lrcK x a) ^ 2 * (b - x) + (b / (a + b) ^ 2 - x / (a + x) ^ 2) := by
    have hab : a + b ≠ 0 := by linarith
    have hax : a + x ≠ 0 := by linarith
    simp only [lrcR2b, lrcwb, lrcdb, lrcd, ssDg]
    generalize lrcL x a = L
    generalize lrcE x u = E
    field_simp
    try ring
  have hud : lrcR2b x a x u - lrcR2b x a x (3 / 4) = (u - 3 / 4) * (2 * (2 * (a - x) /
      lrcK x a) * (2 * lrcd x a x - lrcL x a * (1 + x) - 1) + 1 / a) := by
    simp only [lrcR2b, lrcwb, lrcdb, lrcE]
    ring
  have hbase : 1 / 40 + 1 / 1000 ≤ lrcR2b x a x (3 / 4) := by
    have hP := lrcPb0s_pos (t := x - 41 / 25) (s := a - 1) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [← lrcPb0x_eq] at hP
    have := lrcPb0_id hx ha1
    have : 0 ≤ lrcPb0x x a / (a * (x + a) ^ 2 * (x * (x + 2) + a ^ 2) ^ 2) :=
      div_nonneg hP (by positivity)
    unfold lrcK at *
    linarith
  -- the norm part
  have hn : 0 ≤ (u - 3 / 4) * (2 * (2 * (a - x) / lrcK x a) * (2 * lrcd x a x - lrcL x a *
      (1 + x) - 1) + 1 / a) := by
    apply mul_nonneg (by linarith)
    have h1 : 2 * (a - x) / lrcK x a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hKp.le
    have h2 : 2 * lrcd x a x - lrcL x a * (1 + x) - 1 ≤ 0 := by
      obtain ⟨hDx0, hDx1, -, -⟩ := lrc_dom (b := x) hx hx2 ha1 ha2 le_rfl (by nlinarith)
      unfold lrcd lrcL
      have e : 2 * (ssDg x x a / lrcK x a) - (1 + x) ^ 2 / lrcK x a * (1 + x) - 1 =
          (2 * ssDg x x a - (1 + x) ^ 3 - lrcK x a) / lrcK x a := by field_simp; try ring
      rw [e]
      apply div_nonpos_of_nonpos_of_nonneg _ hKp.le
      unfold ssDg lrcK; nlinarith
    have : 0 < 1 / a := by positivity
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h1 h2]
  -- the beta part
  have hph := lr_phi27 ha0 hx0.le hb0
  have hb : (b - x) / (27 * a ^ 2) ≤ 4 * u * (2 * (a - x) / lrcK x a) ^ 2 * (b - x) := by
    have e : 4 * u * (2 * (a - x) / lrcK x a) ^ 2 * (b - x) =
        (16 * u * (x - a) ^ 2 / lrcK x a ^ 2) * (b - x) := by field_simp; ring
    rw [e, div_eq_mul_inv, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hxa : 0 ≤ x - a := by linarith
    have h3 : lrcK x a ^ 2 ≤ (18 * a * (x - a)) ^ 2 := pow_le_pow_left₀ hKp.le h18 2
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 27 * a ^ 2),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ u - 3 / 4) (sq_nonneg (x - a)))
        (sq_nonneg a)]
  linarith

/-- `(r₁)_β ≥ 1/40 + 1/1000` at `u = 19/25`. -/
theorem lrc_R1b_ge {x a b : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 7 / 6)
    (hb0 : x ≤ b) (hb1 : b ≤ x + 10 / 13 * (a - 1)) :
    1 / 40 + 1 / 1000 ≤ lrcR1b x a b (19 / 25) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hKp : 0 < lrcK x a := by unfold lrcK; positivity
  rw [lrc_R1b_eq hx0 ha0 (by linarith)]
  have hQ : 3 / 2 * a ≤ lrcQ0 x a (19 / 25) := by
    have hP := lrcPQs_pos (t := x - 41 / 25) (s := a - 1) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [← lrcPQx_eq] at hP
    have := lrcPQ_id hx ha1
    have : 0 ≤ lrcPQx x a / (a * (x * (x + 2) + a ^ 2)) := div_nonneg hP (by positivity)
    linarith
  have hbase : 1 / 40 + 1 / 1000 ≤ lrcR1bf x a x (19 / 25) := by
    have hP := lrcPb1s_pos (t := x - 41 / 25) (s := a - 1) (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [← lrcPb1x_eq] at hP
    have := lrcPb1_id hx ha1
    have : 0 ≤ lrcPb1x x a / (a * (x + a) ^ 2 * (x * (x + 2) + a ^ 2)) :=
      div_nonneg hP (by positivity)
    linarith
  have hd : lrcR1bf x a x (19 / 25) ≤ lrcR1bf x a b (19 / 25) := by
    unfold lrcR1bf
    set Q := lrcQ0 x a (19 / 25)
    have hB1 : 0 < a + x := by linarith
    have hBB : a + x ≤ a + b := by linarith
    have hB3 : a + b ≤ 3 * a := by nlinarith
    have hab : a + b ≠ 0 := by linarith
    have hax : a + x ≠ 0 := by linarith
    have e : (1 / (a + b) - Q / (a + b) ^ 2) - (1 / (a + x) - Q / (a + x) ^ 2) =
        ((a + b) - (a + x)) * (Q * ((a + b) + (a + x)) - (a + b) * (a + x)) /
          ((a + b) ^ 2 * (a + x) ^ 2) := by
      field_simp; ring
    have : 0 ≤ ((a + b) - (a + x)) * (Q * ((a + b) + (a + x)) - (a + b) * (a + x)) /
        ((a + b) ^ 2 * (a + x) ^ 2) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith)
      nlinarith
    linarith
  linarith

/-- **The second test decreases in `β` at `u = 19/25`.** -/
theorem lrc_F1_bstep {x a b1 b2 : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 7 / 6) (hb1 : x + (a - 1) / 2 ≤ b1) (hb12 : b1 ≤ b2) (hb2 : b2 ≤ x + 10 / 13 * (a - 1)) :
    lrcF1 x a b2 (19 / 25) ≤ lrcF1 x a b1 (19 / 25) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have key := ss_le_of_deriv (f := fun t => -lrcF1 x a t (19 / 25))
    (f' := fun t => -(0 * (lrcGx x (19 / 25) - 7 / 96 * lrcR1x x a t (19 / 25)) +
      1 * (-(7 / 96) * lrcR1b x a t (19 / 25)) +
      0 * (lrcGu x (19 / 25) - 7 / 96 * (lrcR2u x a t + (lrcT x a t - 2) * lrcwu x a t)) +
      7 / 96 * lreps (lrcy x a t) * (-(2 * (1 + x) / lrcK x a) * 0 + 1 / (a + t) * 1)))
    (x := b1) (y := b2) hb12
    (fun t ht => (lrc_F1_hasDerivAt (a := a) (hasDerivAt_const t x) (hasDerivAt_id' t)
      (hasDerivAt_const t (19 / 25)) hx0 ha0 (by linarith [ht.1])).neg)
    (fun t ht => by
      have ht0 : x + (a - 1) / 2 ≤ t := by linarith [ht.1]
      have ht1 : t ≤ x + 10 / 13 * (a - 1) := by linarith [ht.2]
      have hR := lrc_R1b_ge hx hx2 ha1 ha2 (by linarith) ht1
      obtain ⟨hy0, hy1⟩ := lrc_y_bounds (b := t) (by linarith) hx2 ha1 ha2 (by linarith) (by linarith)
      have he := lr_eps_le hy0 hy1
      have he0 := lr_eps_nonneg (lrcy x a t)
      have hi : 1 / (a + t) ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      have hi0 : 0 ≤ 1 / (a + t) := div_nonneg zero_le_one (by linarith)
      have : lreps (lrcy x a t) * (1 / (a + t)) ≤ 1 / 625 * (1 / 2) :=
        mul_le_mul he hi hi0 (by norm_num)
      simp only [zero_mul, one_mul, mul_zero, zero_add, add_zero, mul_one]
      nlinarith)
  linarith

/-- **The first test decreases in `β` along the ceiling `u_ℓ(x, β)`**. -/
theorem lrc_F0_bstep {x a b1 b2 : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 7 / 6) (haU : a ≤ (1013 * x + 676) / 2340) (hb1 : x + (a - 1) / 2 ≤ b1)
    (hb12 : b1 ≤ b2) (hb2 : b2 ≤ x + 10 / 13 * (a - 1)) :
    lrcF0 x a b2 (ssUl x b2) ≤ lrcF0 x a b1 (ssUl x b1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  have key := ss_le_of_deriv (f := fun t => -lrcF0 x a t (ssUl x t))
    (f' := fun t => -(0 * (lrcGx x (ssUl x t) - 7 / 96 * lrcR2x x a t (ssUl x t)) +
      0 * (-(7 / 96) * lrcR2a x a t (ssUl x t)) + 1 * (-(7 / 96) * lrcR2b x a t (ssUl x t)) +
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) *
        (lrcGu x (ssUl x t) - 7 / 96 * lrcR2u x a t) +
      7 / 96 * lreps (lrcy x a t) * (-(2 * (1 + x) / lrcK x a) * 0 +
        (1 / a + 1 / (a + t) - 2 * a / lrcK x a) * 0 + 1 / (a + t) * 1)))
    (x := b1) (y := b2) hb12
    (fun t ht => (lrc_F0_hasDerivAt (hasDerivAt_const t x) (hasDerivAt_const t a)
      (hasDerivAt_id' t) (lr_Ul_hasDerivAt hx1 (by linarith [ht.1])) hx0 ha0
      (by linarith [ht.1])).neg)
    (fun t ht => by
      have ht0 : x + (a - 1) / 2 ≤ t := by linarith [ht.1]
      have ht1 : t ≤ x + 10 / 13 * (a - 1) := by linarith [ht.2]
      have htx : x ≤ t := by linarith
      obtain ⟨hU0, hU1⟩ := lr_Ul_bounds hx1 hx2 htx
      obtain ⟨hd0, hd1⟩ := lr_Ul_deriv_bounds hx1 hx2 htx
      have hR := lrc_R2b_ge hx hx2 ha1 ha2 htx ht1 hU0
      have hu1 := lrc_F0u_ge (u := ssUl x t) hx hx2 ha1 haU ht0 ht1 (by linarith)
      have hu2 := (lrc_Fu_nonpos (u := ssUl x t) hx hx2 ha1 ha2 ht0 ht1 hU0).1
      obtain ⟨hy0, hy1⟩ := lrc_y_bounds (b := t) (by linarith) hx2 ha1 ha2 (by linarith) (by linarith)
      have he := lr_eps_le hy0 hy1
      have he0 := lr_eps_nonneg (lrcy x a t)
      have hi : 1 / (a + t) ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      have hi0 : 0 ≤ 1 / (a + t) := div_nonneg zero_le_one (by linarith)
      have hε : lreps (lrcy x a t) * (1 / (a + t)) ≤ 1 / 625 * (1 / 2) :=
        mul_le_mul he hi hi0 (by norm_num)
      have hprod : -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) *
          (lrcGu x (ssUl x t) - 7 / 96 * lrcR2u x a t) ≤ 15 / 1992 * (1 / 5) := by
        generalize -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) = U' at hd0 hd1 ⊢
        generalize lrcGu x (ssUl x t) - 7 / 96 * lrcR2u x a t = G at hu1 hu2 ⊢
        have := mul_le_mul (show -U' ≤ 15 / 1992 by linarith) (show -G ≤ 1 / 5 by linarith)
          (by linarith) (by norm_num)
        nlinarith
      simp only [zero_mul, one_mul, mul_zero, zero_add, add_zero, mul_one]
      nlinarith)
  linarith

end SmoothedOctagon

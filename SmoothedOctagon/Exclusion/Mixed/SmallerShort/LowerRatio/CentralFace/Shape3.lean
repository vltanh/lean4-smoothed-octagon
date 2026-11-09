module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Shape2

/-!
# Smaller-short window, lower ratio, central face: the shape step

* First test: along `β₊ = x + (10/13)(α - 1)` at a fixed norm, `(r₀)_α + (10/13)(r₀)_β ≥ 1/40 + 2/625`
  below the tangent chord `α_U` of the cap (affine in `u`; two-variable signs at `u = 3/4, 19/25`),
  so `F₀` decreases with slope `≤ -c/40`; along the ceiling `u_ℓ(x, β₊)` the norm motion costs at
  most `(1/5)(15/1992)(10/13)` per unit: `lrc_F0_astep`.
* Second test at `u = 19/25`: `F₁(x, α, β₊, 19/25) = Γ - c φ(α) - g` with
  `φ = N/V + ℓ(Y/K)`, `V = αBK`, `Y = 2αB`; `φ″ ≥ (N/V)″ + (log y)″ - (1/625)y″/y`
  (`ℓ″ ≥ -1/y²`, `yℓ′(y) = 1 - ε ≥ 624/625`, `y″ ≥ 0`) and `V³((N/V)″ + (log y)″)` is the curvature
  circuit, at least `V³/700` below the cap (`SmallerShort/LowerRatio/CentralFace/Shape2`); so `φ` is convex and
  `F₁(α) ≥ min(F₁(1), F₁(α_c))`: `lrc_F1_conc`.

The convexity uses only the positivity of the circuit below the cap, and the slope of the first
test is bounded below the tangent chord `α_U` directly.

## Main API

* `lrPhi1`, `lrPhi2`, `lr_qphi_hasDerivAt`, `lrcN`, `lrcV`, `lrcY`, `lrc_F1_phi`,
  `lrc_F0_astep`, `lrc_F1_conc`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real


/-! ### Derivatives of the circuit pieces -/

theorem lr_quart_hasDerivAt (c0 c1 c2 c3 c4 t : ℝ) :
    HasDerivAt (fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 + c4 * s ^ 4)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3) t := by
  have hid := hasDerivAt_id' t
  have h := ((((hid.const_mul c1).const_add c0).add ((hid.fun_pow 2).const_mul c2)).add
    ((hid.fun_pow 3).const_mul c3)).add ((hid.fun_pow 4).const_mul c4)
  convert h using 1
  push_cast; ring

theorem lrcN_d (x t : ℝ) : HasDerivAt (lrcN x) (lrcN1 x t) t := by
  have h := lr_quart_hasDerivAt (-12 / 25 * x ^ 5 + 3197 / 1300 * x ^ 4 - 88 / 25 * x ^ 3 +
    17933 / 4225 * x ^ 2 - 1746 / 4225 * x) (-42 / 325 * x ^ 4 + 79 / 65 * x ^ 3 + 51 / 169 * x ^ 2 -
    808 / 325 * x + 12 / 65) (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x - 276 / 845)
    (-3522 / 845 * x + 308 / 169) (-1643 / 676) t
  exact h

theorem lrcN1_d (x t : ℝ) : HasDerivAt (lrcN1 x) (lrcN2 x t) t := by
  have h := lr_quart_hasDerivAt (-42 / 325 * x ^ 4 + 79 / 65 * x ^ 3 + 51 / 169 * x ^ 2 -
    808 / 325 * x + 12 / 65) (2 * (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x -
    276 / 845)) (3 * (-3522 / 845 * x + 308 / 169)) (4 * (-1643 / 676)) 0 t
  convert h using 1
  · funext s; unfold lrcN1; ring
  · unfold lrcN2; ring

theorem lrcB_d (x t : ℝ) : HasDerivAt (lrcB x) (23 / 13) t := by
  have h := (hasDerivAt_id' t).add ((((hasDerivAt_id' t).sub_const 1).const_mul (10 / 13)).const_add x)
  have hf : lrcB x = fun s => s + (x + 10 / 13 * (s - 1)) := rfl
  rw [hf]
  convert h using 1
  ring

theorem lrcK_d (x t : ℝ) : HasDerivAt (lrcK x) (2 * t) t := by
  have h := ((hasDerivAt_id' t).fun_pow 2).const_add (x * (x + 2))
  have hf : lrcK x = fun s => x * (x + 2) + s ^ 2 := rfl
  rw [hf]
  convert h using 1
  push_cast; ring

theorem lrcV_d (x t : ℝ) : HasDerivAt (lrcV x) (lrcV1 x t) t := by
  have h := ((hasDerivAt_id' t).fun_mul (lrcB_d x t)).fun_mul (lrcK_d x t)
  have hf : lrcV x = fun s => s * lrcB x s * lrcK x s := rfl
  rw [hf]
  convert h using 1
  unfold lrcV1; ring

theorem lrcV1_d (x t : ℝ) : HasDerivAt (lrcV1 x) (lrcV2 x t) t := by
  have hB := lrcB_d x t
  have hK := lrcK_d x t
  have hid := hasDerivAt_id' t
  have h := ((hB.fun_mul hK).add ((hid.const_mul (23 / 13)).fun_mul hK)).add ((hid.fun_mul hB).fun_mul
    (hid.const_mul 2))
  have hf : lrcV1 x = fun s => lrcB x s * lrcK x s + s * (23 / 13) * lrcK x s +
      s * lrcB x s * (2 * s) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply]; ring
  · unfold lrcV2; ring

theorem lrcY_d (x t : ℝ) : HasDerivAt (lrcY x) (lrcY1 x t) t := by
  have h := ((hasDerivAt_id' t).const_mul 2).fun_mul (lrcB_d x t)
  have hf : lrcY x = fun s => 2 * s * lrcB x s := rfl
  rw [hf]
  convert h using 1
  unfold lrcY1; ring

theorem lrcY1_d (x t : ℝ) : HasDerivAt (lrcY1 x) (lrcY2 x t) t := by
  have h := ((lrcB_d x t).const_mul 2).add ((hasDerivAt_id' t).const_mul (2 * (23 / 13)))
  have hf : lrcY1 x = fun s => 2 * lrcB x s + 2 * s * (23 / 13) := by
    funext s; unfold lrcY1; ring
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply]; ring
  · unfold lrcY2; ring

theorem lrcK1_d (t : ℝ) : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
  simpa using (hasDerivAt_id' t).const_mul 2

/-! ### The second test as `Γ - cφ - g` -/

theorem lrc_F1_phi {x t : ℝ} (hx : 0 < x) (ht : 1 ≤ t) :
    lrcF1 x t (x + 10 / 13 * (t - 1)) (19 / 25) = lrcG x (19 / 25) -
      7 / 96 * (lrcN x t / lrcV x t + lrell (lrcY x t / lrcK x t)) - 9193 / 50000 := by
  have ht0 : 0 < t := by linarith
  have hy : lrcy x t (x + 10 / 13 * (t - 1)) = lrcY x t / lrcK x t := by
    unfold lrcy lrcY lrcB; ring
  have hB : t + (x + 10 / 13 * (t - 1)) ≠ 0 := by nlinarith
  have hS : 1 + x ≠ 0 := by linarith
  have hKn : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  simp only [lrcF1, lrcF0, lrcR2]
  rw [hy]
  generalize lrell (lrcY x t / lrcK x t) = L
  simp only [lrcw, lrcEL, lrcq, lrcT, lrcL, lrcd, lrcv, lrcE, ssDg, lrcN, lrcV, lrcB,
    lrcK]
  field_simp
  ring

/-! ### Convexity of `φ` below the cap -/

theorem lrc_phi2_nonneg {x t : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ht1 : 1 ≤ t)
    (ht2 : t ≤ 7 / 6) (htU : t ≤ (1013 * x + 676) / 2340) :
    0 ≤ lrPhi2 (lrcN x t) (lrcN1 x t) (lrcN2 x t) (lrcV x t) (lrcV1 x t) (lrcV2 x t)
      (lrcY x t) (lrcY1 x t) (lrcY2 x t) (lrcK x t) (2 * t) 2 := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hKp : 0 < lrcK x t := by unfold lrcK; positivity
  have hBp : 0 < lrcB x t := by unfold lrcB; nlinarith
  have hVp : 0 < lrcV x t := by unfold lrcV; positivity
  -- the logarithm argument
  set y := lrcY x t / lrcK x t with hydef
  have hyc : lrcy x t (x + 10 / 13 * (t - 1)) = y := by
    rw [hydef]; unfold lrcy lrcY lrcB; ring
  obtain ⟨hy0, -⟩ := lrc_y_bounds (b := x + 10 / 13 * (t - 1)) (by linarith) hx2 ht1 ht2
    (by nlinarith) (by nlinarith)
  rw [hyc] at hy0
  have hy1 : y ≤ 1 := by
    obtain ⟨-, -, hT, -⟩ := lrc_dom (b := x + 10 / 13 * (t - 1)) hx hx2 ht1 ht2 (by nlinarith) le_rfl
    rw [hydef, div_le_one hKp]; unfold lrcY lrcB; linarith
  have hyp : 0 < y := by linarith
  -- the two signs of `y″`
  set y1 := (lrcY1 x t * lrcK x t - lrcY x t * (2 * t)) / lrcK x t ^ 2 with hy1def
  set y2 := ((lrcY2 x t * lrcK x t - lrcY x t * 2) * lrcK x t - 2 * (2 * t) *
    (lrcY1 x t * lrcK x t - lrcY x t * (2 * t))) / lrcK x t ^ 3 with hy2def
  have hKn : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  have hs0 : 0 ≤ (1013 * x + 676) / 2340 - t := by linarith
  have hs1 : (1013 * x + 676) / 2340 - t ≤ 31 / 200 := by linarith
  have hy2a : 0 ≤ y2 := by
    have hP := lrcPy2s_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
      (by linarith) hs0 hs1
    rw [← lrcPy2x_eq] at hP
    have e : y2 = lrcPy2x x t / lrcK x t ^ 3 := by
      rw [hy2def]; simp only [lrcY, lrcY1, lrcY2, lrcB, lrcK, lrcPy2x]
      field_simp; ring
    rw [e]; positivity
  have hy2b : y2 ≤ 1 / 2 := by
    have hP := lrcPy3s_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
      (by linarith) hs0 hs1
    rw [← lrcPy3x_eq] at hP
    have e : 1 / 2 - y2 = lrcPy3x x t / lrcK x t ^ 3 := by
      rw [hy2def]; simp only [lrcY, lrcY1, lrcY2, lrcB, lrcK, lrcPy3x]
      field_simp; ring
    have : 0 ≤ lrcPy3x x t / lrcK x t ^ 3 := by positivity
    linarith
  -- the majorant bounds
  have hl2 := lr_ell2_ge hyp hy1
  have hl1 : 624 / 625 ≤ y * lrell1 y := by
    have e : y * lrell1 y = 1 - lreps y := by
      unfold lrell1 lreps; have : y + 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]; have := lr_eps_le hy0 (by linarith); linarith
  have hA : -(y1 ^ 2 / y ^ 2) ≤ lrell2 y * y1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right hl2 (sq_nonneg y1)
    have e : -(1 / y ^ 2) * y1 ^ 2 = -(y1 ^ 2 / y ^ 2) := by ring
    linarith
  have hB2 : 624 / 625 * (y2 / y) ≤ lrell1 y * y2 := by
    have e : lrell1 y * y2 = (y * lrell1 y) * (y2 / y) := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right hl1 (div_nonneg hy2a hyp.le)
  -- `(log y)″` and the circuit
  have hlog : y2 / y - y1 ^ 2 / y ^ 2 =
      -(1 / t ^ 2) - (23 / 13) ^ 2 / lrcB x t ^ 2 - (2 * lrcK x t - 4 * t ^ 2) / lrcK x t ^ 2 := by
    rw [hy2def, hy1def, hydef]
    simp only [lrcY, lrcY1, lrcY2]
    have hBn : lrcB x t ≠ 0 := hBp.ne'
    have hKn' : lrcK x t ≠ 0 := hKp.ne'
    field_simp
    ring
  have hcirc : 1 / 700 ≤ ((lrcN2 x t * lrcV x t - lrcN x t * lrcV2 x t) * lrcV x t -
      2 * lrcV1 x t * (lrcN1 x t * lrcV x t - lrcN x t * lrcV1 x t)) / lrcV x t ^ 3 +
      (-(1 / t ^ 2) - (23 / 13) ^ 2 / lrcB x t ^ 2 - (2 * lrcK x t - 4 * t ^ 2) / lrcK x t ^ 2) := by
    have hP := lrcPcs_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
      (by linarith) hs0 hs1
    rw [← lrcPcx_eq] at hP
    have e : ((lrcN2 x t * lrcV x t - lrcN x t * lrcV2 x t) * lrcV x t -
        2 * lrcV1 x t * (lrcN1 x t * lrcV x t - lrcN x t * lrcV1 x t)) / lrcV x t ^ 3 +
        (-(1 / t ^ 2) - (23 / 13) ^ 2 / lrcB x t ^ 2 - (2 * lrcK x t - 4 * t ^ 2) /
          lrcK x t ^ 2) - 1 / 700 = lrcPcx x t / 14280500 / lrcV x t ^ 3 := by
      have hc : (lrcN2 x t * lrcV x t - lrcN x t * lrcV2 x t) * lrcV x t -
          2 * lrcV1 x t * (lrcN1 x t * lrcV x t - lrcN x t * lrcV1 x t) -
          t * lrcB x t ^ 3 * lrcK x t ^ 3 - (23 / 13) ^ 2 * t ^ 3 * lrcB x t * lrcK x t ^ 3 -
          2 * t ^ 3 * lrcB x t ^ 3 * lrcK x t ^ 2 + 4 * t ^ 5 * lrcB x t ^ 3 * lrcK x t -
          lrcV x t ^ 3 / 700 = lrcPcx x t / 14280500 := by
        simp only [lrcN, lrcN1, lrcN2, lrcV, lrcV1, lrcV2, lrcB, lrcK, lrcPcx]
        ring
      have hBn : lrcB x t ≠ 0 := hBp.ne'
      have hKn' : lrcK x t ≠ 0 := hKp.ne'
      rw [← hc]
      unfold lrcV
      field_simp
      ring
    have : 0 ≤ lrcPcx x t / 14280500 / lrcV x t ^ 3 := by positivity
    linarith
  have hratio : y2 / y ≤ 3 / 4 := by
    rw [div_le_iff₀ hyp]; nlinarith
  unfold lrPhi2
  rw [← hydef, ← hy1def, ← hy2def]
  nlinarith

end SmoothedOctagon

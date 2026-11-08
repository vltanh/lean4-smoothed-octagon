module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC3b

/-!
# Gate S1 by hand, central face: the shape step

`SHORT_CENTRAL_SHAPE_F0`, `SHORT_CENTRAL_SHAPE_F1`.

* First test: along `β₊ = x + (10/13)(α - 1)` at a fixed norm, `(r₀)_α + (10/13)(r₀)_β ≥ 1/40 + 2/625`
  below the tangent chord `α_U` of the cap (affine in `u`; two-variable signs at `u = 3/4, 19/25`),
  so `F₀` decreases with slope `≤ -c/40`; along the ceiling `u_ℓ(x, β₊)` the norm motion costs at
  most `(1/5)(15/1992)(10/13)` per unit (`SHAPE_F0` (1), (6)): `hl1c_F0_astep`.
* Second test at `u = 19/25`: `F₁(x, α, β₊, 19/25) = Γ - c φ(α) - g` with
  `φ = N/V + ℓ(Y/K)`, `V = αBK`, `Y = 2αB` (`SHAPE_F1` (1)-(3)); `φ″ ≥ (N/V)″ + (log y)″ - (1/625)y″/y`
  (`ℓ″ ≥ -1/y²`, `yℓ′(y) = 1 - ε ≥ 624/625`, `y″ ≥ 0`) and `V³((N/V)″ + (log y)″)` is the curvature
  circuit of `(2)`, at least `V³/500` below the cap; so `φ` is convex and
  `F₁(α) ≥ min(F₁(1), F₁(α_c))`: `hl1c_F1_conc`.

Route: below the cap the circuit is positive, so the third derivative `P_aaa` and the endpoint jets
of `SHAPE_F1` §§2-4 are not needed, and the slope of the first test is bounded below the tangent
chord directly instead of by the cap division `(3)` of `SHAPE_F0`.

## Main API

* `hl1Phi1`, `hl1Phi2`, `hl1_qphi_hasDerivAt`, `hl1cN`, `hl1cV`, `hl1cY`, `hl1c_F1_phi`,
  `hl1c_F0_astep`, `hl1c_F1_conc`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real


/-! ### Derivatives of the circuit pieces -/

theorem hl1_quart_hasDerivAt (c0 c1 c2 c3 c4 t : ℝ) :
    HasDerivAt (fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 + c4 * s ^ 4)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3) t := by
  have hid := hasDerivAt_id' t
  have h := ((((hid.const_mul c1).const_add c0).add ((hid.fun_pow 2).const_mul c2)).add
    ((hid.fun_pow 3).const_mul c3)).add ((hid.fun_pow 4).const_mul c4)
  convert h using 1
  push_cast; ring

theorem hl1cN_d (x t : ℝ) : HasDerivAt (hl1cN x) (hl1cN1 x t) t := by
  have h := hl1_quart_hasDerivAt (-12 / 25 * x ^ 5 + 3197 / 1300 * x ^ 4 - 88 / 25 * x ^ 3 +
    17933 / 4225 * x ^ 2 - 1746 / 4225 * x) (-42 / 325 * x ^ 4 + 79 / 65 * x ^ 3 + 51 / 169 * x ^ 2 -
    808 / 325 * x + 12 / 65) (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x - 276 / 845)
    (-3522 / 845 * x + 308 / 169) (-1643 / 676) t
  exact h

theorem hl1cN1_d (x t : ℝ) : HasDerivAt (hl1cN1 x) (hl1cN2 x t) t := by
  have h := hl1_quart_hasDerivAt (-42 / 325 * x ^ 4 + 79 / 65 * x ^ 3 + 51 / 169 * x ^ 2 -
    808 / 325 * x + 12 / 65) (2 * (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x -
    276 / 845)) (3 * (-3522 / 845 * x + 308 / 169)) (4 * (-1643 / 676)) 0 t
  convert h using 1
  · funext s; unfold hl1cN1; ring
  · unfold hl1cN2; ring

theorem hl1cB_d (x t : ℝ) : HasDerivAt (hl1cB x) (23 / 13) t := by
  have h := (hasDerivAt_id' t).add ((((hasDerivAt_id' t).sub_const 1).const_mul (10 / 13)).const_add x)
  have hf : hl1cB x = fun s => s + (x + 10 / 13 * (s - 1)) := rfl
  rw [hf]
  convert h using 1
  ring

theorem hl1cK_d (x t : ℝ) : HasDerivAt (hh1cK x) (2 * t) t := by
  have h := ((hasDerivAt_id' t).fun_pow 2).const_add (x * (x + 2))
  have hf : hh1cK x = fun s => x * (x + 2) + s ^ 2 := rfl
  rw [hf]
  convert h using 1
  push_cast; ring

theorem hl1cV_d (x t : ℝ) : HasDerivAt (hl1cV x) (hl1cV1 x t) t := by
  have h := ((hasDerivAt_id' t).fun_mul (hl1cB_d x t)).fun_mul (hl1cK_d x t)
  have hf : hl1cV x = fun s => s * hl1cB x s * hh1cK x s := rfl
  rw [hf]
  convert h using 1
  unfold hl1cV1; ring

theorem hl1cV1_d (x t : ℝ) : HasDerivAt (hl1cV1 x) (hl1cV2 x t) t := by
  have hB := hl1cB_d x t
  have hK := hl1cK_d x t
  have hid := hasDerivAt_id' t
  have h := ((hB.fun_mul hK).add ((hid.const_mul (23 / 13)).fun_mul hK)).add ((hid.fun_mul hB).fun_mul
    (hid.const_mul 2))
  have hf : hl1cV1 x = fun s => hl1cB x s * hh1cK x s + s * (23 / 13) * hh1cK x s +
      s * hl1cB x s * (2 * s) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply]; ring
  · unfold hl1cV2; ring

theorem hl1cY_d (x t : ℝ) : HasDerivAt (hl1cY x) (hl1cY1 x t) t := by
  have h := ((hasDerivAt_id' t).const_mul 2).fun_mul (hl1cB_d x t)
  have hf : hl1cY x = fun s => 2 * s * hl1cB x s := rfl
  rw [hf]
  convert h using 1
  unfold hl1cY1; ring

theorem hl1cY1_d (x t : ℝ) : HasDerivAt (hl1cY1 x) (hl1cY2 x t) t := by
  have h := ((hl1cB_d x t).const_mul 2).add ((hasDerivAt_id' t).const_mul (2 * (23 / 13)))
  have hf : hl1cY1 x = fun s => 2 * hl1cB x s + 2 * s * (23 / 13) := by
    funext s; unfold hl1cY1; ring
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply]; ring
  · unfold hl1cY2; ring

theorem hl1cK1_d (t : ℝ) : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
  simpa using (hasDerivAt_id' t).const_mul 2

/-! ### The second test as `Γ - cφ - g` -/

theorem hl1c_F1_phi {x t : ℝ} (hx : 0 < x) (ht : 1 ≤ t) :
    hh1cF1 x t (x + 10 / 13 * (t - 1)) (19 / 25) = hh1cG x (19 / 25) -
      7 / 96 * (hl1cN x t / hl1cV x t + hh1ell (hl1cY x t / hh1cK x t)) - 9193 / 50000 := by
  have ht0 : 0 < t := by linarith
  have hy : hh1cy x t (x + 10 / 13 * (t - 1)) = hl1cY x t / hh1cK x t := by
    unfold hh1cy hl1cY hl1cB; ring
  have hB : t + (x + 10 / 13 * (t - 1)) ≠ 0 := by nlinarith
  have hS : 1 + x ≠ 0 := by linarith
  have hKn : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  simp only [hh1cF1, hh1cF0, hh1cR2]
  rw [hy]
  generalize hh1ell (hl1cY x t / hh1cK x t) = L
  simp only [hh1cw, hh1cEL, hh1cq, hh1cT, hh1cL, hh1cd, hh1cv, hh1cE, hsDg, hl1cN, hl1cV, hl1cB,
    hh1cK]
  field_simp
  ring

/-! ### Convexity of `φ` below the cap -/

theorem hl1c_phi2_nonneg {x t : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ht1 : 1 ≤ t)
    (ht2 : t ≤ 7 / 6) (htU : t ≤ (1013 * x + 676) / 2340) :
    0 ≤ hl1Phi2 (hl1cN x t) (hl1cN1 x t) (hl1cN2 x t) (hl1cV x t) (hl1cV1 x t) (hl1cV2 x t)
      (hl1cY x t) (hl1cY1 x t) (hl1cY2 x t) (hh1cK x t) (2 * t) 2 := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hKp : 0 < hh1cK x t := by unfold hh1cK; positivity
  have hBp : 0 < hl1cB x t := by unfold hl1cB; nlinarith
  have hVp : 0 < hl1cV x t := by unfold hl1cV; positivity
  -- the logarithm argument
  set y := hl1cY x t / hh1cK x t with hydef
  have hyc : hh1cy x t (x + 10 / 13 * (t - 1)) = y := by
    rw [hydef]; unfold hh1cy hl1cY hl1cB; ring
  obtain ⟨hy0, -⟩ := hh1c_y_bounds (b := x + 10 / 13 * (t - 1)) (by linarith) hx2 ht1 ht2
    (by nlinarith) (by nlinarith)
  rw [hyc] at hy0
  have hy1 : y ≤ 1 := by
    obtain ⟨-, -, hT, -⟩ := hl1c_dom (b := x + 10 / 13 * (t - 1)) hx hx2 ht1 ht2 (by nlinarith) le_rfl
    rw [hydef, div_le_one hKp]; unfold hl1cY hl1cB; linarith
  have hyp : 0 < y := by linarith
  -- the two signs of `y″`
  set y1 := (hl1cY1 x t * hh1cK x t - hl1cY x t * (2 * t)) / hh1cK x t ^ 2 with hy1def
  set y2 := ((hl1cY2 x t * hh1cK x t - hl1cY x t * 2) * hh1cK x t - 2 * (2 * t) *
    (hl1cY1 x t * hh1cK x t - hl1cY x t * (2 * t))) / hh1cK x t ^ 3 with hy2def
  have hKn : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  have hs0 : 0 ≤ (1013 * x + 676) / 2340 - t := by linarith
  have hs1 : (1013 * x + 676) / 2340 - t ≤ 31 / 200 := by linarith
  have hy2a : 0 ≤ y2 := by
    have hP := hl1cPy2s_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
      (by linarith) hs0 hs1
    rw [← hl1cPy2x_eq] at hP
    have e : y2 = hl1cPy2x x t / hh1cK x t ^ 3 := by
      rw [hy2def]; simp only [hl1cY, hl1cY1, hl1cY2, hl1cB, hh1cK, hl1cPy2x]
      field_simp; ring
    rw [e]; positivity
  have hy2b : y2 ≤ 1 / 2 := by
    have hP := hl1cPy3s_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
      (by linarith) hs0 hs1
    rw [← hl1cPy3x_eq] at hP
    have e : 1 / 2 - y2 = hl1cPy3x x t / hh1cK x t ^ 3 := by
      rw [hy2def]; simp only [hl1cY, hl1cY1, hl1cY2, hl1cB, hh1cK, hl1cPy3x]
      field_simp; ring
    have : 0 ≤ hl1cPy3x x t / hh1cK x t ^ 3 := by positivity
    linarith
  -- the majorant bounds
  have hl2 := hl1_ell2_ge hyp hy1
  have hl1 : 624 / 625 ≤ y * hl1ell1 y := by
    have e : y * hl1ell1 y = 1 - hh1eps y := by
      unfold hl1ell1 hh1eps; have : y + 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]; have := hh1_eps_le hy0 (by linarith); linarith
  have hA : -(y1 ^ 2 / y ^ 2) ≤ hl1ell2 y * y1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right hl2 (sq_nonneg y1)
    have e : -(1 / y ^ 2) * y1 ^ 2 = -(y1 ^ 2 / y ^ 2) := by ring
    linarith
  have hB2 : 624 / 625 * (y2 / y) ≤ hl1ell1 y * y2 := by
    have e : hl1ell1 y * y2 = (y * hl1ell1 y) * (y2 / y) := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right hl1 (div_nonneg hy2a hyp.le)
  -- `(log y)″` and the circuit
  have hlog : y2 / y - y1 ^ 2 / y ^ 2 =
      -(1 / t ^ 2) - (23 / 13) ^ 2 / hl1cB x t ^ 2 - (2 * hh1cK x t - 4 * t ^ 2) / hh1cK x t ^ 2 := by
    rw [hy2def, hy1def, hydef]
    simp only [hl1cY, hl1cY1, hl1cY2]
    have hBn : hl1cB x t ≠ 0 := hBp.ne'
    have hKn' : hh1cK x t ≠ 0 := hKp.ne'
    field_simp
    ring
  have hcirc : 1 / 700 ≤ ((hl1cN2 x t * hl1cV x t - hl1cN x t * hl1cV2 x t) * hl1cV x t -
      2 * hl1cV1 x t * (hl1cN1 x t * hl1cV x t - hl1cN x t * hl1cV1 x t)) / hl1cV x t ^ 3 +
      (-(1 / t ^ 2) - (23 / 13) ^ 2 / hl1cB x t ^ 2 - (2 * hh1cK x t - 4 * t ^ 2) / hh1cK x t ^ 2) := by
    have hP := hl1cPcs_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
      (by linarith) hs0 hs1
    rw [← hl1cPcx_eq] at hP
    have e : ((hl1cN2 x t * hl1cV x t - hl1cN x t * hl1cV2 x t) * hl1cV x t -
        2 * hl1cV1 x t * (hl1cN1 x t * hl1cV x t - hl1cN x t * hl1cV1 x t)) / hl1cV x t ^ 3 +
        (-(1 / t ^ 2) - (23 / 13) ^ 2 / hl1cB x t ^ 2 - (2 * hh1cK x t - 4 * t ^ 2) /
          hh1cK x t ^ 2) - 1 / 700 = hl1cPcx x t / 14280500 / hl1cV x t ^ 3 := by
      have hc : (hl1cN2 x t * hl1cV x t - hl1cN x t * hl1cV2 x t) * hl1cV x t -
          2 * hl1cV1 x t * (hl1cN1 x t * hl1cV x t - hl1cN x t * hl1cV1 x t) -
          t * hl1cB x t ^ 3 * hh1cK x t ^ 3 - (23 / 13) ^ 2 * t ^ 3 * hl1cB x t * hh1cK x t ^ 3 -
          2 * t ^ 3 * hl1cB x t ^ 3 * hh1cK x t ^ 2 + 4 * t ^ 5 * hl1cB x t ^ 3 * hh1cK x t -
          hl1cV x t ^ 3 / 700 = hl1cPcx x t / 14280500 := by
        simp only [hl1cN, hl1cN1, hl1cN2, hl1cV, hl1cV1, hl1cV2, hl1cB, hh1cK, hl1cPcx]
        ring
      have hBn : hl1cB x t ≠ 0 := hBp.ne'
      have hKn' : hh1cK x t ≠ 0 := hKp.ne'
      rw [← hc]
      unfold hl1cV
      field_simp
      ring
    have : 0 ≤ hl1cPcx x t / 14280500 / hl1cV x t ^ 3 := by positivity
    linarith
  have hratio : y2 / y ≤ 3 / 4 := by
    rw [div_le_iff₀ hyp]; nlinarith
  unfold hl1Phi2
  rw [← hydef, ← hy1def, ← hy2def]
  nlinarith

end SmoothedOctagon

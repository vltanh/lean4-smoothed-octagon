module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXSign
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXNorm
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXDeriv

/-!
# S2 hand signs: the central x comparison

`archive/lighter-proofs/SHORT_RATIO_CENTRAL_X.md`: on `13/6 ≤ x ≤ 12/5`, `1 ≤ a ≤ 4/3`, along the
curve `b = b_+(x, a)`, `u = u_C(x, b)`, both duration-tangent tests `F₀(t)`, `F₁(t)` (`t ≥ 2`
fixed) are nonincreasing in `x`, so they are at most their values at `x = 13/6` (§1 (4)-(6)).

The total x-derivative of `F₀` is `R₀(u, u_x)` and that of `F₁` is `R₁(u, u_x) + φ(t)T_x`,
`φ(t) = (t - 1)/t² - 1/4 ≤ 0`, `T_x = Z/(aB²) > 0` (`S2HandCenXDeriv`, (25), (28)). Both `R_i`
are affine in `(u, u_x)` with positive coefficients `C`, `C_x` (`hl2cx_R0_aff`, (23)-(24)), so
`u ≤ U`, `u_x ≤ V` (`S2HandCenXNorm`, (8)) give `R_i(u, u_x) ≤ R_i(U, V) < 0`
(`S2HandCenXSign`).

Route: as in `S2HandCenXSign`, the signs of `R_i(U, V)`, `C`, `C_x` are proved on their exact
cleared numerators by the termwise rule (35), instead of the note's degree-eight Taylor
polynomials with a geometric remainder (§5-§6) and its shape bounds (14)-(24).

## Main API

* `hl2cx_F0_deriv`, `hl2cx_F1_deriv`: the total x-derivatives of the two tests.
* `hl2cx_R0_nonpos`, `hl2cx_R1_nonpos`: `R_i(u, u_x) ≤ 0`.
* `hl2c_xmono`: both tests are at most their values at `x = 13/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- **The total x-derivative of `F₀`** along `b = b_+(x, a)`, `u = u_C` (`SHORT_RATIO_CENTRAL_X`
(25), (28)). -/
theorem hl2cx_F0_deriv {t a y : ℝ} (ht : t ≠ 0) (ha : a ≠ 0) (hB : a + hl2cbp y a ≠ 0)
    (hK0 : hl2cK y a ≠ 0) (hS : 1 + y ≠ 0) (hL : hl2cxLb y a ≠ 0) :
    HasDerivAt (fun z => hl2cF0 t z a (hl2cbp z a) (hsUC z (hl2cbp z a)))
      (hl2cxR0 a (hl2cxl a) (1 + y) (hl2cK y a) (a + hl2cbp y a) (hsDg y (hl2cbp y a) a)
        (hl2cxDx y a) (hsUC y (hl2cbp y a)) (hl2cxup y a)) y := by
  have hb := hl2cx_bp_deriv a y
  have hu := hl2cx_uC_deriv (a := a) hS hL
  have h := ((hl2cx_d_Rlog (t := t) hb hu ha hB hK0 ht).fun_add (hl2cx_d_gh0 hb hu hK0)).add_const
    (4 / t - 2 / t ^ 2 - 3 / 2)
  have hf : (fun z => hl2cF0 t z a (hl2cbp z a) (hsUC z (hl2cbp z a))) = fun z =>
      hl2cR z a (hl2cbp z a) (hsUC z (hl2cbp z a)) + log (t * hl2ck z a (hl2cbp z a)) +
        (4 - 7 * hl2ck z a (hl2cbp z a) / 2) *
          (hl2cw z a (hl2cbp z a) (hsUC z (hl2cbp z a)) - 3 / 4) +
        (4 / t - 2 / t ^ 2 - 3 / 2) := by
    funext z
    unfold hl2cF0
    ring
  rw [hf]
  refine h.congr_deriv ?_
  unfold hl2cxR0 hl2cxDx
  ring

/-- **The total x-derivative of `F₁`** along `b = b_+(x, a)`, `u = u_C` (`SHORT_RATIO_CENTRAL_X`
(5)-(6), (25), (28)): `R₁ + φ(t)Z/(aB²)`. -/
theorem hl2cx_F1_deriv {t a y : ℝ} (ht : t ≠ 0) (ha : a ≠ 0) (hB : a + hl2cbp y a ≠ 0)
    (hK0 : hl2cK y a ≠ 0) (hS : 1 + y ≠ 0) (hL : hl2cxLb y a ≠ 0) :
    HasDerivAt (fun z => hl2cF1 t z a (hl2cbp z a) (hsUC z (hl2cbp z a)))
      (hl2cxR1 a (hl2cxl a) (1 + y) (hl2cK y a) (a + hl2cbp y a) (hsDg y (hl2cbp y a) a)
          (hl2cxDx y a) (hsUC y (hl2cbp y a)) (hl2cxup y a) +
        ((t - 1) / t ^ 2 - 1 / 4) *
          (hl2cxZ (hl2cxl a) (1 + y) (hl2cK y a) (a + hl2cbp y a) /
            (a * (a + hl2cbp y a) ^ 2))) y := by
  have hb := hl2cx_bp_deriv a y
  have hu := hl2cx_uC_deriv (a := a) hS hL
  have h := (((hl2cx_d_Rlog (t := t) hb hu ha hB hK0 ht).fun_add
    (hl2cx_d_gh1 hb hu ha hB hK0)).fun_add
      (hl2cx_d_T (φ := (t - 1) / t ^ 2 - 1 / 4) hb ha hB hK0)).add_const (2 / t - 1)
  have hf : (fun z => hl2cF1 t z a (hl2cbp z a) (hsUC z (hl2cbp z a))) = fun z =>
      hl2cR z a (hl2cbp z a) (hsUC z (hl2cbp z a)) + log (t * hl2ck z a (hl2cbp z a)) +
        (1 / hl2ck z a (hl2cbp z a) + 1 / 4) *
          (hl2cw z a (hl2cbp z a) (hsUC z (hl2cbp z a)) - 3 / 4) +
        1 / hl2ck z a (hl2cbp z a) * ((t - 1) / t ^ 2 - 1 / 4) + (2 / t - 1) := by
    funext z
    unfold hl2cF1
    ring
  rw [hf]
  refine h.congr_deriv ?_
  unfold hl2cxR1 hl2cxDx
  ring

theorem hl2cx_pos {z a : ℝ} (hz : 13 / 6 ≤ z) (ha : 1 ≤ a) :
    0 < a ∧ 0 < a + hl2cbp z a ∧ 0 < hl2cK z a ∧ 0 < 1 + z ∧ 0 < hl2cxLb z a := by
  have hb : 0 ≤ (24 * z + 51) * (a - 1) / 128 := div_nonneg (mul_nonneg (by linarith) (by linarith))
    (by norm_num)
  refine ⟨by linarith, ?_, ?_, by linarith, hl2cx_Lb_pos hz ha⟩
  · unfold hl2cbp
    linarith
  · unfold hl2cK
    have : 0 < z := by linarith
    positivity

/-- **`G_x ≤ R₀(U, V) < 0`** (`SHORT_RATIO_CENTRAL_X` (4), (25), (28)). -/
theorem hl2cx_R0_nonpos {z a : ℝ} (hz : 13 / 6 ≤ z) (hz2 : z ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    hl2cxR0 a (hl2cxl a) (1 + z) (hl2cK z a) (a + hl2cbp z a) (hsDg z (hl2cbp z a) a)
      (hl2cxDx z a) (hsUC z (hl2cbp z a)) (hl2cxup z a) ≤ 0 := by
  obtain ⟨ha0, hB, hK, -, -⟩ := hl2cx_pos hz ha
  have e := hl2cx_R0_aff (l := hl2cxl a) (S := 1 + z) (B := a + hl2cbp z a)
    (D := hsDg z (hl2cbp z a) a) (Dx := hl2cxDx z a) (u := hsUC z (hl2cbp z a))
    (v := hl2cxup z a) (U := hl2cxU z a) (V := hl2cxV a) ha0.ne' hK.ne'
  have h1 : 0 ≤ (hl2cxV a - hl2cxup z a) * (hl2cxMv0 a (1 + z) (hl2cK z a) (a + hl2cbp z a)
      (hsDg z (hl2cbp z a) a) / (a * hl2cK z a ^ 3)) :=
    mul_nonneg (sub_nonneg.2 (hl2cx_up_le hz hz2 ha ha2))
      (div_pos (hl2cx_Mv0_pos hz hz2 ha ha2) (by positivity)).le
  have h2 : 0 ≤ (hl2cxU z a - hsUC z (hl2cbp z a)) * (hl2cxMu0 a (hl2cxl a) (1 + z) (hl2cK z a)
      (a + hl2cbp z a) (hsDg z (hl2cbp z a) a) (hl2cxDx z a) / (a * hl2cK z a ^ 4)) :=
    mul_nonneg (sub_nonneg.2 (hl2cx_u_le hz hz2 ha ha2))
      (div_pos (hl2cx_Mu0_pos hz hz2 ha ha2) (by positivity)).le
  have hN := hl2cx_N0_neg hz hz2 ha ha2
  rw [← hl2cx_R0_eq ha0.ne' hB.ne' hK.ne'] at hN
  have h3 := neg_of_mul_neg_right hN (by positivity)
  linarith

/-- **`H_x ≤ R₁(U, V) < 0`** (`SHORT_RATIO_CENTRAL_X` (4), (25), (28)). -/
theorem hl2cx_R1_nonpos {z a : ℝ} (hz : 13 / 6 ≤ z) (hz2 : z ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    hl2cxR1 a (hl2cxl a) (1 + z) (hl2cK z a) (a + hl2cbp z a) (hsDg z (hl2cbp z a) a)
      (hl2cxDx z a) (hsUC z (hl2cbp z a)) (hl2cxup z a) ≤ 0 := by
  obtain ⟨ha0, hB, hK, -, -⟩ := hl2cx_pos hz ha
  have e := hl2cx_R1_aff (l := hl2cxl a) (S := 1 + z) (D := hsDg z (hl2cbp z a) a)
    (Dx := hl2cxDx z a) (u := hsUC z (hl2cbp z a))
    (v := hl2cxup z a) (U := hl2cxU z a) (V := hl2cxV a) ha0.ne' hB.ne' hK.ne'
  have h1 : 0 ≤ (hl2cxV a - hl2cxup z a) * (hl2cxMv1 a (1 + z) (hl2cK z a) (a + hl2cbp z a)
      (hsDg z (hl2cbp z a) a) / (a * (a + hl2cbp z a) * hl2cK z a ^ 2)) :=
    mul_nonneg (sub_nonneg.2 (hl2cx_up_le hz hz2 ha ha2))
      (div_pos (hl2cx_Mv1_pos hz hz2 ha ha2) (by positivity)).le
  have h2 : 0 ≤ (hl2cxU z a - hsUC z (hl2cbp z a)) * (hl2cxMu1 a (hl2cxl a) (1 + z) (hl2cK z a)
      (a + hl2cbp z a) (hsDg z (hl2cbp z a) a) (hl2cxDx z a) /
        (a * (a + hl2cbp z a) ^ 2 * hl2cK z a ^ 3)) :=
    mul_nonneg (sub_nonneg.2 (hl2cx_u_le hz hz2 ha ha2))
      (div_pos (hl2cx_Mu1_pos hz hz2 ha ha2) (by positivity)).le
  have hN := hl2cx_N1_neg hz hz2 ha ha2
  rw [← hl2cx_R1_eq ha0.ne' hB.ne' hK.ne'] at hN
  have h3 := neg_of_mul_neg_right hN (by positivity)
  linarith

/-- **The x comparison** (`SHORT_RATIO_CENTRAL_X` (4)-(6)): along `b = b_+(x, a)`, `u = u_C`, both
duration-tangent tests at `t ≥ 2` are at most their values at `x = 13/6`. -/
theorem hl2c_xmono {t x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3)
    (ht : 2 ≤ t) (ht2 : t ≤ 8 / 3) :
    hl2cF0 t x a (hl2cbp x a) (hsUC x (hl2cbp x a)) ≤
        hl2cF0 t (13 / 6) a (hl2cbp (13 / 6) a) (hsUC (13 / 6) (hl2cbp (13 / 6) a)) ∧
      hl2cF1 t x a (hl2cbp x a) (hsUC x (hl2cbp x a)) ≤
        hl2cF1 t (13 / 6) a (hl2cbp (13 / 6) a) (hsUC (13 / 6) (hl2cbp (13 / 6) a)) := by
  -- only `t ≥ 2` is used; `t ≤ 8/3` is the range of the caller's duration tangent
  have _ht2 := ht2
  have ht0 : t ≠ 0 := by linarith
  constructor
  · have h := ss_le_of_deriv (f := fun z => -hl2cF0 t z a (hl2cbp z a) (hsUC z (hl2cbp z a)))
      (f' := fun z => -hl2cxR0 a (hl2cxl a) (1 + z) (hl2cK z a) (a + hl2cbp z a)
        (hsDg z (hl2cbp z a) a) (hl2cxDx z a) (hsUC z (hl2cbp z a)) (hl2cxup z a)) hx
      (fun z hz => by
        obtain ⟨ha0, hB, hK, hS, hL⟩ := hl2cx_pos hz.1 ha
        exact (hl2cx_F0_deriv ht0 ha0.ne' hB.ne' hK.ne' hS.ne' hL.ne').neg)
      (fun z hz => by
        have := hl2cx_R0_nonpos hz.1.le (by linarith [hz.2]) ha ha2
        linarith)
    linarith
  · have h := ss_le_of_deriv (f := fun z => -hl2cF1 t z a (hl2cbp z a) (hsUC z (hl2cbp z a)))
      (f' := fun z => -(hl2cxR1 a (hl2cxl a) (1 + z) (hl2cK z a) (a + hl2cbp z a)
          (hsDg z (hl2cbp z a) a) (hl2cxDx z a) (hsUC z (hl2cbp z a)) (hl2cxup z a) +
        ((t - 1) / t ^ 2 - 1 / 4) *
          (hl2cxZ (hl2cxl a) (1 + z) (hl2cK z a) (a + hl2cbp z a) / (a * (a + hl2cbp z a) ^ 2))))
      hx
      (fun z hz => by
        obtain ⟨ha0, hB, hK, hS, hL⟩ := hl2cx_pos hz.1 ha
        exact (hl2cx_F1_deriv ht0 ha0.ne' hB.ne' hK.ne' hS.ne' hL.ne').neg)
      (fun z hz => by
        have h1 := hl2cx_R1_nonpos hz.1.le (by linarith [hz.2]) ha ha2
        obtain ⟨ha0, hB, -, -, -⟩ := hl2cx_pos hz.1.le ha
        have hZ := hl2cx_Z_pos hz.1.le (by linarith [hz.2]) ha ha2
        -- `φ(t) = (t - 1)/t² - 1/4 = -(t - 2)²/(4t²) ≤ 0`
        have hφ : (t - 1) / t ^ 2 - 1 / 4 ≤ 0 := by
          have e : (t - 1) / t ^ 2 - 1 / 4 = -((t - 2) ^ 2 / (4 * t ^ 2)) := by
            field_simp
            ring
          rw [e]
          have : 0 ≤ (t - 2) ^ 2 / (4 * t ^ 2) := by positivity
          linarith
        have h2 := mul_nonpos_of_nonpos_of_nonneg hφ
          (div_pos hZ (by positivity : (0 : ℝ) < a * (a + hl2cbp z a) ^ 2)).le
        linarith)
    linarith

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Signs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Norm
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.ChainRule

/-!
# Smaller-short window, upper ratio: the central x comparison

On `13/6 ≤ x ≤ 12/5`, `1 ≤ a ≤ 4/3`, along the curve `b = b_+(x, a)`, `u = u_C(x, b)`, both
duration-tangent tests `F₀(t)`, `F₁(t)` (`t ≥ 2` fixed) are nonincreasing in `x`, so they are at
most their values at `x = 13/6`.

The total x-derivative of `F₀` is `R₀(u, u_x)` and that of `F₁` is `R₁(u, u_x) + φ(t)T_x`,
`φ(t) = (t - 1)/t² - 1/4 ≤ 0`, `T_x = Z/(aB²) > 0` (`Ratio/ChainRule`). Both `R_i`
are affine in `(u, u_x)` with positive coefficients `C`, `C_x` (`urcx_R0_aff`), so
`u ≤ U`, `u_x ≤ V` (`Ratio/Norm`) give `R_i(u, u_x) ≤ R_i(U, V) < 0`
(`Ratio/Signs`).

The signs of `R_i(U, V)`, `C`, `C_x` are proved in `Ratio/Signs` on their exact cleared
numerators by a termwise bound of their monomials.

## Main API

* `urcx_F0_deriv`, `urcx_F1_deriv`: the total x-derivatives of the two tests.
* `urcx_R0_nonpos`, `urcx_R1_nonpos`: `R_i(u, u_x) ≤ 0`.
* `urc_xmono`: both tests are at most their values at `x = 13/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- **The total x-derivative of `F₀`** along `b = b_+(x, a)`, `u = u_C`: `R₀(u, u_x)`. -/
theorem urcx_F0_deriv {t a y : ℝ} (ht : t ≠ 0) (ha : a ≠ 0) (hB : a + urcbp y a ≠ 0)
    (hK0 : urcK y a ≠ 0) (hS : 1 + y ≠ 0) (hL : urcxLb y a ≠ 0) :
    HasDerivAt (fun z => urcF0 t z a (urcbp z a) (ssUC z (urcbp z a)))
      (urcxR0 a (urcxl a) (1 + y) (urcK y a) (a + urcbp y a) (ssDg y (urcbp y a) a)
        (urcxDx y a) (ssUC y (urcbp y a)) (urcxup y a)) y := by
  have hb := urcx_bp_deriv a y
  have hu := urcx_uC_deriv (a := a) hS hL
  have h := ((urcx_d_Rlog (t := t) hb hu ha hB hK0 ht).fun_add (urcx_d_gh0 hb hu hK0)).add_const
    (4 / t - 2 / t ^ 2 - 3 / 2)
  have hf : (fun z => urcF0 t z a (urcbp z a) (ssUC z (urcbp z a))) = fun z =>
      urcR z a (urcbp z a) (ssUC z (urcbp z a)) + log (t * urck z a (urcbp z a)) +
        (4 - 7 * urck z a (urcbp z a) / 2) *
          (urcw z a (urcbp z a) (ssUC z (urcbp z a)) - 3 / 4) +
        (4 / t - 2 / t ^ 2 - 3 / 2) := by
    funext z
    unfold urcF0
    ring
  rw [hf]
  refine h.congr_deriv ?_
  unfold urcxR0 urcxDx
  ring

/-- **The total x-derivative of `F₁`** along `b = b_+(x, a)`, `u = u_C`: `R₁ + φ(t)Z/(aB²)`. -/
theorem urcx_F1_deriv {t a y : ℝ} (ht : t ≠ 0) (ha : a ≠ 0) (hB : a + urcbp y a ≠ 0)
    (hK0 : urcK y a ≠ 0) (hS : 1 + y ≠ 0) (hL : urcxLb y a ≠ 0) :
    HasDerivAt (fun z => urcF1 t z a (urcbp z a) (ssUC z (urcbp z a)))
      (urcxR1 a (urcxl a) (1 + y) (urcK y a) (a + urcbp y a) (ssDg y (urcbp y a) a)
          (urcxDx y a) (ssUC y (urcbp y a)) (urcxup y a) +
        ((t - 1) / t ^ 2 - 1 / 4) *
          (urcxZ (urcxl a) (1 + y) (urcK y a) (a + urcbp y a) /
            (a * (a + urcbp y a) ^ 2))) y := by
  have hb := urcx_bp_deriv a y
  have hu := urcx_uC_deriv (a := a) hS hL
  have h := (((urcx_d_Rlog (t := t) hb hu ha hB hK0 ht).fun_add
    (urcx_d_gh1 hb hu ha hB hK0)).fun_add
      (urcx_d_T (φ := (t - 1) / t ^ 2 - 1 / 4) hb ha hB hK0)).add_const (2 / t - 1)
  have hf : (fun z => urcF1 t z a (urcbp z a) (ssUC z (urcbp z a))) = fun z =>
      urcR z a (urcbp z a) (ssUC z (urcbp z a)) + log (t * urck z a (urcbp z a)) +
        (1 / urck z a (urcbp z a) + 1 / 4) *
          (urcw z a (urcbp z a) (ssUC z (urcbp z a)) - 3 / 4) +
        1 / urck z a (urcbp z a) * ((t - 1) / t ^ 2 - 1 / 4) + (2 / t - 1) := by
    funext z
    unfold urcF1
    ring
  rw [hf]
  refine h.congr_deriv ?_
  unfold urcxR1 urcxDx
  ring

theorem urcx_pos {z a : ℝ} (hz : 13 / 6 ≤ z) (ha : 1 ≤ a) :
    0 < a ∧ 0 < a + urcbp z a ∧ 0 < urcK z a ∧ 0 < 1 + z ∧ 0 < urcxLb z a := by
  have hb : 0 ≤ (24 * z + 51) * (a - 1) / 128 := div_nonneg (mul_nonneg (by linarith) (by linarith))
    (by norm_num)
  refine ⟨by linarith, ?_, ?_, by linarith, urcx_Lb_pos hz ha⟩
  · unfold urcbp
    linarith
  · unfold urcK
    have : 0 < z := by linarith
    positivity

/-- **`G_x ≤ R₀(U, V) < 0`**: `R₀` is affine in `(u, u_x)` with positive coefficients, and
`u ≤ U`, `u_x ≤ V`. -/
theorem urcx_R0_nonpos {z a : ℝ} (hz : 13 / 6 ≤ z) (hz2 : z ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    urcxR0 a (urcxl a) (1 + z) (urcK z a) (a + urcbp z a) (ssDg z (urcbp z a) a)
      (urcxDx z a) (ssUC z (urcbp z a)) (urcxup z a) ≤ 0 := by
  obtain ⟨ha0, hB, hK, -, -⟩ := urcx_pos hz ha
  have e := urcx_R0_aff (l := urcxl a) (S := 1 + z) (B := a + urcbp z a)
    (D := ssDg z (urcbp z a) a) (Dx := urcxDx z a) (u := ssUC z (urcbp z a))
    (v := urcxup z a) (U := urcxU z a) (V := urcxV a) ha0.ne' hK.ne'
  have h1 : 0 ≤ (urcxV a - urcxup z a) * (urcxMv0 a (1 + z) (urcK z a) (a + urcbp z a)
      (ssDg z (urcbp z a) a) / (a * urcK z a ^ 3)) :=
    mul_nonneg (sub_nonneg.2 (urcx_up_le hz hz2 ha ha2))
      (div_pos (urcx_Mv0_pos hz hz2 ha ha2) (by positivity)).le
  have h2 : 0 ≤ (urcxU z a - ssUC z (urcbp z a)) * (urcxMu0 a (urcxl a) (1 + z) (urcK z a)
      (a + urcbp z a) (ssDg z (urcbp z a) a) (urcxDx z a) / (a * urcK z a ^ 4)) :=
    mul_nonneg (sub_nonneg.2 (urcx_u_le hz hz2 ha ha2))
      (div_pos (urcx_Mu0_pos hz hz2 ha ha2) (by positivity)).le
  have hN := urcx_N0_neg hz hz2 ha ha2
  rw [← urcx_R0_eq ha0.ne' hB.ne' hK.ne'] at hN
  have h3 := neg_of_mul_neg_right hN (by positivity)
  linarith

/-- **`H_x ≤ R₁(U, V) < 0`**: `R₁` is affine in `(u, u_x)` with positive coefficients, and
`u ≤ U`, `u_x ≤ V`. -/
theorem urcx_R1_nonpos {z a : ℝ} (hz : 13 / 6 ≤ z) (hz2 : z ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    urcxR1 a (urcxl a) (1 + z) (urcK z a) (a + urcbp z a) (ssDg z (urcbp z a) a)
      (urcxDx z a) (ssUC z (urcbp z a)) (urcxup z a) ≤ 0 := by
  obtain ⟨ha0, hB, hK, -, -⟩ := urcx_pos hz ha
  have e := urcx_R1_aff (l := urcxl a) (S := 1 + z) (D := ssDg z (urcbp z a) a)
    (Dx := urcxDx z a) (u := ssUC z (urcbp z a))
    (v := urcxup z a) (U := urcxU z a) (V := urcxV a) ha0.ne' hB.ne' hK.ne'
  have h1 : 0 ≤ (urcxV a - urcxup z a) * (urcxMv1 a (1 + z) (urcK z a) (a + urcbp z a)
      (ssDg z (urcbp z a) a) / (a * (a + urcbp z a) * urcK z a ^ 2)) :=
    mul_nonneg (sub_nonneg.2 (urcx_up_le hz hz2 ha ha2))
      (div_pos (urcx_Mv1_pos hz hz2 ha ha2) (by positivity)).le
  have h2 : 0 ≤ (urcxU z a - ssUC z (urcbp z a)) * (urcxMu1 a (urcxl a) (1 + z) (urcK z a)
      (a + urcbp z a) (ssDg z (urcbp z a) a) (urcxDx z a) /
        (a * (a + urcbp z a) ^ 2 * urcK z a ^ 3)) :=
    mul_nonneg (sub_nonneg.2 (urcx_u_le hz hz2 ha ha2))
      (div_pos (urcx_Mu1_pos hz hz2 ha ha2) (by positivity)).le
  have hN := urcx_N1_neg hz hz2 ha ha2
  rw [← urcx_R1_eq ha0.ne' hB.ne' hK.ne'] at hN
  have h3 := neg_of_mul_neg_right hN (by positivity)
  linarith

/-- **The x comparison**: along `b = b_+(x, a)`, `u = u_C`, both
duration-tangent tests at `t ≥ 2` are at most their values at `x = 13/6`. -/
theorem urc_xmono {t x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3)
    (ht : 2 ≤ t) (ht2 : t ≤ 8 / 3) :
    urcF0 t x a (urcbp x a) (ssUC x (urcbp x a)) ≤
        urcF0 t (13 / 6) a (urcbp (13 / 6) a) (ssUC (13 / 6) (urcbp (13 / 6) a)) ∧
      urcF1 t x a (urcbp x a) (ssUC x (urcbp x a)) ≤
        urcF1 t (13 / 6) a (urcbp (13 / 6) a) (ssUC (13 / 6) (urcbp (13 / 6) a)) := by
  -- only `t ≥ 2` is used; `t ≤ 8/3` is the range of the caller's duration tangent
  have _ht2 := ht2
  have ht0 : t ≠ 0 := by linarith
  constructor
  · have h := ss_le_of_deriv (f := fun z => -urcF0 t z a (urcbp z a) (ssUC z (urcbp z a)))
      (f' := fun z => -urcxR0 a (urcxl a) (1 + z) (urcK z a) (a + urcbp z a)
        (ssDg z (urcbp z a) a) (urcxDx z a) (ssUC z (urcbp z a)) (urcxup z a)) hx
      (fun z hz => by
        obtain ⟨ha0, hB, hK, hS, hL⟩ := urcx_pos hz.1 ha
        exact (urcx_F0_deriv ht0 ha0.ne' hB.ne' hK.ne' hS.ne' hL.ne').neg)
      (fun z hz => by
        have := urcx_R0_nonpos hz.1.le (by linarith [hz.2]) ha ha2
        linarith)
    linarith
  · have h := ss_le_of_deriv (f := fun z => -urcF1 t z a (urcbp z a) (ssUC z (urcbp z a)))
      (f' := fun z => -(urcxR1 a (urcxl a) (1 + z) (urcK z a) (a + urcbp z a)
          (ssDg z (urcbp z a) a) (urcxDx z a) (ssUC z (urcbp z a)) (urcxup z a) +
        ((t - 1) / t ^ 2 - 1 / 4) *
          (urcxZ (urcxl a) (1 + z) (urcK z a) (a + urcbp z a) / (a * (a + urcbp z a) ^ 2))))
      hx
      (fun z hz => by
        obtain ⟨ha0, hB, hK, hS, hL⟩ := urcx_pos hz.1 ha
        exact (urcx_F1_deriv ht0 ha0.ne' hB.ne' hK.ne' hS.ne' hL.ne').neg)
      (fun z hz => by
        have h1 := urcx_R1_nonpos hz.1.le (by linarith [hz.2]) ha ha2
        obtain ⟨ha0, hB, -, -, -⟩ := urcx_pos hz.1.le ha
        have hZ := urcx_Z_pos hz.1.le (by linarith [hz.2]) ha ha2
        -- `φ(t) = (t - 1)/t² - 1/4 = -(t - 2)²/(4t²) ≤ 0`
        have hφ : (t - 1) / t ^ 2 - 1 / 4 ≤ 0 := by
          have e : (t - 1) / t ^ 2 - 1 / 4 = -((t - 2) ^ 2 / (4 * t ^ 2)) := by
            field_simp
            ring
          rw [e]
          have : 0 ≤ (t - 2) ^ 2 / (4 * t ^ 2) := by positivity
          linarith
        have h2 := mul_nonpos_of_nonpos_of_nonneg hφ
          (div_pos hZ (by positivity : (0 : ℝ) < a * (a + urcbp z a) ^ 2)).le
        linarith)
    linarith

end SmoothedOctagon

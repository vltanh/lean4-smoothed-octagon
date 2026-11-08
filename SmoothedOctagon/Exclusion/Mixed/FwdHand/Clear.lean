module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Coef
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Secant

/-!
# Case M2, forward successor by hand: clearing the rational substitutions

The links between the combined residual and the certificate polynomials substitute rational
values for `v`, `log q` and the floor; since `fhComb` is affine in them
(`fh_comb_sub_v`, `fh_comb_sub_L`, `fh_comb_sub_F`), the denominators are cleared once here with
abstract coefficients, so that the remaining identity is polynomial (checked by `ring`).

## Main API

* `fh_comb_dec`: `fhComb(v, L, F) = fhComb(0, 0, 0) + v C_v + L C_L + F·4qW²M`.
* `fh_clear_LR`: the cleared form of the low-ratio links.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The affine decomposition of the combined residual in `v`, `L`, `F`. -/
theorem fh_comb_dec (α M t x k q v L F : ℝ) :
    fhComb α M t x k q v L F = fhComb α M t x k q 0 0 0 + v * fhCv α M t x k q + L * fhCL α t x k q
      + F * (4 * q * (1 + x) ^ 2 * M) := by
  have e1 := fh_comb_sub_v α M t x k q v 0 L F
  have e2 := fh_comb_sub_L α M t x k q 0 L 0 F
  have e3 := fh_comb_sub_F α M t x k q 0 0 F 0
  linarith

/-- Clearing for the low-ratio links (`v = N_v/(12RW²(q + 1))`, `L = N_L/(6q(q + 1))`, `F = 0`). -/
theorem fh_clear_LR {C0 Cv CL CF Nv NL W q R : ℝ} (hW : W ≠ 0) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0)
    (hR : R ≠ 0) :
    W * q * (48 * (q + 1) * W * R * (C0 + Nv / (12 * R * W ^ 2 * (q + 1)) * Cv
      + NL / (6 * q * (q + 1)) * CL + 0 * CF)) =
      W * q * (48 * (q + 1) * W * R) * C0 + 4 * q * Nv * Cv + 8 * W ^ 2 * R * NL * CL := by
  field_simp
  ring

end SmoothedOctagon

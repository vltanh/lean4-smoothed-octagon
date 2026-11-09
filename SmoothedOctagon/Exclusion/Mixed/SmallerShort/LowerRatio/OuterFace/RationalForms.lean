module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.ReciprocalShape

/-!
# Smaller-short window, lower ratio: explicit rational forms of the outer tests

The cubic majorant at a quotient, `ℓ(p/q) = 8(p³ - q³)/(3(p + q)³)`, and the outer tests written
with polynomial denominators only (`lro_F1_expl`, `lro_F0_expl`), for substituting a terminal
curve before clearing denominators. Also two small curvature tools for the reciprocal shape:
`γ₄ = -(Su - A₀)²/576 ≤ 0` (`lrg4_nonpos`) and the termwise bound of the curvature
(`lr_curv_bound`).

## Main API

* `lr_ell_frac`, `lro_F1_expl`, `lro_F0_expl`, `lrg4_nonpos`, `lr_curv_bound`.
-/

@[expose] public section

namespace SmoothedOctagon

theorem lr_ell_frac {p q : ℝ} (hq : 0 < q) (hp : 0 < p) :
    lrell (p / q) = 8 * (p ^ 3 - q ^ 3) / (3 * (p + q) ^ 3) := by
  unfold lrell
  have h1 : p + q ≠ 0 := by positivity
  field_simp
  ring

/-- `F₁` with polynomial denominators. -/
theorem lro_F1_expl {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : 0 < a + b) :
    lroF1 x a b u = (4 * u * lroM x a - lroJ x a u ^ 2) / (576 * a ^ 4) - 7 / 96 *
      (a / (a + b) * (7 * ((lroM x a + u * ssDg x b a ^ 2 - ssDg x b a * lroJ x a u) /
        (49 * a ^ 4)) - 17 / 4) + (u - 1) * (a + b) / a - (2 * u * ssDg x b a - lroJ x a u) /
          (7 * a ^ 2) + 8 * ((2 * (a + b)) ^ 3 - (7 * a) ^ 3) / (3 * (2 * (a + b) + 7 * a) ^ 3) +
            6 / 7) - 9193 / 50000 := by
  rw [lro_F1_R1 ha.ne' hab.ne', lro_G hx ha.ne', lro_w hx ha.ne', lro_EL hx ha.ne']
  unfold lroy
  rw [lr_ell_frac (by positivity) (by positivity)]

/-- `F₀` with polynomial denominators. -/
theorem lro_F0_expl {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : 0 < a + b) :
    lroF0 x a b u = (4 * u * lroM x a - lroJ x a u ^ 2) / (576 * a ^ 4) - 7 / 96 *
      (2 * ((lroM x a + u * ssDg x b a ^ 2 - ssDg x b a * lroJ x a u) / (49 * a ^ 4)) - 1 / 2 +
        (u - 1) * (a + b) / a + a / (a + b) - 1 / 7 -
          (2 * u * ssDg x b a - lroJ x a u) / (7 * a ^ 2) +
            8 * ((2 * (a + b)) ^ 3 - (7 * a) ^ 3) / (3 * (2 * (a + b) + 7 * a) ^ 3)) -
              9193 / 50000 := by
  unfold lroF0 lroR2
  rw [lro_G hx ha.ne', lro_w hx ha.ne', lro_EL hx ha.ne']
  unfold lroy
  rw [lr_ell_frac (by positivity) (by positivity)]

/-- `γ₄ = -(Su - A₀)²/576 ≤ 0`. -/
theorem lrg4_nonpos {x u : ℝ} (hx : 0 < x) : lrb4 x u ≤ 0 := by
  have hS : (1 + x) ≠ 0 := by positivity
  have key : lrb4 x u = -((1 + x) * u - ((1 + x) - 1 + 1 / (1 + x))) ^ 2 / 576 := by
    simp only [lrb4, lrg4, lrJ2, ssE0]
    field_simp
    ring
  rw [key]
  have := sq_nonneg ((1 + x) * u - ((1 + x) - 1 + 1 / (1 + x)))
  linarith

/-- **Termwise curvature bound**: with `b₄, b₃, Q ≤ 0`,
`r ≥ 1/x`, `0 < Z_lo ≤ Z ≤ S`, the curvature is at most
`2b₂ + 6b₃/x + 2Qe²/S³ + ce²/Z_lo²`. -/
theorem lr_curv_bound {b2 b3 b4 Q d e s x S Zl : ℝ} (hb4 : b4 ≤ 0) (hb3 : b3 ≤ 0) (hQ : Q ≤ 0)
    (_hx : 0 < x) (hs : 1 / x ≤ s) (hZl : 0 < Zl) (hZ0 : Zl ≤ d + e * s) (hZ1 : d + e * s ≤ S) :
    2 * b2 + 6 * b3 * s + 12 * b4 * s ^ 2 + 2 * Q * e ^ 2 / (d + e * s) ^ 3 +
      7 / 96 * e ^ 2 / (d + e * s) ^ 2 ≤
        2 * b2 + 6 * b3 / x + 2 * Q * e ^ 2 / S ^ 3 + 7 / 96 * e ^ 2 / Zl ^ 2 := by
  have hZ : 0 < d + e * s := lt_of_lt_of_le hZl hZ0
  have h1 : 12 * b4 * s ^ 2 ≤ 0 := by nlinarith [sq_nonneg s]
  have h2 : 6 * b3 * s ≤ 6 * b3 / x := by
    have : 6 * b3 / x = 6 * b3 * (1 / x) := by ring
    rw [this]; nlinarith
  have h3 : 2 * Q * e ^ 2 / (d + e * s) ^ 3 ≤ 2 * Q * e ^ 2 / S ^ 3 := by
    have hS0 : 0 < S := lt_of_lt_of_le hZ hZ1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 := pow_le_pow_left₀ hZ.le hZ1 3
    have h6 : 2 * Q * e ^ 2 ≤ 0 := by nlinarith [sq_nonneg e]
    nlinarith [mul_le_mul_of_nonpos_left h5 h6]
  have h4 : 7 / 96 * e ^ 2 / (d + e * s) ^ 2 ≤ 7 / 96 * e ^ 2 / Zl ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hZl.le hZ0 2
  linarith

end SmoothedOctagon

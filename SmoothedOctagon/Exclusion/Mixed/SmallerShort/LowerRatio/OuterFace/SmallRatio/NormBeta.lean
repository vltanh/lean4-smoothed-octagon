module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.BetaSum

/-!
# Smaller-short window, lower ratio, outer face, small ratios: the norm and beta reductions

On the enlarged domain `1 ≤ α ≤ x ≤ 3/2`, `x ≤ β ≤ αx`,
`3/4 ≤ u ≤ 19/25` (with `A = α - 1`, `X = x - α ∈ [0, 1/2]`):

* `E_L > 0` and `w > 3/4`: both are monotone in `β` and `u`, so they are bounded
  below by their values at `β = αx`, `u = 19/25`, which are `P_E/(175α²S)`, `3/4 + P_w/(4900α⁴S)`
  (`lro_S_w`); hence `F₀ ≥ F₁` (`lro_S_F0_ge`);
* `w₀ > (19 + 2x)/28`, so `β ↦ F₁` has the convex bracket of `OuterFace/BetaSum`;
* `(R₁)_β ≤ R(x, α, u) ≤ R(x, α, 19/25) = 1/25 - P_β/(700α⁵S³)`; hence
  `F₁(β) ≥ F₁(x + (8/17)(α - 1)) - 77/176800` for `β = x + C(α - 1)`, `8/17 ≤ C ≤ 10/13`
  (`lro_S_beta`).

`R` increases in `u` because `∂_u R = 4x(x - α)/(7α³) + 1/α + D₀(KS - D₀)/(7α⁵S²) > 0`
termwise. Each polynomial sign `P > 0` on `A, X ∈ [0, 1/2]` is proved by bounding its negative
monomials termwise.

## Main API

* `lrPE`, `lrPw`, `lrP0`, `lrPb` and their signs;
* `lroRS`, `lro_S_EL`, `lro_S_w`, `lro_S_F0_ge`, `lro_S_w0`, `lro_S_beta`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `P_E(A, X)`: `E_L(x, α, αx, 19/25) = P_E/(175α²S)`, `A = α - 1`, `X = x - α`. -/
noncomputable def lrPE (A X : ℝ) : ℝ :=
  36 * A ^ 4 - 4 * A ^ 3 * X + 254 * A ^ 3 - 116 * A ^ 2 * X ^ 2 + 22 * A ^ 2 * X + 502 * A ^ 2 - 76 * A * X ^ 3 - 308 * A * X ^ 2 + 120 * A * X + 437 * A - 76 * X ^ 3 - 160 * X ^ 2 + 145 * X + 147

/-- `P_w(A, X)`: `w(x, α, αx, 19/25) = 3/4 + P_w/(4900α⁴S)`. -/
noncomputable def lrPw (A X : ℝ) : ℝ :=
  -288 * A ^ 6 * X + 144 * A ^ 6 - 560 * A ^ 5 * X ^ 2 - 2320 * A ^ 5 * X + 1441 * A ^ 5 + 48 * A ^ 4 * X ^ 3 - 4112 * A ^ 4 * X ^ 2 - 5775 * A ^ 4 * X + 4838 * A ^ 4 + 624 * A ^ 3 * X ^ 4 - 80 * A ^ 3 * X ^ 3 - 10144 * A ^ 3 * X ^ 2 - 5572 * A ^ 3 * X + 7454 * A ^ 3 + 304 * A ^ 2 * X ^ 5 + 2176 * A ^ 2 * X ^ 4 - 1008 * A ^ 2 * X ^ 3 - 11928 * A ^ 2 * X ^ 2 - 1162 * A ^ 2 * X + 5832 * A ^ 2 + 608 * A * X ^ 5 + 2224 * A * X ^ 4 - 1992 * A * X ^ 3 - 6868 * A * X ^ 2 + 1420 * A * X + 2289 * A + 304 * X ^ 5 + 672 * X ^ 4 - 1060 * X ^ 3 - 1404 * X ^ 2 + 729 * X + 370

/-- `P_0(A, X)`: `w₀(x, α, 19/25) = (19 + 2x)/28 + P_0/(4900α⁴S)`. -/
noncomputable def lrP0 (A X : ℝ) : ℝ :=
  -206 * A ^ 6 - 124 * A ^ 5 * X - 659 * A ^ 5 + 370 * A ^ 4 * X ^ 2 + 1413 * A ^ 4 * X - 62 * A ^ 4 + 288 * A ^ 3 * X ^ 3 + 3528 * A ^ 3 * X ^ 2 + 7036 * A ^ 3 * X + 1854 * A ^ 3 + 1456 * A ^ 2 * X ^ 3 + 9428 * A ^ 2 * X ^ 2 + 11534 * A ^ 2 * X + 2682 * A ^ 2 + 2304 * A * X ^ 3 + 10316 * A * X ^ 2 + 8440 * A * X + 1589 * A + 1188 * X ^ 3 + 4174 * X ^ 2 + 2381 * X + 370

/-- `P_β(A, X)`: `R(x, α, 19/25) = 1/25 - P_β/(700α⁵S³)`. -/
noncomputable def lrPb (A X : ℝ) : ℝ :=
  28 * A ^ 8 + 84 * A ^ 7 * X + 476 * A ^ 7 + 84 * A ^ 6 * X ^ 2 + 956 * A ^ 6 * X + 2580 * A ^ 6 + 28 * A ^ 5 * X ^ 3 - 124 * A ^ 5 * X ^ 2 + 3328 * A ^ 5 * X + 7461 * A ^ 5 - 1516 * A ^ 4 * X ^ 3 - 4092 * A ^ 4 * X ^ 2 + 6165 * A ^ 4 * X + 13266 * A ^ 4 - 1216 * A ^ 3 * X ^ 4 - 8792 * A ^ 3 * X ^ 3 - 13224 * A ^ 3 * X ^ 2 + 7400 * A ^ 3 * X + 14594 * A ^ 3 - 304 * A ^ 2 * X ^ 5 - 4560 * A ^ 2 * X ^ 4 - 17320 * A ^ 2 * X ^ 3 - 16860 * A ^ 2 * X ^ 2 + 6058 * A ^ 2 * X + 9556 * A ^ 2 - 608 * A * X ^ 5 - 5472 * A * X ^ 4 - 14212 * A * X ^ 3 - 8728 * A * X ^ 2 + 3292 * A * X + 3437 * A - 304 * X ^ 5 - 2128 * X ^ 4 - 4088 * X ^ 3 - 1080 * X ^ 2 + 901 * X + 538

theorem lrPE_pos {A X : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ (1 / 2 : ℝ)) (hX0 : 0 ≤ X) (hX1 : X ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) < lrPE A X := by
  unfold lrPE
  nlinarith [(by positivity : (0 : ℝ) ≤ X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X ^ 2),
    (by positivity : (0 : ℝ) ≤ A),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ X ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 4)]

theorem lrPw_pos {A X : ℝ} (hA0 : 0 ≤ A) (_hA1 : A ≤ (1 / 2 : ℝ)) (hX0 : 0 ≤ X)
    (hX1 : X ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) < lrPw A X := by
  unfold lrPw
  nlinarith [hX1,
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X ^ 2),
    (by positivity : (0 : ℝ) ≤ X ^ 4),
    (by positivity : (0 : ℝ) ≤ X ^ 5),
    (by positivity : (0 : ℝ) ≤ A),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A * X ^ 4),
    (by positivity : (0 : ℝ) ≤ A * X ^ 5),
    (by positivity : (0 : ℝ) ≤ A ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 4),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 5),
    (by positivity : (0 : ℝ) ≤ A ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 4),
    (by positivity : (0 : ℝ) ≤ A ^ 4),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 4),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 4 * X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 5),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 5),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 5 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 6)]

theorem lrP0_pos {A X : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ (1 / 2 : ℝ)) (hX0 : 0 ≤ X)
    (_hX1 : X ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) < lrP0 A X := by
  unfold lrP0
  nlinarith [(by positivity : (0 : ℝ) ≤ X),
    (by positivity : (0 : ℝ) ≤ X ^ 2),
    (by positivity : (0 : ℝ) ≤ X ^ 3),
    (by positivity : (0 : ℝ) ≤ A),
    (by positivity : (0 : ℝ) ≤ A * X),
    (by positivity : (0 : ℝ) ≤ A * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A * X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 3),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 4 * X ^ 2),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 4),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 5)]

theorem lrPb_pos {A X : ℝ} (hA0 : 0 ≤ A) (_hA1 : A ≤ (1 / 2 : ℝ)) (hX0 : 0 ≤ X)
    (hX1 : X ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) < lrPb A X := by
  unfold lrPb
  nlinarith [hX1,
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X ^ 4),
    (by positivity : (0 : ℝ) ≤ A),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X ^ 4),
    (by positivity : (0 : ℝ) ≤ A ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 4),
    (by positivity : (0 : ℝ) ≤ A ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 2),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 4),
    (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 5),
    (by positivity : (0 : ℝ) ≤ A ^ 5 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 5 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 5 * X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 6),
    (by positivity : (0 : ℝ) ≤ A ^ 6 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 6 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 7),
    (by positivity : (0 : ℝ) ≤ A ^ 7 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 8)]

/-! ### Identities at `β = αx`, `u = 19/25` -/

theorem lro_EL_ax {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lroEL x a (a * x) (19 / 25) = lrPE (a - 1) (x - a) / (175 * a ^ 2 * (1 + x)) := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [lro_EL hx ha0]
  simp only [lroJ, lroK, ssE0, ssDg, lrPE]
  field_simp
  ring

theorem lro_w_ax {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lrow x a (a * x) (19 / 25) = 3 / 4 + lrPw (a - 1) (x - a) / (4900 * a ^ 4 * (1 + x)) := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [lro_w hx ha0]
  simp only [lroM, lroJ, lroK, ssE0, ssDg, lrPw]
  field_simp
  ring

theorem lro_w0_19 {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lrow0 x a (19 / 25) = (19 + 2 * x) / 28 + lrP0 (a - 1) (x - a) / (4900 * a ^ 4 * (1 + x)) := by
  have ha0 : a ≠ 0 := ha.ne'
  simp only [lrow0, lroM, lroJ, lroK, ssE0, lroD0, lrP0]
  field_simp
  ring

/-- `R(x, α, u) = A₁ + 1/(αS) - (7w₀ - 17/4)/(αS²)`, the bound on `(R₁)_β`. -/
noncomputable def lroRS (x a u : ℝ) : ℝ :=
  lroA1 x a u + 1 / (a * (1 + x)) - (7 * lrow0 x a u - 17 / 4) / (a * (1 + x) ^ 2)

theorem lro_RS_19 {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lroRS x a (19 / 25) = 1 / 25 - lrPb (a - 1) (x - a) / (700 * a ^ 5 * (1 + x) ^ 3) := by
  have ha0 : a ≠ 0 := ha.ne'
  simp only [lroRS, lroA1, lrow0, lroM, lroJ, lroK, ssE0, lroD0, lrPb]
  field_simp
  ring

theorem lro_RS_diff {x a u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lroRS x a (19 / 25) - lroRS x a u = (19 / 25 - u) * (4 * x * (x - a) / (7 * a ^ 3) + 1 / a +
      lroD0 x a * (lroK a * (1 + x) - lroD0 x a) / (7 * a ^ 5 * (1 + x) ^ 2)) := by
  have ha0 : a ≠ 0 := ha.ne'
  simp only [lroRS, lroA1, lrow0, lroJ, ssE0]
  generalize lroM x a = M
  generalize lroD0 x a = D0
  field_simp
  ring

theorem lro_w0_diff {x a u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    lrow0 x a u - lrow0 x a (19 / 25) =
      (19 / 25 - u) * lroD0 x a * (lroK a * (1 + x) - lroD0 x a) / (49 * a ^ 4) := by
  have ha0 : a ≠ 0 := ha.ne'
  simp only [lrow0, lroJ, ssE0]
  generalize lroM x a = M
  generalize lroD0 x a = D0
  field_simp
  ring

/-! ### The S-domain bounds -/

theorem lro_KS_D0 {x a : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) :
    0 < lroD0 x a ∧ lroD0 x a < lroK a * (1 + x) := by
  unfold lroD0 lroK
  constructor
  · apply mul_pos <;> linarith
  · nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hax), mul_nonneg (sub_nonneg.2 ha1)
      (sub_nonneg.2 ha1)]

/-- `E_L > 0` on the S domain. -/
theorem lro_S_EL {x a b u : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2) (hxb : x ≤ b)
    (hbx : b ≤ a * x) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) : 0 < lroEL x a b u := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hS : lroEL x a b u - lroEL x a (a * x) (19 / 25) =
      (2 * u * (2 * (x - a) * (a * x - b)) +
        (19 / 25 - u) * (lroK a * (1 + x) - 2 * ssDg x (a * x) a)) / (7 * a ^ 2) := by
    rw [lro_EL hx0 ha.ne', lro_EL hx0 ha.ne']
    simp only [lroJ, ssE0, ssDg, lroK]
    field_simp
    ring
  have hP := lrPE_pos (A := a - 1) (X := x - a) (by linarith) (by linarith) (by linarith)
    (by linarith)
  rw [lro_EL_ax hx0 ha] at hS
  have h1 : 0 ≤ lroK a * (1 + x) - 2 * ssDg x (a * x) a := by
    unfold lroK ssDg; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hax)]
  have h2 : 0 ≤ (2 * u * (2 * (x - a) * (a * x - b)) +
      (19 / 25 - u) * (lroK a * (1 + x) - 2 * ssDg x (a * x) a)) / (7 * a ^ 2) := by
    apply div_nonneg _ (by positivity)
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * u)
      (by linarith : (0 : ℝ) ≤ 2 * (x - a))) (by linarith : (0 : ℝ) ≤ a * x - b)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 19 / 25 - u) h1]
  have h3 : 0 < lrPE (a - 1) (x - a) / (175 * a ^ 2 * (1 + x)) := by
    apply div_pos (by linarith) (by positivity)
  linarith

/-- `w ≥ 3/4 + P_w/(4900α⁴S) > 3/4` on the S domain. -/
theorem lro_S_w {x a b u : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2) (hxb : x ≤ b)
    (hbx : b ≤ a * x) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) : 3 / 4 < lrow x a b u := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hE := lro_S_EL ha1 hax hx (by nlinarith) le_rfl hu0 hu1
  have hid : lrow x a b u - lrow x a (a * x) (19 / 25) =
      ((ssDg x b a - ssDg x (a * x) a) * (u * (ssDg x b a - ssDg x (a * x) a) +
        7 * a ^ 2 * lroEL x a (a * x) u) + (19 / 25 - u) * ssDg x (a * x) a *
          (lroK a * (1 + x) - ssDg x (a * x) a)) / (49 * a ^ 4) := by
    rw [lro_w hx0 ha.ne', lro_w hx0 ha.ne', lro_EL hx0 ha.ne']
    simp only [lroJ, ssE0]
    generalize ssDg x b a = Db
    generalize ssDg x (a * x) a = Dx
    generalize lroM x a = M
    field_simp
    ring
  have hdD : ssDg x b a - ssDg x (a * x) a = 2 * (x - a) * (a * x - b) := by unfold ssDg; ring
  have hD0 : 0 < ssDg x (a * x) a := by
    unfold ssDg; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hax),
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hax)) (sub_nonneg.2 hax)]
  have hD1 : ssDg x (a * x) a ≤ lroK a * (1 + x) := by
    unfold lroK ssDg; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hax)]
  have hpos : 0 ≤ ((ssDg x b a - ssDg x (a * x) a) * (u * (ssDg x b a - ssDg x (a * x) a) +
        7 * a ^ 2 * lroEL x a (a * x) u) + (19 / 25 - u) * ssDg x (a * x) a *
          (lroK a * (1 + x) - ssDg x (a * x) a)) / (49 * a ^ 4) := by
    apply div_nonneg _ (by positivity)
    rw [hdD]
    have e1 : 0 ≤ 2 * (x - a) * (a * x - b) :=
      mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ u * (2 * (x - a) * (a * x - b)) + 7 * a ^ 2 * lroEL x a (a * x) u := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ u) e1
      have := mul_pos (by positivity : (0 : ℝ) < 7 * a ^ 2) hE
      linarith
    have e3 : 0 ≤ (19 / 25 - u) * ssDg x (a * x) a * (lroK a * (1 + x) - ssDg x (a * x) a) :=
      mul_nonneg (mul_nonneg (by linarith) hD0.le) (by linarith)
    nlinarith [mul_nonneg e1 e2]
  have hP := lrPw_pos (A := a - 1) (X := x - a) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h3 : 0 < lrPw (a - 1) (x - a) / (4900 * a ^ 4 * (1 + x)) := by
    apply div_pos (by linarith) (by positivity)
  rw [lro_w_ax hx0 ha] at hid
  linarith

/-- `F₀ ≥ F₁` on the S domain (`T ≥ 2`, `w > 3/4`). -/
theorem lro_S_F0_ge {x a b u : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2) (hxb : x ≤ b)
    (hbx : b ≤ a * x) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) :
    lroF1 x a b u ≤ lroF0 x a b u := by
  have hw := lro_S_w ha1 hax hx hxb hbx hu0 hu1
  have hT : 0 ≤ lroT a b - 2 := by
    unfold lroT
    have hab : 0 < a + b := by nlinarith
    rw [sub_nonneg, le_div_iff₀ hab]
    nlinarith
  unfold lroF1
  nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ lrow x a b u - 3 / 4)]

/-- `w₀ > (19 + 2x)/28` on the S domain for `u ≤ 19/25`. -/
theorem lro_S_w0 {x a u : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2) (hu1 : u ≤ 19 / 25) :
    (19 + 2 * x) / 28 < lrow0 x a u := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have h1 := lro_w0_diff (u := u) hx0 ha
  have h2 := lro_w0_19 hx0 ha
  obtain ⟨hD0, hD1⟩ := lro_KS_D0 ha1 hax
  have h3 : 0 ≤ (19 / 25 - u) * lroD0 x a * (lroK a * (1 + x) - lroD0 x a) / (49 * a ^ 4) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hD0.le) (by linarith)) (by positivity)
  have hP := lrP0_pos (A := a - 1) (X := x - a) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h4 : 0 < lrP0 (a - 1) (x - a) / (4900 * a ^ 4 * (1 + x)) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- **The S-branch beta loss**: for `8/17 ≤ C ≤ 10/13`,
`F₁(x, α, x + C(α - 1), u) ≥ F₁(x, α, x + (8/17)(α - 1), u) - 77/176800`. -/
theorem lro_S_beta {x a u C : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2)
    (_hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) (hC0 : 8 / 17 ≤ C) (hC1 : C ≤ 10 / 13) :
    lroF1 x a (x + 8 / 17 * (a - 1)) u - 77 / 176800 ≤ lroF1 x a (x + C * (a - 1)) u := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < 2 / (7 * a) := by positivity
  have hw0 := lro_S_w0 ha1 hax hx hu1
  set γ := a * (7 * lrow0 x a u - 17 / 4) with hγ
  have hγ2 : a * (1 + x) ≤ 2 * γ := by
    rw [hγ]; nlinarith
  have hkB : 2 / (7 * a) * (a * (1 + x)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith
  have hA1 : 0 ≤ a - 1 := by linarith
  have hinc := lr_phi_incr (p := lroA0 x a u) (q := lroA1 x a u) (γ := γ) (k := 2 / (7 * a))
    (B1 := a + x) (B2 := a * (1 + x)) (s := a + (x + 8 / 17 * (a - 1)))
    (t := a + (x + C * (a - 1))) (by linarith) hk0 hkB hγ2 (by nlinarith) (by nlinarith)
    (by nlinarith)
  -- the right-end derivative is at most `R(x, α, u) ≤ R(x, α, 19/25) < 1/25`
  have hd : lrphi1 (lroA1 x a u) γ (2 / (7 * a)) (a * (1 + x)) ≤ lroRS x a u := by
    unfold lrphi1 lroRS
    have hy : 0 < 2 / (7 * a) * (a * (1 + x)) := by positivity
    have hl := lr_ell1_le hy
    have e1 : 2 / (7 * a) * (1 / (2 / (7 * a) * (a * (1 + x)))) = 1 / (a * (1 + x)) := by
      field_simp
    have e2 : γ / (a * (1 + x)) ^ 2 = (7 * lrow0 x a u - 17 / 4) / (a * (1 + x) ^ 2) := by
      rw [hγ]; field_simp
    have := mul_le_mul_of_nonneg_left hl hk0.le
    rw [e1] at this
    rw [e2]
    linarith
  have hR : lroRS x a u ≤ lroRS x a (19 / 25) := by
    have := lro_RS_diff (u := u) hx0 ha
    obtain ⟨hD0, hD1⟩ := lro_KS_D0 ha1 hax
    have : 0 ≤ (19 / 25 - u) * (4 * x * (x - a) / (7 * a ^ 3) + 1 / a +
        lroD0 x a * (lroK a * (1 + x) - lroD0 x a) / (7 * a ^ 5 * (1 + x) ^ 2)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ 4 * x * (x - a) / (7 * a ^ 3) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have : 0 ≤ lroD0 x a * (lroK a * (1 + x) - lroD0 x a) / (7 * a ^ 5 * (1 + x) ^ 2) :=
        div_nonneg (mul_nonneg hD0.le (by linarith)) (by positivity)
      have : 0 < 1 / a := by positivity
      linarith
    linarith
  have hR19 : lroRS x a (19 / 25) ≤ 1 / 25 := by
    rw [lro_RS_19 hx0 ha]
    have hP := lrPb_pos (A := a - 1) (X := x - a) (by linarith) (by linarith) (by linarith)
      (by linarith)
    have : 0 ≤ lrPb (a - 1) (x - a) / (700 * a ^ 5 * (1 + x) ^ 3) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  have hts : 0 ≤ a + (x + C * (a - 1)) - (a + (x + 8 / 17 * (a - 1))) := by nlinarith
  have hts1 : a + (x + C * (a - 1)) - (a + (x + 8 / 17 * (a - 1))) ≤ 33 / 221 := by
    have : (C - 8 / 17) * (a - 1) ≤ (10 / 13 - 8 / 17) * (1 / 2) :=
      mul_le_mul (by linarith) (by linarith) hA1 (by norm_num)
    nlinarith
  have hphi : lrphi (lroA0 x a u) (lroA1 x a u) γ (2 / (7 * a)) (a + (x + C * (a - 1))) -
      lrphi (lroA0 x a u) (lroA1 x a u) γ (2 / (7 * a)) (a + (x + 8 / 17 * (a - 1))) ≤
        1 / 25 * (33 / 221) := by
    have h1 := mul_le_mul_of_nonneg_right (hd.trans (hR.trans hR19)) hts
    have h2 : 1 / 25 * (a + (x + C * (a - 1)) - (a + (x + 8 / 17 * (a - 1)))) ≤
        1 / 25 * (33 / 221) := by linarith
    linarith
  have hb0 : 0 < a + (x + 8 / 17 * (a - 1)) := by nlinarith
  have hb1 : 0 < a + (x + C * (a - 1)) := by nlinarith
  rw [lro_F1_B hx0 ha hb0, lro_F1_B hx0 ha hb1]
  simp only [lrphi] at hphi
  linarith

end SmoothedOctagon

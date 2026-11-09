module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestOne

/-!
# Smaller-short window, lower ratio, outer face, small shapes: signs for the test `F₀`

On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`, `x ≤ β ≤ x + (10/13)(α - 1)`,
`u_f ≤ u ≤ u_ℓ(x, β)`:

* norm concavity at the actual point reduces `u` to the two curves `u_f(x)`, `u_ℓ(x, β)`;
* `β ↦ F₀` decreases with slope `≤ -7/5120` at a fixed norm (`lro_F0_bmono`), and along the ceiling
  `u_ℓ(x, β)` as well: `(F₀)_u ≥ -1/6` on the capped strip (`(F₀)_u` is affine
  decreasing in `u` and concave in `β`) and `0 ≤ -(u_ℓ)_β ≤ 15/1992`; so `C = 10/13`;
* at `C = 10/13`, `α ↦ F₀` increases at a fixed norm: in the reciprocal shape
  `g′(r) ≤ P′(r) + ce/Z² - (399/400)ce/Z ≤ -1/400` (`ℓ′(y) ≥ (1 - (5/23)⁴)/y`, and
  `P′ = Σ i pᵢ r^{i-1}` decreases in `u ≥ 3/4`); along the ceiling the norm motion costs at most
  `(1/4)(15/1992)(10/13)` per unit of `α` since `(F₀)_u ≤ Γ_u ≤ 1/4`; so
  `α = α_*(x)`, `1` on `x ≤ 5/3`, `(45x + 22)/97` on `x ≥ 5/3`;
* the four terminal curves are positive.

The shape derivative is bounded through the reciprocal-shape form at the single slope
`C = 10/13` (two-variable signs in `(x, r)`), and the terminal curves are cleared and bounded
termwise.

## Main API

* the polynomial signs `lrPhX1_pos`, …, `lrPdA_pos` and the terminal curves `lro_B_U1f`,
  `lro_B_U1l`, `lro_B_U97f`, `lro_B_U97l`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `P′(r) = p₁ + 2p₂r + 3p₃r² + 4p₄r³`, the derivative of the polynomial part of `F₀`. -/
noncomputable def lroPd (x C u r : ℝ) : ℝ :=
  lrp1 x C u + 2 * lrp2 x C u * r + 3 * lrp3 x C u * r ^ 2 + 4 * lrp4 x C u * r ^ 3

/-- Numerator of `(F₀)_u + 1/6` at `u = 19/25`, `β = x`, `x = 3/2 + t`, `α = 1 + s`. -/
noncomputable def lrPhX1 (t s : ℝ) : ℝ :=
  -1 / 84 * t ^ 4 - 1 / 28 * t ^ 3 * s ^ 2 - 1 / 21 * t ^ 3 * s - 11 / 168 * t ^ 3 + 3 / 100 * t ^ 2 * s ^ 4 + 109 / 700 * t ^ 2 * s ^ 3 + 223 / 4200 * t ^ 2 * s ^ 2 - 91 / 600 * t ^ 2 * s - 111 / 700 * t ^ 2 + 59 / 560 * t * s ^ 4 + 1751 / 3360 * t * s ^ 3 + 97 / 210 * t * s ^ 2 - 131 / 1120 * t * s - 37 / 180 * t + 5 / 16 * s ^ 4 + 591 / 448 * s ^ 3 + 403 / 224 * s ^ 2 + 59 / 64 * s + 1 / 8

theorem lrPhX1_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 4 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 5 : ℝ)) :
    (0 : ℝ) ≤ lrPhX1 t s := by
  unfold lrPhX1
  nlinarith [(by positivity : (0 : ℝ) ≤ s),
    (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ s ^ 3),
    (by positivity : (0 : ℝ) ≤ s ^ 4),
    ht1,
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ s),
    (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t * s ^ 4),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3)]

/-- Numerator of `(F₀)_u + 1/6` at `u = 19/25`, `β = x`, `x = 7/4 + t`, `α = 4x/7 + s`. -/
noncomputable def lrPhX2 (t s : ℝ) : ℝ :=
  192 / 60025 * t ^ 6 + 192 / 8575 * t ^ 5 * s + 508 / 16807 * t ^ 5 + 72 / 1225 * t ^ 4 * s ^ 2 + 12098 / 60025 * t ^ 4 * s + 592787 / 5042100 * t ^ 4 + 12 / 175 * t ^ 3 * s ^ 3 + 16019 / 34300 * t ^ 3 * s ^ 2 + 49431 / 60025 * t ^ 3 * s + 117709 / 480200 * t ^ 3 + 3 / 100 * t ^ 2 * s ^ 4 + 2111 / 4900 * t ^ 2 * s ^ 3 + 708227 / 411600 * t ^ 2 * s ^ 2 + 368923 / 205800 * t ^ 2 * s + 17561 / 58800 * t ^ 2 + 337 / 2800 * t * s ^ 4 + 6481 / 4704 * t * s ^ 3 + 701663 / 235200 * t * s ^ 2 + 2089 / 1050 * t * s + 291233 / 1411200 * t + 477 / 1400 * s ^ 4 + 98059 / 67200 * s ^ 3 + 12271 / 6400 * s ^ 2 + 9883 / 11200 * s + 101011 / 1612800

theorem lrPhX2_pos {t s : ℝ} (ht0 : 0 ≤ t) (_ht1 : t ≤ (1 / 4 : ℝ)) (hs0 : 0 ≤ s)
    (_hs1 : s ≤ (1 / 5 : ℝ)) :
    (0 : ℝ) ≤ lrPhX2 t s := by
  unfold lrPhX2
  nlinarith [(by positivity : (0 : ℝ) ≤ s),
    (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ s ^ 3),
    (by positivity : (0 : ℝ) ≤ s ^ 4),
    (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t * s),
    (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t * s ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 5),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 6)]

/-- Numerator of `(F₀)_u + 1/6` at `u = 19/25`, `β = αx`, `x = 3/2 + t`, `α = 1 + s`. -/
noncomputable def lrPhAX1 (t s : ℝ) : ℝ :=
  -1 / 84 * t ^ 4 * s ^ 2 - 1 / 42 * t ^ 4 * s - 1 / 84 * t ^ 4 - 1 / 84 * t ^ 3 * s ^ 3 - 3 / 28 * t ^ 3 * s ^ 2 - 9 / 56 * t ^ 3 * s - 11 / 168 * t ^ 3 + 113 / 2100 * t ^ 2 * s ^ 4 + 101 / 1050 * t ^ 2 * s ^ 3 - 877 / 4200 * t ^ 2 * s ^ 2 - 1133 / 2800 * t ^ 2 * s - 111 / 700 * t ^ 2 + 569 / 3360 * t * s ^ 4 + 673 / 1680 * t * s ^ 3 - 103 / 3360 * t * s ^ 2 - 501 / 1120 * t * s - 37 / 180 * t + 159 / 448 * s ^ 4 + 69 / 56 * s ^ 3 + 47 / 32 * s ^ 2 + 47 / 64 * s + 1 / 8

theorem lrPhAX1_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 4 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 5 : ℝ)) :
    (0 : ℝ) ≤ lrPhAX1 t s := by
  unfold lrPhAX1
  nlinarith [(by positivity : (0 : ℝ) ≤ s),
    (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ s ^ 3),
    (by positivity : (0 : ℝ) ≤ s ^ 4),
    ht1,
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t * s ^ 4),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s)]

/-- Numerator of `(F₀)_u + 1/6` at `u = 19/25`, `β = αx`, `x = 7/4 + t`, `α = 4x/7 + s`. -/
noncomputable def lrPhAX2 (t s : ℝ) : ℝ :=
  -156 / 420175 * t ^ 6 + 894 / 60025 * t ^ 5 * s - 110 / 7203 * t ^ 5 + 7523 / 102900 * t ^ 4 * s ^ 2 + 3709 / 51450 * t ^ 4 * s - 146571 / 1680700 * t ^ 4 + 1633 / 14700 * t ^ 3 * s ^ 3 + 6101 / 14700 * t ^ 3 * s ^ 2 + 311519 / 1440600 * t ^ 3 * s - 44133 / 240100 * t ^ 3 + 113 / 2100 * t ^ 2 * s ^ 4 + 643 / 1200 * t ^ 2 * s ^ 3 + 1034429 / 823200 * t ^ 2 * s ^ 2 + 164239 / 274400 * t ^ 2 * s - 10127 / 78400 * t ^ 2 + 157 / 800 * t * s ^ 4 + 12815 / 9408 * t * s ^ 3 + 167621 / 78400 * t * s ^ 2 + 583 / 600 * t * s + 59183 / 1411200 * t + 26921 / 67200 * s ^ 4 + 179843 / 134400 * s ^ 3 + 111077 / 76800 * s ^ 2 + 79921 / 134400 * s + 101011 / 1612800

theorem lrPhAX2_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 4 : ℝ)) (hs0 : 0 ≤ s)
    (_hs1 : s ≤ (1 / 5 : ℝ)) :
    (0 : ℝ) ≤ lrPhAX2 t s := by
  unfold lrPhAX2
  nlinarith [(by positivity : (0 : ℝ) ≤ s),
    (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ s ^ 3),
    (by positivity : (0 : ℝ) ≤ s ^ 4),
    ht1,
    (by positivity : (0 : ℝ) ≤ t * s),
    (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t * s ^ 4),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * s),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5)]

/-- Numerator of `1/4 - Γ_u(x, α, 3/4)` at `x = 3/2 + t`, `α = 1 + s`. -/
noncomputable def lrPGu (t s : ℝ) : ℝ :=
  -1 / 32 * t ^ 2 * s ^ 4 - 1 / 8 * t ^ 2 * s ^ 3 - 5 / 32 * t ^ 2 * s ^ 2 - 1 / 16 * t ^ 2 * s - 1 / 1152 * t ^ 2 - 5 / 32 * t * s ^ 4 - 5 / 8 * t * s ^ 3 - 73 / 96 * t * s ^ 2 - 13 / 48 * t * s + 23 / 1152 * t - 9 / 128 * s ^ 4 - 9 / 32 * s ^ 3 - 83 / 384 * s ^ 2 + 25 / 192 * s + 623 / 4608

theorem lrPGu_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 2 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 5 : ℝ)) :
    (0 : ℝ) ≤ lrPGu t s := by
  unfold lrPGu
  nlinarith [mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 3),
    ht1,
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3)]

/-- `-∂_u P′(x, 3/4, r)` at `C = 10/13`, `x = 3/2 + t`, `r = 5/6 + s`. -/
noncomputable def lrPdA (t s : ℝ) : ℝ :=
  1 / 21 * t ^ 4 * s ^ 3 + 5 / 42 * t ^ 4 * s ^ 2 + 25 / 252 * t ^ 4 * s + 125 / 4536 * t ^ 4 + 11 / 78 * t ^ 3 * s ^ 3 + 367 / 1092 * t ^ 3 * s ^ 2 + 2213 / 6552 * t ^ 3 * s + 2185 / 16848 * t ^ 3 + 24329 / 340704 * t ^ 2 * s ^ 3 + 125605 / 681408 * t ^ 2 * s ^ 2 + 2091641 / 4088448 * t ^ 2 * s + 24388837 / 73592064 * t ^ 2 - 19651 / 340704 * t * s ^ 3 - 9233 / 97344 * t * s ^ 2 + 292451 / 584064 * t * s + 37865641 / 73592064 * t - 21487 / 1362816 * s ^ 3 - 1433 / 29952 * s ^ 2 + 3287825 / 16353792 * s + 6510961 / 22643712

theorem lrPdA_pos {t s : ℝ} (ht0 : 0 ≤ t) (_ht1 : t ≤ (1 / 2 : ℝ)) (hs0 : 0 ≤ s)
    (hs1 : s ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) ≤ lrPdA t s := by
  unfold lrPdA
  nlinarith [(by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s),
    mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 3)]

theorem lro_B_U1f_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) < -11 / 147 * z ^ 9 - 79 / 42 * z ^ 8 - 89507 / 4704 * z ^ 7 - 116857 / 1176 * z ^ 6 - 25499903491 / 88200000 * z ^ 5 - 42840292793 / 88200000 * z ^ 4 - 359049638669 / 705600000 * z ^ 3 - 123248137109 / 352800000 * z ^ 2 - 237180901 / 5040000 * z + 28871623 / 504000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8)]

theorem lro_B_U1f_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (5 / 3 : ℝ)) :
    lroF0 x (1) (x) (ssUf x) - (0 : ℝ) = (-11 / 147 * (x - (3 / 2 : ℝ)) ^ 9 - 79 / 42 * (x - (3 / 2 : ℝ)) ^ 8 - 89507 / 4704 * (x - (3 / 2 : ℝ)) ^ 7 - 116857 / 1176 * (x - (3 / 2 : ℝ)) ^ 6 - 25499903491 / 88200000 * (x - (3 / 2 : ℝ)) ^ 5 - 42840292793 / 88200000 * (x - (3 / 2 : ℝ)) ^ 4 - 359049638669 / 705600000 * (x - (3 / 2 : ℝ)) ^ 3 - 123248137109 / 352800000 * (x - (3 / 2 : ℝ)) ^ 2 - 237180901 / 5040000 * (x - (3 / 2 : ℝ)) + 28871623 / 504000) /
      ((x + 1) ^ 2 * (2 * x + 9) ^ 3) := by
  rw [lro_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (1) + (x) = (x + 1) / (1 : ℝ) by ring,
    show 2 * ((x + 1) / (1 : ℝ)) + 7 * (1) = (2 * x + 9) / (1 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg, ssUf]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : 2 * x + 9 ≠ 0 := by nlinarith
  have hp0 : x + 1 ≠ 0 := by nlinarith
  have hq0 : 2 * x + 9 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : x + 1 = p at hp0 ⊢
  generalize hq : 2 * x + 9 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_U1f {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF0 x (1) (x) (ssUf x) := by
  have hid := lro_B_U1f_id h0 h1
  have hn := lro_B_U1f_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x + 9 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (2 * x + 9) ^ 3 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 3))
  have : 0 < lroF0 x (1) (x) (ssUf x) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_U1l_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) < -565 / 6 * z ^ 11 - 228653 / 84 * z ^ 10 - 29760023 / 896 * z ^ 9 - 200719275 / 896 * z ^ 8 - 3723343957621 / 4032000 * z ^ 7 - 1540346718769 / 630000 * z ^ 6 - 1731591386210549 / 403200000 * z ^ 5 - 2067360180037667 / 403200000 * z ^ 4 - 6592646350394563 / 1612800000 * z ^ 3 - 1422774715433003 / 806400000 * z ^ 2 + 855927072977 / 26880000 * z + 1961576203087 / 8064000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10)]

theorem lro_B_U1l_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (5 / 3 : ℝ)) :
    lroF0 x (1) (x) (ssUl x x) - (0 : ℝ) = (-565 / 6 * (x - (3 / 2 : ℝ)) ^ 11 - 228653 / 84 * (x - (3 / 2 : ℝ)) ^ 10 - 29760023 / 896 * (x - (3 / 2 : ℝ)) ^ 9 - 200719275 / 896 * (x - (3 / 2 : ℝ)) ^ 8 - 3723343957621 / 4032000 * (x - (3 / 2 : ℝ)) ^ 7 - 1540346718769 / 630000 * (x - (3 / 2 : ℝ)) ^ 6 - 1731591386210549 / 403200000 * (x - (3 / 2 : ℝ)) ^ 5 - 2067360180037667 / 403200000 * (x - (3 / 2 : ℝ)) ^ 4 - 6592646350394563 / 1612800000 * (x - (3 / 2 : ℝ)) ^ 3 - 1422774715433003 / 806400000 * (x - (3 / 2 : ℝ)) ^ 2 + 855927072977 / 26880000 * (x - (3 / 2 : ℝ)) + 1961576203087 / 8064000) /
      ((x + 1) ^ 2 * (35 * x + 13) ^ 2 * (2 * x + 9) ^ 3) := by
  rw [lro_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (1) + (x) = (x + 1) / (1 : ℝ) by ring,
    show 2 * ((x + 1) / (1 : ℝ)) + 7 * (1) = (2 * x + 9) / (1 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg, ssUl]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : 35 * x + 13 ≠ 0 := by nlinarith
  have hd2 : 2 * x + 9 ≠ 0 := by nlinarith
  have hp0 : x + 1 ≠ 0 := by nlinarith
  have hq0 : 2 * x + 9 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : x + 1 = p at hp0 ⊢
  generalize hq : 2 * x + 9 = q at hq0 ⊢
  have hLx0 : x - 1 ≠ 0 := by nlinarith
  generalize hLx : x - 1 = Lx at hLx0 ⊢
  have hLz0 : 35 * x + 13 ≠ 0 := by nlinarith
  generalize hLz : 35 * x + 13 = Lz at hLz0 ⊢
  field_simp
  subst hp hq hLx hLz
  ring

theorem lro_B_U1l {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF0 x (1) (x) (ssUl x x) := by
  have hid := lro_B_U1l_id h0 h1
  have hn := lro_B_U1l_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 35 * x + 13 := by nlinarith
  have hP2 : 0 < 2 * x + 9 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (35 * x + 13) ^ 2 * (2 * x + 9) ^ 3 := (mul_pos (mul_pos (pow_pos hP0 2) (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF0 x (1) (x) (ssUl x x) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_U97f_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 3 : ℝ)) :
    (0 : ℝ) < -141705871639236725625 / 64 * z ^ 12 - 1070707538682984243825 / 32 * z ^ 11 - 983182314545603902405109 / 3840 * z ^ 10 - 1833848980322619136963641431 / 1310400 * z ^ 9 - 4753628148567551382195902042911 / 794976000 * z ^ 8 - 172895166291578251318256372781107 / 8943480000 * z ^ 7 - 751667603870589823079782154896249 / 16769025000 * z ^ 6 - 735054788368249761228537109103401 / 10319400000 * z ^ 5 - 2087917905693597895831567622793389 / 28576800000 * z ^ 4 - 128494780213520337819007075291489 / 3061800000 * z ^ 3 - 531879232640077330224334068829489 / 85730400000 * z ^ 2 + 131930143469966991783606243108461 / 20667150000 * z + 171021499204505973044820195125599 / 62001450000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem lro_B_U97f_id {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF0 x ((45 * x + 22) / 97) (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) (ssUf x) - (0 : ℝ) = (-141705871639236725625 / 64 * (x - (5 / 3 : ℝ)) ^ 12 - 1070707538682984243825 / 32 * (x - (5 / 3 : ℝ)) ^ 11 - 983182314545603902405109 / 3840 * (x - (5 / 3 : ℝ)) ^ 10 - 1833848980322619136963641431 / 1310400 * (x - (5 / 3 : ℝ)) ^ 9 - 4753628148567551382195902042911 / 794976000 * (x - (5 / 3 : ℝ)) ^ 8 - 172895166291578251318256372781107 / 8943480000 * (x - (5 / 3 : ℝ)) ^ 7 - 751667603870589823079782154896249 / 16769025000 * (x - (5 / 3 : ℝ)) ^ 6 - 735054788368249761228537109103401 / 10319400000 * (x - (5 / 3 : ℝ)) ^ 5 - 2087917905693597895831567622793389 / 28576800000 * (x - (5 / 3 : ℝ)) ^ 4 - 128494780213520337819007075291489 / 3061800000 * (x - (5 / 3 : ℝ)) ^ 3 - 531879232640077330224334068829489 / 85730400000 * (x - (5 / 3 : ℝ)) ^ 2 + 131930143469966991783606243108461 / 20667150000 * (x - (5 / 3 : ℝ)) + 171021499204505973044820195125599 / 62001450000) /
      ((287 * x - 58) * (x + 1) ^ 2 * (8687 * x + 1074) ^ 3 * (45 * x + 22) ^ 4) := by
  rw [lro_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show ((45 * x + 22) / 97) + (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) = (287 * x - 58) / (1261 / 8 : ℝ) by ring,
    show 2 * ((287 * x - 58) / (1261 / 8 : ℝ)) + 7 * ((45 * x + 22) / 97) = (8687 * x + 1074) / (1261 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg, ssUf]
  have hd0 : 287 * x - 58 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 8687 * x + 1074 ≠ 0 := by nlinarith
  have hd3 : 45 * x + 22 ≠ 0 := by nlinarith
  have hp0 : 287 * x - 58 ≠ 0 := by nlinarith
  have hq0 : 8687 * x + 1074 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 287 * x - 58 = p at hp0 ⊢
  generalize hq : 8687 * x + 1074 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_U97f {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF0 x ((45 * x + 22) / 97) (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) (ssUf x) := by
  have hid := lro_B_U97f_id h0 h1
  have hn := lro_B_U97f_num (z := x - (5 / 3 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 287 * x - 58 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 8687 * x + 1074 := by nlinarith
  have hP3 : 0 < 45 * x + 22 := by nlinarith
  have hD : 0 < (287 * x - 58) * (x + 1) ^ 2 * (8687 * x + 1074) ^ 3 * (45 * x + 22) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF0 x ((45 * x + 22) / 97) (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) (ssUf x) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_U97l_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 3 : ℝ)) :
    (0 : ℝ) < -118493442194276523355269080625 / 16 * z ^ 16 - 2338499036774983530599312844375 / 16 * z ^ 15 - 1103048163917892725080604310674245 / 768 * z ^ 14 - 18270465380437857391113785018270833 / 1872 * z ^ 13 - 18905402477640216948787011491925374051 / 365040 * z ^ 12 - 2398479369577953870461380514343924380107 / 10951200 * z ^ 11 - 3327586385490572843366373174659437181196341 / 4599504000 * z ^ 10 - 31494095112623452239266752090453292216597983 / 17248140000 * z ^ 9 - 597397575273106487364152510742843033761609521 / 172481400000 * z ^ 8 - 96616042974348237469877301136636557959308031 / 19901700000 * z ^ 7 - 25685610760101888562969300241472626225569987 / 5248800000 * z ^ 6 - 138887696867703675213128959328690408260837367 / 41334300000 * z ^ 5 - 339408657959279863538117985848907488706066391 / 248005800000 * z ^ 4 - 14250546839462342360482119026213072853172019 / 93002175000 * z ^ 3 + 75743557520603752625076433163541652778355091 / 558013050000 * z ^ 2 + 1369809228862637997756250285520235330077534 / 20925489375 * z + 11656267493955296736437180160935544886067659 / 1255529362500 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 12),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 13),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 14),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 15)]

theorem lro_B_U97l_id {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF0 x ((45 * x + 22) / 97) (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) (ssUl x (x + 10 / 13 * ((45 * x + 22) / 97 - 1))) - (0 : ℝ) = (-118493442194276523355269080625 / 16 * (x - (5 / 3 : ℝ)) ^ 16 - 2338499036774983530599312844375 / 16 * (x - (5 / 3 : ℝ)) ^ 15 - 1103048163917892725080604310674245 / 768 * (x - (5 / 3 : ℝ)) ^ 14 - 18270465380437857391113785018270833 / 1872 * (x - (5 / 3 : ℝ)) ^ 13 - 18905402477640216948787011491925374051 / 365040 * (x - (5 / 3 : ℝ)) ^ 12 - 2398479369577953870461380514343924380107 / 10951200 * (x - (5 / 3 : ℝ)) ^ 11 - 3327586385490572843366373174659437181196341 / 4599504000 * (x - (5 / 3 : ℝ)) ^ 10 - 31494095112623452239266752090453292216597983 / 17248140000 * (x - (5 / 3 : ℝ)) ^ 9 - 597397575273106487364152510742843033761609521 / 172481400000 * (x - (5 / 3 : ℝ)) ^ 8 - 96616042974348237469877301136636557959308031 / 19901700000 * (x - (5 / 3 : ℝ)) ^ 7 - 25685610760101888562969300241472626225569987 / 5248800000 * (x - (5 / 3 : ℝ)) ^ 6 - 138887696867703675213128959328690408260837367 / 41334300000 * (x - (5 / 3 : ℝ)) ^ 5 - 339408657959279863538117985848907488706066391 / 248005800000 * (x - (5 / 3 : ℝ)) ^ 4 - 14250546839462342360482119026213072853172019 / 93002175000 * (x - (5 / 3 : ℝ)) ^ 3 + 75743557520603752625076433163541652778355091 / 558013050000 * (x - (5 / 3 : ℝ)) ^ 2 + 1369809228862637997756250285520235330077534 / 20925489375 * (x - (5 / 3 : ℝ)) + 11656267493955296736437180160935544886067659 / 1255529362500) /
      ((287 * x - 58) * (x + 1) ^ 2 * (35 * x + 13) ^ 2 * (1711 * x - 2011) ^ 2 * (8687 * x + 1074) ^ 3 * (45 * x + 22) ^ 4) := by
  rw [lro_F0_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show ((45 * x + 22) / 97) + (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) = (287 * x - 58) / (1261 / 8 : ℝ) by ring,
    show 2 * ((287 * x - 58) / (1261 / 8 : ℝ)) + 7 * ((45 * x + 22) / 97) = (8687 * x + 1074) / (1261 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg, ssUl]
  rw [show x + 10 / 13 * ((45 * x + 22) / 97 - 1) - 1 = (1711 * x - 2011) / 1261 by ring]
  have hd0 : 287 * x - 58 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 35 * x + 13 ≠ 0 := by nlinarith
  have hd3 : 1711 * x - 2011 ≠ 0 := by nlinarith
  have hd4 : 8687 * x + 1074 ≠ 0 := by nlinarith
  have hd5 : 45 * x + 22 ≠ 0 := by nlinarith
  have hp0 : 287 * x - 58 ≠ 0 := by nlinarith
  have hq0 : 8687 * x + 1074 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 287 * x - 58 = p at hp0 ⊢
  generalize hq : 8687 * x + 1074 = q at hq0 ⊢
  have hLz0 : 35 * x + 13 ≠ 0 := by nlinarith
  generalize hLz : 35 * x + 13 = Lz at hLz0 ⊢
  have hLb0 : 1711 * x - 2011 ≠ 0 := by nlinarith
  generalize hLb : 1711 * x - 2011 = Lb at hLb0 ⊢
  field_simp
  subst hp hq hLz hLb
  ring

theorem lro_B_U97l {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF0 x ((45 * x + 22) / 97) (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) (ssUl x (x + 10 / 13 * ((45 * x + 22) / 97 - 1))) := by
  have hid := lro_B_U97l_id h0 h1
  have hn := lro_B_U97l_num (z := x - (5 / 3 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 287 * x - 58 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 35 * x + 13 := by nlinarith
  have hP3 : 0 < 1711 * x - 2011 := by nlinarith
  have hP4 : 0 < 8687 * x + 1074 := by nlinarith
  have hP5 : 0 < 45 * x + 22 := by nlinarith
  have hD : 0 < (287 * x - 58) * (x + 1) ^ 2 * (35 * x + 13) ^ 2 * (1711 * x - 2011) ^ 2 * (8687 * x + 1074) ^ 3 * (45 * x + 22) ^ 4 := (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 2)) (pow_pos hP3 2)) (pow_pos hP4 3)) (pow_pos hP5 4))
  have : 0 < lroF0 x ((45 * x + 22) / 97) (x + 10 / 13 * ((45 * x + 22) / 97 - 1)) (ssUl x (x + 10 / 13 * ((45 * x + 22) / 97 - 1))) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


end SmoothedOctagon

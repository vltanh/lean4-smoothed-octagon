module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Defs

/-!
# Smaller-short window, upper ratio: the central x comparison, the seven polynomial signs

The signs used by the central x comparison, in cleared form. With `X = x - 13/6 ∈ [0, 7/30]`,
`A = 4/3 - a ∈ [0, 1/3]`, each statement below is a polynomial in `(X, A)` once the atoms
`S, K, B, D, D_x, ℓ, U, V` are substituted; `linarith` expands it and a termwise rule applies:
every term of total degree at most two is kept, a term of total degree at least three is
discarded when it has the favourable sign and is otherwise bounded by its value at the far corner
times `A²/(1/3)²` (when its `A`-degree is at least two) or `X²/(7/30)²` (`urcx_box`). The
resulting quadratic has the required sign on the rectangle by `A² ≤ A/3`, `XA ≤ X/3` and the
nonnegativity of `X, A, X², XA, A²`.

The exact cleared numerators `N₀ = aB²K⁴R₀` (134 monomials, degree 17), `N₁ = aB²K³R₁`
(99 monomials, degree 14) and the cleared coefficients `M_v, M_u` are bounded directly by this
termwise rule; no coefficient table is printed, the polynomials are the products of the
primitives of `Ratio/Defs` and are expanded by `linarith` itself. The resulting quadratic
bounds are `N₀ ≤ -1501.7 + 3100.7A + 2203.5A² - 17392X - 37078XA - 67329X²` and
`N₁ ≤ -274.4 + 281.6A + 967.6A² - 2068X - 315XA - 4942X²` (coefficients rounded). The two
numerator signs raise `maxRecDepth` to 2000 for the normalization inside `linarith`.

## Main API

* `urcx_N0_neg`, `urcx_N1_neg`: `R₀(U, V) < 0`, `R₁(U, V) < 0` in cleared form.
* `urcx_Mv0_pos`, `urcx_Mu0_pos`, `urcx_Mv1_pos`, `urcx_Mu1_pos`: the incoming coefficients
  `C` and `C_x` of both tests are positive.
* `urcx_Z_pos`: `Z = 2SB - ℓK > 0`, so `T_x > 0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

set_option maxRecDepth 2000 in
/-- **`N₀ < 0`** (cleared form): `aB²K⁴R₀(U, V) < 0`. -/
theorem urcx_N0_neg {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    urcxN0 a (urcxl a) (1 + x) (urcK x a) (a + urcbp x a) (ssDg x (urcbp x a) a)
      (urcxDx x a) (urcxU x a) (urcxV a) < 0 := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxN0 urcxPa urcxP1 urcxP2 urcxG0 urcxC0 urcxH0 urcxH1 urcxE0 urcxE1
    urcxDx urcxU urcxV urcxl urcK urcbp ssDg
  linarith [hAA 11 5 (by norm_num), hm 11 4, hm 11 3, hAA 11 2 (by norm_num), hm 11 1,
    hXX 11 0 (by norm_num), hm 10 7, hAA 10 6 (by norm_num), hAA 10 5 (by norm_num), hm 10 4,
    hAA 10 3 (by norm_num), hAA 10 2 (by norm_num), hm 10 1, hXX 10 0 (by norm_num), hm 9 8, hm 9 7,
    hAA 9 6 (by norm_num), hm 9 5, hm 9 4, hAA 9 3 (by norm_num), hm 9 2, hm 9 1,
    hXX 9 0 (by norm_num), hm 8 9, hm 8 8, hAA 8 7 (by norm_num), hAA 8 6 (by norm_num), hm 8 5,
    hm 8 4, hAA 8 3 (by norm_num), hm 8 2, hXX 8 1 (by norm_num), hm 8 0, hm 7 10, hm 7 9, hm 7 8,
    hAA 7 7 (by norm_num), hAA 7 6 (by norm_num), hm 7 5, hAA 7 4 (by norm_num),
    hAA 7 3 (by norm_num), hm 7 2, hXX 7 1 (by norm_num), hm 7 0, hAA 6 11 (by norm_num), hm 6 10,
    hm 6 9, hm 6 8, hAA 6 7 (by norm_num), hm 6 6, hm 6 5, hAA 6 4 (by norm_num), hm 6 3, hm 6 2,
    hXX 6 1 (by norm_num), hm 6 0, hAA 5 12 (by norm_num), hAA 5 11 (by norm_num), hm 5 10, hm 5 9,
    hAA 5 8 (by norm_num), hAA 5 7 (by norm_num), hm 5 6, hAA 5 5 (by norm_num),
    hAA 5 4 (by norm_num), hm 5 3, hAA 5 2 (by norm_num), hXX 5 1 (by norm_num), hm 5 0,
    hAA 4 12 (by norm_num), hAA 4 11 (by norm_num), hm 4 10, hm 4 9, hAA 4 8 (by norm_num), hm 4 7,
    hm 4 6, hAA 4 5 (by norm_num), hm 4 4, hm 4 3, hAA 4 2 (by norm_num), hXX 4 1 (by norm_num),
    hm 4 0, hAA 3 12 (by norm_num), hAA 3 11 (by norm_num), hm 3 10, hm 3 9, hAA 3 8 (by norm_num),
    hm 3 7, hAA 3 6 (by norm_num), hAA 3 5 (by norm_num), hm 3 4, hAA 3 3 (by norm_num),
    hAA 3 2 (by norm_num), hm 3 1, hm 3 0, hAA 2 12 (by norm_num), hAA 2 11 (by norm_num), hm 2 10,
    hm 2 9, hAA 2 8 (by norm_num), hm 2 7, hAA 2 6 (by norm_num), hAA 2 5 (by norm_num), hm 2 4,
    hAA 2 3 (by norm_num), hm 2 2, hm 2 1, hAA 1 12 (by norm_num), hAA 1 11 (by norm_num), hm 1 10,
    hAA 1 9 (by norm_num), hAA 1 8 (by norm_num), hm 1 7, hAA 1 6 (by norm_num), hm 1 5, hm 1 4,
    hAA 1 3 (by norm_num), hm 1 2, hAA 0 12 (by norm_num), hAA 0 11 (by norm_num), hm 0 10,
    hAA 0 9 (by norm_num), hAA 0 8 (by norm_num), hm 0 7, hAA 0 6 (by norm_num), hm 0 5,
    hAA 0 4 (by norm_num), hAA 0 3 (by norm_num), hX, hA, hX', hA', mul_nonneg hX hA,
    mul_nonneg hX hX, mul_nonneg hA hA, mul_nonneg hX (sub_nonneg.2 hA'),
    mul_nonneg hA (sub_nonneg.2 hA'), mul_nonneg hX (sub_nonneg.2 hX'),
    mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

set_option maxRecDepth 2000 in
/-- **`N₁ < 0`** (cleared form): `aB²K³R₁(U, V) < 0`. -/
theorem urcx_N1_neg {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    urcxN1 a (urcxl a) (1 + x) (urcK x a) (a + urcbp x a) (ssDg x (urcbp x a) a)
      (urcxDx x a) (urcxU x a) (urcxV a) < 0 := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxN1 urcxPa urcxP1 urcxP2 urcxG1 urcxC1 urcxH0 urcxH1 urcxE0 urcxE1
    urcxDx urcxU urcxV urcxl urcK urcbp ssDg
  linarith [hAA 10 3 (by norm_num), hAA 10 2 (by norm_num), hm 10 1, hXX 10 0 (by norm_num),
    hAA 9 5 (by norm_num), hm 9 4, hAA 9 3 (by norm_num), hm 9 2, hm 9 1, hXX 9 0 (by norm_num),
    hAA 8 6 (by norm_num), hAA 8 5 (by norm_num), hm 8 4, hAA 8 3 (by norm_num), hm 8 2,
    hXX 8 1 (by norm_num), hXX 8 0 (by norm_num), hAA 7 7 (by norm_num), hAA 7 6 (by norm_num),
    hAA 7 5 (by norm_num), hm 7 4, hAA 7 3 (by norm_num), hm 7 2, hXX 7 1 (by norm_num), hm 7 0,
    hAA 6 8 (by norm_num), hAA 6 7 (by norm_num), hAA 6 6 (by norm_num), hAA 6 5 (by norm_num),
    hm 6 4, hAA 6 3 (by norm_num), hm 6 2, hXX 6 1 (by norm_num), hm 6 0, hm 5 9,
    hAA 5 8 (by norm_num), hAA 5 7 (by norm_num), hm 5 6, hm 5 5, hAA 5 4 (by norm_num),
    hAA 5 3 (by norm_num), hm 5 2, hXX 5 1 (by norm_num), hm 5 0, hm 4 10, hm 4 9,
    hAA 4 8 (by norm_num), hAA 4 7 (by norm_num), hm 4 6, hm 4 5, hAA 4 4 (by norm_num), hm 4 3,
    hm 4 2, hXX 4 1 (by norm_num), hm 4 0, hm 3 10, hm 3 9, hm 3 8, hAA 3 7 (by norm_num), hm 3 6,
    hAA 3 5 (by norm_num), hAA 3 4 (by norm_num), hm 3 3, hAA 3 2 (by norm_num),
    hXX 3 1 (by norm_num), hm 3 0, hm 2 10, hm 2 9, hm 2 8, hAA 2 7 (by norm_num), hm 2 6,
    hAA 2 5 (by norm_num), hm 2 4, hm 2 3, hAA 2 2 (by norm_num), hXX 2 1 (by norm_num), hm 1 10,
    hm 1 9, hm 1 8, hAA 1 7 (by norm_num), hm 1 6, hAA 1 5 (by norm_num), hm 1 4,
    hAA 1 3 (by norm_num), hAA 1 2 (by norm_num), hm 0 10, hm 0 9, hAA 0 8 (by norm_num),
    hAA 0 7 (by norm_num), hm 0 6, hAA 0 5 (by norm_num), hm 0 4, hAA 0 3 (by norm_num), hX, hA,
    hX', hA', mul_nonneg hX hA, mul_nonneg hX hX, mul_nonneg hA hA,
    mul_nonneg hX (sub_nonneg.2 hA'), mul_nonneg hA (sub_nonneg.2 hA'),
    mul_nonneg hX (sub_nonneg.2 hX'), mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

/-- `C > 0` for the first test (cleared form). -/
theorem urcx_Mv0_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    0 < urcxMv0 a (1 + x) (urcK x a) (a + urcbp x a) (ssDg x (urcbp x a) a) := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxMv0 urcxG0 urcK urcbp ssDg
  linarith [hm 7 2, hXX 7 1 (by norm_num), hm 7 0, hAA 6 4 (by norm_num), hm 6 3, hm 6 2,
    hXX 6 1 (by norm_num), hm 6 0, hAA 5 5 (by norm_num), hAA 5 4 (by norm_num), hm 5 3,
    hAA 5 2 (by norm_num), hXX 5 1 (by norm_num), hm 5 0, hm 4 6, hAA 4 5 (by norm_num), hm 4 4,
    hm 4 3, hAA 4 2 (by norm_num), hXX 4 1 (by norm_num), hm 4 0, hm 3 7, hm 3 6,
    hAA 3 5 (by norm_num), hm 3 4, hm 3 3, hAA 3 2 (by norm_num), hXX 3 1 (by norm_num), hm 3 0,
    hm 2 7, hAA 2 6 (by norm_num), hAA 2 5 (by norm_num), hm 2 4, hAA 2 3 (by norm_num),
    hAA 2 2 (by norm_num), hXX 2 1 (by norm_num), hm 1 7, hAA 1 6 (by norm_num),
    hAA 1 5 (by norm_num), hm 1 4, hAA 1 3 (by norm_num), hAA 1 2 (by norm_num), hm 0 7,
    hAA 0 6 (by norm_num), hm 0 5, hm 0 4, hAA 0 3 (by norm_num), hX, hA, hX', hA',
    mul_nonneg hX hA, mul_nonneg hX hX, mul_nonneg hA hA, mul_nonneg hX (sub_nonneg.2 hA'),
    mul_nonneg hA (sub_nonneg.2 hA'), mul_nonneg hX (sub_nonneg.2 hX'),
    mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

/-- `C_x > 0` for the first test (cleared form). -/
theorem urcx_Mu0_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    0 < urcxMu0 a (urcxl a) (1 + x) (urcK x a) (a + urcbp x a) (ssDg x (urcbp x a) a)
      (urcxDx x a) := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxMu0 urcxG0 urcxC0 urcxDx urcxl urcK urcbp ssDg
  linarith [hm 8 2, hXX 8 1 (by norm_num), hm 8 0, hm 7 2, hXX 7 1 (by norm_num), hm 7 0, hm 6 5,
    hm 6 4, hAA 6 3 (by norm_num), hm 6 2, hXX 6 1 (by norm_num), hm 6 0, hAA 5 6 (by norm_num),
    hm 5 5, hAA 5 4 (by norm_num), hAA 5 3 (by norm_num), hm 5 2, hXX 5 1 (by norm_num), hm 5 0,
    hAA 4 7 (by norm_num), hAA 4 6 (by norm_num), hm 4 5, hAA 4 4 (by norm_num),
    hAA 4 3 (by norm_num), hm 4 2, hXX 4 1 (by norm_num), hm 4 0, hm 3 8, hAA 3 7 (by norm_num),
    hm 3 6, hm 3 5, hAA 3 4 (by norm_num), hm 3 3, hm 3 2, hXX 3 1 (by norm_num), hm 3 0, hm 2 9,
    hm 2 8, hAA 2 7 (by norm_num), hm 2 6, hAA 2 5 (by norm_num), hAA 2 4 (by norm_num), hm 2 3,
    hm 2 2, hXX 2 1 (by norm_num), hm 1 9, hAA 1 8 (by norm_num), hAA 1 7 (by norm_num), hm 1 6,
    hAA 1 5 (by norm_num), hAA 1 4 (by norm_num), hm 1 3, hAA 1 2 (by norm_num), hm 0 9,
    hAA 0 8 (by norm_num), hAA 0 7 (by norm_num), hm 0 6, hAA 0 5 (by norm_num), hm 0 4, hm 0 3, hX,
    hA, hX', hA', mul_nonneg hX hA, mul_nonneg hX hX, mul_nonneg hA hA,
    mul_nonneg hX (sub_nonneg.2 hA'), mul_nonneg hA (sub_nonneg.2 hA'),
    mul_nonneg hX (sub_nonneg.2 hX'), mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

/-- `C > 0` for the second test (cleared form). -/
theorem urcx_Mv1_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    0 < urcxMv1 a (1 + x) (urcK x a) (a + urcbp x a) (ssDg x (urcbp x a) a) := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxMv1 urcxG1 urcK urcbp ssDg
  linarith [hXX 7 1 (by norm_num), hm 7 0, hAA 6 3 (by norm_num), hm 6 2, hXX 6 1 (by norm_num),
    hm 6 0, hAA 5 4 (by norm_num), hAA 5 3 (by norm_num), hm 5 2, hXX 5 1 (by norm_num), hm 5 0,
    hm 4 5, hAA 4 4 (by norm_num), hAA 4 3 (by norm_num), hm 4 2, hXX 4 1 (by norm_num), hm 4 0,
    hm 3 6, hm 3 5, hAA 3 4 (by norm_num), hm 3 3, hm 3 2, hXX 3 1 (by norm_num), hm 3 0, hm 2 6,
    hm 2 5, hAA 2 4 (by norm_num), hm 2 3, hm 2 2, hXX 2 1 (by norm_num), hm 1 6,
    hAA 1 5 (by norm_num), hAA 1 4 (by norm_num), hm 1 3, hm 1 2, hm 0 6, hAA 0 5 (by norm_num),
    hm 0 4, hAA 0 3 (by norm_num), hX, hA, hX', hA', mul_nonneg hX hA, mul_nonneg hX hX,
    mul_nonneg hA hA, mul_nonneg hX (sub_nonneg.2 hA'), mul_nonneg hA (sub_nonneg.2 hA'),
    mul_nonneg hX (sub_nonneg.2 hX'), mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

/-- `C_x > 0` for the second test (cleared form). -/
theorem urcx_Mu1_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    0 < urcxMu1 a (urcxl a) (1 + x) (urcK x a) (a + urcbp x a) (ssDg x (urcbp x a) a)
      (urcxDx x a) := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxMu1 urcxG1 urcxC1 urcxDx urcxl urcK urcbp ssDg
  linarith [hm 9 2, hXX 9 1 (by norm_num), hm 9 0, hm 8 4, hAA 8 3 (by norm_num), hm 8 2,
    hXX 8 1 (by norm_num), hm 8 0, hm 7 4, hAA 7 3 (by norm_num), hm 7 2, hXX 7 1 (by norm_num),
    hm 7 0, hm 6 6, hAA 6 5 (by norm_num), hm 6 4, hAA 6 3 (by norm_num), hm 6 2,
    hXX 6 1 (by norm_num), hm 6 0, hm 5 7, hm 5 6, hAA 5 5 (by norm_num), hm 5 4,
    hAA 5 3 (by norm_num), hm 5 2, hXX 5 1 (by norm_num), hm 5 0, hAA 4 8 (by norm_num), hm 4 7,
    hm 4 6, hAA 4 5 (by norm_num), hm 4 4, hAA 4 3 (by norm_num), hm 4 2, hXX 4 1 (by norm_num),
    hm 4 0, hAA 3 9 (by norm_num), hAA 3 8 (by norm_num), hm 3 7, hAA 3 6 (by norm_num),
    hAA 3 5 (by norm_num), hm 3 4, hAA 3 3 (by norm_num), hm 3 2, hXX 3 1 (by norm_num), hm 3 0,
    hAA 2 9 (by norm_num), hAA 2 8 (by norm_num), hm 2 7, hAA 2 6 (by norm_num), hm 2 5, hm 2 4,
    hAA 2 3 (by norm_num), hm 2 2, hXX 2 1 (by norm_num), hAA 1 9 (by norm_num), hm 1 8, hm 1 7,
    hAA 1 6 (by norm_num), hm 1 5, hm 1 4, hAA 1 3 (by norm_num), hm 1 2, hAA 0 9 (by norm_num),
    hm 0 8, hm 0 7, hAA 0 6 (by norm_num), hm 0 5, hAA 0 4 (by norm_num), hAA 0 3 (by norm_num), hX,
    hA, hX', hA', mul_nonneg hX hA, mul_nonneg hX hX, mul_nonneg hA hA,
    mul_nonneg hX (sub_nonneg.2 hA'), mul_nonneg hA (sub_nonneg.2 hA'),
    mul_nonneg hX (sub_nonneg.2 hX'), mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

/-- `Z > 0`, so `T_x > 0`. -/
theorem urcx_Z_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) :
    0 < urcxZ (urcxl a) (1 + x) (urcK x a) (a + urcbp x a) := by
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  obtain ⟨A, rfl⟩ : ∃ A, a = 4 / 3 - A := ⟨4 / 3 - a, by ring⟩
  have hX : 0 ≤ X := by linarith
  have hX' : X ≤ 7 / 30 := by linarith
  have hA : 0 ≤ A := by linarith
  have hA' : A ≤ 1 / 3 := by linarith
  obtain ⟨hm, hAA, hXX⟩ := urcx_box hX hX' hA hA'
  clear hx hx2 ha ha2
  unfold urcxZ urcxl urcK urcbp
  linarith [hXX 2 1 (by norm_num), hm 0 3, hX, hA, hX', hA', mul_nonneg hX hA, mul_nonneg hX hX,
    mul_nonneg hA hA, mul_nonneg hX (sub_nonneg.2 hA'), mul_nonneg hA (sub_nonneg.2 hA'),
    mul_nonneg hX (sub_nonneg.2 hX'), mul_nonneg (sub_nonneg.2 hX') (sub_nonneg.2 hA')]

end SmoothedOctagon

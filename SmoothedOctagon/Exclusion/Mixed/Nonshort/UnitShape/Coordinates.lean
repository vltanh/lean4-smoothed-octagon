module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Leading

/-!
# Coordinates for the unit-face cubic

Put `r = 1 - 2t - x` and rescale `q - 1 = xz`. After clearing
the positive secant denominator, the constant coefficient is `constant`.
The value at `z = 1` is `value`, and `cross` is the coefficient of
`z(1-z)` in the square decomposition. All four quantities use the
same positive normalization.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

def constant {R : Type*} [CommRing R] (x r : R) : R :=
  6 * (1 + x) * (1 + x + r) ^ 2 *
    (x * (1 + x) * (x ^ 2 + 2 * x + 2) + r * (x ^ 3 + 4 * x ^ 2 + 8 * x + 6))

def value0 {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 8 + 30 * x ^ 7 + 136 * x ^ 6 + 338 * x ^ 5 + 477 * x ^ 4
    + 364 * x ^ 3 + 114 * x ^ 2 - 12 * x - 12

def value1 {R : Type*} [CommRing R] (x : R) : R :=
  9 * x ^ 8 + 89 * x ^ 7 + 367 * x ^ 6 + 872 * x ^ 5 + 1475 * x ^ 4
    + 2053 * x ^ 3 + 2263 * x ^ 2 + 1602 * x + 504

def value2 {R : Type*} [CommRing R] (x : R) : R :=
  9 * x ^ 5 + 63 * x ^ 4 + 126 * x ^ 3 + 86 * x ^ 2 + 24 * x + 12

def value3 {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 4 + 19 * x ^ 3 + 21 * x ^ 2 - 18 * x - 24

def value {R : Type*} [CommRing R] (x r : R) : R :=
  x * (1 + x) * ((1 + x) * value0 x + value1 x * r
    + (1 + x) ^ 2 * value2 x * r ^ 2 + (1 + x) ^ 2 * value3 x * r ^ 3)

def cross0 {R : Type*} [CommRing R] (x : R) : R :=
  -3 * x ^ 8 - 21 * x ^ 7 - 61 * x ^ 6 - 53 * x ^ 5 + 102 * x ^ 4
    + 278 * x ^ 3 + 246 * x ^ 2 + 60 * x - 36

def cross1 {R : Type*} [CommRing R] (x : R) : R :=
  -9 * x ^ 9 - 62 * x ^ 8 - 142 * x ^ 7 - 107 * x ^ 6 + 124 * x ^ 5
    + 539 * x ^ 4 + 1037 * x ^ 3 + 1158 * x ^ 2 + 600 * x + 72

def cross2 {R : Type*} [CommRing R] (x : R) : R :=
  -9 * x ^ 9 - 63 * x ^ 8 - 105 * x ^ 7 + 85 * x ^ 6 + 498 * x ^ 5
    + 894 * x ^ 4 + 1186 * x ^ 3 + 1104 * x ^ 2 + 528 * x + 72

def cross3 {R : Type*} [CommRing R] (x : R) : R :=
  -3 * x ^ 5 - 13 * x ^ 4 + 20 * x ^ 3 + 81 * x ^ 2 + 42 * x - 12

def cross {R : Type*} [CommRing R] (x r : R) : R :=
  x * (1 + x) ^ 2 * cross0 x + (1 + x) * cross1 x * r
    + cross2 x * r ^ 2 + x * (1 + x) ^ 2 * cross3 x * r ^ 3

def slope {R : Type*} [CommRing R] (x r : R) : R := 3 * value x r - cross x r

def remainder {R : Type*} [CommRing R] (x r : R) : R :=
  9 * value x r - 9 * cross x r + 18 * leading x r + 8 * constant x r

theorem constant_pos {x r : ℝ} (hx : 0 < x) (hr : 0 ≤ r) : 0 < constant x r := by
  unfold constant
  positivity

end SmoothedOctagon.UnitShape

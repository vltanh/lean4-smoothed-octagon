module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Quartic

/-!
# The low-scale quartics with the reciprocal-mean ceiling

Clear the denominator `12(q+1)(1+x)²(x²+6x+6)` after using the full
incoming floor weight. The unit and increasing-shape faces have
five coefficients each. The two reduced incoming coefficients
retain their useful positive prefactors.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

def incoming0 {R : Type*} [CommRing R] (t x : R) : R :=
  2 * t ^ 2 * x ^ 3 + 14 * t ^ 2 * x ^ 2 + 24 * t ^ 2 * x + 12 * t ^ 2 - t * x ^ 4 - 3 * t * x ^ 3 - 11 * t
    * x ^ 2 - 16 * t * x - 6 * t + 3 * x ^ 2 + 4 * x

def incoming1 {R : Type*} [CommRing R] (t x : R) : R :=
  -6 * t ^ 3 * x ^ 4 - 38 * t ^ 3 * x ^ 3 - 44 * t ^ 3 * x ^ 2 + 12 * t ^ 3 * x + 24 * t ^ 3 + 4 * t ^ 2 * x
    ^ 6 + 37 * t ^ 2 * x ^ 5 + 109 * t ^ 2 * x ^ 4 + 191 * t ^ 2 * x ^ 3 + 152 * t ^ 2 * x ^ 2 + 6 * t ^ 2 *
    x - 24 * t ^ 2 - 21 * t * x ^ 5 - 85 * t * x ^ 4 - 163 * t * x ^ 3 - 113 * t * x ^ 2 + 6 * t * x + 6 * t
    + 7 * x ^ 4 + 34 * x ^ 3 + 28 * x ^ 2 - 6 * x

def highIncoming0 {R : Type*} [CommRing R] (t x : R) : R :=
  2 * t ^ 2 * x ^ 4 + 17 * t ^ 2 * x ^ 3 + 47 * t ^ 2 * x ^ 2 + 60 * t ^ 2 * x + 30 * t ^ 2 - 2 * t * x ^ 4
    - 8 * t * x ^ 3 - 17 * t * x ^ 2 - 22 * t * x - 12 * t + 3 * x ^ 2 + 4 * x

def highIncoming1 {R : Type*} [CommRing R] (t x : R) : R :=
  -8 * t ^ 3 * x ^ 6 - 82 * t ^ 3 * x ^ 5 - 299 * t ^ 3 * x ^ 4 - 511 * t ^ 3 * x ^ 3 - 422 * t ^ 3 * x ^ 2
    - 90 * t ^ 3 * x + 60 * t ^ 3 + 8 * t ^ 2 * x ^ 6 + 130 * t ^ 2 * x ^ 5 + 502 * t ^ 2 * x ^ 4 + 878 * t
    ^ 2 * x ^ 3 + 795 * t ^ 2 * x ^ 2 + 288 * t ^ 2 * x - 30 * t ^ 2 - 45 * t * x ^ 5 - 180 * t * x ^ 4 -
    296 * t * x ^ 3 - 233 * t * x ^ 2 - 66 * t * x + 6 * t + 7 * x ^ 4 + 34 * x ^ 3 + 28 * x ^ 2 - 6 * x

def unit0 {R : Type*} [CommRing R] (t x : R) : R :=
  24 * x ^ 2 * (1 - t) ^ 2 * incoming0 t x

def unit1 {R : Type*} [CommRing R] (t x : R) : R :=
  12 * x * (1 - t) * incoming1 t x

def unit2 {R : Type*} [CommRing R] (t x : R) : R :=
  24 * t ^ 4 * x ^ 5 + 96 * t ^ 4 * x ^ 4 - 216 * t ^ 4 * x ^ 3 - 720 * t ^ 4 * x ^ 2 - 432 * t ^ 4 * x - 72
    * t ^ 3 * x ^ 7 - 600 * t ^ 3 * x ^ 6 - 1568 * t ^ 3 * x ^ 5 - 1948 * t ^ 3 * x ^ 4 - 488 * t ^ 3 * x ^
    3 + 912 * t ^ 3 * x ^ 2 + 240 * t ^ 3 * x - 144 * t ^ 3 + 96 * t ^ 2 * x ^ 7 + 1144 * t ^ 2 * x ^ 6 +
    3460 * t ^ 2 * x ^ 5 + 4354 * t ^ 2 * x ^ 4 + 970 * t ^ 2 * x ^ 3 - 1596 * t ^ 2 * x ^ 2 - 228 * t ^ 2 *
    x + 72 * t ^ 2 - 24 * t * x ^ 7 - 568 * t * x ^ 6 - 2250 * t * x ^ 5 - 3568 * t * x ^ 4 - 1346 * t * x ^
    3 + 900 * t * x ^ 2 + 60 * t * x + 12 * x ^ 6 + 214 * x ^ 5 + 634 * x ^ 4 + 312 * x ^ 3 - 228 * x ^ 2

def unit3 {R : Type*} [CommRing R] (t x : R) : R :=
  -24 * t ^ 4 * x ^ 4 - 168 * t ^ 4 * x ^ 3 - 288 * t ^ 4 * x ^ 2 - 144 * t ^ 4 * x - 24 * t ^ 3 * x ^ 7 -
    160 * t ^ 3 * x ^ 6 - 152 * t ^ 3 * x ^ 5 + 596 * t ^ 3 * x ^ 4 + 1524 * t ^ 3 * x ^ 3 + 1044 * t ^ 3 *
    x ^ 2 - 72 * t ^ 3 + 88 * t ^ 2 * x ^ 7 + 900 * t ^ 2 * x ^ 6 + 2752 * t ^ 2 * x ^ 5 + 3338 * t ^ 2 * x
    ^ 4 + 1024 * t ^ 2 * x ^ 3 - 242 * t ^ 2 * x ^ 2 + 372 * t ^ 2 * x + 60 * t ^ 2 + 20 * t * x ^ 8 + 176 *
    t * x ^ 7 + 356 * t * x ^ 6 - 108 * t * x ^ 5 - 664 * t * x ^ 4 + 376 * t * x ^ 3 + 864 * t * x ^ 2 - 48
    * t * x + 22 * x ^ 6 + 208 * x ^ 5 + 462 * x ^ 4 + 156 * x ^ 3 - 180 * x ^ 2

def unit4 {R : Type*} [CommRing R] (t x : R) : R :=
  2 * x * (t + x) * (x + 2) * (6 * t + 5 * x - 1) * (x ^ 2 + 6 * x + 6) * (t * x ^ 2 + 2 * t * x + 1)

def high0 {R : Type*} [CommRing R] (t x : R) : R :=
  12 * x ^ 2 * (1 - t) ^ 1 * highIncoming0 t x

def high1 {R : Type*} [CommRing R] (t x : R) : R :=
  6 * x * highIncoming1 t x

def high2 {R : Type*} [CommRing R] (t x : R) : R :=
  -72 * t ^ 3 * x ^ 7 - 672 * t ^ 3 * x ^ 6 - 2094 * t ^ 3 * x ^ 5 - 2748 * t ^ 3 * x ^ 4 - 1002 * t ^ 3 * x
    ^ 3 + 1260 * t ^ 3 * x ^ 2 + 1116 * t ^ 3 * x + 96 * t ^ 2 * x ^ 7 + 1302 * t ^ 2 * x ^ 6 + 4641 * t ^ 2
    * x ^ 5 + 7456 * t ^ 2 * x ^ 4 + 6049 * t ^ 2 * x ^ 3 + 1800 * t ^ 2 * x ^ 2 - 354 * t ^ 2 * x + 36 * t
    ^ 2 - 24 * t * x ^ 7 - 579 * t * x ^ 6 - 2084 * t * x ^ 5 - 3024 * t * x ^ 4 - 1963 * t * x ^ 3 - 438 *
    t * x ^ 2 + 30 * t * x + 6 * x ^ 6 + 107 * x ^ 5 + 317 * x ^ 4 + 156 * x ^ 3 - 114 * x ^ 2

def high3 {R : Type*} [CommRing R] (t x : R) : R :=
  -24 * t ^ 3 * x ^ 7 - 184 * t ^ 3 * x ^ 6 - 304 * t ^ 3 * x ^ 5 + 474 * t ^ 3 * x ^ 4 + 2090 * t ^ 3 * x ^
    3 + 2648 * t ^ 3 * x ^ 2 + 1284 * t ^ 3 * x + 48 * t ^ 3 + 88 * t ^ 2 * x ^ 7 + 970 * t ^ 2 * x ^ 6 +
    3366 * t ^ 2 * x ^ 5 + 5495 * t ^ 2 * x ^ 4 + 4648 * t ^ 2 * x ^ 3 + 1643 * t ^ 2 * x ^ 2 - 54 * t ^ 2 *
    x + 30 * t ^ 2 + 20 * t * x ^ 8 + 176 * t * x ^ 7 + 384 * t * x ^ 6 + 164 * t * x ^ 5 - 272 * t * x ^ 4
    - 256 * t * x ^ 3 - 72 * t * x ^ 2 - 24 * t * x + 11 * x ^ 6 + 104 * x ^ 5 + 231 * x ^ 4 + 78 * x ^ 3 -
    90 * x ^ 2

def high4 {R : Type*} [CommRing R] (t x : R) : R :=
  x * (t + x) * (x + 2) * (6 * t + 5 * x - 1) * (x ^ 2 + 6 * x + 6) * (2 * t * x ^ 2 + 4 * t * x + 4 * t + 1)

end SmoothedOctagon.LowScale

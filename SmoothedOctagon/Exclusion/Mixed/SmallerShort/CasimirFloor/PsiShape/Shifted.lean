module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiShape.Numerator

/-!
# Smaller-short window, Casimir floor: the cleared numerator of `Ψ_a` in the shifted variables

With `c = a - 1`, `h = x - 2`, `z = b - x`, the numerator `V = -7a²B²K²Ψ_a` of `PsiShape/Numerator` is affine
in the norm `u` (`cas_w2_V_affine`, the `u`-coefficient `casW2V1` being `-7a²B²K²Ψ_au`), and

* `7a²B²K²Ψ_au = U₀ + U₁z + U₂z² + U₃z³` (`cas_w2_V1_eq`),
* `28a²B²K²Ψ_a(x, a, b, 3/4) = P_* + T₁z + T₂z² + T₃z³` (`cas_w2_V_eq34`), whose
  `z⁰` coefficient `P_*` is the value at `b = x`.

Together: `-4V = (P_* + T₁z + T₂z² + T₃z³) + (4u - 3)(U₀ + U₁z + U₂z² + U₃z³)` (`cas_w2_V_eq`).

The dependence on `b` is controlled by the `z`-coefficients `T₁, T₂, T₃` of the same numerator at
`u = 3/4`, which are displayed and shown positive by the monomial rule (`PsiShape/Coefficients`).
The two identities are polynomial identities in `c, h, z` of total degree at most eight with 111
and 108 monomials.

## Main API

* `casW2Ps` (`P_*`), `casW2T1`, `casW2T2`, `casW2T3`, `casW2U0`, …, `casW2U3`,
  `casW2Tz`, `casW2Uz`, `casW2V1`.
* `cas_w2_V_affine`, `cas_w2_V_eq34`, `cas_w2_V1_eq`, `cas_w2_V_eq`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `P_*(c, h)`, the `z⁰` coefficient. -/
noncomputable def casW2Ps (c h : ℝ) : ℝ :=
  -c ^ 6 * h - 2 * c ^ 6 + 2 * c ^ 5 * h ^ 2 + 2 * c ^ 5 * h - 4 * c ^ 5 + 3 * c ^ 4 * h ^ 4 +
    12 * c ^ 4 * h ^ 3 + 51 * c ^ 4 * h ^ 2 + 138 * c ^ 4 * h + 120 * c ^ 4 - 6 * c ^ 3 * h ^ 5 -
    22 * c ^ 3 * h ^ 4 + 26 * c ^ 3 * h ^ 3 + 366 * c ^ 3 * h ^ 2 + 900 * c ^ 3 * h + 704 * c ^ 3 -
    5 * c ^ 2 * h ^ 6 - 71 * c ^ 2 * h ^ 5 - 374 * c ^ 2 * h ^ 4 - 1024 * c ^ 2 * h ^ 3 -
    1447 * c ^ 2 * h ^ 2 - 769 * c ^ 2 * h + 90 * c ^ 2 - 4 * c * h ^ 7 - 62 * c * h ^ 6 -
    398 * c * h ^ 5 - 1424 * c * h ^ 4 - 3216 * c * h ^ 3 - 4654 * c * h ^ 2 - 3870 * c * h -
    1348 * c - 2 * h ^ 8 - 32 * h ^ 7 - 210 * h ^ 6 - 712 * h ^ 5 - 1278 * h ^ 4 - 1024 * h ^ 3 +
    74 * h ^ 2 + 616 * h + 264

/-- `T₁(c, h)`, the `z` coefficient of `-4V` at `u = 3/4`. -/
noncomputable def casW2T1 (c h : ℝ) : ℝ :=
  -c ^ 6 + 4 * c ^ 5 * h + 2 * c ^ 5 + 3 * c ^ 4 * h ^ 3 - 32 * c ^ 4 * h ^ 2 - 103 * c ^ 4 * h -
    72 * c ^ 4 - 4 * c ^ 3 * h ^ 4 + 24 * c ^ 3 * h ^ 3 + 92 * c ^ 3 * h ^ 2 + 160 * c ^ 3 * h +
    176 * c ^ 3 - 11 * c ^ 2 * h ^ 5 - 77 * c ^ 2 * h ^ 4 - 136 * c ^ 2 * h ^ 3 -
    16 * c ^ 2 * h ^ 2 + 283 * c ^ 2 * h + 389 * c ^ 2 - 4 * c * h ^ 6 - 54 * c * h ^ 5 -
    210 * c * h ^ 4 - 304 * c * h ^ 3 - 228 * c * h ^ 2 - 234 * c * h - 118 * c - 4 * h ^ 7 -
    44 * h ^ 6 - 150 * h ^ 5 + 56 * h ^ 4 + 1528 * h ^ 3 + 3684 * h ^ 2 + 3586 * h + 1264

/-- `T₂(c, h)`, the `z²` coefficient of `-4V` at `u = 3/4`. -/
noncomputable def casW2T2 (c h : ℝ) : ℝ :=
  2 * c ^ 5 - 39 * c ^ 4 * h - 68 * c ^ 4 + 2 * c ^ 3 * h ^ 3 + 10 * c ^ 3 * h ^ 2 -
    102 * c ^ 3 * h - 210 * c ^ 3 - 6 * c ^ 2 * h ^ 4 + 30 * c ^ 2 * h ^ 3 + 264 * c ^ 2 * h ^ 2 +
    390 * c ^ 2 * h + 74 * c ^ 2 + 6 * c * h ^ 4 + 222 * c * h ^ 3 + 1050 * c * h ^ 2 +
    1698 * c * h + 880 * c - 2 * h ^ 6 - h ^ 5 + 164 * h ^ 4 + 1108 * h ^ 3 + 3036 * h ^ 2 +
    3797 * h + 1786

/-- `T₃(c, h)`, the `z³` coefficient of `-4V` at `u = 3/4`. -/
noncomputable def casW2T3 (c h : ℝ) : ℝ :=
  -c ^ 4 - 24 * c ^ 3 * h - 52 * c ^ 3 + 34 * c ^ 2 * h ^ 2 + 60 * c ^ 2 * h - 22 * c ^ 2 +
    68 * c * h ^ 2 + 192 * c * h + 108 * c + 11 * h ^ 4 + 108 * h ^ 3 + 414 * h ^ 2 + 684 * h +
    399

/-- `U₀(c, h)`. -/
noncomputable def casW2U0 (c h : ℝ) : ℝ :=
  4 * c ^ 5 * h ^ 2 + 20 * c ^ 5 * h + 24 * c ^ 5 - 3 * c ^ 4 * h ^ 4 - 37 * c ^ 4 * h ^ 3 -
    113 * c ^ 4 * h ^ 2 - 81 * c ^ 4 * h + 42 * c ^ 4 + 6 * c ^ 3 * h ^ 5 + 74 * c ^ 3 * h ^ 4 +
    282 * c ^ 3 * h ^ 3 + 478 * c ^ 3 * h ^ 2 + 464 * c ^ 3 * h + 280 * c ^ 3 + 5 * c ^ 2 * h ^ 6 +
    96 * c ^ 2 * h ^ 5 + 688 * c ^ 2 * h ^ 4 + 2318 * c ^ 2 * h ^ 3 + 3939 * c ^ 2 * h ^ 2 +
    3282 * c ^ 2 * h + 1096 * c ^ 2 + 4 * c * h ^ 7 + 92 * c * h ^ 6 + 844 * c * h ^ 5 +
    4000 * c * h ^ 4 + 10556 * c * h ^ 3 + 15468 * c * h ^ 2 + 11572 * c * h + 3352 * c +
    2 * h ^ 8 + 49 * h ^ 7 + 504 * h ^ 6 + 2853 * h ^ 5 + 9704 * h ^ 4 + 20219 * h ^ 3 +
    25032 * h ^ 2 + 16655 * h + 4470

/-- `U₁(c, h)`. -/
noncomputable def casW2U1 (c h : ℝ) : ℝ :=
  4 * c ^ 5 * h + 8 * c ^ 5 - 3 * c ^ 4 * h ^ 3 - 41 * c ^ 4 * h ^ 2 - 91 * c ^ 4 * h - 39 * c ^ 4 +
    4 * c ^ 3 * h ^ 4 + 56 * c ^ 3 * h ^ 3 + 176 * c ^ 3 * h ^ 2 + 264 * c ^ 3 * h + 220 * c ^ 3 +
    11 * c ^ 2 * h ^ 5 + 182 * c ^ 2 * h ^ 4 + 1068 * c ^ 2 * h ^ 3 + 2846 * c ^ 2 * h ^ 2 +
    3641 * c ^ 2 * h + 1900 * c ^ 2 + 4 * c * h ^ 6 + 110 * c * h ^ 5 + 1060 * c * h ^ 4 +
    4744 * c * h ^ 3 + 10808 * c * h ^ 2 + 12266 * c * h + 5568 * c + 4 * h ^ 7 + 93 * h ^ 6 +
    876 * h ^ 5 + 4413 * h ^ 4 + 12884 * h ^ 3 + 21815 * h ^ 2 + 19868 * h + 7535

/-- `U₂(c, h)`. -/
noncomputable def casW2U2 (c h : ℝ) : ℝ :=
  2 * c ^ 5 - 9 * c ^ 4 * h - 8 * c ^ 4 - 2 * c ^ 3 * h ^ 3 - 18 * c ^ 3 * h ^ 2 - 66 * c ^ 3 * h -
    54 * c ^ 3 + 6 * c ^ 2 * h ^ 4 + 98 * c ^ 2 * h ^ 3 + 424 * c ^ 2 * h ^ 2 + 706 * c ^ 2 * h +
    430 * c ^ 2 + 22 * c * h ^ 4 + 306 * c * h ^ 3 + 1294 * c * h ^ 2 + 2214 * c * h + 1364 * c +
    2 * h ^ 6 + 49 * h ^ 5 + 432 * h ^ 4 + 1900 * h ^ 3 + 4468 * h ^ 2 + 5363 * h + 2586

/-- `U₃(c, h)`. -/
noncomputable def casW2U3 (c h : ℝ) : ℝ :=
  c ^ 4 - 8 * c ^ 3 * h - 12 * c ^ 3 + 14 * c ^ 2 * h ^ 2 + 36 * c ^ 2 * h + 22 * c ^ 2 +
    28 * c * h ^ 2 + 96 * c * h + 84 * c + 5 * h ^ 4 + 52 * h ^ 3 + 210 * h ^ 2 + 372 * h + 241
/-- `P_* + T₁z + T₂z² + T₃z³ = 28a²B²K²Ψ_a` at `u = 3/4`. -/
noncomputable def casW2Tz (c h z : ℝ) : ℝ :=
  casW2Ps c h + z * (casW2T1 c h + z * (casW2T2 c h + z * casW2T3 c h))

/-- `U₀ + U₁z + U₂z² + U₃z³ = 7a²B²K²Ψ_au`. -/
noncomputable def casW2Uz (c h z : ℝ) : ℝ :=
  casW2U0 c h + z * (casW2U1 c h + z * (casW2U2 c h + z * casW2U3 c h))

/-- The `u`-coefficient of `V`: with `Q_u = 2D - S³`, `N_u = D² - DS³` (`S = 1 + x`),
`V_u = 2Q_u aB²K - N_u(BK + aK + 2a²B) - bB²K² - 4a²B³K + 2a³B²Q_u`. -/
noncomputable def casW2V1 (x be al : ℝ) : ℝ :=
  2 * (2 * ssDg x be al - (1 + x) ^ 3) * al * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) -
    (ssDg x be al ^ 2 - ssDg x be al * (1 + x) ^ 3) *
      ((al + be) * (x * (x + 2) + al ^ 2) + al * (x * (x + 2) + al ^ 2) + 2 * al ^ 2 * (al + be)) -
    be * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) ^ 2 -
    4 * al ^ 2 * (al + be) ^ 3 * (x * (x + 2) + al ^ 2) +
    2 * al ^ 3 * (al + be) ^ 2 * (2 * ssDg x be al - (1 + x) ^ 3)

/-- `V` is affine in the norm `u`. -/
theorem cas_w2_V_affine (x be al u : ℝ) :
    casW2V x be al u = casW2V x be al (3 / 4) + (u - 3 / 4) * casW2V1 x be al := by
  unfold casW2V casW2V1 casW2N casW2Q casClosedP casW2Va
  generalize ssDg x be al = D
  generalize x * (x + 2) + al ^ 2 = K
  ring

/-- `-4V = P_* + T₁z + T₂z² + T₃z³` at `u = 3/4`, in `c = a - 1`, `h = x - 2`, `z = b - x`. -/
theorem cas_w2_V_eq34 (c h z : ℝ) :
    casW2V (2 + h) (2 + h + z) (1 + c) (3 / 4) = -(1 / 4) * casW2Tz c h z := by
  unfold casW2V casW2N casW2Q casClosedP casW2Va ssDg casW2Tz casW2Ps casW2T1 casW2T2
    casW2T3
  ring

/-- `-V_u = 7a²B²K²Ψ_au = U₀ + U₁z + U₂z² + U₃z³`. -/
theorem cas_w2_V1_eq (c h z : ℝ) :
    casW2V1 (2 + h) (2 + h + z) (1 + c) = -casW2Uz c h z := by
  unfold casW2V1 ssDg casW2Uz casW2U0 casW2U1 casW2U2 casW2U3
  ring

/-- `-4V = (P_* + T₁z + T₂z² + T₃z³) + (4u - 3)(U₀ + U₁z + U₂z² + U₃z³)`. -/
theorem cas_w2_V_eq (c h z u : ℝ) :
    casW2V (2 + h) (2 + h + z) (1 + c) u =
      -(1 / 4) * (casW2Tz c h z + (4 * u - 3) * casW2Uz c h z) := by
  rw [cas_w2_V_affine, cas_w2_V_eq34, cas_w2_V1_eq]
  ring

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Clearing
public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.UnitShape.BaseQuadratic

/-!
# Case M2, forward successor: the low-ratio coefficient signs

The coefficient signs of the low-ratio unit-shape residual at `k = 1`. With `h = 1 - 2t`,
`j = 2t + x - 1`, `y = q - 1`, the cleared residual is `∑ᵢ C̃ᵢ(h, y) jⁱ` (`Nonshort/Forward/LowRatio/UnitShape`);
here that sum is shown positive for `1/3 ≤ h ≤ 1/2`, `0 ≤ y ≤ h`, `j ≥ 0`.

* The quadratic part is `h³w³(𝒜₀ + β𝒜₁ + wβ²𝒜₂)`, `β = j/(hw)`. Each `𝒜ᵢ` increases in `h`
  (`nlr_A0_ge`, …: `∂_h𝒜ᵢ = Eᵢ/2 ≥ 0`), and at `h = 1/3` the base quadratic exceeds `4`
  (`nlr_base`: positive diagonal terms and a determinant bound for the comparison quadratic).
* `C̃₃, …, C̃₁₀ ≥ 0` from the factored forms and the monomial bounds of their univariate factors.

The lower bounds of `U₀₂, U₀₃, U₁₂, U₁₃, U₂₀, U₂₁, U₂₂` use their Taylor coefficients at
`h = 1/3` (all nonnegative beyond the constant); the `h⁹` terms stay inside `C̃₁` (and `𝒜₁`); for
`C̃₃` and `C̃₄` only nonnegativity is used.

## Main API

* the univariate factors `nlrBᵢₙ`, `nlrPᵢₙ`, `nlrUᵢₙ`, `nlrSᵢ`, `nlra0`, …, `nlrQC`; `nlrA0`, …,
  `nlrE0`, …; `nlrC0`, …, `nlrC10`.
* `nlr_base`, `nlr_A0_ge`, `nlr_A1_ge`, `nlr_A2_ge`, `nlr_quad_pos`;
  `nlr_sum_pos`: **`∑ᵢ C̃ᵢ jⁱ > 0`**.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### The univariate factors -/

/-- `B_{00}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB00 (h : ℝ) : ℝ :=
  -1860 + 2570 * h + 9766 * h ^ (2 : ℕ) + 6540 * h ^ (3 : ℕ) + 1008 * h ^ (4 : ℕ)

/-- `B_{01}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB01 (h : ℝ) : ℝ :=
  4020 - 6440 * h + 3929 * h ^ (2 : ℕ) + 42003 * h ^ (3 : ℕ) + 38424 * h ^ (4 : ℕ) + 11076 * h ^ (5 : ℕ) + 1008 * h ^ (6 : ℕ)

/-- `B_{02}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB02 (h : ℝ) : ℝ :=
  -4860 - 2970 * h - 22149 * h ^ (2 : ℕ) - 2496 * h ^ (3 : ℕ) + 74854 * h ^ (4 : ℕ) + 78347 * h ^ (5 : ℕ) + 26922 * h ^ (6 : ℕ) + 2952 * h ^ (7 : ℕ)

/-- `B_{03}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB03 (h : ℝ) : ℝ :=
  -1380 + 940 * h + 11318 * h ^ (2 : ℕ) - 20921 * h ^ (3 : ℕ) - 24625 * h ^ (4 : ℕ) + 49257 * h ^ (5 : ℕ) + 68533 * h ^ (6 : ℕ) + 27134 * h ^ (7 : ℕ) + 3264 * h ^ (8 : ℕ)

/-- `B_{04}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB04 (h : ℝ) : ℝ :=
  -4740 + 16160 * h + 55824 * h ^ (2 : ℕ) + 19838 * h ^ (3 : ℕ) - 32254 * h ^ (4 : ℕ) - 6242 * h ^ (5 : ℕ) + 21486 * h ^ (6 : ℕ) + 11984 * h ^ (7 : ℕ) + 1608 * h ^ (8 : ℕ)

/-- `B_{05}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB05 (h : ℝ) : ℝ :=
  -3960 + 16440 * h + 54756 * h ^ (2 : ℕ) + 34662 * h ^ (3 : ℕ) - 15206 * h ^ (4 : ℕ) - 19306 * h ^ (5 : ℕ) - 2315 * h ^ (6 : ℕ) + 1811 * h ^ (7 : ℕ) + 330 * h ^ (8 : ℕ)

/-- `B_{06}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB06 (h : ℝ) : ℝ :=
  -600 + 5720 * h + 17120 * h ^ (2 : ℕ) + 12368 * h ^ (3 : ℕ) - 3058 * h ^ (4 : ℕ) - 6760 * h ^ (5 : ℕ) - 2251 * h ^ (6 : ℕ) - 93 * h ^ (7 : ℕ) + 18 * h ^ (8 : ℕ)

/-- `B_{07}(h)`, a univariate factor of `C̃₀` and `𝒜₀`. -/
noncomputable def nlrB07 (h : ℝ) : ℝ :=
  -360 - 240 * h + 516 * h ^ (2 : ℕ) + 360 * h ^ (3 : ℕ) - 144 * h ^ (4 : ℕ) - 120 * h ^ (5 : ℕ) - 12 * h ^ (6 : ℕ)

/-- `B_{10}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB10 (h : ℝ) : ℝ :=
  -720 - 7780 * h + 17094 * h ^ (2 : ℕ) + 58240 * h ^ (3 : ℕ) + 43434 * h ^ (4 : ℕ) + 9612 * h ^ (5 : ℕ) + 432 * h ^ (6 : ℕ)

/-- `B_{11}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB11 (h : ℝ) : ℝ :=
  3000 + 1950 * h - 45830 * h ^ (2 : ℕ) + 58853 * h ^ (3 : ℕ) + 296430 * h ^ (4 : ℕ) + 276717 * h ^ (5 : ℕ) + 95736 * h ^ (6 : ℕ) + 12852 * h ^ (7 : ℕ) + 432 * h ^ (8 : ℕ)

/-- `B_{12}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB12 (h : ℝ) : ℝ :=
  -14760 - 38280 * h - 67107 * h ^ (2 : ℕ) - 128528 * h ^ (3 : ℕ) + 130659 * h ^ (4 : ℕ) + 606701 * h ^ (5 : ℕ) + 580936 * h ^ (6 : ℕ) + 221237 * h ^ (7 : ℕ) + 33270 * h ^ (8 : ℕ)

/-- `B_{13}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB13 (h : ℝ) : ℝ :=
  -26090 + 70056 * h + 197151 * h ^ (2 : ℕ) + 457 * h ^ (3 : ℕ) - 6473 * h ^ (4 : ℕ) + 406129 * h ^ (5 : ℕ) + 490144 * h ^ (6 : ℕ) + 210010 * h ^ (7 : ℕ) + 33264 * h ^ (8 : ℕ)

/-- `B_{14}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB14 (h : ℝ) : ℝ :=
  -21670 + 265968 * h + 673800 * h ^ (2 : ℕ) + 344090 * h ^ (3 : ℕ) - 190550 * h ^ (4 : ℕ) - 103404 * h ^ (5 : ℕ) + 113432 * h ^ (6 : ℕ) + 82418 * h ^ (7 : ℕ) + 14364 * h ^ (8 : ℕ)

/-- `B_{15}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB15 (h : ℝ) : ℝ :=
  -7500 + 225732 * h + 570762 * h ^ (2 : ℕ) + 352498 * h ^ (3 : ℕ) - 139977 * h ^ (4 : ℕ) - 209647 * h ^ (5 : ℕ) - 49376 * h ^ (6 : ℕ) + 7787 * h ^ (7 : ℕ) + 2427 * h ^ (8 : ℕ)

/-- `B_{16}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB16 (h : ℝ) : ℝ :=
  2300 + 67140 * h + 162036 * h ^ (2 : ℕ) + 106516 * h ^ (3 : ℕ) - 38155 * h ^ (4 : ℕ) - 69897 * h ^ (5 : ℕ) - 24205 * h ^ (6 : ℕ) - 1657 * h ^ (7 : ℕ) + 114 * h ^ (8 : ℕ)

/-- `B_{17}(h)`, a univariate factor of `C̃₁` and `𝒜₁`. -/
noncomputable def nlrB17 (h : ℝ) : ℝ :=
  -360 - 3000 * h - 1092 * h ^ (2 : ℕ) + 4794 * h ^ (3 : ℕ) + 2652 * h ^ (4 : ℕ) - 1668 * h ^ (5 : ℕ) - 1200 * h ^ (6 : ℕ) - 126 * h ^ (7 : ℕ)

/-- `B_{20}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB20 (h : ℝ) : ℝ :=
  4140 - 7620 * h - 16404 * h ^ (2 : ℕ) + 58692 * h ^ (3 : ℕ) + 89088 * h ^ (4 : ℕ) + 31248 * h ^ (5 : ℕ) + 2592 * h ^ (6 : ℕ)

/-- `B_{21}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB21 (h : ℝ) : ℝ :=
  -1020 + 21780 * h - 58914 * h ^ (2 : ℕ) - 94500 * h ^ (3 : ℕ) + 319626 * h ^ (4 : ℕ) + 559212 * h ^ (5 : ℕ) + 287076 * h ^ (6 : ℕ) + 58104 * h ^ (7 : ℕ) + 3456 * h ^ (8 : ℕ)

/-- `B_{22}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB22 (h : ℝ) : ℝ :=
  -69330 - 38967 * h - 134046 * h ^ (2 : ℕ) - 28145 * h ^ (3 : ℕ) + 801370 * h ^ (4 : ℕ) + 1181276 * h ^ (5 : ℕ) + 633062 * h ^ (6 : ℕ) + 141564 * h ^ (7 : ℕ) + 8496 * h ^ (8 : ℕ)

/-- `B_{23}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB23 (h : ℝ) : ℝ :=
  -35562 + 617251 * h + 751883 * h ^ (2 : ℕ) + 58120 * h ^ (3 : ℕ) + 313793 * h ^ (4 : ℕ) + 840895 * h ^ (5 : ℕ) + 552800 * h ^ (6 : ℕ) + 132804 * h ^ (7 : ℕ) + 7272 * h ^ (8 : ℕ)

/-- `B_{24}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB24 (h : ℝ) : ℝ :=
  96574 + 1457524 * h + 1892122 * h ^ (2 : ℕ) + 83240 * h ^ (3 : ℕ) - 722248 * h ^ (4 : ℕ) - 91608 * h ^ (5 : ℕ) + 166850 * h ^ (6 : ℕ) + 51438 * h ^ (7 : ℕ) + 2196 * h ^ (8 : ℕ)

/-- `B_{25}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB25 (h : ℝ) : ℝ :=
  105396 + 1075590 * h + 1426392 * h ^ (2 : ℕ) + 65394 * h ^ (3 : ℕ) - 716286 * h ^ (4 : ℕ) - 318393 * h ^ (5 : ℕ) - 13182 * h ^ (6 : ℕ) + 6807 * h ^ (7 : ℕ) + 126 * h ^ (8 : ℕ)

/-- `B_{26}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB26 (h : ℝ) : ℝ :=
  37820 + 278958 * h + 371896 * h ^ (2 : ℕ) + 9338 * h ^ (3 : ℕ) - 212931 * h ^ (4 : ℕ) - 102230 * h ^ (5 : ℕ) - 10287 * h ^ (6 : ℕ) + 252 * h ^ (7 : ℕ)

/-- `B_{27}(h)`, a univariate factor of `C̃₂` and `𝒜₂`. -/
noncomputable def nlrB27 (h : ℝ) : ℝ :=
  -2400 - 6882 * h + 7536 * h ^ (2 : ℕ) + 10380 * h ^ (3 : ℕ) - 3564 * h ^ (4 : ℕ) - 4506 * h ^ (5 : ℕ) - 564 * h ^ (6 : ℕ)

/-- `P_{04}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrP04 (h : ℝ) : ℝ :=
  -4740 + 32320 * h + 167472 * h ^ (2 : ℕ) + 79352 * h ^ (3 : ℕ) - 161270 * h ^ (4 : ℕ) - 37452 * h ^ (5 : ℕ) + 150402 * h ^ (6 : ℕ) + 95872 * h ^ (7 : ℕ) + 14472 * h ^ (8 : ℕ)

/-- `P_{05}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrP05 (h : ℝ) : ℝ :=
  -7920 + 49320 * h + 219024 * h ^ (2 : ℕ) + 173310 * h ^ (3 : ℕ) - 91236 * h ^ (4 : ℕ) - 135142 * h ^ (5 : ℕ) - 18520 * h ^ (6 : ℕ) + 16299 * h ^ (7 : ℕ) + 3300 * h ^ (8 : ℕ)

/-- `P_{06}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrP06 (h : ℝ) : ℝ :=
  -1800 + 22880 * h + 85600 * h ^ (2 : ℕ) + 74208 * h ^ (3 : ℕ) - 21406 * h ^ (4 : ℕ) - 54080 * h ^ (5 : ℕ) - 20259 * h ^ (6 : ℕ) - 930 * h ^ (7 : ℕ) + 198 * h ^ (8 : ℕ)

/-- `P_{14}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrP14 (h : ℝ) : ℝ :=
  -43340 + 797904 * h + 2695200 * h ^ (2 : ℕ) + 1720450 * h ^ (3 : ℕ) - 1143300 * h ^ (4 : ℕ) - 723828 * h ^ (5 : ℕ) + 907456 * h ^ (6 : ℕ) + 741762 * h ^ (7 : ℕ) + 143640 * h ^ (8 : ℕ)

/-- `P_{15}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrP15 (h : ℝ) : ℝ :=
  -22500 + 902928 * h + 2853810 * h ^ (2 : ℕ) + 2114988 * h ^ (3 : ℕ) - 979839 * h ^ (4 : ℕ) - 1677176 * h ^ (5 : ℕ) - 444384 * h ^ (6 : ℕ) + 77870 * h ^ (7 : ℕ) + 26697 * h ^ (8 : ℕ)

/-- `P_{16}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrP16 (h : ℝ) : ℝ :=
  9200 + 335700 * h + 972216 * h ^ (2 : ℕ) + 745612 * h ^ (3 : ℕ) - 305240 * h ^ (4 : ℕ) - 629073 * h ^ (5 : ℕ) - 242050 * h ^ (6 : ℕ) - 18227 * h ^ (7 : ℕ) + 1368 * h ^ (8 : ℕ)

/-- `P_{24}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrP24 (h : ℝ) : ℝ :=
  289722 + 5830096 * h + 9460610 * h ^ (2 : ℕ) + 499440 * h ^ (3 : ℕ) - 5055736 * h ^ (4 : ℕ) - 732864 * h ^ (5 : ℕ) + 1501650 * h ^ (6 : ℕ) + 514380 * h ^ (7 : ℕ) + 24156 * h ^ (8 : ℕ)

/-- `P_{25}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrP25 (h : ℝ) : ℝ :=
  421584 + 5377950 * h + 8558352 * h ^ (2 : ℕ) + 457758 * h ^ (3 : ℕ) - 5730288 * h ^ (4 : ℕ) - 2865537 * h ^ (5 : ℕ) - 131820 * h ^ (6 : ℕ) + 74877 * h ^ (7 : ℕ) + 1512 * h ^ (8 : ℕ)

/-- `P_{26}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrP26 (h : ℝ) : ℝ :=
  189100 + 1673748 * h + 2603272 * h ^ (2 : ℕ) + 74704 * h ^ (3 : ℕ) - 1916379 * h ^ (4 : ℕ) - 1022300 * h ^ (5 : ℕ) - 113157 * h ^ (6 : ℕ) + 3024 * h ^ (7 : ℕ)

/-- `P_{30}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP30 (h : ℝ) : ℝ :=
  750 + 2735 * h - 5619 * h ^ (2 : ℕ) - 833 * h ^ (3 : ℕ) + 18639 * h ^ (4 : ℕ) + 11844 * h ^ (5 : ℕ) + 1620 * h ^ (6 : ℕ)

/-- `P_{31}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP31 (h : ℝ) : ℝ :=
  8705 + 32414 * h - 38975 * h ^ (2 : ℕ) - 51137 * h ^ (3 : ℕ) + 231183 * h ^ (4 : ℕ) + 424449 * h ^ (5 : ℕ) + 268647 * h ^ (6 : ℕ) + 72306 * h ^ (7 : ℕ) + 6048 * h ^ (8 : ℕ)

/-- `P_{32}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP32 (h : ℝ) : ℝ :=
  -72759 + 74553 * h + 160411 * h ^ (2 : ℕ) + 412787 * h ^ (3 : ℕ) + 1338365 * h ^ (4 : ℕ) + 1800478 * h ^ (5 : ℕ) + 1148415 * h ^ (6 : ℕ) + 338190 * h ^ (7 : ℕ) + 29232 * h ^ (8 : ℕ)

/-- `P_{33}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP33 (h : ℝ) : ℝ :=
  225967 + 1979598 * h + 2750577 * h ^ (2 : ℕ) + 849874 * h ^ (3 : ℕ) + 45928 * h ^ (4 : ℕ) + 832220 * h ^ (5 : ℕ) + 873028 * h ^ (6 : ℕ) + 297504 * h ^ (7 : ℕ) + 24696 * h ^ (8 : ℕ)

/-- `P_{34}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP34 (h : ℝ) : ℝ :=
  338793 + 2000238 * h + 2548635 * h ^ (2 : ℕ) + 261460 * h ^ (3 : ℕ) - 1142100 * h ^ (4 : ℕ) - 495097 * h ^ (5 : ℕ) + 52254 * h ^ (6 : ℕ) + 49671 * h ^ (7 : ℕ) + 3654 * h ^ (8 : ℕ)

/-- `P_{35}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP35 (h : ℝ) : ℝ :=
  510006 + 2740780 * h + 3366742 * h ^ (2 : ℕ) + 73942 * h ^ (3 : ℕ) - 1950176 * h ^ (4 : ℕ) - 1012247 * h ^ (5 : ℕ) - 124034 * h ^ (6 : ℕ) + 7281 * h ^ (7 : ℕ) + 378 * h ^ (8 : ℕ)

/-- `P_{36}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP36 (h : ℝ) : ℝ :=
  135850 + 669914 * h + 790444 * h ^ (2 : ℕ) - 56276 * h ^ (3 : ℕ) - 542205 * h ^ (4 : ℕ) - 264504 * h ^ (5 : ℕ) - 31721 * h ^ (6 : ℕ) + 66 * h ^ (7 : ℕ)

/-- `P_{37}(h)`, a univariate factor of `C̃₃`. -/
noncomputable def nlrP37 (h : ℝ) : ℝ :=
  -919 - 1994 * h + 1078 * h ^ (2 : ℕ) + 3773 * h ^ (3 : ℕ) + 1975 * h ^ (4 : ℕ) + 235 * h ^ (5 : ℕ)

/-- `P_{40}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP40 (h : ℝ) : ℝ :=
  5035 + 5478 * h - 12439 * h ^ (2 : ℕ) + 5742 * h ^ (3 : ℕ) + 16992 * h ^ (4 : ℕ) + 4320 * h ^ (5 : ℕ)

/-- `P_{41}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP41 (h : ℝ) : ℝ :=
  63013 + 145269 * h + 5447 * h ^ (2 : ℕ) - 51105 * h ^ (3 : ℕ) + 240828 * h ^ (4 : ℕ) + 394548 * h ^ (5 : ℕ) + 191808 * h ^ (6 : ℕ) + 24192 * h ^ (7 : ℕ)

/-- `P_{42}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP42 (h : ℝ) : ℝ :=
  66595 + 595624 * h + 709256 * h ^ (2 : ℕ) + 304978 * h ^ (3 : ℕ) + 397461 * h ^ (4 : ℕ) + 727438 * h ^ (5 : ℕ) + 428664 * h ^ (6 : ℕ) + 57456 * h ^ (7 : ℕ)

/-- `P_{43}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP43 (h : ℝ) : ℝ :=
  770791 + 3237631 * h + 2512262 * h ^ (2 : ℕ) - 671793 * h ^ (3 : ℕ) - 1009965 * h ^ (4 : ℕ) + 219446 * h ^ (5 : ℕ) + 345204 * h ^ (6 : ℕ) + 47880 * h ^ (7 : ℕ)

/-- `P_{44}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP44 (h : ℝ) : ℝ :=
  759057 + 2649927 * h + 1602452 * h ^ (2 : ℕ) - 1128401 * h ^ (3 : ℕ) - 1229630 * h ^ (4 : ℕ) - 224572 * h ^ (5 : ℕ) + 42861 * h ^ (6 : ℕ) + 6930 * h ^ (7 : ℕ)

/-- `P_{45}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP45 (h : ℝ) : ℝ :=
  1017184 + 3297010 * h + 1674623 * h ^ (2 : ℕ) - 1755821 * h ^ (3 : ℕ) - 1635636 * h ^ (4 : ℕ) - 347735 * h ^ (5 : ℕ) - 7167 * h ^ (6 : ℕ) + 630 * h ^ (7 : ℕ)

/-- `P_{46}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP46 (h : ℝ) : ℝ :=
  244734 + 742340 * h + 292703 * h ^ (2 : ℕ) - 488049 * h ^ (3 : ℕ) - 369017 * h ^ (4 : ℕ) - 58619 * h ^ (5 : ℕ) - 780 * h ^ (6 : ℕ)

/-- `P_{47}(h)`, a univariate factor of `C̃₄`. -/
noncomputable def nlrP47 (h : ℝ) : ℝ :=
  -759 + 436 * h + 3435 * h ^ (2 : ℕ) + 2440 * h ^ (3 : ℕ) + 360 * h ^ (4 : ℕ)

/-- `P_{50}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP50 (h : ℝ) : ℝ :=
  2045 + 274 * h - 2501 * h ^ (2 : ℕ) + 1194 * h ^ (3 : ℕ) + 1080 * h ^ (4 : ℕ)

/-- `P_{51}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP51 (h : ℝ) : ℝ :=
  33401 + 66473 * h - 1933 * h ^ (2 : ℕ) - 61825 * h ^ (3 : ℕ) + 14408 * h ^ (4 : ℕ) + 47196 * h ^ (5 : ℕ) + 10080 * h ^ (6 : ℕ)

/-- `P_{52}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP52 (h : ℝ) : ℝ :=
  284044 + 1267299 * h + 1354250 * h ^ (2 : ℕ) - 231982 * h ^ (3 : ℕ) - 767868 * h ^ (4 : ℕ) + 134635 * h ^ (5 : ℕ) + 359718 * h ^ (6 : ℕ) + 70560 * h ^ (7 : ℕ)

/-- `P_{53}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP53 (h : ℝ) : ℝ :=
  1189999 + 4187845 * h + 3415677 * h ^ (2 : ℕ) - 1421207 * h ^ (3 : ℕ) - 2664028 * h ^ (4 : ℕ) - 604022 * h ^ (5 : ℕ) + 239184 * h ^ (6 : ℕ) + 57960 * h ^ (7 : ℕ)

/-- `P_{54}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP54 (h : ℝ) : ℝ :=
  943067 + 2881934 * h + 1835589 * h ^ (2 : ℕ) - 1373857 * h ^ (3 : ℕ) - 1813517 * h ^ (4 : ℕ) - 519067 * h ^ (5 : ℕ) + 3549 * h ^ (6 : ℕ) + 8190 * h ^ (7 : ℕ)

/-- `P_{55}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP55 (h : ℝ) : ℝ :=
  386159 + 1084357 * h + 549849 * h ^ (2 : ℕ) - 631562 * h ^ (3 : ℕ) - 663211 * h ^ (4 : ℕ) - 178757 * h ^ (5 : ℕ) - 10645 * h ^ (6 : ℕ) + 210 * h ^ (7 : ℕ)

/-- `P_{56}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP56 (h : ℝ) : ℝ :=
  86727 + 221153 * h + 72618 * h ^ (2 : ℕ) - 162432 * h ^ (3 : ℕ) - 126063 * h ^ (4 : ℕ) - 23153 * h ^ (5 : ℕ) - 594 * h ^ (6 : ℕ)

/-- `P_{57}(h)`, a univariate factor of `C̃₅`. -/
noncomputable def nlrP57 (h : ℝ) : ℝ :=
  50 + 1639 * h + 1776 * h ^ (2 : ℕ) + 347 * h ^ (3 : ℕ)

/-- `P_{60}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP60 (h : ℝ) : ℝ :=
  268 - 163 * h - 156 * h ^ (2 : ℕ) + 108 * h ^ (3 : ℕ)

/-- `P_{61}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP61 (h : ℝ) : ℝ :=
  7958 + 10532 * h - 9131 * h ^ (2 : ℕ) - 10567 * h ^ (3 : ℕ) + 3762 * h ^ (4 : ℕ) + 2016 * h ^ (5 : ℕ)

/-- `P_{62}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP62 (h : ℝ) : ℝ :=
  195401 + 527630 * h + 142618 * h ^ (2 : ℕ) - 447188 * h ^ (3 : ℕ) - 241443 * h ^ (4 : ℕ) + 55950 * h ^ (5 : ℕ) + 27720 * h ^ (6 : ℕ)

/-- `P_{63}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP63 (h : ℝ) : ℝ :=
  1128619 + 2548891 * h + 400113 * h ^ (2 : ℕ) - 2008759 * h ^ (3 : ℕ) - 1111828 * h ^ (4 : ℕ) + 3996 * h ^ (5 : ℕ) + 44856 * h ^ (6 : ℕ)

/-- `P_{64}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP64 (h : ℝ) : ℝ :=
  738348 + 1419620 * h + 15555 * h ^ (2 : ℕ) - 1127405 * h ^ (3 : ℕ) - 564117 * h ^ (4 : ℕ) - 44415 * h ^ (5 : ℕ) + 6174 * h ^ (6 : ℕ)

/-- `P_{65}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP65 (h : ℝ) : ℝ :=
  815314 + 1363151 * h - 204114 * h ^ (2 : ℕ) - 1124336 * h ^ (3 : ℕ) - 476434 * h ^ (4 : ℕ) - 46647 * h ^ (5 : ℕ) + 378 * h ^ (6 : ℕ)

/-- `P_{66}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP66 (h : ℝ) : ℝ :=
  164589 + 220226 * h - 104804 * h ^ (2 : ℕ) - 198254 * h ^ (3 : ℕ) - 51289 * h ^ (4 : ℕ) - 1956 * h ^ (5 : ℕ)

/-- `P_{67}(h)`, a univariate factor of `C̃₆`. -/
noncomputable def nlrP67 (h : ℝ) : ℝ :=
  321 + 707 * h + 206 * h ^ (2 : ℕ)

/-- `P_{70}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP70 (h : ℝ) : ℝ :=
  17 - 6 * h

/-- `P_{71}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP71 (h : ℝ) : ℝ :=
  9055 + 3222 * h - 12343 * h ^ (2 : ℕ) - 1350 * h ^ (3 : ℕ) + 2016 * h ^ (4 : ℕ)

/-- `P_{72}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP72 (h : ℝ) : ℝ :=
  278995 + 384097 * h - 232237 * h ^ (2 : ℕ) - 375241 * h ^ (3 : ℕ) - 29694 * h ^ (4 : ℕ) + 27216 * h ^ (5 : ℕ)

/-- `P_{73}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP73 (h : ℝ) : ℝ :=
  83054 + 97195 * h - 65819 * h ^ (2 : ℕ) - 90166 * h ^ (3 : ℕ) - 12429 * h ^ (4 : ℕ) + 2709 * h ^ (5 : ℕ)

/-- `P_{74}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP74 (h : ℝ) : ℝ :=
  366984 + 353231 * h - 294555 * h ^ (2 : ℕ) - 325325 * h ^ (3 : ℕ) - 51465 * h ^ (4 : ℕ) + 2898 * h ^ (5 : ℕ)

/-- `P_{75}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP75 (h : ℝ) : ℝ :=
  353458 + 264973 * h - 295267 * h ^ (2 : ℕ) - 250699 * h ^ (3 : ℕ) - 38031 * h ^ (4 : ℕ) + 126 * h ^ (5 : ℕ)

/-- `P_{76}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP76 (h : ℝ) : ℝ :=
  58723 + 21049 * h - 54001 * h ^ (2 : ℕ) - 23113 * h ^ (3 : ℕ) - 1218 * h ^ (4 : ℕ)

/-- `P_{77}(h)`, a univariate factor of `C̃₇`. -/
noncomputable def nlrP77 (h : ℝ) : ℝ :=
  119 + 69 * h

/-- `P_{81}(h)`, a univariate factor of `C̃₈`. -/
noncomputable def nlrP81 (h : ℝ) : ℝ :=
  335 + 144 * h - 72 * h ^ (2 : ℕ)

/-- `P_{82}(h)`, a univariate factor of `C̃₈`. -/
noncomputable def nlrP82 (h : ℝ) : ℝ :=
  12812 + 4377 * h - 13406 * h ^ (2 : ℕ) - 4521 * h ^ (3 : ℕ) + 954 * h ^ (4 : ℕ)

/-- `P_{83}(h)`, a univariate factor of `C̃₈`. -/
noncomputable def nlrP83 (h : ℝ) : ℝ :=
  56167 + 13983 * h - 53365 * h ^ (2 : ℕ) - 17055 * h ^ (3 : ℕ) + 1494 * h ^ (4 : ℕ)

/-- `P_{84}(h)`, a univariate factor of `C̃₈`. -/
noncomputable def nlrP84 (h : ℝ) : ℝ :=
  109011 + 15983 * h - 95129 * h ^ (2 : ℕ) - 28335 * h ^ (3 : ℕ) + 774 * h ^ (4 : ℕ)

/-- `P_{85}(h)`, a univariate factor of `C̃₈`. -/
noncomputable def nlrP85 (h : ℝ) : ℝ :=
  29855 + 263 * h - 23477 * h ^ (2 : ℕ) - 6167 * h ^ (3 : ℕ) + 6 * h ^ (4 : ℕ)

/-- `P_{86}(h)`, a univariate factor of `C̃₈`. -/
noncomputable def nlrP86 (h : ℝ) : ℝ :=
  5201 + 3072 * h + 207 * h ^ (2 : ℕ)

/-- `P_{91}(h)`, a univariate factor of `C̃₉`. -/
noncomputable def nlrP91 (h : ℝ) : ℝ :=
  25 - 6 * h

/-- `P_{92}(h)`, a univariate factor of `C̃₉`. -/
noncomputable def nlrP92 (h : ℝ) : ℝ :=
  1417 + 787 * h - 78 * h ^ (2 : ℕ)

/-- `P_{93}(h)`, a univariate factor of `C̃₉`. -/
noncomputable def nlrP93 (h : ℝ) : ℝ :=
  783 + 397 * h - 15 * h ^ (2 : ℕ)

/-- `P_{94}(h)`, a univariate factor of `C̃₉`. -/
noncomputable def nlrP94 (h : ℝ) : ℝ :=
  16871 + 7989 * h - 90 * h ^ (2 : ℕ)

/-- `P_{95}(h)`, a univariate factor of `C̃₉`. -/
noncomputable def nlrP95 (h : ℝ) : ℝ :=
  983 + 421 * h

/-- `P_{96}(h)`, a univariate factor of `C̃₉`. -/
noncomputable def nlrP96 (h : ℝ) : ℝ :=
  161 + 15 * h

/-- `S_{0}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrS0 (h : ℝ) : ℝ :=
  150 + 120 * h - 301 * h ^ (2 : ℕ) - 240 * h ^ (3 : ℕ) + 108 * h ^ (4 : ℕ) + 100 * h ^ (5 : ℕ) + 11 * h ^ (6 : ℕ)

/-- `S_{1}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrS1 (h : ℝ) : ℝ :=
  150 + 1500 * h + 637 * h ^ (2 : ℕ) - 3196 * h ^ (3 : ℕ) - 1989 * h ^ (4 : ℕ) + 1390 * h ^ (5 : ℕ) + 1100 * h ^ (6 : ℕ) + 126 * h ^ (7 : ℕ)

/-- `S_{2}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrS2 (h : ℝ) : ℝ :=
  2400 + 8029 * h - 10048 * h ^ (2 : ℕ) - 15570 * h ^ (3 : ℕ) + 5940 * h ^ (4 : ℕ) + 8261 * h ^ (5 : ℕ) + 1128 * h ^ (6 : ℕ)

/-- `U_{00}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrU00 (h : ℝ) : ℝ :=
  2570 + 19532 * h + 19620 * h ^ (2 : ℕ) + 4032 * h ^ (3 : ℕ)

/-- `U_{01}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrU01 (h : ℝ) : ℝ :=
  -6440 + 7858 * h + 126009 * h ^ (2 : ℕ) + 153696 * h ^ (3 : ℕ) + 55380 * h ^ (4 : ℕ) + 6048 * h ^ (5 : ℕ)

/-- `U_{02}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrU02 (h : ℝ) : ℝ :=
  -2970 - 44298 * h - 7488 * h ^ (2 : ℕ) + 299416 * h ^ (3 : ℕ) + 391735 * h ^ (4 : ℕ) + 161532 * h ^ (5 : ℕ) + 20664 * h ^ (6 : ℕ)

/-- `U_{03}(h)`, a univariate factor of `E₀`. -/
noncomputable def nlrU03 (h : ℝ) : ℝ :=
  940 + 22636 * h - 62763 * h ^ (2 : ℕ) - 98500 * h ^ (3 : ℕ) + 246285 * h ^ (4 : ℕ) + 411198 * h ^ (5 : ℕ) + 189938 * h ^ (6 : ℕ) + 26112 * h ^ (7 : ℕ)

/-- `U_{10}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrU10 (h : ℝ) : ℝ :=
  -7780 + 34188 * h + 174720 * h ^ (2 : ℕ) + 173736 * h ^ (3 : ℕ) + 48060 * h ^ (4 : ℕ) + 2592 * h ^ (5 : ℕ)

/-- `U_{11}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrU11 (h : ℝ) : ℝ :=
  1950 - 91660 * h + 176559 * h ^ (2 : ℕ) + 1185720 * h ^ (3 : ℕ) + 1383585 * h ^ (4 : ℕ) + 574416 * h ^ (5 : ℕ) + 89964 * h ^ (6 : ℕ) + 3456 * h ^ (7 : ℕ)

/-- `U_{12}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrU12 (h : ℝ) : ℝ :=
  -38280 - 134214 * h - 385584 * h ^ (2 : ℕ) + 522636 * h ^ (3 : ℕ) + 3033505 * h ^ (4 : ℕ) + 3485616 * h ^ (5 : ℕ) + 1548659 * h ^ (6 : ℕ) + 266160 * h ^ (7 : ℕ) + 9720 * h ^ (8 : ℕ)

/-- `U_{13}(h)`, a univariate factor of `E₁`. -/
noncomputable def nlrU13 (h : ℝ) : ℝ :=
  -26090 + 140112 * h + 591453 * h ^ (2 : ℕ) + 1828 * h ^ (3 : ℕ) - 32365 * h ^ (4 : ℕ) + 2436774 * h ^ (5 : ℕ) + 3431008 * h ^ (6 : ℕ) + 1680080 * h ^ (7 : ℕ) + 299376 * h ^ (8 : ℕ)

/-- `U_{20}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrU20 (h : ℝ) : ℝ :=
  -7620 - 32808 * h + 176076 * h ^ (2 : ℕ) + 356352 * h ^ (3 : ℕ) + 156240 * h ^ (4 : ℕ) + 15552 * h ^ (5 : ℕ)

/-- `U_{21}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrU21 (h : ℝ) : ℝ :=
  21780 - 117828 * h - 283500 * h ^ (2 : ℕ) + 1278504 * h ^ (3 : ℕ) + 2796060 * h ^ (4 : ℕ) + 1722456 * h ^ (5 : ℕ) + 406728 * h ^ (6 : ℕ) + 27648 * h ^ (7 : ℕ)

/-- `U_{22}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrU22 (h : ℝ) : ℝ :=
  -69330 - 77934 * h - 402138 * h ^ (2 : ℕ) - 112580 * h ^ (3 : ℕ) + 4006850 * h ^ (4 : ℕ) + 7087656 * h ^ (5 : ℕ) + 4431434 * h ^ (6 : ℕ) + 1132512 * h ^ (7 : ℕ) + 76464 * h ^ (8 : ℕ)

/-- `U_{23}(h)`, a univariate factor of `E₂`. -/
noncomputable def nlrU23 (h : ℝ) : ℝ :=
  -71124 * h + 1851753 * h ^ (2 : ℕ) + 3007532 * h ^ (3 : ℕ) + 290600 * h ^ (4 : ℕ) + 1882758 * h ^ (5 : ℕ) + 5886265 * h ^ (6 : ℕ) + 4422400 * h ^ (7 : ℕ) + 1195236 * h ^ (8 : ℕ)

/-- The base-quadratic polynomial `a₀(z) = 𝒜₀(1/3, z)`. -/
noncomputable def nlra0 (z : ℝ) : ℝ :=
  (1514 / 9) + (19741 / 9) * z - (864913 / 243) * z ^ (2 : ℕ) - (632434 / 2187) * z ^ (3 : ℕ) + (7868156 / 6561) * z ^ (4 : ℕ) + (9424115 / 19683) * z ^ (5 : ℕ) + (437189 / 6561) * z ^ (6 : ℕ) - (45152 / 59049) * z ^ (7 : ℕ)

/-- The base-quadratic polynomial `a₁(z) = 𝒜₁(1/3, z)`. -/
noncomputable def nlra1 (z : ℝ) : ℝ :=
  (17812 / 27) + (689290 / 243) * z - (37970326 / 2187) * z ^ (2 : ℕ) + (7854788 / 2187) * z ^ (3 : ℕ) + (166227560 / 19683) * z ^ (4 : ℕ) + (51599650 / 19683) * z ^ (5 : ℕ) + (50122106 / 177147) * z ^ (6 : ℕ) - (51824 / 19683) * z ^ (7 : ℕ)

/-- The base-quadratic polynomial `a₂(z) = 𝒜₂(1/3, z)`. -/
noncomputable def nlra2 (z : ℝ) : ℝ :=
  (14324 / 9) + (115918 / 81) * z - (30095420 / 2187) * z ^ (2 : ℕ) + (3564514 / 243) * z ^ (3 : ℕ) + (286749662 / 19683) * z ^ (4 : ℕ) + (24894044 / 6561) * z ^ (5 : ℕ) + (20583334 / 59049) * z ^ (6 : ℕ) - (429568 / 177147) * z ^ (7 : ℕ)

/-! ### The coefficient functions -/

/-- `𝒜_0(h, z)`, a coefficient function of the quadratic part
`h³w³(𝒜₀ + β𝒜₁ + wβ²𝒜₂)` (`y = hz`). -/
noncomputable def nlrA0 (h z : ℝ) : ℝ :=
  (nlrB00 h + z * nlrB01 h + z ^ (2 : ℕ) * nlrB02 h + z ^ (3 : ℕ) * nlrB03 h + h * z ^ (4 : ℕ) * nlrB04 h + h ^ (2 : ℕ) * z ^ (5 : ℕ) * nlrB05 h + h ^ (3 : ℕ) * z ^ (6 : ℕ) * nlrB06 h + h ^ (5 : ℕ) * z ^ (7 : ℕ) * nlrB07 h) / 2

/-- `𝒜_1(h, z)`, a coefficient function of the quadratic part
`h³w³(𝒜₀ + β𝒜₁ + wβ²𝒜₂)` (`y = hz`). -/
noncomputable def nlrA1 (h z : ℝ) : ℝ :=
  (nlrB10 h + z * nlrB11 h + z ^ (2 : ℕ) * (1080 * h ^ (9 : ℕ) + nlrB12 h) + h * z ^ (3 : ℕ) * (936 * h ^ (9 : ℕ) + nlrB13 h) + h ^ (2 : ℕ) * z ^ (4 : ℕ) * (288 * h ^ (9 : ℕ) + nlrB14 h) + h ^ (3 : ℕ) * z ^ (5 : ℕ) * (18 * h ^ (9 : ℕ) + nlrB15 h) + h ^ (4 : ℕ) * z ^ (6 : ℕ) * nlrB16 h + h ^ (5 : ℕ) * z ^ (7 : ℕ) * nlrB17 h) / 2

/-- `𝒜_2(h, z)`, a coefficient function of the quadratic part
`h³w³(𝒜₀ + β𝒜₁ + wβ²𝒜₂)` (`y = hz`). -/
noncomputable def nlrA2 (h z : ℝ) : ℝ :=
  (nlrB20 h + z * nlrB21 h + h * z ^ (2 : ℕ) * nlrB22 h + h ^ (2 : ℕ) * z ^ (3 : ℕ) * nlrB23 h + h ^ (3 : ℕ) * z ^ (4 : ℕ) * nlrB24 h + h ^ (4 : ℕ) * z ^ (5 : ℕ) * nlrB25 h + h ^ (5 : ℕ) * z ^ (6 : ℕ) * nlrB26 h + h ^ (6 : ℕ) * z ^ (7 : ℕ) * nlrB27 h) / 2

/-- `E_0 = 2∂_h𝒜_0`. -/
noncomputable def nlrE0 (h z : ℝ) : ℝ :=
  nlrU00 h + z * nlrU01 h + z ^ (2 : ℕ) * nlrU02 h + z ^ (3 : ℕ) * nlrU03 h + z ^ (4 : ℕ) * nlrP04 h + h * z ^ (5 : ℕ) * nlrP05 h + h ^ (2 : ℕ) * z ^ (6 : ℕ) * nlrP06 h - 12 * h ^ (4 : ℕ) * z ^ (7 : ℕ) * nlrS0 h

/-- `E_1 = 2∂_h𝒜_1`. -/
noncomputable def nlrE1 (h z : ℝ) : ℝ :=
  nlrU10 h + z * nlrU11 h + z ^ (2 : ℕ) * nlrU12 h + z ^ (3 : ℕ) * (nlrU13 h + 9360 * h ^ (9 : ℕ)) + h * z ^ (4 : ℕ) * (nlrP14 h + 3168 * h ^ (9 : ℕ)) + h ^ (2 : ℕ) * z ^ (5 : ℕ) * (nlrP15 h + 216 * h ^ (9 : ℕ)) + h ^ (3 : ℕ) * z ^ (6 : ℕ) * nlrP16 h - 12 * h ^ (4 : ℕ) * z ^ (7 : ℕ) * nlrS1 h

/-- `E_2 = 2∂_h𝒜_2`. -/
noncomputable def nlrE2 (h z : ℝ) : ℝ :=
  nlrU20 h + z * nlrU21 h + z ^ (2 : ℕ) * nlrU22 h + z ^ (3 : ℕ) * (nlrU23 h + 72720 * h ^ (9 : ℕ)) + h ^ (2 : ℕ) * z ^ (4 : ℕ) * nlrP24 h + h ^ (3 : ℕ) * z ^ (5 : ℕ) * nlrP25 h + h ^ (4 : ℕ) * z ^ (6 : ℕ) * nlrP26 h - 6 * h ^ (5 : ℕ) * z ^ (7 : ℕ) * nlrS2 h

/-- `C̃_0(h, y)`, the coefficient of `j^0` in the collected polynomial. -/
noncomputable def nlrC0 (h y : ℝ) : ℝ :=
  ((1 + h) ^ (3 : ℕ) * h ^ (3 : ℕ) * nlrB00 h / 2) +
    ((1 + h) ^ (3 : ℕ) * h ^ (2 : ℕ) * nlrB01 h / 2) * y +
    ((1 + h) ^ (3 : ℕ) * h * nlrB02 h / 2) * y ^ (2 : ℕ) +
    ((1 + h) ^ (3 : ℕ) * nlrB03 h / 2) * y ^ (3 : ℕ) +
    ((1 + h) ^ (3 : ℕ) * nlrB04 h / 2) * y ^ (4 : ℕ) +
    ((1 + h) ^ (3 : ℕ) * nlrB05 h / 2) * y ^ (5 : ℕ) +
    ((1 + h) ^ (3 : ℕ) * nlrB06 h / 2) * y ^ (6 : ℕ) +
    ((1 + h) ^ (3 : ℕ) * h * nlrB07 h / 2) * y ^ (7 : ℕ)

/-- `C̃_1(h, y)`, the coefficient of `j^1` in the collected polynomial. -/
noncomputable def nlrC1 (h y : ℝ) : ℝ :=
  ((1 + h) ^ (2 : ℕ) * h ^ (2 : ℕ) * nlrB10 h / 2) +
    ((1 + h) ^ (2 : ℕ) * h * nlrB11 h / 2) * y +
    ((1 + h) ^ (2 : ℕ) * (1080 * h ^ (9 : ℕ) + nlrB12 h) / 2) * y ^ (2 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * (936 * h ^ (9 : ℕ) + nlrB13 h) / 2) * y ^ (3 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * (288 * h ^ (9 : ℕ) + nlrB14 h) / 2) * y ^ (4 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * (18 * h ^ (9 : ℕ) + nlrB15 h) / 2) * y ^ (5 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB16 h / 2) * y ^ (6 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB17 h / 2) * y ^ (7 : ℕ)

/-- `C̃_2(h, y)`, the coefficient of `j^2` in the collected polynomial. -/
noncomputable def nlrC2 (h y : ℝ) : ℝ :=
  ((1 + h) ^ (2 : ℕ) * h * nlrB20 h / 2) +
    ((1 + h) ^ (2 : ℕ) * nlrB21 h / 2) * y +
    ((1 + h) ^ (2 : ℕ) * nlrB22 h / 2) * y ^ (2 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB23 h / 2) * y ^ (3 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB24 h / 2) * y ^ (4 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB25 h / 2) * y ^ (5 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB26 h / 2) * y ^ (6 : ℕ) +
    ((1 + h) ^ (2 : ℕ) * nlrB27 h / 2) * y ^ (7 : ℕ)

/-- `C̃_3(h, y)`, the coefficient of `j^3` in the collected polynomial. -/
noncomputable def nlrC3 (h y : ℝ) : ℝ :=
  (2 * (h + 1) ^ (2 : ℕ) * nlrP30 h) +
    ((h + 1) * nlrP31 h) * y +
    ((h + 1) * nlrP32 h / 2) * y ^ (2 : ℕ) +
    ((h + 1) * nlrP33 h / 2) * y ^ (3 : ℕ) +
    ((h + 1) * nlrP34 h) * y ^ (4 : ℕ) +
    ((h + 1) * nlrP35 h / 2) * y ^ (5 : ℕ) +
    ((h + 1) * nlrP36 h / 2) * y ^ (6 : ℕ) +
    (3 * (h + 1) * (1 - h) * nlrP37 h) * y ^ (7 : ℕ)

/-- `C̃_4(h, y)`, the coefficient of `j^4` in the collected polynomial. -/
noncomputable def nlrC4 (h y : ℝ) : ℝ :=
  ((h + 1) ^ (2 : ℕ) * nlrP40 h) +
    ((h + 1) * nlrP41 h / 2) * y +
    ((h + 1) * nlrP42 h / 2) * y ^ (2 : ℕ) +
    ((h + 1) * nlrP43 h / 2) * y ^ (3 : ℕ) +
    ((h + 1) * nlrP44 h) * y ^ (4 : ℕ) +
    ((h + 1) * nlrP45 h / 2) * y ^ (5 : ℕ) +
    ((h + 1) * nlrP46 h / 2) * y ^ (6 : ℕ) +
    (3 * (h + 1) * (1 - h) * nlrP47 h) * y ^ (7 : ℕ)

/-- `C̃_5(h, y)`, the coefficient of `j^5` in the collected polynomial. -/
noncomputable def nlrC5 (h y : ℝ) : ℝ :=
  (3 * (h + 1) ^ (2 : ℕ) * nlrP50 h) +
    (3 * (h + 1) * nlrP51 h / 2) * y +
    (nlrP52 h / 2) * y ^ (2 : ℕ) +
    (nlrP53 h / 2) * y ^ (3 : ℕ) +
    (nlrP54 h) * y ^ (4 : ℕ) +
    (3 * nlrP55 h / 2) * y ^ (5 : ℕ) +
    (3 * nlrP56 h / 2) * y ^ (6 : ℕ) +
    (3 * (h + 1) * (1 - h) * nlrP57 h) * y ^ (7 : ℕ)

/-- `C̃_6(h, y)`, the coefficient of `j^6` in the collected polynomial. -/
noncomputable def nlrC6 (h y : ℝ) : ℝ :=
  (12 * (h + 1) ^ (2 : ℕ) * nlrP60 h) +
    (6 * (h + 1) * nlrP61 h) * y +
    (nlrP62 h) * y ^ (2 : ℕ) +
    (nlrP63 h / 2) * y ^ (3 : ℕ) +
    (nlrP64 h) * y ^ (4 : ℕ) +
    (nlrP65 h / 2) * y ^ (5 : ℕ) +
    (nlrP66 h / 2) * y ^ (6 : ℕ) +
    (3 * (h + 1) * (1 - h) * nlrP67 h) * y ^ (7 : ℕ)

/-- `C̃_7(h, y)`, the coefficient of `j^7` in the collected polynomial. -/
noncomputable def nlrC7 (h y : ℝ) : ℝ :=
  (36 * (h + 1) ^ (2 : ℕ) * (1 - h) * nlrP70 h) +
    (3 * (h + 1) * nlrP71 h) * y +
    (nlrP72 h / 2) * y ^ (2 : ℕ) +
    (4 * nlrP73 h) * y ^ (3 : ℕ) +
    (nlrP74 h) * y ^ (4 : ℕ) +
    (nlrP75 h / 2) * y ^ (5 : ℕ) +
    (nlrP76 h / 2) * y ^ (6 : ℕ) +
    (3 * (h + 1) * (1 - h) * nlrP77 h) * y ^ (7 : ℕ)

/-- `C̃_8(h, y)`, the coefficient of `j^8` in the collected polynomial. -/
noncomputable def nlrC8 (h y : ℝ) : ℝ :=
  (24 * (h + 1) * (1 - h) * nlrP81 h) * y +
    (4 * nlrP82 h) * y ^ (2 : ℕ) +
    (2 * nlrP83 h) * y ^ (3 : ℕ) +
    (nlrP84 h) * y ^ (4 : ℕ) +
    (3 * nlrP85 h / 2) * y ^ (5 : ℕ) +
    ((1 - h) * nlrP86 h) * y ^ (6 : ℕ) +
    (30 * (h + 1) * (1 - h)) * y ^ (7 : ℕ)

/-- `C̃_9(h, y)`, the coefficient of `j^9` in the collected polynomial. -/
noncomputable def nlrC9 (h y : ℝ) : ℝ :=
  (36 * (h + 1) * (1 - h) * nlrP91 h) * y +
    (6 * (1 - h) * nlrP92 h) * y ^ (2 : ℕ) +
    (24 * (1 - h) * nlrP93 h) * y ^ (3 : ℕ) +
    ((1 - h) * nlrP94 h) * y ^ (4 : ℕ) +
    (6 * (1 - h) * nlrP95 h) * y ^ (5 : ℕ) +
    (2 * (1 - h) * nlrP96 h) * y ^ (6 : ℕ)

/-- `C̃_10(h, y)`, the coefficient of `j^10` in the collected polynomial. -/
noncomputable def nlrC10 (h y : ℝ) : ℝ :=
  (432 * (1 - h)) * y ^ (2 : ℕ) +
    (1080 * (1 - h)) * y ^ (3 : ℕ) +
    (960 * (1 - h)) * y ^ (4 : ℕ) +
    (300 * (1 - h)) * y ^ (5 : ℕ)

/-! ### Monomial bounds on `[1/3, 1/2]` -/

theorem nlr_hb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) :
    (1 / 9 : ℝ) ≤ h ^ (2 : ℕ) ∧ h ^ (2 : ℕ) ≤ 1 / 4 ∧ (1 / 27 : ℝ) ≤ h ^ (3 : ℕ) ∧ h ^ (3 : ℕ) ≤ 1 / 8 ∧
      (1 / 81 : ℝ) ≤ h ^ (4 : ℕ) ∧ h ^ (4 : ℕ) ≤ 1 / 16 ∧ (1 / 243 : ℝ) ≤ h ^ (5 : ℕ) ∧ h ^ (5 : ℕ) ≤ 1 / 32 ∧
      (1 / 729 : ℝ) ≤ h ^ (6 : ℕ) ∧ h ^ (6 : ℕ) ≤ 1 / 64 ∧ (1 / 2187 : ℝ) ≤ h ^ (7 : ℕ) ∧ h ^ (7 : ℕ) ≤ 1 / 128 ∧
      (1 / 6561 : ℝ) ≤ h ^ (8 : ℕ) ∧ h ^ (8 : ℕ) ≤ 1 / 256 := by
  have l : ∀ n : ℕ, (1 / 3 : ℝ) ^ n ≤ h ^ n := fun n => pow_le_pow_left₀ (by norm_num) h1 n
  have u : ∀ n : ℕ, h ^ n ≤ (1 / 2 : ℝ) ^ n := fun n => pow_le_pow_left₀ (by linarith) h2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have := l 2; norm_num at this ⊢; linarith) | (have := u 2; norm_num at this ⊢; linarith)
    | (have := l 3; norm_num at this ⊢; linarith) | (have := u 3; norm_num at this ⊢; linarith)
    | (have := l 4; norm_num at this ⊢; linarith) | (have := u 4; norm_num at this ⊢; linarith)
    | (have := l 5; norm_num at this ⊢; linarith) | (have := u 5; norm_num at this ⊢; linarith)
    | (have := l 6; norm_num at this ⊢; linarith) | (have := u 6; norm_num at this ⊢; linarith)
    | (have := l 7; norm_num at this ⊢; linarith) | (have := u 7; norm_num at this ⊢; linarith)
    | (have := l 8; norm_num at this ⊢; linarith) | (have := u 8; norm_num at this ⊢; linarith)

/-- `P04 > 0` by monomial bounds. -/
theorem nlr_P04_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP04 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP04; linarith only [h1, l2, l3, l6, l7, l8, u4, u5]

/-- `P05 > 0` by monomial bounds. -/
theorem nlr_P05_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP05 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP05; linarith only [h1, l2, l3, l7, l8, u4, u5, u6]

/-- `P06 > 0` by monomial bounds. -/
theorem nlr_P06_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP06 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP06; linarith only [h1, l2, l3, l8, u4, u5, u6, u7]

/-- `P14 > 0` by monomial bounds. -/
theorem nlr_P14_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP14 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP14; linarith only [h1, l2, l3, l6, l7, l8, u4, u5]

/-- `P15 > 0` by monomial bounds. -/
theorem nlr_P15_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP15 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP15; linarith only [h1, l2, l3, l7, l8, u4, u5, u6]

/-- `P16 > 0` by monomial bounds. -/
theorem nlr_P16_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP16 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP16; linarith only [h1, l2, l3, l8, u4, u5, u6, u7]

/-- `P24 > 0` by monomial bounds. -/
theorem nlr_P24_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP24 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP24; linarith only [h1, l2, l3, l6, l7, l8, u4, u5]

/-- `P25 > 0` by monomial bounds. -/
theorem nlr_P25_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP25 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP25; linarith only [h1, l2, l3, l7, l8, u4, u5, u6]

/-- `P26 > 0` by monomial bounds. -/
theorem nlr_P26_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP26 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP26; linarith only [h1, l2, l3, l7, u4, u5, u6]

/-- `P30 > 400` by monomial bounds. -/
theorem nlr_P30_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 400 < nlrP30 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP30; linarith only [h1, l4, l5, l6, u2, u3]

/-- `P31 > 0` by monomial bounds. -/
theorem nlr_P31_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP31 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP31; linarith only [h1, l4, l5, l6, l7, l8, u2, u3]

/-- `P32 > 0` by monomial bounds. -/
theorem nlr_P32_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP32 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP32; linarith only [h1, l2, l3, l4, l5, l6, l7, l8]

/-- `P33 > 0` by monomial bounds. -/
theorem nlr_P33_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP33 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP33; linarith only [h1, l2, l3, l4, l5, l6, l7, l8]

/-- `P34 > 0` by monomial bounds. -/
theorem nlr_P34_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP34 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP34; linarith only [h1, l2, l3, l6, l7, l8, u4, u5]

/-- `P35 > 0` by monomial bounds. -/
theorem nlr_P35_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP35 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP35; linarith only [h1, l2, l3, l7, l8, u4, u5, u6]

/-- `P36 > 0` by monomial bounds. -/
theorem nlr_P36_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP36 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP36; linarith only [h1, l2, l7, u3, u4, u5, u6]

/-- `P37 > -2000` by monomial bounds. -/
theorem nlr_P37_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : (-2000 : ℝ) < nlrP37 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP37; linarith only [h2, l2, l3, l4, l5]

/-- `P40 > 4000` by monomial bounds. -/
theorem nlr_P40_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 4000 < nlrP40 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP40; linarith only [h1, l3, l4, l5, u2]

/-- `P41 > 0` by monomial bounds. -/
theorem nlr_P41_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP41 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP41; linarith only [h1, l2, l4, l5, l6, l7, u3]

/-- `P42 > 0` by monomial bounds. -/
theorem nlr_P42_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP42 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP42; linarith only [h1, l2, l3, l4, l5, l6, l7]

/-- `P43 > 0` by monomial bounds. -/
theorem nlr_P43_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP43 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP43; linarith only [h1, l2, l5, l6, l7, u3, u4]

/-- `P44 > 0` by monomial bounds. -/
theorem nlr_P44_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP44 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP44; linarith only [h1, l2, l6, l7, u3, u4, u5]

/-- `P45 > 0` by monomial bounds. -/
theorem nlr_P45_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP45 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP45; linarith only [h1, l2, l7, u3, u4, u5, u6]

/-- `P46 > 0` by monomial bounds. -/
theorem nlr_P46_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP46 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP46; linarith only [h1, l2, u3, u4, u5, u6]

/-- `P47 > -200` by monomial bounds. -/
theorem nlr_P47_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : (-200 : ℝ) < nlrP47 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP47; linarith only [h1, l2, l3, l4]

/-- `P50 > 0` by monomial bounds. -/
theorem nlr_P50_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP50 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP50; linarith only [h1, l3, l4, u2]

/-- `P51 > 0` by monomial bounds. -/
theorem nlr_P51_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP51 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP51; linarith only [h1, l4, l5, l6, u2, u3]

/-- `P52 > 0` by monomial bounds. -/
theorem nlr_P52_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP52 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP52; linarith only [h1, l2, l5, l6, l7, u3, u4]

/-- `P53 > 0` by monomial bounds. -/
theorem nlr_P53_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP53 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP53; linarith only [h1, l2, l6, l7, u3, u4, u5]

/-- `P54 > 0` by monomial bounds. -/
theorem nlr_P54_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP54 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP54; linarith only [h1, l2, l6, l7, u3, u4, u5]

/-- `P55 > 0` by monomial bounds. -/
theorem nlr_P55_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP55 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP55; linarith only [h1, l2, l7, u3, u4, u5, u6]

/-- `P56 > 0` by monomial bounds. -/
theorem nlr_P56_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP56 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP56; linarith only [h1, l2, u3, u4, u5, u6]

/-- `P57 > 0` by monomial bounds. -/
theorem nlr_P57_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP57 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP57; linarith only [h1, l2, l3]

/-- `P60 > 0` by monomial bounds. -/
theorem nlr_P60_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP60 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP60; linarith only [h2, l3, u2]

/-- `P61 > 0` by monomial bounds. -/
theorem nlr_P61_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP61 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP61; linarith only [h1, l4, l5, u2, u3]

/-- `P62 > 0` by monomial bounds. -/
theorem nlr_P62_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP62 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP62; linarith only [h1, l2, l5, l6, u3, u4]

/-- `P63 > 0` by monomial bounds. -/
theorem nlr_P63_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP63 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP63; linarith only [h1, l2, l5, l6, u3, u4]

/-- `P64 > 0` by monomial bounds. -/
theorem nlr_P64_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP64 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP64; linarith only [h1, l2, l6, u3, u4, u5]

/-- `P65 > 0` by monomial bounds. -/
theorem nlr_P65_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP65 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP65; linarith only [h1, l6, u2, u3, u4, u5]

/-- `P66 > 0` by monomial bounds. -/
theorem nlr_P66_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP66 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP66; linarith only [h1, u2, u3, u4, u5]

/-- `P67 > 0` by monomial bounds. -/
theorem nlr_P67_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP67 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP67; linarith only [h1, l2]

/-- `P70 > 0` by monomial bounds. -/
theorem nlr_P70_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP70 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP70; linarith only [h2]

/-- `P71 > 0` by monomial bounds. -/
theorem nlr_P71_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP71 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP71; linarith only [h1, l4, u2, u3]

/-- `P72 > 0` by monomial bounds. -/
theorem nlr_P72_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP72 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP72; linarith only [h1, l5, u2, u3, u4]

/-- `P73 > 0` by monomial bounds. -/
theorem nlr_P73_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP73 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP73; linarith only [h1, l5, u2, u3, u4]

/-- `P74 > 0` by monomial bounds. -/
theorem nlr_P74_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP74 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP74; linarith only [h1, l5, u2, u3, u4]

/-- `P75 > 0` by monomial bounds. -/
theorem nlr_P75_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP75 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP75; linarith only [h1, l5, u2, u3, u4]

/-- `P76 > 0` by monomial bounds. -/
theorem nlr_P76_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP76 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP76; linarith only [h1, u2, u3, u4]

/-- `P77 > 0` by monomial bounds. -/
theorem nlr_P77_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP77 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP77; linarith only [h1]

/-- `P81 > 0` by monomial bounds. -/
theorem nlr_P81_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP81 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP81; linarith only [h1, u2]

/-- `P82 > 0` by monomial bounds. -/
theorem nlr_P82_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP82 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP82; linarith only [h1, l4, u2, u3]

/-- `P83 > 0` by monomial bounds. -/
theorem nlr_P83_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP83 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP83; linarith only [h1, l4, u2, u3]

/-- `P84 > 0` by monomial bounds. -/
theorem nlr_P84_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP84 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP84; linarith only [h1, l4, u2, u3]

/-- `P85 > 0` by monomial bounds. -/
theorem nlr_P85_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP85 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP85; linarith only [h1, l4, u2, u3]

/-- `P86 > 0` by monomial bounds. -/
theorem nlr_P86_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP86 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP86; linarith only [h1, l2]

/-- `P91 > 0` by monomial bounds. -/
theorem nlr_P91_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP91 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP91; linarith only [h2]

/-- `P92 > 0` by monomial bounds. -/
theorem nlr_P92_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP92 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP92; linarith only [h1, u2]

/-- `P93 > 0` by monomial bounds. -/
theorem nlr_P93_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP93 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP93; linarith only [h1, u2]

/-- `P94 > 0` by monomial bounds. -/
theorem nlr_P94_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP94 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP94; linarith only [h1, u2]

/-- `P95 > 0` by monomial bounds. -/
theorem nlr_P95_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP95 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP95; linarith only [h1]

/-- `P96 > 0` by monomial bounds. -/
theorem nlr_P96_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 < nlrP96 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrP96; linarith only [h1]

/-- `U00 ≥ 11000` by monomial bounds. -/
theorem nlr_U00_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 11000 ≤ nlrU00 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrU00; linarith only [h1, l2, l3]

/-- `U01 ≥ 0` by monomial bounds. -/
theorem nlr_U01_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 ≤ nlrU01 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrU01; linarith only [h1, l2, l3, l4, l5]

/-- `U10 ≥ 30000` by monomial bounds. -/
theorem nlr_U10_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 30000 ≤ nlrU10 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrU10; linarith only [h1, l2, l3, l4, l5]

/-- `U11 ≥ 0` by monomial bounds. -/
theorem nlr_U11_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 0 ≤ nlrU11 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrU11; linarith only [h2, l2, l3, l4, l5, l6, l7]

/-- `U23 ≥ 100000` by monomial bounds. -/
theorem nlr_U23_lb {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : 100000 ≤ nlrU23 h := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrU23; linarith only [h2, l2, l3, l4, l5, l6, l7, l8]

/-- `U02 ≥ -2000`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U02_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : (-2000 : ℝ) ≤ nlrU02 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU02 h = (-(157885 / 81) : ℝ) + ((3213850 / 27) * (h - 1 / 3) + 616738 * (h - 1 / 3) ^ (2 : ℕ) + 1016516 * (h - 1 / 3) ^ (3 : ℕ) + 695395 * (h - 1 / 3) ^ (4 : ℕ) + 202860 * (h - 1 / 3) ^ (5 : ℕ) + 20664 * (h - 1 / 3) ^ (6 : ℕ)) := by unfold nlrU02; ring
  have : 0 ≤ (3213850 / 27) * (h - 1 / 3) + 616738 * (h - 1 / 3) ^ (2 : ℕ) + 1016516 * (h - 1 / 3) ^ (3 : ℕ) + 695395 * (h - 1 / 3) ^ (4 : ℕ) + 202860 * (h - 1 / 3) ^ (5 : ℕ) + 20664 * (h - 1 / 3) ^ (6 : ℕ) := by positivity
  rw [e]; linarith

/-- `U03 ≥ 0`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U03_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : 0 ≤ nlrU03 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU03 h = (697102 / 243) + ((3589228 / 243) * (h - 1 / 3) + (5201627 / 27) * (h - 1 / 3) ^ (2 : ℕ) + (7548700 / 9) * (h - 1 / 3) ^ (3 : ℕ) + (11538245 / 9) * (h - 1 / 3) ^ (4 : ℕ) + 852002 * (h - 1 / 3) ^ (5 : ℕ) + 250866 * (h - 1 / 3) ^ (6 : ℕ) + 26112 * (h - 1 / 3) ^ (7 : ℕ)) := by unfold nlrU03; ring
  have : 0 ≤ (3589228 / 243) * (h - 1 / 3) + (5201627 / 27) * (h - 1 / 3) ^ (2 : ℕ) + (7548700 / 9) * (h - 1 / 3) ^ (3 : ℕ) + (11538245 / 9) * (h - 1 / 3) ^ (4 : ℕ) + 852002 * (h - 1 / 3) ^ (5 : ℕ) + 250866 * (h - 1 / 3) ^ (6 : ℕ) + 26112 * (h - 1 / 3) ^ (7 : ℕ) := by positivity
  rw [e]; linarith

/-- `U12 ≥ -60000`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U12_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : (-60000 : ℝ) ≤ nlrU12 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU12 h = (-(4249378 / 81) : ℝ) + ((118666960 / 243) * (h - 1 / 3) + (101534069 / 27) * (h - 1 / 3) ^ (2 : ℕ) + (87341564 / 9) * (h - 1 / 3) ^ (3 : ℕ) + (105996470 / 9) * (h - 1 / 3) ^ (4 : ℕ) + 7224134 * (h - 1 / 3) ^ (5 : ℕ) + 2199939 * (h - 1 / 3) ^ (6 : ℕ) + 292080 * (h - 1 / 3) ^ (7 : ℕ) + 9720 * (h - 1 / 3) ^ (8 : ℕ)) := by unfold nlrU12; ring
  have : 0 ≤ (118666960 / 243) * (h - 1 / 3) + (101534069 / 27) * (h - 1 / 3) ^ (2 : ℕ) + (87341564 / 9) * (h - 1 / 3) ^ (3 : ℕ) + (105996470 / 9) * (h - 1 / 3) ^ (4 : ℕ) + 7224134 * (h - 1 / 3) ^ (5 : ℕ) + 2199939 * (h - 1 / 3) ^ (6 : ℕ) + 292080 * (h - 1 / 3) ^ (7 : ℕ) + 9720 * (h - 1 / 3) ^ (8 : ℕ) := by positivity
  rw [e]; linarith

/-- `U13 ≥ 100000`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U13_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : 100000 ≤ nlrU13 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU13 h = (222083972 / 2187) + ((570508460 / 729) * (h - 1 / 3) + (183568343 / 81) * (h - 1 / 3) ^ (2 : ℕ) + (486213940 / 81) * (h - 1 / 3) ^ (3 : ℕ) + (328964575 / 27) * (h - 1 / 3) ^ (4 : ℕ) + (41519714 / 3) * (h - 1 / 3) ^ (5 : ℕ) + (24847760 / 3) * (h - 1 / 3) ^ (6 : ℕ) + 2478416 * (h - 1 / 3) ^ (7 : ℕ) + 299376 * (h - 1 / 3) ^ (8 : ℕ)) := by unfold nlrU13; ring
  have : 0 ≤ (570508460 / 729) * (h - 1 / 3) + (183568343 / 81) * (h - 1 / 3) ^ (2 : ℕ) + (486213940 / 81) * (h - 1 / 3) ^ (3 : ℕ) + (328964575 / 27) * (h - 1 / 3) ^ (4 : ℕ) + (41519714 / 3) * (h - 1 / 3) ^ (5 : ℕ) + (24847760 / 3) * (h - 1 / 3) ^ (6 : ℕ) + 2478416 * (h - 1 / 3) ^ (7 : ℕ) + 299376 * (h - 1 / 3) ^ (8 : ℕ) := by positivity
  rw [e]; linarith

/-- `U20 ≥ 16000`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U20_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : 16000 ≤ nlrU20 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU20 h = (145792 / 9) + ((682400 / 3) * (h - 1 / 3) + 642348 * (h - 1 / 3) ^ (2 : ℕ) + 581952 * (h - 1 / 3) ^ (3 : ℕ) + 182160 * (h - 1 / 3) ^ (4 : ℕ) + 15552 * (h - 1 / 3) ^ (5 : ℕ)) := by unfold nlrU20; ring
  have : 0 ≤ (682400 / 3) * (h - 1 / 3) + 642348 * (h - 1 / 3) ^ (2 : ℕ) + 581952 * (h - 1 / 3) ^ (3 : ℕ) + 182160 * (h - 1 / 3) ^ (4 : ℕ) + 15552 * (h - 1 / 3) ^ (5 : ℕ) := by positivity
  rw [e]; linarith

/-- `U21 ≥ 0`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U21_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : 0 ≤ nlrU21 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU21 h = (3283264 / 81) + ((17555500 / 27) * (h - 1 / 3) + 3574700 * (h - 1 / 3) ^ (2 : ℕ) + (21700952 / 3) * (h - 1 / 3) ^ (3 : ℕ) + 6380540 * (h - 1 / 3) ^ (4 : ℕ) + 2600424 * (h - 1 / 3) ^ (5 : ℕ) + 471240 * (h - 1 / 3) ^ (6 : ℕ) + 27648 * (h - 1 / 3) ^ (7 : ℕ)) := by unfold nlrU21; ring
  have : 0 ≤ (17555500 / 27) * (h - 1 / 3) + 3574700 * (h - 1 / 3) ^ (2 : ℕ) + (21700952 / 3) * (h - 1 / 3) ^ (3 : ℕ) + 6380540 * (h - 1 / 3) ^ (4 : ℕ) + 2600424 * (h - 1 / 3) ^ (5 : ℕ) + 471240 * (h - 1 / 3) ^ (6 : ℕ) + 27648 * (h - 1 / 3) ^ (7 : ℕ) := by positivity
  rw [e]; linarith

/-- `U22 ≥ -60000`: its Taylor coefficients at `h = 1/3` beyond the constant are nonnegative. -/
theorem nlr_U22_lb {h : ℝ} (h1 : 1 / 3 ≤ h) : (-60000 : ℝ) ≤ nlrU22 h := by
  have s : 0 ≤ h - 1 / 3 := by linarith
  have e : nlrU22 h = (-(42950318 / 729) : ℝ) + ((186657242 / 243) * (h - 1 / 3) + (17109052 / 3) * (h - 1 / 3) ^ (2 : ℕ) + (456153716 / 27) * (h - 1 / 3) ^ (3 : ℕ) + (222655360 / 9) * (h - 1 / 3) ^ (4 : ℕ) + 18751644 * (h - 1 / 3) ^ (5 : ℕ) + 7311850 * (h - 1 / 3) ^ (6 : ℕ) + 1336416 * (h - 1 / 3) ^ (7 : ℕ) + 76464 * (h - 1 / 3) ^ (8 : ℕ)) := by unfold nlrU22; ring
  have : 0 ≤ (186657242 / 243) * (h - 1 / 3) + (17109052 / 3) * (h - 1 / 3) ^ (2 : ℕ) + (456153716 / 27) * (h - 1 / 3) ^ (3 : ℕ) + (222655360 / 9) * (h - 1 / 3) ^ (4 : ℕ) + 18751644 * (h - 1 / 3) ^ (5 : ℕ) + 7311850 * (h - 1 / 3) ^ (6 : ℕ) + 1336416 * (h - 1 / 3) ^ (7 : ℕ) + 76464 * (h - 1 / 3) ^ (8 : ℕ) := by positivity
  rw [e]; linarith

/-- `S0 < 221` by monomial bounds. -/
theorem nlr_S0_ub {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : nlrS0 h ≤ 221 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrS0; linarith only [h2, l2, l3, u4, u5, u6]

/-- `S1 < 1121` by monomial bounds. -/
theorem nlr_S1_ub {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : nlrS1 h ≤ 1121 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrS1; linarith only [h2, l3, l4, u2, u5, u6, u7]

/-- `S2 < 7062` by monomial bounds. -/
theorem nlr_S2_ub {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) : nlrS2 h ≤ 7062 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := nlr_hb h1 h2
  unfold nlrS2; linarith only [h2, l2, l3, u4, u5, u6]

/-! ### The three `h`-derivatives are positive -/

theorem nlr_E0_nonneg {h z : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ nlrE0 h z := by
  have u0 := nlr_U00_lb h1 h2
  have u1 := nlr_U01_lb h1 h2
  have u2 := nlr_U02_lb h1
  have u3 := nlr_U03_lb h1
  have p4 := nlr_P04_lb h1 h2
  have p5 := nlr_P05_lb h1 h2
  have p6 := nlr_P06_lb h1 h2
  have s0 := nlr_S0_ub h1 h2
  have hh : 0 ≤ h := by linarith
  have h4 : h ^ (4 : ℕ) ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hh h2 4; norm_num at this; linarith
  have z2 : z ^ (2 : ℕ) ≤ 1 := pow_le_one₀ hz0 hz1
  have z7 : z ^ (7 : ℕ) ≤ 1 := pow_le_one₀ hz0 hz1
  have t1 : 0 ≤ z * nlrU01 h := mul_nonneg hz0 u1
  have t2 : 0 ≤ z ^ (2 : ℕ) * (nlrU02 h + 2000) := mul_nonneg (by positivity) (by linarith)
  have t3 : 0 ≤ z ^ (3 : ℕ) * nlrU03 h := mul_nonneg (by positivity) u3
  have t4 : 0 ≤ z ^ (4 : ℕ) * nlrP04 h := by positivity
  have t5 : 0 ≤ h * z ^ (5 : ℕ) * nlrP05 h := by positivity
  have t6 : 0 ≤ h ^ (2 : ℕ) * z ^ (6 : ℕ) * nlrP06 h := by positivity
  have c7 : h ^ (4 : ℕ) * nlrS0 h ≤ 221 / 16 := by
    have := mul_le_mul_of_nonneg_left s0 (by positivity : (0 : ℝ) ≤ h ^ (4 : ℕ)); linarith
  have t7 : z ^ (7 : ℕ) * (h ^ (4 : ℕ) * nlrS0 h) ≤ z ^ (7 : ℕ) * (221 / 16) :=
    mul_le_mul_of_nonneg_left c7 (by positivity)
  unfold nlrE0
  linarith

theorem nlr_E1_nonneg {h z : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ nlrE1 h z := by
  have u0 := nlr_U10_lb h1 h2
  have u1 := nlr_U11_lb h1 h2
  have u2 := nlr_U12_lb h1
  have u3 := nlr_U13_lb h1
  have p4 := nlr_P14_lb h1 h2
  have p5 := nlr_P15_lb h1 h2
  have p6 := nlr_P16_lb h1 h2
  have s1 := nlr_S1_ub h1 h2
  have hh : 0 ≤ h := by linarith
  have h4 : h ^ (4 : ℕ) ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hh h2 4; norm_num at this; linarith
  have z7 : z ^ (7 : ℕ) ≤ 1 := pow_le_one₀ hz0 hz1
  have t1 : 0 ≤ z * nlrU11 h := mul_nonneg hz0 u1
  have t2 : 0 ≤ z ^ (2 : ℕ) * (nlrU12 h + 60000) := mul_nonneg (by positivity) (by linarith)
  have t3 : 0 ≤ z ^ (3 : ℕ) * (nlrU13 h - 100000 + 9360 * h ^ (9 : ℕ)) := by
    apply mul_nonneg (by positivity); have : 0 ≤ h ^ (9 : ℕ) := by positivity
    linarith
  have t4 : 0 ≤ h * z ^ (4 : ℕ) * (nlrP14 h + 3168 * h ^ (9 : ℕ)) := by positivity
  have t5 : 0 ≤ h ^ (2 : ℕ) * z ^ (5 : ℕ) * (nlrP15 h + 216 * h ^ (9 : ℕ)) := by positivity
  have t6 : 0 ≤ h ^ (3 : ℕ) * z ^ (6 : ℕ) * nlrP16 h := by positivity
  have c7 : h ^ (4 : ℕ) * nlrS1 h ≤ 1121 / 16 := by
    have := mul_le_mul_of_nonneg_left s1 (by positivity : (0 : ℝ) ≤ h ^ (4 : ℕ)); linarith
  have t7 : z ^ (7 : ℕ) * (h ^ (4 : ℕ) * nlrS1 h) ≤ z ^ (7 : ℕ) * (1121 / 16) :=
    mul_le_mul_of_nonneg_left c7 (by positivity)
  -- `100000z³ - 60000z² = 100000(z - 2/5)²(z + 1/5) - 3200`
  have sq : 0 ≤ (z - 2 / 5) ^ (2 : ℕ) * (z + 1 / 5) := by positivity
  unfold nlrE1
  linarith

theorem nlr_E2_nonneg {h z : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ nlrE2 h z := by
  have u0 := nlr_U20_lb h1
  have u1 := nlr_U21_lb h1
  have u2 := nlr_U22_lb h1
  have u3 := nlr_U23_lb h1 h2
  have p4 := nlr_P24_lb h1 h2
  have p5 := nlr_P25_lb h1 h2
  have p6 := nlr_P26_lb h1 h2
  have s2 := nlr_S2_ub h1 h2
  have hh : 0 ≤ h := by linarith
  have h5 : h ^ (5 : ℕ) ≤ 1 / 32 := by
    have := pow_le_pow_left₀ hh h2 5; norm_num at this; linarith
  have z7 : z ^ (7 : ℕ) ≤ 1 := pow_le_one₀ hz0 hz1
  have t1 : 0 ≤ z * nlrU21 h := mul_nonneg hz0 u1
  have t2 : 0 ≤ z ^ (2 : ℕ) * (nlrU22 h + 60000) := mul_nonneg (by positivity) (by linarith)
  have t3 : 0 ≤ z ^ (3 : ℕ) * (nlrU23 h - 100000 + 72720 * h ^ (9 : ℕ)) := by
    apply mul_nonneg (by positivity); have : 0 ≤ h ^ (9 : ℕ) := by positivity
    linarith
  have t4 : 0 ≤ h ^ (2 : ℕ) * z ^ (4 : ℕ) * nlrP24 h := by positivity
  have t5 : 0 ≤ h ^ (3 : ℕ) * z ^ (5 : ℕ) * nlrP25 h := by positivity
  have t6 : 0 ≤ h ^ (4 : ℕ) * z ^ (6 : ℕ) * nlrP26 h := by positivity
  have c7 : h ^ (5 : ℕ) * nlrS2 h ≤ 7062 / 32 := by
    have := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ h ^ (5 : ℕ)); linarith
  have t7 : z ^ (7 : ℕ) * (h ^ (5 : ℕ) * nlrS2 h) ≤ z ^ (7 : ℕ) * (7062 / 32) :=
    mul_le_mul_of_nonneg_left c7 (by positivity)
  have sq : 0 ≤ (z - 2 / 5) ^ (2 : ℕ) * (z + 1 / 5) := by positivity
  unfold nlrE2
  linarith

/-! ### Monotonicity in `h` -/

/-- A function with nonnegative derivative on `[1/3, 1/2]` is larger at `h` than at `1/3`. -/
theorem nlr_mono_of_deriv {f f' : ℝ → ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
    (hpos : ∀ s, 1 / 3 ≤ s → s ≤ 1 / 2 → 0 ≤ f' s) {h : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) :
    f (1 / 3) ≤ f h := by
  have hmono : MonotoneOn f (Set.Icc (1 / 3) (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      exact hpos s hs.1.le hs.2.le
  exact hmono ⟨le_rfl, by norm_num⟩ ⟨h1, h2⟩ h1

/-- The coefficients of `𝒜_0(·, z)` in powers of `h`. -/
noncomputable def nlrA0List (z : ℝ) : List ℝ :=
  [(-930 + 2010 * z - 2430 * z ^ (2 : ℕ) - 690 * z ^ (3 : ℕ)), (1285 - 3220 * z - 1485 * z ^ (2 : ℕ) + 470 * z ^ (3 : ℕ) - 2370 * z ^ (4 : ℕ)), (4883 + (3929 / 2) * z - (22149 / 2) * z ^ (2 : ℕ) + 5659 * z ^ (3 : ℕ) + 8080 * z ^ (4 : ℕ) - 1980 * z ^ (5 : ℕ)), (3270 + (42003 / 2) * z - 1248 * z ^ (2 : ℕ) - (20921 / 2) * z ^ (3 : ℕ) + 27912 * z ^ (4 : ℕ) + 8220 * z ^ (5 : ℕ) - 300 * z ^ (6 : ℕ)), (504 + 19212 * z + 37427 * z ^ (2 : ℕ) - (24625 / 2) * z ^ (3 : ℕ) + 9919 * z ^ (4 : ℕ) + 27378 * z ^ (5 : ℕ) + 2860 * z ^ (6 : ℕ)), (5538 * z + (78347 / 2) * z ^ (2 : ℕ) + (49257 / 2) * z ^ (3 : ℕ) - 16127 * z ^ (4 : ℕ) + 17331 * z ^ (5 : ℕ) + 8560 * z ^ (6 : ℕ) - 180 * z ^ (7 : ℕ)), (504 * z + 13461 * z ^ (2 : ℕ) + (68533 / 2) * z ^ (3 : ℕ) - 3121 * z ^ (4 : ℕ) - 7603 * z ^ (5 : ℕ) + 6184 * z ^ (6 : ℕ) - 120 * z ^ (7 : ℕ)), (1476 * z ^ (2 : ℕ) + 13567 * z ^ (3 : ℕ) + 10743 * z ^ (4 : ℕ) - 9653 * z ^ (5 : ℕ) - 1529 * z ^ (6 : ℕ) + 258 * z ^ (7 : ℕ)), (1632 * z ^ (3 : ℕ) + 5992 * z ^ (4 : ℕ) - (2315 / 2) * z ^ (5 : ℕ) - 3380 * z ^ (6 : ℕ) + 180 * z ^ (7 : ℕ)), (804 * z ^ (4 : ℕ) + (1811 / 2) * z ^ (5 : ℕ) - (2251 / 2) * z ^ (6 : ℕ) - 72 * z ^ (7 : ℕ)), (165 * z ^ (5 : ℕ) - (93 / 2) * z ^ (6 : ℕ) - 60 * z ^ (7 : ℕ)), (9 * z ^ (6 : ℕ) - 6 * z ^ (7 : ℕ))]

/-- `∂_h 𝒜_0 = E_0 / 2`. -/
theorem nlr_A0_deriv (z s : ℝ) : HasDerivAt (fun h => nlrA0 h z) (nlrE0 s z / 2) s := by
  have H := poly_hasDerivAt_horner (nlrA0List z) s
  have e1 : polyHorner (nlrA0List z) = fun h => nlrA0 h z := by
    funext h; simp only [nlrA0List, polyHorner]; unfold nlrA0 nlrB00 nlrB01 nlrB02 nlrB03 nlrB04 nlrB05 nlrB06 nlrB07; ring
  have e2 : polyHornerD (nlrA0List z) s = nlrE0 s z / 2 := by
    simp only [nlrA0List, polyHornerD, polyHorner]; unfold nlrE0 nlrU00 nlrU01 nlrU02 nlrU03 nlrP04 nlrP05 nlrP06 nlrS0; ring
  rw [e1, e2] at H; exact H

/-- **Monotonicity**: `𝒜_0(h, z) ≥ a_0(z)` on `1/3 ≤ h ≤ 1/2`, `0 ≤ z ≤ 1`. -/
theorem nlr_A0_ge {h z : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    nlra0 z ≤ nlrA0 h z := by
  have key := nlr_mono_of_deriv (f := fun s => nlrA0 s z) (f' := fun s => nlrE0 s z / 2)
    (fun s => nlr_A0_deriv z s)
    (fun s hs1 hs2 => by have := nlr_E0_nonneg hs1 hs2 hz0 hz1; linarith) h1 h2
  have e : nlrA0 (1 / 3) z = nlra0 z := by unfold nlrA0 nlra0 nlrB00 nlrB01 nlrB02 nlrB03 nlrB04 nlrB05 nlrB06 nlrB07; ring
  rw [e] at key; exact key

/-- The coefficients of `𝒜_1(·, z)` in powers of `h`. -/
noncomputable def nlrA1List (z : ℝ) : List ℝ :=
  [(-360 + 1500 * z - 7380 * z ^ (2 : ℕ)), (-3890 + 975 * z - 19140 * z ^ (2 : ℕ) - 13045 * z ^ (3 : ℕ)), (8547 - 22915 * z - (67107 / 2) * z ^ (2 : ℕ) + 35028 * z ^ (3 : ℕ) - 10835 * z ^ (4 : ℕ)), (29120 + (58853 / 2) * z - 64264 * z ^ (2 : ℕ) + (197151 / 2) * z ^ (3 : ℕ) + 132984 * z ^ (4 : ℕ) - 3750 * z ^ (5 : ℕ)), (21717 + 148215 * z + (130659 / 2) * z ^ (2 : ℕ) + (457 / 2) * z ^ (3 : ℕ) + 336900 * z ^ (4 : ℕ) + 112866 * z ^ (5 : ℕ) + 1150 * z ^ (6 : ℕ)), (4806 + (276717 / 2) * z + (606701 / 2) * z ^ (2 : ℕ) - (6473 / 2) * z ^ (3 : ℕ) + 172045 * z ^ (4 : ℕ) + 285381 * z ^ (5 : ℕ) + 33570 * z ^ (6 : ℕ) - 180 * z ^ (7 : ℕ)), (216 + 47868 * z + 290468 * z ^ (2 : ℕ) + (406129 / 2) * z ^ (3 : ℕ) - 95275 * z ^ (4 : ℕ) + 176249 * z ^ (5 : ℕ) + 81018 * z ^ (6 : ℕ) - 1500 * z ^ (7 : ℕ)), (6426 * z + (221237 / 2) * z ^ (2 : ℕ) + 245072 * z ^ (3 : ℕ) - 51702 * z ^ (4 : ℕ) - (139977 / 2) * z ^ (5 : ℕ) + 53258 * z ^ (6 : ℕ) - 546 * z ^ (7 : ℕ)), (216 * z + 16635 * z ^ (2 : ℕ) + 105005 * z ^ (3 : ℕ) + 56716 * z ^ (4 : ℕ) - (209647 / 2) * z ^ (5 : ℕ) - (38155 / 2) * z ^ (6 : ℕ) + 2397 * z ^ (7 : ℕ)), (540 * z ^ (2 : ℕ) + 16632 * z ^ (3 : ℕ) + 41209 * z ^ (4 : ℕ) - 24688 * z ^ (5 : ℕ) - (69897 / 2) * z ^ (6 : ℕ) + 1326 * z ^ (7 : ℕ)), (468 * z ^ (3 : ℕ) + 7182 * z ^ (4 : ℕ) + (7787 / 2) * z ^ (5 : ℕ) - (24205 / 2) * z ^ (6 : ℕ) - 834 * z ^ (7 : ℕ)), (144 * z ^ (4 : ℕ) + (2427 / 2) * z ^ (5 : ℕ) - (1657 / 2) * z ^ (6 : ℕ) - 600 * z ^ (7 : ℕ)), (9 * z ^ (5 : ℕ) + 57 * z ^ (6 : ℕ) - 63 * z ^ (7 : ℕ))]

/-- `∂_h 𝒜_1 = E_1 / 2`. -/
theorem nlr_A1_deriv (z s : ℝ) : HasDerivAt (fun h => nlrA1 h z) (nlrE1 s z / 2) s := by
  have H := poly_hasDerivAt_horner (nlrA1List z) s
  have e1 : polyHorner (nlrA1List z) = fun h => nlrA1 h z := by
    funext h; simp only [nlrA1List, polyHorner]; unfold nlrA1 nlrB10 nlrB11 nlrB12 nlrB13 nlrB14 nlrB15 nlrB16 nlrB17; ring
  have e2 : polyHornerD (nlrA1List z) s = nlrE1 s z / 2 := by
    simp only [nlrA1List, polyHornerD, polyHorner]; unfold nlrE1 nlrU10 nlrU11 nlrU12 nlrU13 nlrP14 nlrP15 nlrP16 nlrS1; ring
  rw [e1, e2] at H; exact H

/-- **Monotonicity**: `𝒜_1(h, z) ≥ a_1(z)` on `1/3 ≤ h ≤ 1/2`, `0 ≤ z ≤ 1`. -/
theorem nlr_A1_ge {h z : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    nlra1 z ≤ nlrA1 h z := by
  have key := nlr_mono_of_deriv (f := fun s => nlrA1 s z) (f' := fun s => nlrE1 s z / 2)
    (fun s => nlr_A1_deriv z s)
    (fun s hs1 hs2 => by have := nlr_E1_nonneg hs1 hs2 hz0 hz1; linarith) h1 h2
  have e : nlrA1 (1 / 3) z = nlra1 z := by unfold nlrA1 nlra1 nlrB10 nlrB11 nlrB12 nlrB13 nlrB14 nlrB15 nlrB16 nlrB17; ring
  rw [e] at key; exact key

/-- The coefficients of `𝒜_2(·, z)` in powers of `h`. -/
noncomputable def nlrA2List (z : ℝ) : List ℝ :=
  [(2070 - 510 * z), (-3810 + 10890 * z - 34665 * z ^ (2 : ℕ)), (-8202 - 29457 * z - (38967 / 2) * z ^ (2 : ℕ) - 17781 * z ^ (3 : ℕ)), (29346 - 47250 * z - 67023 * z ^ (2 : ℕ) + (617251 / 2) * z ^ (3 : ℕ) + 48287 * z ^ (4 : ℕ)), (44544 + 159813 * z - (28145 / 2) * z ^ (2 : ℕ) + (751883 / 2) * z ^ (3 : ℕ) + 728762 * z ^ (4 : ℕ) + 52698 * z ^ (5 : ℕ)), (15624 + 279606 * z + 400685 * z ^ (2 : ℕ) + 29060 * z ^ (3 : ℕ) + 946061 * z ^ (4 : ℕ) + 537795 * z ^ (5 : ℕ) + 18910 * z ^ (6 : ℕ)), (1296 + 143538 * z + 590638 * z ^ (2 : ℕ) + (313793 / 2) * z ^ (3 : ℕ) + 41620 * z ^ (4 : ℕ) + 713196 * z ^ (5 : ℕ) + 139479 * z ^ (6 : ℕ) - 1200 * z ^ (7 : ℕ)), (29052 * z + 316531 * z ^ (2 : ℕ) + (840895 / 2) * z ^ (3 : ℕ) - 361124 * z ^ (4 : ℕ) + 32697 * z ^ (5 : ℕ) + 185948 * z ^ (6 : ℕ) - 3441 * z ^ (7 : ℕ)), (1728 * z + 70782 * z ^ (2 : ℕ) + 276400 * z ^ (3 : ℕ) - 45804 * z ^ (4 : ℕ) - 358143 * z ^ (5 : ℕ) + 4669 * z ^ (6 : ℕ) + 3768 * z ^ (7 : ℕ)), (4248 * z ^ (2 : ℕ) + 66402 * z ^ (3 : ℕ) + 83425 * z ^ (4 : ℕ) - (318393 / 2) * z ^ (5 : ℕ) - (212931 / 2) * z ^ (6 : ℕ) + 5190 * z ^ (7 : ℕ)), (3636 * z ^ (3 : ℕ) + 25719 * z ^ (4 : ℕ) - 6591 * z ^ (5 : ℕ) - 51115 * z ^ (6 : ℕ) - 1782 * z ^ (7 : ℕ)), (1098 * z ^ (4 : ℕ) + (6807 / 2) * z ^ (5 : ℕ) - (10287 / 2) * z ^ (6 : ℕ) - 2253 * z ^ (7 : ℕ)), (63 * z ^ (5 : ℕ) + 126 * z ^ (6 : ℕ) - 282 * z ^ (7 : ℕ))]

/-- `∂_h 𝒜_2 = E_2 / 2`. -/
theorem nlr_A2_deriv (z s : ℝ) : HasDerivAt (fun h => nlrA2 h z) (nlrE2 s z / 2) s := by
  have H := poly_hasDerivAt_horner (nlrA2List z) s
  have e1 : polyHorner (nlrA2List z) = fun h => nlrA2 h z := by
    funext h; simp only [nlrA2List, polyHorner]; unfold nlrA2 nlrB20 nlrB21 nlrB22 nlrB23 nlrB24 nlrB25 nlrB26 nlrB27; ring
  have e2 : polyHornerD (nlrA2List z) s = nlrE2 s z / 2 := by
    simp only [nlrA2List, polyHornerD, polyHorner]; unfold nlrE2 nlrU20 nlrU21 nlrU22 nlrU23 nlrP24 nlrP25 nlrP26 nlrS2; ring
  rw [e1, e2] at H; exact H

/-- **Monotonicity**: `𝒜_2(h, z) ≥ a_2(z)` on `1/3 ≤ h ≤ 1/2`, `0 ≤ z ≤ 1`. -/
theorem nlr_A2_ge {h z : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    nlra2 z ≤ nlrA2 h z := by
  have key := nlr_mono_of_deriv (f := fun s => nlrA2 s z) (f' := fun s => nlrE2 s z / 2)
    (fun s => nlr_A2_deriv z s)
    (fun s hs1 hs2 => by have := nlr_E2_nonneg hs1 hs2 hz0 hz1; linarith) h1 h2
  have e : nlrA2 (1 / 3) z = nlra2 z := by unfold nlrA2 nlra2 nlrB20 nlrB21 nlrB22 nlrB23 nlrB24 nlrB25 nlrB26 nlrB27; ring
  rw [e] at key; exact key

/-! ### The base quadratic -/

/-- The three error identities: `a₀ > A`, `a₁ ≥ B`, `4a₂/3 ≥ C` on `[0, 1]` (each difference is a
polynomial with nonnegative coefficients in `z` and `1 - z`). -/
theorem nlr_base_err {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < nlra0 z - nlrQA z ∧ 0 ≤ nlra1 z - nlrQB z ∧ 0 < 4 / 3 * nlra2 z - nlrQC z := by
  have hz : 0 ≤ 1 - z := by linarith
  have e0 : 59049 * (nlra0 z - nlrQA z) = 13122 + 26244 * z + 40581 * z ^ (2 : ℕ) + 48492 * z ^ (3 : ℕ)
      + 13653 * z ^ (4 : ℕ) + 46923 * z ^ (5 : ℕ) + 51364 * z ^ (6 : ℕ) + 45152 * z ^ (6 : ℕ) * (1 - z) := by
    unfold nlra0 nlrQA; ring
  have e1 : 177147 * (nlra1 z - nlrQB z) = 124659 + 103518 * z + 29808 * z ^ (2 : ℕ) + 102951 * z ^ (3 : ℕ)
      + 41625 * z ^ (4 : ℕ) + 94563 * z ^ (5 : ℕ) + 54530 * z ^ (6 : ℕ) + 466416 * z ^ (6 : ℕ) * (1 - z) := by
    unfold nlra1 nlrQB; ring
  have e2 : 531441 * (4 / 3 * nlra2 z - nlrQC z) = 39366 + 61236 * z + 494829 * z ^ (2 : ℕ)
      + 199746 * z ^ (3 : ℕ) + 277848 * z ^ (4 : ℕ) + 528174 * z ^ (5 : ℕ) + 287435 * z ^ (6 : ℕ)
      + 1718272 * z ^ (6 : ℕ) * (1 - z) := by
    unfold nlra2 nlrQC; ring
  have f0 : 0 < 13122 + 26244 * z + 40581 * z ^ (2 : ℕ) + 48492 * z ^ (3 : ℕ) + 13653 * z ^ (4 : ℕ) + 46923 * z ^ (5 : ℕ)
      + 51364 * z ^ (6 : ℕ) + 45152 * z ^ (6 : ℕ) * (1 - z) := by positivity
  have f1 : 0 < 124659 + 103518 * z + 29808 * z ^ (2 : ℕ) + 102951 * z ^ (3 : ℕ) + 41625 * z ^ (4 : ℕ)
      + 94563 * z ^ (5 : ℕ) + 54530 * z ^ (6 : ℕ) + 466416 * z ^ (6 : ℕ) * (1 - z) := by positivity
  have f2 : 0 < 39366 + 61236 * z + 494829 * z ^ (2 : ℕ) + 199746 * z ^ (3 : ℕ) + 277848 * z ^ (4 : ℕ)
      + 528174 * z ^ (5 : ℕ) + 287435 * z ^ (6 : ℕ) + 1718272 * z ^ (6 : ℕ) * (1 - z) := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **The base quadratic**: `a₀ + βa₁ + (4/3)β²a₂ > 4`, and `a₂ > 0`. -/
theorem nlr_base {z β : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hb : 0 ≤ β) :
    4 < nlra0 z + β * nlra1 z + 4 / 3 * β ^ (2 : ℕ) * nlra2 z ∧ 0 < nlra2 z := by
  obtain ⟨f0, f1, f2⟩ := nlr_base_err hz0 hz1
  obtain ⟨q, c⟩ := nlr_Q_ge hz0 hz1 hb
  have m1 : 0 ≤ β * (nlra1 z - nlrQB z) := mul_nonneg hb f1
  have m2 : 0 ≤ β ^ (2 : ℕ) * (4 / 3 * nlra2 z - nlrQC z) := mul_nonneg (sq_nonneg β) f2.le
  constructor
  · linarith
  · linarith

/-! ### The higher coefficients -/

theorem nlr_C3_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ h) :
    0 ≤ nlrC3 h y := by
  have p30 := nlr_P30_lb h1 h2
  have p31 := nlr_P31_lb h1 h2
  have p32 := nlr_P32_lb h1 h2
  have p33 := nlr_P33_lb h1 h2
  have p34 := nlr_P34_lb h1 h2
  have p35 := nlr_P35_lb h1 h2
  have p36 := nlr_P36_lb h1 h2
  have p37 := nlr_P37_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  have hw : (h + 1) * (1 - h) ≤ 1 := by linarith [sq_nonneg h]
  have hy7 : y ^ (7 : ℕ) ≤ 1 / 128 := by
    have := pow_le_pow_left₀ hy0 (hy.trans h2) 7; norm_num at this; linarith
  have m0 : 0 ≤ y ^ (7 : ℕ) * ((h + 1) * (1 - h)) := by positivity
  have m1 : y ^ (7 : ℕ) * ((h + 1) * (1 - h)) ≤ 1 / 128 := by
    have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ y ^ (7 : ℕ)); linarith
  have t7 : -2000 * (y ^ (7 : ℕ) * ((h + 1) * (1 - h))) ≤ y ^ (7 : ℕ) * ((h + 1) * (1 - h)) * nlrP37 h := by
    have := mul_le_mul_of_nonneg_left p37.le m0; linarith
  have t0 : 400 ≤ (h + 1) ^ (2 : ℕ) * nlrP30 h := by
    have : 1 ≤ (h + 1) ^ (2 : ℕ) := by linarith [sq_nonneg h]
    have := mul_le_mul this p30.le (by norm_num) (by positivity)
    linarith
  have rest : 0 ≤ ((h + 1) * nlrP31 h) * y + ((h + 1) * nlrP32 h / 2) * y ^ (2 : ℕ) + ((h + 1) * nlrP33 h / 2) * y ^ (3 : ℕ) + ((h + 1) * nlrP34 h) * y ^ (4 : ℕ) + ((h + 1) * nlrP35 h / 2) * y ^ (5 : ℕ) + ((h + 1) * nlrP36 h / 2) * y ^ (6 : ℕ) := by positivity
  unfold nlrC3
  linarith

theorem nlr_C4_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ h) :
    0 ≤ nlrC4 h y := by
  have p40 := nlr_P40_lb h1 h2
  have p41 := nlr_P41_lb h1 h2
  have p42 := nlr_P42_lb h1 h2
  have p43 := nlr_P43_lb h1 h2
  have p44 := nlr_P44_lb h1 h2
  have p45 := nlr_P45_lb h1 h2
  have p46 := nlr_P46_lb h1 h2
  have p47 := nlr_P47_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  have hw : (h + 1) * (1 - h) ≤ 1 := by linarith [sq_nonneg h]
  have hy7 : y ^ (7 : ℕ) ≤ 1 / 128 := by
    have := pow_le_pow_left₀ hy0 (hy.trans h2) 7; norm_num at this; linarith
  have m0 : 0 ≤ y ^ (7 : ℕ) * ((h + 1) * (1 - h)) := by positivity
  have m1 : y ^ (7 : ℕ) * ((h + 1) * (1 - h)) ≤ 1 / 128 := by
    have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ y ^ (7 : ℕ)); linarith
  have t7 : -200 * (y ^ (7 : ℕ) * ((h + 1) * (1 - h))) ≤ y ^ (7 : ℕ) * ((h + 1) * (1 - h)) * nlrP47 h := by
    have := mul_le_mul_of_nonneg_left p47.le m0; linarith
  have t0 : 4000 ≤ (h + 1) ^ (2 : ℕ) * nlrP40 h := by
    have : 1 ≤ (h + 1) ^ (2 : ℕ) := by linarith [sq_nonneg h]
    have := mul_le_mul this p40.le (by norm_num) (by positivity)
    linarith
  have rest : 0 ≤ ((h + 1) * nlrP41 h / 2) * y + ((h + 1) * nlrP42 h / 2) * y ^ (2 : ℕ) + ((h + 1) * nlrP43 h / 2) * y ^ (3 : ℕ) + ((h + 1) * nlrP44 h) * y ^ (4 : ℕ) + ((h + 1) * nlrP45 h / 2) * y ^ (5 : ℕ) + ((h + 1) * nlrP46 h / 2) * y ^ (6 : ℕ) := by positivity
  unfold nlrC4
  linarith

theorem nlr_C5_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) :
    0 ≤ nlrC5 h y := by
  have p50 := nlr_P50_lb h1 h2
  have p51 := nlr_P51_lb h1 h2
  have p52 := nlr_P52_lb h1 h2
  have p53 := nlr_P53_lb h1 h2
  have p54 := nlr_P54_lb h1 h2
  have p55 := nlr_P55_lb h1 h2
  have p56 := nlr_P56_lb h1 h2
  have p57 := nlr_P57_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  unfold nlrC5
  positivity

theorem nlr_C6_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) :
    0 ≤ nlrC6 h y := by
  have p60 := nlr_P60_lb h1 h2
  have p61 := nlr_P61_lb h1 h2
  have p62 := nlr_P62_lb h1 h2
  have p63 := nlr_P63_lb h1 h2
  have p64 := nlr_P64_lb h1 h2
  have p65 := nlr_P65_lb h1 h2
  have p66 := nlr_P66_lb h1 h2
  have p67 := nlr_P67_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  unfold nlrC6
  positivity

theorem nlr_C7_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) :
    0 ≤ nlrC7 h y := by
  have p70 := nlr_P70_lb h1 h2
  have p71 := nlr_P71_lb h1 h2
  have p72 := nlr_P72_lb h1 h2
  have p73 := nlr_P73_lb h1 h2
  have p74 := nlr_P74_lb h1 h2
  have p75 := nlr_P75_lb h1 h2
  have p76 := nlr_P76_lb h1 h2
  have p77 := nlr_P77_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  unfold nlrC7
  positivity

theorem nlr_C8_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) :
    0 ≤ nlrC8 h y := by
  have p81 := nlr_P81_lb h1 h2
  have p82 := nlr_P82_lb h1 h2
  have p83 := nlr_P83_lb h1 h2
  have p84 := nlr_P84_lb h1 h2
  have p85 := nlr_P85_lb h1 h2
  have p86 := nlr_P86_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  unfold nlrC8
  positivity

theorem nlr_C9_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) :
    0 ≤ nlrC9 h y := by
  have p91 := nlr_P91_lb h1 h2
  have p92 := nlr_P92_lb h1 h2
  have p93 := nlr_P93_lb h1 h2
  have p94 := nlr_P94_lb h1 h2
  have p95 := nlr_P95_lb h1 h2
  have p96 := nlr_P96_lb h1 h2
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  unfold nlrC9
  positivity

theorem nlr_C10_nonneg {h y : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) :
    0 ≤ nlrC10 h y := by

  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - h := by linarith
  unfold nlrC10
  positivity

/-! ### The sign of the collected polynomial -/

/-- The quadratic Taylor part `C̃₀ + C̃₁j + C̃₂j²` is positive: with `y = hz` it is
`h³w³(𝒜₀ + β𝒜₁ + wβ²𝒜₂)`, bounded below through `nlr_A0_ge`, …, and `nlr_base`. -/
theorem nlr_quad_pos {h y j : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ h)
    (hj : 0 ≤ j) : 0 < nlrC0 h y + nlrC1 h y * j + nlrC2 h y * j ^ (2 : ℕ) := by
  have hh : 0 < h := by linarith
  obtain ⟨z, hz0, hz1, rfl⟩ : ∃ z, 0 ≤ z ∧ z ≤ 1 ∧ y = h * z :=
    ⟨y / h, div_nonneg hy0 hh.le, (div_le_one hh).2 hy, by field_simp⟩
  have e : nlrC0 h (h * z) + nlrC1 h (h * z) * j + nlrC2 h (h * z) * j ^ (2 : ℕ) =
      (1 + h) ^ (2 : ℕ) * h * ((1 + h) * h ^ (2 : ℕ) * nlrA0 h z + h * j * nlrA1 h z + j ^ (2 : ℕ) * nlrA2 h z) := by
    unfold nlrC0 nlrC1 nlrC2 nlrA0 nlrA1 nlrA2; ring
  rw [e]
  have m0 := nlr_A0_ge h1 h2 hz0 hz1
  have m1 := nlr_A1_ge h1 h2 hz0 hz1
  have m2 := nlr_A2_ge h1 h2 hz0 hz1
  have hw : 0 < h * (1 + h) := by positivity
  obtain ⟨β, hb, rfl⟩ : ∃ β, 0 ≤ β ∧ j = β * (h * (1 + h)) :=
    ⟨j / (h * (1 + h)), div_nonneg hj hw.le, by field_simp⟩
  obtain ⟨base, ha2⟩ := nlr_base hz0 hz1 hb
  have k1 : (1 + h) * h ^ (2 : ℕ) * (nlrA0 h z - nlra0 z) + h * (β * (h * (1 + h))) * (nlrA1 h z - nlra1 z)
      + (β * (h * (1 + h))) ^ (2 : ℕ) * (nlrA2 h z - nlra2 z) ≥ 0 := by
    have : 0 ≤ β * (h * (1 + h)) := by positivity
    have a := mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + h) * h ^ (2 : ℕ)) (sub_nonneg.2 m0)
    have b := mul_nonneg (by positivity : (0 : ℝ) ≤ h * (β * (h * (1 + h)))) (sub_nonneg.2 m1)
    have c := mul_nonneg (by positivity : (0 : ℝ) ≤ (β * (h * (1 + h))) ^ (2 : ℕ)) (sub_nonneg.2 m2)
    linarith
  have k2 : (1 + h) * h ^ (2 : ℕ) * nlra0 z + h * (β * (h * (1 + h))) * nlra1 z
      + (β * (h * (1 + h))) ^ (2 : ℕ) * nlra2 z
      = (1 + h) * h ^ (2 : ℕ) * (nlra0 z + β * nlra1 z + (1 + h) * β ^ (2 : ℕ) * nlra2 z) := by ring
  have k3 : 4 / 3 * β ^ (2 : ℕ) * nlra2 z ≤ (1 + h) * β ^ (2 : ℕ) * nlra2 z := by
    have : 0 ≤ β ^ (2 : ℕ) * nlra2 z := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : (4 / 3 : ℝ) ≤ 1 + h) this
    linarith
  have k4 : 0 < (1 + h) * h ^ (2 : ℕ) * (nlra0 z + β * nlra1 z + (1 + h) * β ^ (2 : ℕ) * nlra2 z) := by
    apply mul_pos (by positivity); linarith
  have k5 : 0 < (1 + h) * h ^ (2 : ℕ) * nlrA0 h z + h * (β * (h * (1 + h))) * nlrA1 h z
      + (β * (h * (1 + h))) ^ (2 : ℕ) * nlrA2 h z := by linarith
  exact mul_pos (by positivity) k5

/-- **The collected polynomial is positive**, for `1/3 ≤ h ≤ 1/2`,
`0 ≤ y ≤ h`, `j ≥ 0`. -/
theorem nlr_sum_pos {h y j : ℝ} (h1 : 1 / 3 ≤ h) (h2 : h ≤ 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ h)
    (hj : 0 ≤ j) :
    0 < nlrC0 h y + nlrC1 h y * j + nlrC2 h y * j ^ (2 : ℕ) + nlrC3 h y * j ^ (3 : ℕ) + nlrC4 h y * j ^ (4 : ℕ)
      + nlrC5 h y * j ^ (5 : ℕ) + nlrC6 h y * j ^ (6 : ℕ) + nlrC7 h y * j ^ (7 : ℕ) + nlrC8 h y * j ^ (8 : ℕ)
      + nlrC9 h y * j ^ (9 : ℕ) + nlrC10 h y * j ^ (10 : ℕ) := by
  have q := nlr_quad_pos h1 h2 hy0 hy hj
  have c3 := nlr_C3_nonneg h1 h2 hy0 hy
  have c4 := nlr_C4_nonneg h1 h2 hy0 hy
  have c5 := nlr_C5_nonneg h1 h2 hy0
  have c6 := nlr_C6_nonneg h1 h2 hy0
  have c7 := nlr_C7_nonneg h1 h2 hy0
  have c8 := nlr_C8_nonneg h1 h2 hy0
  have c9 := nlr_C9_nonneg h1 h2 hy0
  have c10 := nlr_C10_nonneg h1 h2 hy0
  have : 0 ≤ nlrC3 h y * j ^ (3 : ℕ) + nlrC4 h y * j ^ (4 : ℕ) + nlrC5 h y * j ^ (5 : ℕ) + nlrC6 h y * j ^ (6 : ℕ)
      + nlrC7 h y * j ^ (7 : ℕ) + nlrC8 h y * j ^ (8 : ℕ) + nlrC9 h y * j ^ (9 : ℕ) + nlrC10 h y * j ^ (10 : ℕ) := by
    positivity
  linarith

end SmoothedOctagon

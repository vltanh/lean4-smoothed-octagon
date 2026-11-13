module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Horner
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Analysis

/-!
# The scale derivative of the low-scale circuit

The coefficients below represent `6 ∂_h S` as a polynomial in the duration increment.
The factor six keeps all coefficients integral. The bridge to the original circuit
is `value_eq`; the cleared boundary values use the exact duration `(h-j)/(1+2j)`.
-/

@[expose] public section

namespace SmoothedOctagon.LowTScale

/-- Coefficients in `h` of the `y^0` term of `6 ∂_h S`. -/
def row0 {R : Type*} [CommRing R] (j : R) : List R :=
  [(-1192 * j + 7414 * j ^ 2 + 63406 * j ^ 3 - 140286 * j ^ 4 - 90006 * j ^ 5 - 8568 * j ^ 6),
   (2456 - 129500 * j - 320820 * j ^ 2 - 590520 * j ^ 3 - 473808 * j ^ 4 - 25620 * j ^ 5 + 17136 * j ^ 6),
   (41838 - 298386 * j - 532404 * j ^ 2 - 233982 * j ^ 3 + 470142 * j ^ 4 + 270018 * j ^ 5 + 25704 * j ^ 6),
   (260944 + 650760 * j + 1663608 * j ^ 2 + 2341752 * j ^ 3 + 1290936 * j ^ 4 + 205632 * j ^ 5),
   (732930 + 2583960 * j + 4082250 * j ^ 2 + 2811180 * j ^ 3 + 642600 * j ^ 4),
   (1070172 + 3096504 * j + 3131064 * j ^ 2 + 1028160 * j ^ 3),
   (868812 + 1745058 * j + 899640 * j ^ 2),
   (387120 + 411264 * j),
   77112]

/-- Coefficients in `h` of the `y^1` term of `6 ∂_h S`. -/
def row1 {R : Type*} [CommRing R] (j : R) : List R :=
  [(23640 * j + 201759 * j ^ 2 - 434931 * j ^ 3 - 1541379 * j ^ 4 - 837321 * j ^ 5 - 109518 * j ^ 6 - 8568 * j ^ 7),
   (-55800 - 355962 * j - 1828482 * j ^ 2 - 4076640 * j ^ 3 - 2413932 * j ^ 4 + 113286 * j ^ 5 + 173508 * j ^ 6 + 17724 * j ^ 7),
   (-74313 - 904815 * j - 2079774 * j ^ 2 + 840735 * j ^ 3 + 4297149 * j ^ 4 + 2176047 * j ^ 5 + 328554 * j ^ 6 + 25704 * j ^ 7),
   (455040 + 1832484 * j + 7548636 * j ^ 2 + 13057668 * j ^ 3 + 8082780 * j ^ 4 + 1879128 * j ^ 5 + 239904 * j ^ 6),
   (1371525 + 7059720 * j + 16110255 * j ^ 2 + 14321250 * j ^ 3 + 5081550 * j ^ 4 + 899640 * j ^ 5),
   (1928430 + 9012564 * j + 13444992 * j ^ 2 + 7485660 * j ^ 3 + 1799280 * j ^ 4),
   (1885632 + 6478143 * j + 6202854 * j ^ 2 + 2099160 * j ^ 3),
   (1265592 + 2726544 * j + 1439424 * j ^ 2),
   (496098 + 539784 * j),
   85680]

/-- Coefficients in `h` of the `y^2` term of `6 ∂_h S`. -/
def row2 {R : Type*} [CommRing R] (j : R) : List R :=
  [(-47696 + 141894 * j + 442594 * j ^ 2 - 1120023 * j ^ 3 - 2674920 * j ^ 4 - 1755537 * j ^ 5 - 364773 * j ^ 6 + 67428 * j ^ 7 + 17136 * j ^ 8),
   (-433778 - 1000790 * j - 2394792 * j ^ 2 - 3032970 * j ^ 3 - 180714 * j ^ 4 + 2156436 * j ^ 5 + 1573182 * j ^ 6 + 279750 * j ^ 7),
   (-1082952 - 2975781 * j - 1849302 * j ^ 2 + 5468661 * j ^ 3 + 9206505 * j ^ 4 + 5606901 * j ^ 5 + 1094319 * j ^ 6 - 23868 * j ^ 7),
   (-1771572 - 5336568 * j - 1947768 * j ^ 2 + 4948116 * j ^ 3 + 4751928 * j ^ 4 + 987372 * j ^ 5 - 203184 * j ^ 6),
   (-3824940 - 12205290 * j - 13172175 * j ^ 2 - 7627590 * j ^ 3 - 2706375 * j ^ 4 - 688500 * j ^ 5),
   (-6363684 - 17333496 * j - 17507070 * j ^ 2 - 7644474 * j ^ 3 - 1230120 * j ^ 4),
   (-5898501 - 12191067 * j - 7841295 * j ^ 2 - 1263780 * j ^ 3),
   (-2962368 - 3766776 * j - 749088 * j ^ 2),
   (-707913 - 236844 * j),
   -30600]

/-- Coefficients in `h` of the `y^3` term of `6 ∂_h S`. -/
def row3 {R : Type*} [CommRing R] (j : R) : List R :=
  [(109024 + 1793312 * j + 7701260 * j ^ 2 + 15182959 * j ^ 3 + 14881485 * j ^ 4 + 6243003 * j ^ 5 + 757932 * j ^ 6 + 50376 * j ^ 7 + 408 * j ^ 8),
   (465792 + 8248256 * j + 29816286 * j ^ 2 + 41914260 * j ^ 3 + 20318616 * j ^ 4 - 473478 * j ^ 5 - 1293360 * j ^ 6 - 103320 * j ^ 7),
   (1151160 + 12734511 * j + 24165882 * j ^ 2 - 3597741 * j ^ 3 - 32457429 * j ^ 4 - 16825185 * j ^ 5 - 2273796 * j ^ 6 - 146880 * j ^ 7),
   (-1620704 - 15841908 * j - 67629660 * j ^ 2 - 110015040 * j ^ 3 - 65856252 * j ^ 4 - 13559664 * j ^ 5 - 1341504 * j ^ 6),
   (-12988395 - 74512680 * j - 151388340 * j ^ 2 - 122459550 * j ^ 3 - 37086300 * j ^ 4 - 4920480 * j ^ 5),
   (-24556374 - 95646294 * j - 120034692 * j ^ 2 - 54585432 * j ^ 3 - 9620640 * j ^ 4),
   (-23046975 - 60102609 * j - 44909340 * j ^ 2 - 10967040 * j ^ 3),
   (-12152664 - 19525536 * j - 7344000 * j ^ 2),
   (-3504924 - 2687904 * j),
   -416160]

/-- Coefficients in `h` of the `y^4` term of `6 ∂_h S`. -/
def row4 {R : Type*} [CommRing R] (j : R) : List R :=
  [(-93048 + 802692 * j + 7408122 * j ^ 2 + 18755130 * j ^ 3 + 20127108 * j ^ 4 + 9039360 * j ^ 5 + 1239363 * j ^ 6 + 4836 * j ^ 7 - 11832 * j ^ 8),
   (209940 + 9230460 * j + 38584272 * j ^ 2 + 55368720 * j ^ 3 + 25969914 * j ^ 4 - 2169234 * j ^ 5 - 2936850 * j ^ 6 - 366270 * j ^ 7),
   (2388510 + 21592278 * j + 39060252 * j ^ 2 - 3157362 * j ^ 3 - 45927675 * j ^ 4 - 25355502 * j ^ 5 - 3718089 * j ^ 6 - 137700 * j ^ 7),
   (1888248 - 5394552 * j - 70247724 * j ^ 2 - 134101188 * j ^ 3 - 83518716 * j ^ 4 - 16926492 * j ^ 5 - 1270512 * j ^ 6),
   (-9247860 - 72535770 * j - 167244885 * j ^ 2 - 139377720 * j ^ 3 - 40745775 * j ^ 4 - 4709340 * j ^ 5),
   (-22375962 - 97614558 * j - 126421578 * j ^ 2 - 55923102 * j ^ 3 - 9308520 * j ^ 4),
   (-21951783 - 59662302 * j - 44148615 * j ^ 2 - 10731420 * j ^ 3),
   (-11513544 - 18717864 * j - 7270560 * j ^ 2),
   (-3309417 - 2693412 * j),
   -422280]

/-- Coefficients in `h` of the `y^5` term of `6 ∂_h S`. -/
def row5 {R : Type*} [CommRing R] (j : R) : List R :=
  [(-258384 - 909780 * j - 106134 * j ^ 2 + 2882145 * j ^ 3 + 3915714 * j ^ 4 + 1755465 * j ^ 5 + 211251 * j ^ 6 + 34896 * j ^ 7 + 6528 * j ^ 8),
   (-656952 + 149484 * j + 7839690 * j ^ 2 + 13921950 * j ^ 3 + 7462074 * j ^ 4 + 379302 * j ^ 5 - 184902 * j ^ 6 + 9360 * j ^ 7),
   (259110 + 6506181 * j + 14644701 * j ^ 2 + 4882275 * j ^ 3 - 8069967 * j ^ 4 - 4797531 * j ^ 5 - 633753 * j ^ 6 - 36720 * j ^ 7),
   (1559520 + 3921960 * j - 10576056 * j ^ 2 - 30031428 * j ^ 3 - 19745232 * j ^ 4 - 3989928 * j ^ 5 - 340272 * j ^ 6),
   (-725325 - 14791830 * j - 41149740 * j ^ 2 - 35947050 * j ^ 3 - 10559025 * j ^ 4 - 1266840 * j ^ 5),
   (-5040108 - 25114068 * j - 33838722 * j ^ 2 - 14973912 * j ^ 3 - 2515320 * j ^ 4),
   (-5757738 - 16183251 * j - 11946795 * j ^ 2 - 2913120 * j ^ 3),
   (-3124080 - 5074128 * j - 1982880 * j ^ 2),
   (-895563 - 738072 * j),
   -116280]

/-- Coefficients in `h` of the `y^6` term of `6 ∂_h S`. -/
def row6 {R : Type*} [CommRing R] (j : R) : List R :=
  [(-8616 - 37116 * j - 63516 * j ^ 2 - 65376 * j ^ 3 - 41856 * j ^ 4 - 18300 * j ^ 5 - 3672 * j ^ 6 + 1416 * j ^ 7 + 408 * j ^ 8),
   (-23736 - 53832 * j - 37896 * j ^ 2 + 17280 * j ^ 3 + 48624 * j ^ 4 + 38352 * j ^ 5 + 21528 * j ^ 6 + 4080 * j ^ 7),
   (4212 + 89316 * j + 200160 * j ^ 2 + 223488 * j ^ 3 + 131688 * j ^ 4 + 54900 * j ^ 5 + 11016 * j ^ 6),
   (61632 + 188352 * j + 221472 * j ^ 2 + 117264 * j ^ 3 + 31008 * j ^ 4 + 8160 * j ^ 5),
   (48240 + 57060 * j - 5820 * j ^ 2 - 45600 * j ^ 3 - 10200 * j ^ 4),
   (-7848 - 50472 * j - 67032 * j ^ 2 - 22032 * j ^ 3),
   (-17052 - 28476 * j - 14280 * j ^ 2),
   (-3264 - 3264 * j)]

/-- The coefficient of `y^i` in `6 ∂_h S`. -/
def coefficient {R : Type*} [CommRing R] (i : Fin 7) (h j : R) : R :=
  let cs := match (i : ℕ) with
    | 0 => row0 j
    | 1 => row1 j
    | 2 => row2 j
    | 3 => row3 j
    | 4 => row4 j
    | 5 => row5 j
    | _ => row6 j
  cs.foldr (fun c v => c + h * v) 0

/-- Evaluation and every other ring homomorphism preserve these polynomial coefficients. -/
theorem coefficient_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin 7) (h j : R) : f (coefficient i h j) = coefficient i (f h) (f j) := by
  fin_cases i <;> simp [coefficient, row0, row1, row2, row3, row4, row5, row6, map_ofNat]

/-- The scale derivative, multiplied by six. -/
def value {R : Type*} [CommRing R] (h j y : R) : R :=
  ∑ i : Fin 7, coefficient i h j * y ^ (i : ℕ)

private theorem coefficient0_eq (h j : ℝ) : coefficient 0 h j =
    6 * polyHorner (nltDer (nltL0 j)) h := by
  norm_num [coefficient, row0, nltL0, nltDer, nltDerAux, polyHorner]
  ring

private theorem coefficient1_eq (h j : ℝ) : coefficient 1 h j =
    6 * polyHorner (nltDer (nltL1 j)) h := by
  norm_num [coefficient, row1, nltL1, nltDer, nltDerAux, polyHorner]
  ring

private theorem coefficient2_eq (h j : ℝ) : coefficient 2 h j =
    6 * polyHorner (nltDer (nltL2 j)) h := by
  norm_num [coefficient, row2, nltL2, nltDer, nltDerAux, polyHorner]
  ring

private theorem coefficient3_eq (h j : ℝ) : coefficient 3 h j =
    6 * polyHorner (nltDer (nltL3 j)) h := by
  norm_num [coefficient, row3, nltL3, nltDer, nltDerAux, polyHorner]
  ring

private theorem coefficient4_eq (h j : ℝ) : coefficient 4 h j =
    6 * polyHorner (nltDer (nltL4 j)) h := by
  norm_num [coefficient, row4, nltL4, nltDer, nltDerAux, polyHorner]
  ring

private theorem coefficient5_eq (h j : ℝ) : coefficient 5 h j =
    6 * polyHorner (nltDer (nltL5 j)) h := by
  norm_num [coefficient, row5, nltL5, nltDer, nltDerAux, polyHorner]
  ring

private theorem coefficient6_eq (h j : ℝ) : coefficient 6 h j =
    6 * polyHorner (nltDer (nltL6 j)) h := by
  norm_num [coefficient, row6, nltL6, nltDer, nltDerAux, polyHorner]
  ring

theorem coefficient_eq (i : Fin 7) (h j : ℝ) :
    coefficient i h j = 6 * polyHorner
      (nltDer (![nltL0 j, nltL1 j, nltL2 j, nltL3 j, nltL4 j, nltL5 j, nltL6 j] i)) h := by
  fin_cases i
  · exact coefficient0_eq h j
  · exact coefficient1_eq h j
  · exact coefficient2_eq h j
  · exact coefficient3_eq h j
  · exact coefficient4_eq h j
  · exact coefficient5_eq h j
  · exact coefficient6_eq h j

theorem value_eq (h j y : ℝ) : value h j y =
    6 * (polyHorner (nltDer (nltL0 j)) h + polyHorner (nltDer (nltL1 j)) h * y
      + polyHorner (nltDer (nltL2 j)) h * y ^ 2 + polyHorner (nltDer (nltL3 j)) h * y ^ 3
      + polyHorner (nltDer (nltL4 j)) h * y ^ 4 + polyHorner (nltDer (nltL5 j)) h * y ^ 5
      + polyHorner (nltDer (nltL6 j)) h * y ^ 6) := by
  norm_num [value, Fin.sum_univ_succ, coefficient_eq]
  ring

/-- Clear the duration denominator in the value at its maximum. -/
def boundary {R : Type*} [CommRing R] (h j : R) : R :=
  ∑ i : Fin 7, coefficient i h j * (h - j) ^ (i : ℕ) * (1 + 2 * j) ^ (6 - (i : ℕ))

/-- Clear the duration denominator in the duration derivative at its maximum. -/
def boundaryDerivative {R : Type*} [CommRing R] (h j : R) : R :=
  ∑ i : Fin 6, ((i + 1 : ℕ) : R) * coefficient ⟨i + 1, by omega⟩ h j *
    (h - j) ^ (i : ℕ) * (1 + 2 * j) ^ (5 - (i : ℕ))

theorem boundaryDerivative_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h j : R) : f (boundaryDerivative h j) = boundaryDerivative (f h) (f j) := by
  simp [boundaryDerivative, coefficient_map, map_ofNat]

/-- Clear the factor `32^3` in one sixth of the third duration derivative at `y=9/32`. -/
def curvatureEnd {R : Type*} [CommRing R] (h j : R) : R :=
  32 ^ 3 * coefficient 3 h j + 4 * 9 * 32 ^ 2 * coefficient 4 h j
    + 10 * 9 ^ 2 * 32 * coefficient 5 h j + 20 * 9 ^ 3 * coefficient 6 h j

noncomputable def durationPolynomial (h j : ℝ) : Polynomial ℝ :=
  ∑ i : Fin 7, Polynomial.C (coefficient i h j) * Polynomial.X ^ (i : ℕ)

theorem duration_eval (h j y : ℝ) : (durationPolynomial h j).eval y = value h j y := by
  norm_num [durationPolynomial, value, Fin.sum_univ_succ]

theorem duration_third (h j y : ℝ) :
    (durationPolynomial h j).derivative.derivative.derivative.eval y =
      6 * coefficient 3 h j + 24 * coefficient 4 h j * y
        + 60 * coefficient 5 h j * y ^ 2 + 120 * coefficient 6 h j * y ^ 3 := by
  norm_num [durationPolynomial, Fin.sum_univ_succ, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  ring

theorem boundary_eq (h j : ℝ) (hd : 1 + 2 * j ≠ 0) :
    (1 + 2 * j) ^ 6 * value h j ((h - j) / (1 + 2 * j)) = boundary h j := by
  norm_num [value, boundary, Fin.sum_univ_succ]
  field_simp

theorem boundaryDerivative_eq (h j : ℝ) (hd : 1 + 2 * j ≠ 0) :
    (1 + 2 * j) ^ 5 * (durationPolynomial h j).derivative.eval ((h - j) / (1 + 2 * j)) =
      boundaryDerivative h j := by
  norm_num [durationPolynomial, boundaryDerivative, Fin.sum_univ_succ,
    Polynomial.derivative_mul, Polynomial.derivative_pow]
  field_simp

end SmoothedOctagon.LowTScale

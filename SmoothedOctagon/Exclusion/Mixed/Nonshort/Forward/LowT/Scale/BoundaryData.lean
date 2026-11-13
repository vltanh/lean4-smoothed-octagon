module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.SlopeData

/-!
# The scale derivative at maximum duration

The coefficients below belong to the boundary value itself, after clearing
its positive duration denominator. Their order is by increasing gap degree.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

def boundaryCoefficients {R : Type*} [CommRing R] (h : R) : List R :=
  [-116280 * h ^ 14 - 1321107 * h ^ 13 - 6866709 * h ^ 12 - 20814654 * h ^ 11 - 39718548 * h ^ 10 - 48552900 * h ^ 9 - 36796299 * h ^ 8 - 14955705 * h ^ 7 - 925460 * h ^ 6 + 1772841 * h ^ 5 + 477762 * h ^ 4 - 138123 * h ^ 3 - 61658 * h ^ 2 + 2456 * h,
    -232560 * h ^ 14 - 3640182 * h ^ 13 - 23592285 * h ^ 12 - 86274627 * h ^ 11 - 194625600 * h ^ 10 - 273015579 * h ^ 9 - 221122455 * h ^ 8 - 67796742 * h ^ 7 + 43142301 * h ^ 6 + 49855515 * h ^ 5 + 16766414 * h ^ 4 + 796265 * h ^ 3 - 335169 * h ^ 2 + 74804 * h - 1192,
    -2002464 * h ^ 13 - 22891398 * h ^ 12 - 115038207 * h ^ 11 - 323539272 * h ^ 10 - 519269532 * h ^ 9 - 393893034 * h ^ 8 + 76698954 * h ^ 7 + 418644270 * h ^ 6 + 331423248 * h ^ 5 + 91752285 * h ^ 4 - 7610846 * h ^ 3 - 5786075 * h ^ 2 - 2697 * h - 78226,
    -6257088 * h ^ 12 - 54600354 * h ^ 11 - 200982429 * h ^ 10 - 330558360 * h ^ 9 + 14271570 * h ^ 8 + 976796310 * h ^ 7 + 1611250643 * h ^ 6 + 1113814374 * h ^ 5 + 234392763 * h ^ 4 - 87377101 * h ^ 3 - 33514638 * h ^ 2 + 242631 * h - 706003,
    -6560640 * h ^ 11 - 24598218 * h ^ 10 + 70794774 * h ^ 9 + 748382874 * h ^ 8 + 2247775623 * h ^ 7 + 3247158900 * h ^ 6 + 2200858554 * h ^ 5 + 336375316 * h ^ 4 - 294382820 * h ^ 3 - 69711459 * h ^ 2 + 14244665 * h - 3761015,
    9260784 * h ^ 10 + 139434060 * h ^ 9 + 788236086 * h ^ 8 + 2318915064 * h ^ 7 + 3587304087 * h ^ 6 + 2510699712 * h ^ 5 + 148365957 * h ^ 4 - 542325784 * h ^ 3 - 12881044 * h ^ 2 + 74052942 * h - 15920412,
    35221824 * h ^ 9 + 305292348 * h ^ 8 + 1138186386 * h ^ 7 + 2056839798 * h ^ 6 + 1381668291 * h ^ 5 - 474962184 * h ^ 4 - 714094370 * h ^ 3 + 181893236 * h ^ 2 + 173403469 * h - 51547114,
    39931776 * h ^ 8 + 230836956 * h ^ 7 + 469232694 * h ^ 6 - 3595218 * h ^ 5 - 1061778213 * h ^ 4 - 766844790 * h ^ 3 + 352715577 * h ^ 2 + 229533512 * h - 116205156,
    9576576 * h ^ 7 - 35516268 * h ^ 6 - 398234343 * h ^ 5 - 978429723 * h ^ 4 - 612602661 * h ^ 3 + 369944256 * h ^ 2 + 202708578 * h - 174347291,
    -24932880 * h ^ 6 - 185644062 * h ^ 5 - 468947793 * h ^ 4 - 308316405 * h ^ 3 + 291335757 * h ^ 2 + 159613947 * h - 169105018,
    -31535136 * h ^ 5 - 123683790 * h ^ 4 - 94842195 * h ^ 3 + 173268594 * h ^ 2 + 128617653 * h - 100365102,
    -17263296 * h ^ 4 - 24072090 * h ^ 3 + 59394279 * h ^ 2 + 77692842 * h - 31132881,
    -4700160 * h ^ 3 + 6586254 * h ^ 2 + 25185828 * h - 1792266,
    -506736 * h ^ 2 + 2969256 * h + 1390584,
    210936]

def boundaryHorner {R : Type*} [CommRing R] (h j : R) : R :=
  (boundaryCoefficients h).foldr (fun c v => c + j * v) 0

theorem boundaryHorner_eq {R : Type*} [CommRing R] (h j : R) :
    boundaryHorner h j = boundary h j := by
  norm_num [boundaryHorner, boundaryCoefficients, boundary, Fin.sum_univ_succ, coefficient,
    row0, row1, row2, row3, row4, row5, row6]
  ring

theorem boundaryHorner_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h j : R) : f (boundaryHorner h j) = boundaryHorner (f h) (f j) := by
  simp [boundaryHorner, boundaryCoefficients, map_ofNat]

noncomputable def boundaryPolynomial (h : ℝ) : Polynomial ℝ :=
  boundaryHorner (Polynomial.C h) Polynomial.X

theorem boundary_eval (h j : ℝ) : (boundaryPolynomial h).eval j = boundary h j := by
  rw [← boundaryHorner_eq]
  simpa [boundaryPolynomial] using
    boundaryHorner_map (Polynomial.evalRingHom j) (Polynomial.C h) Polynomial.X

theorem boundary_eval_horner (h j : ℝ) :
    (boundaryPolynomial h).eval j = polyHorner (boundaryCoefficients h) j := by
  rw [boundary_eval, ← boundaryHorner_eq]
  rfl

theorem boundary_derivative_horner (n : ℕ) (h j : ℝ) :
    ((Polynomial.derivative^[n]) (boundaryPolynomial h)).eval j =
      polyHorner ((nltDer^[n]) (boundaryCoefficients h)) j :=
  iterate_horner (fun s => boundary_eval_horner h s) n j

/-- The actual coefficient of the twice-differentiated rational boundary numerator. -/
def boundaryCurvatureCoefficient {R : Type*} [CommRing R] (i : Fin 15) (h : R) : R :=
  let b (k : ℕ) := (boundaryCoefficients h)[k]?.getD 0
  ((i + 2 : ℕ) : R) * ((i + 1 : ℕ) : R) * b (i + 2)
    + 4 * ((i + 1 : ℕ) : R) * (((i : ℕ) : R) - 6) * b (i + 1)
    + 4 * (((i : ℕ) : R) - 6) * (((i : ℕ) : R) - 7) * b i

def boundaryCurvature (h j : ℝ) : ℝ :=
  ∑ i : Fin 15, boundaryCurvatureCoefficient i h * j ^ (i : ℕ)

theorem boundaryCurvatureCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Fin 15) (h : R) :
    f (boundaryCurvatureCoefficient i h) = boundaryCurvatureCoefficient i (f h) := by
  fin_cases i <;> simp [boundaryCurvatureCoefficient, boundaryCoefficients, map_ofNat]

noncomputable def boundaryCoefficientPolynomial (i : Fin 15) : Polynomial ℝ :=
  boundaryCurvatureCoefficient i Polynomial.X

theorem boundary_coefficient_eval (i : Fin 15) (h : ℝ) :
    (boundaryCoefficientPolynomial i).eval h = boundaryCurvatureCoefficient i h := by
  simpa [boundaryCoefficientPolynomial] using
    boundaryCurvatureCoefficient_map (Polynomial.evalRingHom h) i Polynomial.X

end SmoothedOctagon.LowTScale

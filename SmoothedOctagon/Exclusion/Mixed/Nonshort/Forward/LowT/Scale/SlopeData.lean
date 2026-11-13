module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.SlopePolynomial

/-!
# A Horner form for the maximum-duration slope numerator

This is the boundary polynomial itself, with its duration denominator
cleared. Grouping its terms by scale makes its scale derivatives inexpensive
to check.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

def slopeCoefficients {R : Type*} [CommRing R] (j : R) : List R :=
  [-286416 * j ^ 13 - 1819824 * j ^ 12 + 4805214 * j ^ 11 + 72038193 * j ^ 10 + 261196137 * j ^ 9 + 493614066 * j ^ 8 + 561110182 * j ^ 7 + 401592353 * j ^ 6 + 182133850 * j ^ 5 + 51765385 * j ^ 4 + 9376735 * j ^ 3 + 1244579 * j ^ 2 + 119032 * j,
    -5223120 * j ^ 12 - 46130028 * j ^ 11 - 134413122 * j ^ 10 - 125257026 * j ^ 9 + 96815694 * j ^ 8 + 252931620 * j ^ 7 + 82964886 * j ^ 6 - 149441726 * j ^ 5 - 163890536 * j ^ 4 - 66834122 * j ^ 3 - 12215926 * j ^ 2 - 1179898 * j - 151192,
    -102816 * j ^ 12 - 28650666 * j ^ 11 - 233552331 * j ^ 10 - 725569257 * j ^ 9 - 1245093057 * j ^ 8 - 1580947092 * j ^ 7 - 1805040474 * j ^ 6 - 1652247814 * j ^ 5 - 978797760 * j ^ 4 - 318896567 * j ^ 3 - 46339766 * j ^ 2 - 2759877 * j - 614797,
    53856 * j ^ 11 - 53953848 * j ^ 10 - 331465596 * j ^ 9 - 662317860 * j ^ 8 - 573621300 * j ^ 7 - 361224660 * j ^ 6 - 389574894 * j ^ 5 - 265333212 * j ^ 4 + 3339474 * j ^ 3 + 68887320 * j ^ 2 + 17239698 * j - 685680,
    6807888 * j ^ 10 + 52188834 * j ^ 9 + 493054509 * j ^ 8 + 2198076978 * j ^ 7 + 4558285353 * j ^ 6 + 5114075862 * j ^ 5 + 3482820378 * j ^ 4 + 1585811016 * j ^ 3 + 485863404 * j ^ 2 + 75938739 * j + 829701,
    36242640 * j ^ 9 + 415921800 * j ^ 8 + 2201894376 * j ^ 7 + 5673581424 * j ^ 6 + 7664167674 * j ^ 5 + 5734646364 * j ^ 4 + 2425543344 * j ^ 3 + 558103638 * j ^ 2 + 48057966 * j - 4365978,
    88069248 * j ^ 8 + 789257916 * j ^ 7 + 2841868098 * j ^ 6 + 4640670984 * j ^ 5 + 3344773239 * j ^ 4 + 552912012 * j ^ 3 - 541628526 * j ^ 2 - 286255044 * j - 41100795,
    114585984 * j ^ 7 + 688176240 * j ^ 6 + 1306481880 * j ^ 5 + 220155000 * j ^ 4 - 1828101360 * j ^ 3 - 2008613460 * j ^ 2 - 809321574 * j - 113369100,
    71045856 * j ^ 6 + 142906452 * j ^ 5 - 595099398 * j ^ 4 - 2095142136 * j ^ 3 - 2286481194 * j ^ 2 - 1036031799 * j - 167330244,
    -5566752 * j ^ 5 - 267401376 * j ^ 4 - 1037052252 * j ^ 3 - 1408278246 * j ^ 2 - 779131380 * j - 150506370,
    -42276960 * j ^ 4 - 265686834 * j ^ 3 - 509457111 * j ^ 2 - 364323447 * j - 85465926,
    -30095712 * j ^ 3 - 104305464 * j ^ 2 - 104920956 * j - 30208860,
    -9486000 * j ^ 2 - 17096454 * j - 6186519,
    -1162800 * j - 581400]

def slopeHorner {R : Type*} [CommRing R] (h j : R) : R :=
  (slopeCoefficients j).foldr (fun c v => c + h * v) 0

theorem slopeHorner_eq {R : Type*} [CommRing R] (h j : R) :
    slopeHorner h j = boundaryDerivative h j := by
  norm_num [slopeHorner, slopeCoefficients, boundaryDerivative, Fin.sum_univ_succ, coefficient,
    row1, row2, row3, row4, row5, row6]
  ring

theorem slopePolynomial_eq (j : ℝ) :
    slopePolynomial j = slopeHorner Polynomial.X (Polynomial.C j) := by
  rw [slopePolynomial, slopeHorner_eq]

theorem slopeHorner_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h j : R) : f (slopeHorner h j) = slopeHorner (f h) (f j) := by
  simp [slopeHorner, slopeCoefficients, map_ofNat]

theorem slopeJet_zero : slopeJet 0 = slopeHorner (Polynomial.C (1 / 4)) Polynomial.X := by
  simpa [slopeJet, slopeJoint, ← slopeHorner_eq] using
    slopeHorner_map (Polynomial.evalRingHom (Polynomial.C (1 / 4 : ℝ)))
      Polynomial.X (Polynomial.C Polynomial.X)

theorem slope_eval_horner (h j : ℝ) :
    (slopePolynomial j).eval h = polyHorner (slopeCoefficients j) h := by
  rw [slope_eval, ← slopeHorner_eq]
  rfl

/-- Differentiating coefficient lists agrees with repeated polynomial differentiation. -/
theorem iterate_horner {p : Polynomial ℝ} {cs : List ℝ}
    (hp : ∀ s, p.eval s = polyHorner cs s) (n : ℕ) (h : ℝ) :
    ((Polynomial.derivative^[n]) p).eval h = polyHorner ((nltDer^[n]) cs) h := by
  induction n generalizing h with
  | zero => exact hp h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have he : (fun s => ((Polynomial.derivative^[n]) p).eval s) =
        polyHorner ((nltDer^[n]) cs) := funext ih
    have hd := ((Polynomial.derivative^[n]) p).hasDerivAt h
    rw [he] at hd
    exact hd.unique (nlt_hasDerivAt_horner ((nltDer^[n]) cs) h)

theorem slope_derivative_horner (n : ℕ) (h j : ℝ) :
    ((Polynomial.derivative^[n]) (slopePolynomial j)).eval h =
      polyHorner ((nltDer^[n]) (slopeCoefficients j)) h :=
  iterate_horner (fun s => slope_eval_horner s j) n h

end SmoothedOctagon.LowTScale

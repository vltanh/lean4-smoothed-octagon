module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Polynomial

/-!
# The duration slope at maximum duration

Clearing the positive duration denominator gives a polynomial in the scale
and order gap. Its scale derivatives at `1/4` are polynomials in the gap.
Evaluation commutes with differentiation, so no separate coefficient data
are needed for these derivatives.
-/

@[expose] public section

namespace SmoothedOctagon.LowTScale

noncomputable def slopePolynomial (j : ℝ) : Polynomial ℝ :=
  boundaryDerivative Polynomial.X (Polynomial.C j)

noncomputable def slopeJoint : Polynomial (Polynomial ℝ) :=
  boundaryDerivative Polynomial.X (Polynomial.C Polynomial.X)

noncomputable def slopeJet (n : ℕ) : Polynomial ℝ :=
  ((Polynomial.derivative^[n]) slopeJoint).eval (Polynomial.C (1 / 4))

theorem slope_eval (h j : ℝ) : (slopePolynomial j).eval h = boundaryDerivative h j := by
  simpa [slopePolynomial] using
    boundaryDerivative_map (Polynomial.evalRingHom h) Polynomial.X (Polynomial.C j)

theorem slopeJoint_map (j : ℝ) :
    slopeJoint.map (Polynomial.evalRingHom j) = slopePolynomial j := by
  simpa [slopeJoint, slopePolynomial] using
    boundaryDerivative_map (Polynomial.mapRingHom (Polynomial.evalRingHom j))
      Polynomial.X (Polynomial.C Polynomial.X)

theorem slopeJet_eval (n : ℕ) (j : ℝ) :
    (slopeJet n).eval j = ((Polynomial.derivative^[n]) (slopePolynomial j)).eval (1 / 4) := by
  rw [← slopeJoint_map, Polynomial.iterate_derivative_map]
  have hm := Polynomial.eval_map_apply (Polynomial.evalRingHom j)
    (p := (Polynomial.derivative^[n]) slopeJoint) (Polynomial.C (1 / 4))
  simpa [slopeJet] using hm.symm

end SmoothedOctagon.LowTScale

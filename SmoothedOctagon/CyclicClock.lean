module

public import SmoothedOctagon.BalancedClock
public import SmoothedOctagon.ContactLift

/-!
# Cyclic determinant time for an actual worst disk

The positive contact successor of an actual worst disk is conjugated by the
constructed determinant clock to translation by one sixth of the new full period.
The normalized contacts retain every balanced-pair clause. Their frame satisfies
`G (t + P/6) = G t * R`, and differentiation gives the logarithmic-state identity
`Y (t + P/6) = R⁻¹ * Y t * R`.

Consequently the initial frame and both control terminal conditions follow from
actual balanced circle geometry. The subsequent realization theorem supplies the
measurable control and exact cost; no optimality against arbitrary control
trajectories is claimed here. Source draft only: compilation and kernel validation
have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real Matrix SmoothedPolygons

/-- A cyclic frame identity determines the conjugacy of its logarithmic state.
The determinant-one frame hypothesis discharges the inverse cancellations. -/
theorem state_cyclic_of_frame {G Y : ℝ → Mat2} {T : ℝ}
    (hD : ∀ t, HasDerivAtEntrywise G (G t * Y t) t)
    (hdet : ∀ t, (G t).det = 1)
    (hshift : ∀ t, G (t + T) = G t * R) :
    ∀ t, Y (t + T) = R⁻¹ * Y t * R := by
  have hRdet : R.det = 1 := by
    have h := congrArg Matrix.det (hshift 0)
    simpa only [Matrix.det_mul, hdet, one_mul] using h.symm
  have hRunit : IsUnit R.det := by
    rw [hRdet]
    exact isUnit_one
  have hfun : (fun u ↦ G (u + T)) = fun u ↦ G u * R := funext hshift
  intro t
  have hGunit : IsUnit (G t).det := by
    rw [hdet t]
    exact isUnit_one
  have hleft : HasDerivAtEntrywise (fun u ↦ G (u + T))
      (G (t + T) * Y (t + T)) t := by
    simpa only [one_smul] using
      (hD (t + T)).scomp ((hasDerivAt_id t).add_const T)
  rw [hfun] at hleft
  have hmatrix := hleft.unique ((hD t).mul_const R)
  rw [hshift t] at hmatrix
  have hrel : R * Y (t + T) = Y t * R := by
    have h := congrArg (fun M : Mat2 ↦ (G t)⁻¹ * M) hmatrix
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGunit,
      Matrix.one_mul] using h
  have h := congrArg (fun M : Mat2 ↦ R⁻¹ * M) hrel
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRunit,
    Matrix.one_mul] using h

/-- The actual positive cyclic contact lift and the constructed determinant clock
produce a balanced circle representation with a constant contact time step. The
frame and state satisfy the global cyclic identities and the exact terminal
conditions at `P / 6`. All clock and contact-lift hypotheses are constructed. -/
theorem balanced_exists_cyclic_determinant_clock {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hK : IsWorstDisk K) (hbal : IsBalancedPair K σ tf)
    (hcirc : IsCircleRepresentation σ) :
    ∃ P : ℝ, 0 < P ∧ ∃ a : ℝ ≃o ℝ,
      a 0 = 0 ∧ ContDiff ℝ 1 (fun t ↦ a t) ∧
      (∀ t, 0 < deriv (fun u ↦ a u) t) ∧
      (∀ t, a (t + P) = a t + 6 * tf) ∧
      IsBalancedPair K (fun j ↦ σ j ∘ a) (P / 6) ∧
      IsCircleRepresentation (fun j ↦ σ j ∘ a) ∧
      (∀ j t, σ j (a (t + P / 6)) = σ (j + 1) (a t)) ∧
      (∀ t, IsStarState (normalizedContactState σ a t)) ∧
      LipschitzOnEntrywise (normalizedContactState σ a) univ ∧
      (∀ t, HasDerivAtEntrywise (fun u ↦ contactFrame σ (a u))
        (contactFrame σ (a t) * normalizedContactState σ a t) t) ∧
      (∀ t, contactFrame σ (a (t + P / 6)) = contactFrame σ (a t) * R) ∧
      (∀ t, normalizedContactState σ a (t + P / 6) =
        R⁻¹ * normalizedContactState σ a t * R) ∧
      contactFrame σ (a 0) = 1 ∧ contactFrame σ (a (P / 6)) = R ∧
      normalizedContactState σ a (P / 6) = R⁻¹ * normalizedContactState σ a 0 * R := by
  obtain ⟨P, hP, a, ha0, haC, haD, hapos, haper, hstar, hLip, hg⟩ :=
    balanced_exists_determinant_clock hbal
  obtain ⟨φ, hφ, hφpos, hshift, hφsix, _, _⟩ :=
    exists_positive_cyclic_contact_lift hK hbal hcirc
  have hconj := determinantClock_conjugates_successor hbal a haD haper
    hφ hφpos hshift hφsix
  have hτbal := balancedPair_determinantClock_reparam hbal a ha0 haC hapos hP
    haper hLip hg
  have hτcircle : IsCircleRepresentation (fun j ↦ σ j ∘ a) := by
    intro j
    change σ j (a 0) = sixthRoot j
    rw [ha0]
    exact hcirc j
  have hτshift : ∀ j t, σ j (a (t + P / 6)) = σ (j + 1) (a t) := by
    intro j t
    rw [← hconj t]
    exact hshift j (a t)
  have hGshift : ∀ t, contactFrame σ (a (t + P / 6)) = contactFrame σ (a t) * R := by
    intro t
    rw [← hconj t]
    exact contactFrame_shift_of_contacts hbal.2.2.2.1 hshift (a t)
  have hYshift := state_cyclic_of_frame hg
    (fun t ↦ contactFrame_det hbal.2.2.2.1 (a t)) hGshift
  have hG0 : contactFrame σ (a 0) = 1 := by
    rw [ha0]
    exact contactFrame_initial hcirc
  have hGT : contactFrame σ (a (P / 6)) = R := by
    simpa only [zero_add, hG0, Matrix.one_mul] using hGshift 0
  have hYT : normalizedContactState σ a (P / 6) =
      R⁻¹ * normalizedContactState σ a 0 * R := by
    simpa only [zero_add] using hYshift 0
  exact ⟨P, hP, a, ha0, haC, hapos, haper, hτbal, hτcircle, hτshift,
    hstar, hLip, hg, hGshift, hYshift, hG0, hGT, hYT⟩

end SmoothedOctagon

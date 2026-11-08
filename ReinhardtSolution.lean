module

public import SmoothedOctagon.Main
public import SmoothedOctagon.Interval.SmallerShort

/-!
# Proofs of the statements of `ReinhardtChallenge.lean`

Each theorem of `ReinhardtChallenge.lean` is restated here word for word and proved from the library:
`SmoothedOctagon.Main` (the main theorems in the Challenge's vocabulary) and the kernel-checked
interval certificate `SmoothedOctagon.Interval.certSmallerShort`, which discharges the last
interval cover. Palomar's Comparator checks that these theorems are exactly the Challenge's.
-/

@[expose] public section

/-- The interval cover of the proof, kernel-checked. -/
theorem SmoothedOctagon.Solution.covers : SmoothedOctagon.Certificates.IntervalCovers :=
  ⟨⟨SmoothedOctagon.Interval.certSmallerShort⟩⟩


namespace ReinhardtChallenge

open SmoothedPolygons SmoothedOctagon MeasureTheory

/-- **The smoothed octagon.** Reinhardt's smoothed octagon is a centrally symmetric convex disk of
greatest packing density `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`. -/
theorem octagon_density :
    IsConvexDisk smoothedOctagon ∧ (∀ x ∈ smoothedOctagon, -x ∈ smoothedOctagon) ∧
      greatestPackingDensity smoothedOctagon = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  exact SmoothedOctagon.smoothedOctagon_spec

/-- **The Reinhardt conjecture.** Every centrally symmetric convex disk `K` in the plane has
greatest packing density at least `δ_oct`, the density of the smoothed octagon. -/
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  exact SmoothedOctagon.reinhardt_of SmoothedOctagon.Solution.covers K hK hsymm

/-- **The equality case.** A centrally symmetric convex disk has greatest packing density `δ_oct`
if and only if it is the image of the smoothed octagon under an invertible affine map. -/
theorem reinhardt_equality (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
      ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = A '' smoothedOctagon := by
  exact SmoothedOctagon.reinhardt_equality_classical_of SmoothedOctagon.Solution.covers K hK hsymm

end ReinhardtChallenge

end

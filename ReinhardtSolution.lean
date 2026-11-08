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


open SmoothedPolygons MeasureTheory

/-- **The Reinhardt conjecture.** Every centrally symmetric convex disk `K` in the plane has
greatest packing density at least `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`, the density of the
smoothed octagon. -/
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  exact SmoothedOctagon.reinhardt_of SmoothedOctagon.Solution.covers K hK hsymm

/-- **The equality case.** The trajectory of the smoothed octagon exists, and a centrally symmetric
convex disk has greatest packing density `δ_oct` if and only if it is the image of the smoothed
octagon, the convex hull of the arcs `g([0, t_f]) s_j`, under an invertible affine map. -/
theorem reinhardt_equality :
    (∃ g X : ℝ → Mat2,
      IsStateTrajectory (tf 1) (polygonControl 1) g X ∧ g 0 = 1 ∧ X 0 = Φ 0 (y₀ 1)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ 1) →
      ∀ K : Set (Fin 2 → ℝ), IsConvexDisk K → (∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) →
        (greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
          ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ),
            K = A '' convexHull ℝ
              (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1))) := by
  exact SmoothedOctagon.reinhardt_equality_of SmoothedOctagon.Solution.covers

/-- **The control form.** Every trajectory of Hales's control problem from `g(0) = I` to
`g(T) = R` with `X(T) = R⁻¹ X(0) R`, for any terminal time `T` and any measurable control, has
cost at least `√12 δ_oct`. -/
theorem reinhardt_cost (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2)
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (hgT : g T = R)
    (hXT : X T = R⁻¹ * X 0 * R) :
    √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ≤ reinhardtCost T X := by
  exact SmoothedOctagon.reinhardt_cost_of SmoothedOctagon.Solution.covers T u g X h hg0 hgT hXT

/-- **The smoothed octagon.** For the octagon trajectory, the convex hull of the arcs
`g([0, t_f]) s_j` is a convex disk symmetric about the origin, of area `√12 δ_oct` and greatest
packing density `δ_oct`. -/
theorem octagon_area (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf 1) (polygonControl 1) g X) (hg0 : g 0 = 1)
    (hX0 : X 0 = Φ 0 (y₀ 1)) :
    let K := convexHull ℝ (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1))
    IsConvexDisk K ∧ (∀ x ∈ K, -x ∈ K) ∧
      volume.real K = √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ∧
      greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  exact SmoothedOctagon.octagon_area g X h hg0 hX0

end ReinhardtChallenge

end

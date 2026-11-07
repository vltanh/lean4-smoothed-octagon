module

public import SmoothedOctagon.LowerBound
public import SmoothedOctagon.Equality.Transport
public import SmoothedOctagon.Equality.Converse
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# The Reinhardt conjecture

The main theorems, first in the library's vocabulary (`fullReinhardtConjecture`: the smoothed
octagon is a worst disk, and every worst disk is a linear image of it), then in the vocabulary of
`Challenge.lean`: arbitrary centres of symmetry, invertible affine maps, the octagon as the convex
hull of the six arcs of its trajectory, and the constant written `(8 - 4√2 - log 2)/(2√2 - 1)`.

Both are conditional on the two named hypotheses of the proof: Hales–Vajjha's Theorem 5.0.2
(`Cited.HalesVajjha.Theorem5_0_2`, until Chapter 5 is formalized in `lean4-smoothed-polygon`) and
the interval covers (`Certificates.IntervalCovers`, until their hand replacements are complete).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-- **The Reinhardt conjecture with its equality case**, in the library's vocabulary. -/
theorem fullReinhardtConjecture (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) : FullReinhardtConjecture :=
  ⟨reinhardtConjecture h502 hcov, worstDisk_eq_linear_image h502 hcov⟩

/-! ### The statements of `Challenge.lean`, under the two hypotheses -/

/-- `Challenge.reinhardt`, under the hypotheses. -/
theorem reinhardt_of (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  sorry

/-- `Challenge.reinhardt_equality`, under the hypotheses. -/
theorem reinhardt_equality_of (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) :
    (∃ g X : ℝ → Mat2,
      IsStateTrajectory (tf 1) (polygonControl 1) g X ∧ g 0 = 1 ∧ X 0 = Φ 0 (y₀ 1)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ 1) →
      ∀ K : Set (Fin 2 → ℝ), IsConvexDisk K → (∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) →
        (greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
          ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ),
            K = A '' convexHull ℝ
              (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1))) := by
  sorry

/-- `Challenge.reinhardt_cost`, under the hypotheses. -/
theorem reinhardt_cost_of (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2)
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (hgT : g T = R)
    (hXT : X T = R⁻¹ * X 0 * R) :
    √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ≤ reinhardtCost T X := by
  sorry

/-- `Challenge.octagon_area` (unconditional). -/
theorem octagon_area (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf 1) (polygonControl 1) g X) (hg0 : g 0 = 1)
    (hX0 : X 0 = Φ 0 (y₀ 1)) :
    let K := convexHull ℝ (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1))
    IsConvexDisk K ∧ (∀ x ∈ K, -x ∈ K) ∧
      volume.real K = √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ∧
      greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  sorry

end SmoothedOctagon

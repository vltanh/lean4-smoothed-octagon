module

public import SmoothedOctagon.LowerBound
public import SmoothedOctagon.Equality.Transport
public import SmoothedOctagon.Equality.Converse
public import SmoothedOctagon.Bridge.Density
public import SmoothedOctagon.Bridge.Octagon
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# The Reinhardt conjecture

The main theorems, first in the library's vocabulary (`fullReinhardtConjecture`: the smoothed
octagon is a worst disk, and every worst disk is a linear image of it), then in the vocabulary of
`Challenge.lean`: arbitrary centres of symmetry, invertible affine maps, the octagon as the convex
hull of the six arcs of its trajectory, and the constant written `(8 - 4√2 - log 2)/(2√2 - 1)`.

Both are conditional on the one remaining named hypothesis of the proof, the interval covers
(`Certificates.IntervalCovers`, until their hand replacements are complete). Hales–Vajjha's
Theorem 5.0.2 is proved in `lean4-smoothed-polygon` (`SmoothedPolygons.theorem5_0_2`).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-- **The Reinhardt conjecture with its equality case**, in the library's vocabulary. -/
theorem fullReinhardtConjecture (hcov : Certificates.IntervalCovers) : FullReinhardtConjecture :=
  ⟨reinhardtConjecture hcov, worstDisk_eq_linear_image hcov⟩

/-! ### The statements of `Challenge.lean`, under the hypothesis -/

/-- `Challenge.reinhardt`, under the hypothesis. -/
theorem reinhardt_of (hcov : Certificates.IntervalCovers) (K : Set (Fin 2 → ℝ))
    (hK : IsConvexDisk K) (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  obtain ⟨c, hc⟩ := hsymm
  rw [bridge_octagonDensity_eq, ← bridge_greatestPackingDensity_translate K (-c)]
  exact reinhardtConjecture_iff_density_lower_bound.mp (reinhardtConjecture hcov) _
    (bridge_isCCSDisk_centre hK hc)

/-- `Challenge.reinhardt_equality`, under the hypothesis. -/
theorem reinhardt_equality_of (hcov : Certificates.IntervalCovers) :
    (∃ g X : ℝ → Mat2,
      IsStateTrajectory (tf 1) (polygonControl 1) g X ∧ g 0 = 1 ∧ X 0 = Φ 0 (y₀ 1)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ 1) →
      ∀ K : Set (Fin 2 → ℝ), IsConvexDisk K → (∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) →
        (greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
          ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ),
            K = A '' convexHull ℝ
              (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1))) := by
  refine ⟨⟨smoothedPolygonG 1, smoothedPolygonX 1, smoothedPolygon_isStateTrajectory 1 le_rfl⟩, ?_⟩
  intro g X h hg0 hX0 K hK hsymm
  rw [bridge_convexHull_arcs g X h hg0 hX0, bridge_octagonDensity_eq]
  constructor
  · -- A disk of density `δ_oct`, centred at the origin, is a worst disk, hence a linear image of
    -- the octagon.
    intro hd
    obtain ⟨c, hc⟩ := hsymm
    have hW : IsWorstDisk ((fun x ↦ x + -c) '' K) := by
      refine ⟨bridge_isCCSDisk_centre hK hc, ?_⟩
      rw [bridge_greatestPackingDensity_translate, hd,
        reinhardtConjecture_iff_minimax.mp (reinhardtConjecture hcov)]
    obtain ⟨A, hA⟩ := worstDisk_eq_linear_image hcov _ hW
    refine ⟨A.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Fin 2 → ℝ) c), ?_⟩
    rw [AffineEquiv.coe_trans, image_comp]
    change K = _ '' ((A : (Fin 2 → ℝ) → (Fin 2 → ℝ)) '' octagon)
    rw [← hA, image_image]
    simp
  · -- An affine image of the octagon is a translate of a linear image.
    rintro ⟨A, rfl⟩
    have e : (A : (Fin 2 → ℝ) → (Fin 2 → ℝ)) '' octagon =
        (fun y ↦ y + A 0) '' (A.linear '' octagon) := by
      rw [image_image]
      refine image_congr fun x _ ↦ ?_
      have := A.map_vadd 0 x
      simpa using this
    rw [e, bridge_greatestPackingDensity_translate, greatestPackingDensity_linear_image_octagon]

/-- `Challenge.reinhardt_cost`, under the hypothesis. -/
theorem reinhardt_cost_of (hcov : Certificates.IntervalCovers) (T : ℝ) (u : ℝ → Fin 3 → ℝ)
    (g X : ℝ → Mat2) (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (hgT : g T = R)
    (hXT : X T = R⁻¹ * X 0 * R) :
    √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ≤ reinhardtCost T X := by
  have := controlLowerBound hcov T u g X ⟨h, hg0, hgT, hXT⟩
  rwa [volume_real_octagon, octagonCost, ← bridge_octagonDensity_eq] at this

/-- `Challenge.octagon_area` (unconditional). -/
theorem octagon_area (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf 1) (polygonControl 1) g X) (hg0 : g 0 = 1)
    (hX0 : X 0 = Φ 0 (y₀ 1)) :
    let K := convexHull ℝ (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1))
    IsConvexDisk K ∧ (∀ x ∈ K, -x ∈ K) ∧
      volume.real K = √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ∧
      greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  intro K
  have hK : K = octagon := bridge_convexHull_arcs g X h hg0 hX0
  rw [hK, bridge_octagonDensity_eq]
  obtain ⟨hconv, hcomp, hint, hneg⟩ := octagon_isCCSDisk
  exact ⟨⟨hconv, hcomp, hint⟩, hneg, by rw [volume_real_octagon, octagonCost], octagon_density⟩

end SmoothedOctagon

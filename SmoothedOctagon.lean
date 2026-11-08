module

public import SmoothedOctagon.Foundations.Problem
public import SmoothedOctagon.Foundations.Normalization
public import SmoothedOctagon.Foundations.BoundaryTrace
public import SmoothedOctagon.Foundations.SupportNormal
public import SmoothedOctagon.Foundations.RadialRegularity
public import SmoothedOctagon.Foundations.ArcLength
public import SmoothedOctagon.Foundations.BalancedReduction
public import SmoothedOctagon.Foundations.BalancedTargets
public import SmoothedOctagon.Foundations.DeterminantClock
public import SmoothedOctagon.Foundations.ControlTrajectory
public import SmoothedOctagon.Foundations.ContactLift
public import SmoothedOctagon.Foundations.BalancedClock
public import SmoothedOctagon.Foundations.CyclicClock
public import SmoothedOctagon.Foundations.AdmissibleRealization
public import SmoothedOctagon.Foundations.LowCostWinding
public import SmoothedOctagon.Foundations.AdmissibleRegularity
public import SmoothedOctagon.Foundations.ControlBounds
public import SmoothedOctagon.Foundations.ReverseGeometry
public import SmoothedOctagon.Foundations.CyclicExtension
public import SmoothedOctagon.Foundations.ReverseComparison
public import SmoothedOctagon.Foundations.SingularLocus
public import SmoothedOctagon.Foundations.CircleExclusion
public import SmoothedOctagon.Foundations.SingularArc
public import SmoothedOctagon.Foundations.SwitchingMargin
public import SmoothedOctagon.Foundations.StrongSwitching
public import SmoothedOctagon.LowerBound
public import SmoothedOctagon.Equality.Transport
public import SmoothedOctagon.Equality.Converse
public import SmoothedOctagon.Bridge.Density
public import SmoothedOctagon.Bridge.Octagon
public import SmoothedOctagon.Bridge.Classical
public import SmoothedOctagon.Defs
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# The Reinhardt conjecture

The smoothed octagon has the least greatest packing density among centrally symmetric convex disks
in the plane, `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`, and it is the only such disk up to invertible
affine maps. This module states the main theorems and is the Solution of `Palomar/Challenge.lean`:

* in the library's vocabulary, `fullReinhardtConjecture`: the smoothed octagon is a worst disk, and
  every worst disk is a linear image of it;
* Hales's control form: the equality case with the smoothed octagon given as the convex hull of
  the six arcs of its trajectory, the lower bound on the cost of every admissible trajectory, and
  the octagon's area;
* the three statements of `Palomar/Challenge.lean`, restated word for word: arbitrary centres of
  symmetry, invertible affine maps, Reinhardt's smoothed octagon `smoothedOctagon`, and the
  constant written `(8 - 4√2 - log 2)/(2√2 - 1)`. Palomar's Comparator checks that they are exactly
  the Challenge's.

They have no hypothesis. The proof is organized by stage:

* `Foundations/`: the geometric reformulation. A worst disk, normalized and parametrized by its
  balanced boundary, is realized by a trajectory of Hales's control problem whose cost is its area;
  conversely every admissible trajectory of cost below `π`, with any measurable control, bounds a
  balanced disk of that area. So the conjecture is equivalent to the control lower bound, and the
  realization of a worst disk is a global control minimizer.
* `Reduction/`: a global minimizer is a normal vertex period with finitely many pieces in the compact
  domain `𝔥**`.
* `Period/`: vertex periods, margins, switch signs and the partition of sign sequences into the
  classes R, F, M3, M1, M2.
* `Exclusion/`: each class is impossible for competitive periods with at least six pieces.
* `Terminal/`: periods with at most five pieces cost at least `A_oct`, with equality only for the
  octagon.
* `LowerBound`, `Equality/`: the assembly.
* `Bridge/`: the Challenge's vocabulary, and Reinhardt's description of the smoothed octagon.
* `Defs`: the definitions the statements use, shared with the Challenge.

`Cited/` holds Hales–Vajjha's Definition 5.0.1 of the compact domain `𝔥**`. Their Theorem 5.0.2
is proved in `lean4-smoothed-polygon` (`SmoothedPolygons.theorem5_0_2`) and bridged in
`Reduction/CompactDomain.lean`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-- **The Reinhardt conjecture with its equality case**, in the library's vocabulary. -/
theorem fullReinhardtConjecture : FullReinhardtConjecture :=
  ⟨reinhardtConjecture, worstDisk_eq_linear_image⟩

/-! ### Hales's control form -/

/-- **The equality case**, with the smoothed octagon given by its trajectory: the trajectory
exists, and the worst disks are the affine images of the convex hull of its six arcs. -/
theorem reinhardt_equality_trajectory :
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
        reinhardtConjecture_iff_minimax.mp (reinhardtConjecture)]
    obtain ⟨A, hA⟩ := worstDisk_eq_linear_image _ hW
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

/-- **The control form.** Every trajectory of Hales's control problem from `g(0) = I` to
`g(T) = R` with `X(T) = R⁻¹ X(0) R`, for any terminal time `T` and any measurable control, has
cost at least `√12 δ_oct`. -/
theorem reinhardt_cost (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2)
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (hgT : g T = R)
    (hXT : X T = R⁻¹ * X 0 * R) :
    √12 * ((8 - 4 * √2 - Real.log 2) / (2 * √2 - 1)) ≤ reinhardtCost T X := by
  have := controlLowerBound T u g X ⟨h, hg0, hgT, hXT⟩
  rwa [volume_real_octagon, octagonCost, ← bridge_octagonDensity_eq] at this

/-- The smoothed octagon given by its trajectory has area `√12 δ_oct`, the cost of the trajectory,
and greatest packing density `δ_oct`. -/
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

namespace ReinhardtChallenge

/-- **The smoothed octagon.** Reinhardt's smoothed octagon is a centrally symmetric convex disk of
greatest packing density `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`. -/
theorem octagon_density :
    IsConvexDisk smoothedOctagon ∧ (∀ x ∈ smoothedOctagon, -x ∈ smoothedOctagon) ∧
      greatestPackingDensity smoothedOctagon = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  rw [SmoothedOctagon.cls_isConvexDisk_iff, SmoothedOctagon.cls_greatestPackingDensity_eq]
  exact SmoothedOctagon.smoothedOctagon_spec

/-- **The Reinhardt conjecture.** Every centrally symmetric convex disk `K` in the plane has
greatest packing density at least `δ_oct`, the density of the smoothed octagon. -/
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  rw [SmoothedOctagon.cls_isConvexDisk_iff] at hK
  rw [SmoothedOctagon.cls_greatestPackingDensity_eq]
  obtain ⟨c, hc⟩ := hsymm
  rw [SmoothedOctagon.bridge_octagonDensity_eq,
    ← SmoothedOctagon.bridge_greatestPackingDensity_translate K (-c)]
  exact SmoothedOctagon.reinhardtConjecture_iff_density_lower_bound.mp
    (SmoothedOctagon.reinhardtConjecture) _
    (SmoothedOctagon.bridge_isCCSDisk_centre hK hc)

/-- **The equality case.** A centrally symmetric convex disk has greatest packing density `δ_oct`
if and only if it is the image of the smoothed octagon under an invertible affine map. -/
theorem reinhardt_equality (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
      ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = A '' smoothedOctagon := by
  rw [SmoothedOctagon.cls_isConvexDisk_iff] at hK
  rw [SmoothedOctagon.cls_greatestPackingDensity_eq]
  obtain ⟨⟨g, X, h, hg0, hX0⟩, heq⟩ := SmoothedOctagon.reinhardt_equality_trajectory
  rw [heq g X h hg0 hX0 K hK hsymm, SmoothedOctagon.bridge_convexHull_arcs g X h hg0 hX0,
    SmoothedOctagon.cls_exists_affine_iff]

end ReinhardtChallenge

end

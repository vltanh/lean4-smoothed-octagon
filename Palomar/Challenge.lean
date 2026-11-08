module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The Reinhardt conjecture

Reinhardt (1934) asked which centrally symmetric convex disk in the plane packs worst: which one
has the least greatest packing density. He conjectured that the answer is the *smoothed octagon*,
a regular octagon whose corners are cut off by arcs of hyperbolas, with density

  `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1) = 0.902414…`,

and that it is the only worst disk up to affine maps. This file states the conjecture with its
equality case. It imports only Mathlib.

## Definitions

The definitions between the markers are copied word for word from `SmoothedOctagon/Defs.lean`
(`python3 scripts/sync_challenge_defs.py`). The packing definitions there are those of Hales and
Vajjha, *Packings of Smoothed Polygons* (arXiv:2405.04331), Definition 2.1.1, as formalized in
`lean4-smoothed-polygon`. Points of the plane are `Fin 2 → ℝ`, and areas are Lebesgue measure.

* `IsConvexDisk K`: `K` is compact and convex with nonempty interior. The theorems below take a
  centre `c` of symmetry, `2c - x ∈ K` for every `x ∈ K`.
* `greatestPackingDensity K` is the greatest density `δ(K)` of a packing of the plane by congruent
  copies of `K`: the supremum, over packings whose density exists, of the limit of the fraction of
  the disk of radius `r` that they cover, as `r → ∞`.
* `smoothedOctagon` is Reinhardt's smoothed octagon. With `octagonSideDist k x` the distance from
  `x` to the line `x₀ cos(kπ/4) + x₁ sin(kπ/4) = 1` of the `k`-th side of the regular octagon of
  inradius `1` (`k : Fin 8`), it is the regular octagon `0 ≤ octagonSideDist k x` with the corner
  between sides `k` and `k + 1` cut off along the hyperbola
  `octagonSideDist (k - 1) x * octagonSideDist (k + 2) x = √2/4`, whose asymptotes are the next
  two side lines.

## Theorems

* `octagon_density`: the smoothed octagon is a centrally symmetric convex disk of greatest packing
  density `δ_oct`.
* `reinhardt`: every centrally symmetric convex disk has greatest packing density at least
  `δ_oct`.
* `reinhardt_equality`: a centrally symmetric convex disk has greatest packing density `δ_oct` if
  and only if it is the image of the smoothed octagon under an invertible affine map of the plane.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

namespace ReinhardtChallenge

open MeasureTheory

/-! ### Convex disks and packing densities (Definition 2.1.1) -/

/-- A convex disk (§1.1, §2.1): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The Euclidean disk `B_r = {x | x₀² + x₁² ≤ r²}` of radius `r` centered at the origin
(Definition 2.1.1). -/
def euclidDisk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- `K'` is a congruent copy of `K` (§2.1): its image `{A x + b | x ∈ K}` under a Euclidean
isometry, with `A` an orthogonal matrix. -/
def IsCongruentCopy (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ Matrix.mulVec A x + b) '' K

/-- A packing (§2.1): a family of convex disks, any two distinct members of which do not overlap,
that is, have disjoint interiors. -/
def IsPacking (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  (∀ K' ∈ P, IsConvexDisk K') ∧ P.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- A packing with congruent copies of `K` (Definition 2.1.1). -/
def IsPackingOfCopies (K : Set (Fin 2 → ℝ)) (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  IsPacking P ∧ ∀ K' ∈ P, IsCongruentCopy K K'

/-- The ratio `(1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of Definition 2.1.1, in `[0, ∞]`. -/
noncomputable def packingRatio (P : Set (Set (Fin 2 → ℝ))) (r : ℝ) : ENNReal :=
  (∑' K' : P, volume ((K' : Set (Fin 2 → ℝ)) ∩ euclidDisk r)) / volume (euclidDisk r)

/-- The upper density `limsup_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def upperDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.limsup (packingRatio P) Filter.atTop

/-- The lower density `liminf_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def lowerDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.liminf (packingRatio P) Filter.atTop

/-- The density of `P` exists (Definition 2.1.1): the upper and lower densities exist (are
finite) and coincide. -/
def HasDensity (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  upperDensity P ≠ ⊤ ∧ upperDensity P = lowerDensity P

/-- The density `δ(K, P)` of a packing (Definition 2.1.1): the common value of the upper and
lower densities, when the density exists (`HasDensity`). -/
noncomputable def packingDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ :=
  (upperDensity P).toReal

/-- **Definition 2.1.1** (greatest packing density).
`δ(K) = sup {δ(K, P) | δ(K, P) exists, and P is a packing with congruent copies of K}`. -/
noncomputable def greatestPackingDensity (K : Set (Fin 2 → ℝ)) : ℝ :=
  sSup {d | ∃ P, IsPackingOfCopies K P ∧ HasDensity P ∧ packingDensity P = d}

/-! ### Reinhardt's smoothed octagon -/

/-- The distance `d_k(x) = 1 - (x₀ cos(kπ/4) + x₁ sin(kπ/4))` from `x` to the line
`x₀ cos(kπ/4) + x₁ sin(kπ/4) = 1` of the `k`-th side of the regular octagon of inradius `1`
(`k : Fin 8`), positive on the side of the origin. -/
noncomputable def octagonSideDist (k : Fin 8) (x : Fin 2 → ℝ) : ℝ :=
  1 - (x 0 * Real.cos ((k : ℕ) * Real.pi / 4) + x 1 * Real.sin ((k : ℕ) * Real.pi / 4))

/-- **Reinhardt's smoothed octagon**, as Reinhardt described it: the regular octagon `d_k ≥ 0` of
inradius `1` with each corner cut off by an arc of a hyperbola. The corner between sides `k` and
`k + 1` is replaced by the arc of the hyperbola `d_{k-1} d_{k+2} = √2/4`, whose asymptotes are the
next two side lines; the arc touches the two sides where `d_k + d_{k+1} = 3/2 - √2`, and beyond
that chord only the points with `d_{k-1} d_{k+2} ≥ √2/4` are kept. -/
def smoothedOctagon : Set (Fin 2 → ℝ) :=
  {x | ∀ k : Fin 8, 0 ≤ octagonSideDist k x ∧
    (octagonSideDist k x + octagonSideDist (k + 1) x ≤ 3 / 2 - √2 →
      √2 / 4 ≤ octagonSideDist (k - 1) x * octagonSideDist (k + 2) x)}

end ReinhardtChallenge

-- END SHARED DEFINITIONS

namespace ReinhardtChallenge

/-- **The smoothed octagon.** Reinhardt's smoothed octagon is a centrally symmetric convex disk of
greatest packing density `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`. -/
theorem octagon_density :
    IsConvexDisk smoothedOctagon ∧ (∀ x ∈ smoothedOctagon, -x ∈ smoothedOctagon) ∧
      greatestPackingDensity smoothedOctagon = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  sorry

/-- **The Reinhardt conjecture.** Every centrally symmetric convex disk `K` in the plane has
greatest packing density at least `δ_oct`, the density of the smoothed octagon. -/
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  sorry

/-- **The equality case.** A centrally symmetric convex disk has greatest packing density `δ_oct`
if and only if it is the image of the smoothed octagon under an invertible affine map. -/
theorem reinhardt_equality (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
      ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = A '' smoothedOctagon := by
  sorry

end ReinhardtChallenge

end

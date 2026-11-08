module

public import SmoothedPolygons.Ch4.StarDomain

/-!
# The compact state domain (Hales–Vajjha, Definition 5.0.1)

T. Hales and K. Vajjha, *Packings of Smoothed Polygons*, arXiv:2405.04331v1, Chapter 5.
Definition 5.0.1 cuts the ideal triangle `𝔥*` of star states down to a compact region `𝔥**`. The
proof of the Reinhardt bound uses it to keep every margin of a minimizing trajectory at least
`2/15`.

Theorem 5.0.2 (`th:compactification`: the state of a balanced disk whose area is at most that of
the smoothed octagon never leaves `𝔥**`) is proved in `SmoothedPolygons`
(`SmoothedPolygons.theorem5_0_2`, `Ch5/Theorem502.lean`), where `𝔥**` is `truncatedStarDomain`, and
bridged in `SmoothedOctagon/Reduction/CompactDomain.lean`
(`SmoothedOctagon.Reduction.compactDomain_eq_truncatedStarDomain`,
`SmoothedOctagon.Reduction.inCompactDomain_of_isReinhardtMinimizer`).
-/

@[expose] public section

namespace Cited.HalesVajjha

open SmoothedPolygons

/-- **Definition 5.0.1** (`𝔥**`). The ideal triangle `𝔥*` of star states (`y > 0`, `|x| < 1/√3`,
`x² + y² > 1/3`), less the horoball `B(i∞) = {y > 9/2}`, its two images `B(±1/√3)` under `R^{±1}`
(the open disks of radius `4/27` tangent to `ℝ` at `±1/√3`), and the three neighbourhoods
`Π_k⁺ = {ρ_k < 1/15}` of the edges, written with the star functions of `Φ(x + iy)`. -/
def compactDomain : Set (ℝ × ℝ) :=
  {p | p ∈ starDomain ∧ p.2 ≤ 9 / 2 ∧
    8 / 27 * p.2 ≤ (p.1 - 1 / √3) ^ 2 + p.2 ^ 2 ∧ 8 / 27 * p.2 ≤ (p.1 + 1 / √3) ^ 2 + p.2 ^ 2 ∧
    1 / 15 ≤ ρ₀ (Φ p.1 p.2) ∧ 1 / 15 ≤ ρ₁ (Φ p.1 p.2) ∧ 1 / 15 ≤ ρ₂ (Φ p.1 p.2)}

/-- A state `X` lies in `𝔥**`: `X = Φ(x + iy)` with `(x, y) ∈ 𝔥**`. -/
def InCompactDomain (X : Mat2) : Prop :=
  ∃ x y : ℝ, X = Φ x y ∧ (x, y) ∈ compactDomain

end Cited.HalesVajjha

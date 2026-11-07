module

public import SmoothedPolygons.Ch2.BalancedCircle
public import SmoothedPolygons.Ch4.StarDomain
public import SmoothedPolygons.Ch3.AreaFormula
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# The compact state domain (Hales–Vajjha, Chapter 5)

T. Hales and K. Vajjha, *Packings of Smoothed Polygons*, arXiv:2405.04331v1, Chapter 5.
Definition 5.0.1 cuts the ideal triangle `𝔥*` of star states down to a compact region `𝔥**`;
Theorem 5.0.2 (`th:compactification`) says that the state `z(t) = Φ⁻¹(X(t))` of a balanced disk
whose area is at most that of the smoothed octagon never leaves `𝔥**`. The proof of the Reinhardt
bound uses it to keep every margin of a minimizing trajectory at least `2/15`.

Chapter 5 is not yet formalized (it is planned in `lean4-smoothed-polygon`). Until it is,
`Theorem5_0_2` is a named hypothesis of every statement whose proof uses it; nothing here asserts
it.

The statement below is the book's, in the vocabulary of `SmoothedPolygons`: a balanced disk `K` in
circle representation with multi-curve `σ`, a boundary trajectory `(g, X)` with control `u`
(`σ_j(t) = g(t) s_j*` on `[0, t_f]`, `σ_j(t + t_f) = σ_{j+1}(t)`), and a time `t` at which the state
leaves `𝔥**`; then the area of `K`, which is the cost of `(g, X)`, exceeds the area of the smoothed
octagon.
-/

@[expose] public section

namespace Cited.HalesVajjha

open SmoothedPolygons MeasureTheory Set Matrix

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

/-- **Theorem 5.0.2** (`th:compactification`), as a proposition. Let `K` be a balanced disk in
circle representation with boundary trajectory `(g, X)` on `[0, t_f]`. If the state leaves `𝔥**` at
some time, the area of `K` is strictly greater than the area of the smoothed octagon. -/
def Theorem5_0_2 : Prop :=
  ∀ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (u : ℝ → Fin 3 → ℝ)
    (g X : ℝ → Mat2),
    IsBalancedPair K σ tf → IsCircleRepresentation σ →
    (∀ j, ∀ t ∈ Icc 0 tf, σ j t = g t *ᵥ sixthRoot j) → (∀ j t, σ j (t + tf) = σ (j + 1) t) →
    IsStateTrajectory tf u g X → (∃ t ∈ Icc 0 tf, ¬ InCompactDomain (X t)) →
    volume.real (smoothedPolygonDisk 1) < volume.real K

end Cited.HalesVajjha

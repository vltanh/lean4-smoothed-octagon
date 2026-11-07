module

public import SmoothedOctagon.Period.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# The terminal comparison: periods with at most five pieces

`SMALL_PERIOD_COST_EQUALITY_AUDIT`, with the hand proofs `legacy/FOUR_LINK_HAND_PROOF` and
`legacy/FIVE_ARC_PROGRESS`.

* Fewer than four pieces are impossible: the fixed-edge endpoint obstruction and twisted rebasing.
* Four pieces: tangent closure forces alternating factors and state closure forces the initial
  state; the cost, as a function of the factors, has its unique minimum `A_oct` at the octagon's
  factors `√2`, initial state `Φ(0, y₀)` and word `e₂ e₀ e₁ e₂`.
* Five pieces: with the twist, a five-piece word is mixed (the orbit of `01020`), which costs
  strictly more than `A_oct`, or entirely reverse (the orbit of `02102`), which case R excludes.

Equality therefore forces the smoothed octagon's trajectory, up to the relabeling of the vertices
by a power of `R`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-- **Terminal cost bound.** A normal vertex period with at most five pieces costs at least
`A_oct`. -/
theorem terminal_cost (P : NormalPeriod) (hN : P.N ≤ 5) : octagonCost ≤ P.cost := by
  sorry

/-- **Terminal equality.** A normal vertex period with at most five pieces and cost `A_oct` is the
smoothed octagon's trajectory, after relabeling the vertices by `C = R^r`:
`C⁻¹ g C` and `C⁻¹ X C` are the octagon's frame and state on `[0, t_f]`. -/
theorem terminal_equality (P : NormalPeriod) (hN : P.N ≤ 5) (heq : P.cost = octagonCost) :
    P.T = tf 1 ∧ ∃ r : ℕ, ∀ t ∈ Icc 0 P.T,
      (R ^ r)⁻¹ * P.g t * R ^ r = smoothedPolygonG 1 t ∧
        (R ^ r)⁻¹ * P.X t * R ^ r = smoothedPolygonX 1 t := by
  sorry

end SmoothedOctagon

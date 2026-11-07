module

public import SmoothedOctagon.Terminal.Words

/-!
# Terminal comparison: five mixed pieces

`legacy/FIVE_ARC_PROGRESS`. A closed cycle with the word `0 1 0 2 0` has factors
`(P(u), Q(u), r, Q(v), P(v))`, `P(t) = (1 + t²)/(2t)`, `Q(t) = (1 + t²)/(1 - t²)`,
`r = 4uv/((1 - u²)(1 - v²)) > 1`, for `u, v ∈ (0, 1)` with `u + v + uv > 1` (tangent closure,
FAP (4)-(7)), initial margins `(2/√N)(A, d, B)` with `d = (1 - u)(1 - v)`, `N = d(4 - d)`,
`A = (1 + u)(1 - v)`, `B = (1 - u)(1 + v)` (state closure, FAP (8)-(11)), and raw cost
`8 δ(u, v)`, `δ(u, v) = [2(d + 2) - (d/2)(F(u) + F(v))]/(4 - d)` (FAP (17)-(18)). The strict
inequality `δ(u, v) > δ_oct` is FAP (19)-(25).

* `Term.fiveF`, `Term.fiveDensity`, `Term.fivePiece_density_gt` (still `sorry`: pure real
  analysis, FAP (19)-(25)).
* `Term.Cycle.five_param` (still `sorry`: closure, forced state and cost algebra, FAP (4)-(18),
  checked numerically in these conventions), `Term.Cycle.five_rawCost_gt`.
-/

@[expose] public section

namespace SmoothedOctagon

namespace Term

open SmoothedPolygons

/-- `F(t) = ((1+t)/(1-t))² log((1+t²)/(2t)) + t⁻² log((1+t²)/(1-t²)) + log(2t/(1-t²))`
(FAP (17)). -/
noncomputable def fiveF (t : ℝ) : ℝ :=
  ((1 + t) / (1 - t)) ^ 2 * Real.log ((1 + t ^ 2) / (2 * t)) +
    Real.log ((1 + t ^ 2) / (1 - t ^ 2)) / t ^ 2 + Real.log (2 * t / (1 - t ^ 2))

/-- The density `δ(u, v)` of the mixed five-piece family (FAP (18)). -/
noncomputable def fiveDensity (u v : ℝ) : ℝ :=
  (2 * ((1 - u) * (1 - v) + 2) - (1 - u) * (1 - v) / 2 * (fiveF u + fiveF v)) /
    (4 - (1 - u) * (1 - v))

/-- **The five-piece density inequality** (FAP (19)-(25)): `δ(u, v) > δ_oct`. -/
theorem fivePiece_density_gt {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (huv : 1 < u + v + u * v) : octagonDensity < fiveDensity u v := by
  sorry

namespace Cycle

/-- **The mixed five-piece cycles** (FAP (4)-(18)). -/
theorem five_param (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) :
    ∃ u v : ℝ, 0 < u ∧ u < 1 ∧ 0 < v ∧ v < 1 ∧ 1 < u + v + u * v ∧
      c.rawCost = 8 * fiveDensity u v := by
  sorry

/-- **Five-piece bound**: `8 δ_oct < rawCost` for the word `0 1 0 2 0`. -/
theorem five_rawCost_gt (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1) (h2 : c.lab 2 = 0)
    (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) : 8 * octagonDensity < c.rawCost := by
  obtain ⟨u, v, hu0, hu1, hv0, hv1, huv, hcost⟩ := c.five_param h0 h1 h2 h3 h4
  rw [hcost]
  linarith [fivePiece_density_gt hu0 hu1 hv0 hv1 huv]

end Cycle

end Term

end SmoothedOctagon

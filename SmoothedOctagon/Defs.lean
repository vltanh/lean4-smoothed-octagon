module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Reinhardt's smoothed octagon

The smoothed octagon as Reinhardt described it: the regular octagon of inradius `1` with each
corner cut off by an arc of a hyperbola. The statements of `ReinhardtChallenge.lean` use it, so the
block between the markers is copied word for word into that file
(`python3 scripts/sync_challenge_defs.py`); this module imports only Mathlib.
-/

@[expose] public section

-- BEGIN SHARED OCTAGON
namespace SmoothedOctagon

/-- The distance `d_k(x) = 1 - (x₀ cos(kπ/4) + x₁ sin(kπ/4))` from `x` to the line
`x₀ cos(kπ/4) + x₁ sin(kπ/4) = 1` of the `k`-th side of the regular octagon of inradius `1`,
positive on the side of the origin. -/
noncomputable def octagonSideDist (k : Fin 8) (x : Fin 2 → ℝ) : ℝ :=
  1 - (x 0 * Real.cos ((k : ℕ) * Real.pi / 4) + x 1 * Real.sin ((k : ℕ) * Real.pi / 4))

/-- **Reinhardt's smoothed octagon.** The regular octagon `d_k ≥ 0` (`k : Fin 8`) with each corner
cut off by an arc of a hyperbola. The corner between sides `k` and `k + 1` is replaced by the arc of
the hyperbola `d_{k-1} d_{k+2} = √2/4`, whose asymptotes are the next two side lines; the arc
touches the two sides where `d_k + d_{k+1} = 3/2 - √2`, and beyond that chord only the points with
`d_{k-1} d_{k+2} ≥ √2/4` are kept. -/
def smoothedOctagon : Set (Fin 2 → ℝ) :=
  {x | ∀ k : Fin 8, 0 ≤ octagonSideDist k x ∧
    (octagonSideDist k x + octagonSideDist (k + 1) x ≤ 3 / 2 - √2 →
      √2 / 4 ≤ octagonSideDist (k - 1) x * octagonSideDist (k + 2) x)}

end SmoothedOctagon
-- END SHARED OCTAGON

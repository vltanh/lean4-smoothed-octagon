module

public import SmoothedOctagon.Exclusion.ShortRun.Centre

/-!
# Case M1: the projective winding of the centre angles

`MIXED_GLOBAL_PROJECTIVE_WINDING` (1)-(2) for the all-short word `(− − +)^m`: with the switch
vectors of `MIXED_GLOBAL_COSTATE_ELLIPTIC` collapsed at the turns, the `m` centre angles
`φ_j ∈ (0, π)` (unsigned angles in the positive definite metric `S = -J₀U`, with
`cos φ_j = e_j / √(d_- d_+) = E_j / (2 √(u_j v_j))`) sum to `(m + 1) π / 3` over one period.

## Main API

* `m1_winding`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The all-short winding identity** (MGPW (2), MGSRAE (2)). -/
theorem m1_winding (P : NormalPeriod) (hc : P.IsCompetitive) {k₀ : ℤ} {m : ℕ}
    (hpat : P.m1_IsPattern k₀) (hN : P.N = 3 * m) (hpos : 0 < P.costateCycle.gam2 0) :
    ∑ j ∈ Finset.range m, Real.arccos (P.m1_E (m1_centre k₀ j) /
      (2 * √(P.m1_u (m1_centre k₀ j) * P.m1_v (m1_centre k₀ j)))) = (m + 1) * π / 3 := by
  sorry

end SmoothedOctagon

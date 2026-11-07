module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Certificates.Covers

/-!
# Case F: no competitive entirely forward period with six or more pieces

`GLOBAL_FORWARD_PERIOD_EXCLUSION`. A competitive normal vertex period with every switch forward has
at most five pieces (with the twist, `N ≡ 1 mod 3`, so `N = 4`: the octagon's word). The proof
reduces the period to its global-minimum window, then uses the cost–Casimir inequality, the neighbour
contraction and the complementary Casimir bound. The last two are, for now, the interval covers
`Certificates.ForwardCovers` (hand replacement in progress: gate H-F).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case F** (`GLOBAL_FORWARD_PERIOD_EXCLUSION`). No competitive normal vertex period with at least
six pieces has every switch forward. -/
theorem forward_exclusion (hcov : Certificates.ForwardCovers) (P : NormalPeriod)
    (hc : P.IsCompetitive) (hF : P.rep.AllForward) (hN : 6 ≤ P.N) : False := by
  sorry

end SmoothedOctagon

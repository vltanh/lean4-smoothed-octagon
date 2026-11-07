module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Certificates.Covers

/-!
# Case M2: no competitive mixed period with a nonshort forward run

`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION`. Take the global minimum of the active margins; in class M2
it sits at the centre of a reverse run (`MIXED_GLOBAL_MINIMUM_STRUCTURE`,
`MIXED_GLOBAL_SMALL_FORWARD_MINIMUM`). Choose the smaller adjacent turn. If the forward run on that
side is short, `MIXED_SMALLER_SHORT_PERIOD_EXCLUSION` applies; otherwise the next switch is forward
or reverse (`MIXED_SMALLER_TURN_CONTINUATION`), and both alternatives are excluded after the scalar
boundary comparison (`MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION`,
`MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION`, `MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION`,
`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`, with the hand corner
`MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION`). The scalar exclusions are, for now, the interval covers
`Certificates.MixedCovers` (hand replacement in progress: gates H-S and H-N).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case M2** (`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION`). No competitive normal vertex period with
state in `𝔥**` and at least six pieces has mixed signs, every reverse run of length two, and a
forward run of length at least two. -/
theorem nonshort_exclusion (hcov : Certificates.MixedCovers) (P : NormalPeriod)
    (hc : P.IsCompetitive) (hK : P.InCompactDomain) (h : P.rep.ClassM2) (hN : 6 ≤ P.N) :
    False := by
  sorry

end SmoothedOctagon

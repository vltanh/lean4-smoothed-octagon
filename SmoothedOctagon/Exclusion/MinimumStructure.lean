module

public import SmoothedOctagon.Period.Defs

/-!
# Case M3: reverse runs have exactly two switches

`MIXED_GLOBAL_MINIMUM_STRUCTURE`. In a mixed normal vertex period every maximal run of reverse
switches has exactly two switches, and its centre margin is a strict local minimum of the margins.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case M3** (`MIXED_GLOBAL_MINIMUM_STRUCTURE`). No normal vertex period has mixed switch signs
with a maximal reverse run of length other than two. -/
theorem minimumStructure_exclusion (P : NormalPeriod) (h : P.rep.ClassM3) : False := by
  sorry

end SmoothedOctagon

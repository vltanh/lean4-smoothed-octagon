module

public import SmoothedOctagon.Period.Defs

/-!
# Case R: no period is entirely reverse

`GLOBAL_REVERSE_PERIOD_EXCLUSION`. A normal vertex period cannot have every switch reverse, for any
number of pieces. The proof uses the needle (first-variation) inequalities of the same lift at each
reverse switch, read around the whole twisted period.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case R** (`GLOBAL_REVERSE_PERIOD_EXCLUSION`, Corollary R). No normal vertex period has every
switch reverse. -/
theorem reverse_exclusion (P : NormalPeriod) (hR : P.rep.AllReverse) : False := by
  sorry

end SmoothedOctagon

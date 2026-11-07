module

public import SmoothedOctagon.Period.Defs

/-!
# Case M1: no competitive all-short mixed period

`MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION`, with its two-centre base `MIXED_GLOBAL_SHORT_RUN_PERIOD`.
A competitive normal vertex period whose cyclic sign word is `(− − +)^m` does not exist: the
whole-period winding identity (`MIXED_GLOBAL_PROJECTIVE_WINDING`) and the angle budget of a
competitive period (`MIXED_GLOBAL_REVERSE_ANGLE_DENSITY`) are incompatible.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case M1** (`MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION`). No competitive normal vertex period has
mixed signs with every reverse run of length two and every forward run of length one. -/
theorem shortRuns_exclusion (P : NormalPeriod) (hc : P.IsCompetitive) (h : P.rep.ClassM1) :
    False := by
  sorry

end SmoothedOctagon

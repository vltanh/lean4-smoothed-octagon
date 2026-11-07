module

public import SmoothedOctagon.Period.Defs

/-!
# Case M3: reverse runs have exactly two switches

`MIXED_GLOBAL_MINIMUM_STRUCTURE`. In a mixed normal vertex period every maximal run of reverse
switches has exactly two switches, and the active margin of its centre piece is strictly smaller
than the active margins of the two pieces on each side. The positive form is used again by cases F
and M2; case M3 itself is the first half.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Reverse runs** (`MIXED_GLOBAL_MINIMUM_STRUCTURE`, Theorem). In a mixed normal vertex period, a
maximal run of reverse switches `k, …, k + L - 1` has `L = 2`, and the centre piece `k + 1` has an
active margin strictly smaller than those of the pieces `k - 1`, `k`, `k + 2` and `k + 3`. -/
theorem reverseRun_two_and_centre_min (P : NormalPeriod) (hmix : P.rep.IsMixed) {k : ℤ} {L : ℕ}
    (h : P.rep.IsReverseRun k L) :
    L = 2 ∧ P.activeMargin (k + 1) < P.activeMargin (k - 1) ∧
      P.activeMargin (k + 1) < P.activeMargin k ∧ P.activeMargin (k + 1) < P.activeMargin (k + 2) ∧
      P.activeMargin (k + 1) < P.activeMargin (k + 3) := by
  sorry

/-- **Case M3.** No normal vertex period has mixed switch signs with a maximal reverse run of
length other than two. -/
theorem minimumStructure_exclusion (P : NormalPeriod) (h : P.rep.ClassM3) : False := by
  obtain ⟨hmix, k, L, hrun, hL⟩ := h
  exact hL (reverseRun_two_and_centre_min P hmix hrun).1

end SmoothedOctagon

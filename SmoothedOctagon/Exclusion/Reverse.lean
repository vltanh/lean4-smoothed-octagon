module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.Reverse.Four

/-!
# Case R: no period is entirely reverse

A normal vertex period cannot have every switch reverse, for any number of pieces. The proof uses
exact identities between the explicit costate coordinates of the same lift at the reverse switches
(`Period/Costate.lean`, `Exclusion/Reverse/Four.lean`), read around the whole twisted period: the
periodic active margins have a minimum, and the four pieces around it violate the reverse-four
principle `CostateCycle.reverse_four_third`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case R.** No normal vertex period has every switch reverse. -/
theorem reverse_exclusion (P : NormalPeriod) (hR : P.rep.AllReverse) : False := by
  set C := P.costateCycle
  obtain ⟨m, hm⟩ := C.exists_act_min P.rep.N_pos
  have hrev : ∀ k, C.lab (k + 1) = C.lab k - 1 := hR
  refine C.reverse_four_third (m - 2) (hrev _) ?_ ?_ ⟨?_, ?_, ?_⟩
  · rw [show m - 2 + 2 = m - 2 + 1 + 1 by ring]; exact hrev _
  · rw [show m - 2 + 3 = m - 2 + 2 + 1 by ring]; exact hrev _
  · rw [show m - 2 + 2 = m by ring]; exact hm _
  · rw [show m - 2 + 2 = m by ring]; exact hm _
  · rw [show m - 2 + 2 = m by ring]; exact hm _

end SmoothedOctagon

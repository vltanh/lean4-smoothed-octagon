module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.Mixed.Extraction
public import SmoothedOctagon.Exclusion.Mixed.Nonshort
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort

/-!
# Case M2: no competitive mixed period with a nonshort forward run

Take the global minimum of the active margins; in class M2 it sits at the centre of a reverse run
(by the strict centre minimum of reverse runs and the small-forward-minimum theorem). Choose the
smaller adjacent turn. If the forward run on that side is short, the smaller-short window is
excluded directly; otherwise the next switch is forward or reverse, and both alternatives are
excluded by scalar inequalities on the window: a comparison with the boundary of the admissible
region, then separate exclusions of the reverse successor, of the forward successor at low scale
(`a ≤ 1/2`) and at higher scale, and of a small-parameter corner.

The proof (modules `Exclusion/Mixed/*`):

1. `m2_min_centre` (`Mixed/Location`): the global minimum `m` is a reverse centre.
2. `m2_reflect` (`Mixed/Reflection`): if the incoming turn is the smaller one, pass to the
   reflected, time-reversed period, in which it is outgoing (`m2_reflect_classM2`).
3. `m2_window`, `m2_short_window` (`Mixed/Extraction`): the scalar window of the chosen turn.
4. `m2_nonshort_scalar` (`Mixed/Nonshort`): the reverse successor by `m2_reverse_exclusion`, the
   forward successor by `m2_forward_exclusion`; `m2_smallerShort_exclusion` (`Mixed/SmallerShort`):
   the smaller-short window by the seven bounds of `Mixed/SmallerShort/`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The oriented case: a global minimum at a reverse centre whose outgoing turn is the smaller
one. -/
private theorem m2_oriented (P : NormalPeriod)
    (hc : P.IsCompetitive) (hK : P.InCompactDomain) (h : P.rep.ClassM2) (hN : 6 ≤ P.N) {m : ℤ}
    (hm : ∀ k, P.costateCycle.act m ≤ P.costateCycle.act k)
    (h2 : P.costateCycle.m2Fwd (m - 2)) (h1 : ¬ P.costateCycle.m2Fwd (m - 1))
    (h0 : ¬ P.costateCycle.m2Fwd m) (h3 : P.costateCycle.m2Fwd (m + 1))
    (hcb : P.costateCycle.act (m + 1) ≤ P.costateCycle.act (m - 1)) : False := by
  by_cases h4 : P.costateCycle.m2Fwd (m + 2)
  · obtain ⟨W, -, -, -, -, -, -, hF, hR⟩ := m2_window P hc hK h hN hm h2 h1 h0 h3 hcb h4
    by_cases h5 : P.costateCycle.m2Fwd (m + 3)
    · exact m2_nonshort_scalar W (Or.inl (hF h5))
    · exact m2_nonshort_scalar W (Or.inr (hR h5))
  · obtain ⟨D, -⟩ := m2_short_window P hc hK h hN hm h2 h1 h0 h3 hcb h4
    exact m2_smallerShort_exclusion D

/-- **Case M2.** No competitive normal vertex period with state in `𝔥**` and at least six pieces has
mixed signs, every reverse run of length two, and a forward run of length at least two. -/
theorem nonshort_exclusion (P : NormalPeriod)
    (hc : P.IsCompetitive) (hK : P.InCompactDomain) (h : P.rep.ClassM2) (hN : 6 ≤ P.N) :
    False := by
  obtain ⟨m, hm, h2, h1, h0, h3⟩ := m2_min_centre P hc h hN
  by_cases hcb : P.costateCycle.act (m + 1) ≤ P.costateCycle.act (m - 1)
  · exact m2_oriented P hc hK h hN hm h2 h1 h0 h3 hcb
  -- the incoming turn is the smaller one: reflect
  obtain ⟨P', hN', hcost, hK', ⟨c, hl⟩, hact⟩ := m2_reflect P
  have act' : ∀ k, P'.costateCycle.act k = P.costateCycle.act (-1 - k) := fun k => by
    rw [CostateCycle.act, P'.costateCycle_m_lab, CostateCycle.act, P.costateCycle_m_lab, hact]
  have fwd' : ∀ k, P'.costateCycle.m2Fwd k ↔ P.costateCycle.m2Fwd (-2 - k) :=
    fun k => m2_reflect_fwd_iff hl k
  have hc' : P'.IsCompetitive := by
    unfold NormalPeriod.IsCompetitive; rw [hcost]; exact hc
  refine m2_oriented P' hc' (hK' hK) (m2_reflect_classM2 hl h) (by rw [hN']; exact hN)
    (m := -1 - m) (fun k => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [act', act', show -1 - (-1 - m) = m by ring]; exact hm _
  · rw [fwd', show -2 - (-1 - m - 2) = m + 1 by ring]; exact h3
  · rw [fwd', show -2 - (-1 - m - 1) = m by ring]; exact h0
  · rw [fwd', show -2 - (-1 - m) = m - 1 by ring]; exact h1
  · rw [fwd', show -2 - (-1 - m + 1) = m - 2 by ring]; exact h2
  · rw [act', act', show -1 - (-1 - m + 1) = m - 1 by ring,
      show -1 - (-1 - m - 1) = m + 1 by ring]
    exact (lt_of_not_ge hcb).le

end SmoothedOctagon

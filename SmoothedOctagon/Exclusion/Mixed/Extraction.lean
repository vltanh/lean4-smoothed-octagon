module

public import SmoothedOctagon.Exclusion.Mixed.Location
public import SmoothedOctagon.Exclusion.Mixed.Reflection

/-!
# Case M2: the scalar windows of an actual period

`MIXED_SMALLER_TURN_CONTINUATION` (CONT) §§1-3, `MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §3 and
`MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION` §1 (inventory E1 R10-R26). Let `m` be a global minimum
of the active margins at a reverse centre (`m2_min_centre`), oriented (`m2_reflect`) so that the
smaller adjacent turn `c = a_{m+1} ≤ b = a_{m-1}` is outgoing. The switch `m + 2` after the turn is

* forward (nonshort side): the pieces `m - 2, …, m + 3` carry the `M2Window`
  `0(p), 1(b), 0(a), 2(c), 0(d), 1(r)` (CONT (1)), and the switch `m + 3` gives
  `M2Window.ForwardNext` or `M2Window.ReverseNext` (CONT (15)-(18));
* reverse (short side): the pieces `m - 2, …, m + 4` carry the `M2Short` window.

Ingredients, all on the costate cycle of the period and its covector calculus
(`NormalPeriod.M2Calculus`):

* the factor formulas CE (2) from the margin transports of `Term.Cycle` (`m_act`, `m_grow`,
  `m_decr`, `m_quad`): `q = s_- s_+/K` (`++`), `K/(s_- s_+)` (`--`), `s_+/s_-` (`-+`),
  `s_- / s_+` (`+-`), and strict star `a_i a_{i+1} < 4` at every switch;
* the compact domain at the switching times (`Reduction.two_div_fifteen_le_margin` for every
  margin, the pair sums `> 1/2` and margins `< 8` of `MIXED_NONSHORT_BLOWUP_REDUCTION` §1 from
  `y ≤ 9/2`);
* the strict centre minima (`reverseRun_two_and_centre_min`) and three-arc log-concavity
  (`CostateCycle.three_arc`);
* the transports of the calculus (`M2Calculus.transport`): the centre frame
  `M m = [[h, -K²v/(8S²)], [S²u/8, -h]]` (CONT (8)), `M (m + 2) = U_d` with `h_d = h + vY/8` and
  `w = (uK² + 16hY + vY²)/Q²` (CONT (10)), and the next norm `t` (CONT (14), (16)), independent
  of the next margin; in the short window the Gram transport `w = λ²v + d²u - dλE`,
  `E_L = 2du - λE` to the outer centre (E1 R24);
* stationarity at the centre and at `d` (CONT (9), (11)), the turn secants, the switching
  inequalities and the missing-control floors (CONT (6)-(7), (12));
* the Casimir bounds (`M2Calculus.cas_lt`, `cas_gt`) and the scale bound (`m2_centre`,
  `m2_scale`);
* for the short window, the middle missing-control slack and the two-turn window-defect inequality
  (`MIXED_GENERAL_SHORT_DEFECT_INTERFACE` (M), (A), (8)-(9)).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The smaller-nonshort window** (CONT §§1-3). -/
theorem m2_window (P : NormalPeriod) (hc : P.IsCompetitive) (hK : P.InCompactDomain)
    (h : P.rep.ClassM2) (hN : 6 ≤ P.N) {m : ℤ}
    (hm : ∀ k, P.costateCycle.act m ≤ P.costateCycle.act k)
    (h2 : P.costateCycle.m2Fwd (m - 2)) (h1 : ¬ P.costateCycle.m2Fwd (m - 1))
    (h0 : ¬ P.costateCycle.m2Fwd m) (h3 : P.costateCycle.m2Fwd (m + 1))
    (hcb : P.costateCycle.act (m + 1) ≤ P.costateCycle.act (m - 1))
    (h4 : P.costateCycle.m2Fwd (m + 2)) :
    ∃ W : M2Window, W.p = P.costateCycle.act (m - 2) ∧ W.b = P.costateCycle.act (m - 1) ∧
      W.a = P.costateCycle.act m ∧ W.c = P.costateCycle.act (m + 1) ∧
      W.d = P.costateCycle.act (m + 2) ∧ W.r = P.costateCycle.act (m + 3) ∧
      (P.costateCycle.m2Fwd (m + 3) → W.ForwardNext) ∧
      (¬ P.costateCycle.m2Fwd (m + 3) → W.ReverseNext) := by
  sorry

/-- **The smaller-short window** (`MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION` §1, E1 R10-R26). -/
theorem m2_short_window (P : NormalPeriod) (hc : P.IsCompetitive) (hK : P.InCompactDomain)
    (h : P.rep.ClassM2) (hN : 6 ≤ P.N) {m : ℤ}
    (hm : ∀ k, P.costateCycle.act m ≤ P.costateCycle.act k)
    (h2 : P.costateCycle.m2Fwd (m - 2)) (h1 : ¬ P.costateCycle.m2Fwd (m - 1))
    (h0 : ¬ P.costateCycle.m2Fwd m) (h3 : P.costateCycle.m2Fwd (m + 1))
    (hcb : P.costateCycle.act (m + 1) ≤ P.costateCycle.act (m - 1))
    (h4 : ¬ P.costateCycle.m2Fwd (m + 2)) :
    ∃ D : M2Short, D.pb = P.costateCycle.act (m - 2) ∧ D.b = P.costateCycle.act (m - 1) ∧
      D.a = P.costateCycle.act m ∧ D.C = P.costateCycle.act (m + 1) ∧
      D.B = P.costateCycle.act (m + 2) ∧ D.A = P.costateCycle.act (m + 3) ∧
      D.Pf = P.costateCycle.act (m + 4) := by
  sorry

end SmoothedOctagon

module

public import SmoothedOctagon.Exclusion.Mixed.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallMin.Window

/-!
# Case M2: no small forward minimum

Five consecutive active margins `p, b, a, c, d` of a normal vertex period with the four switches
between them forward, the three interior pieces distinct, and `0 < a ≤ min(p, b, c, d)`,
`a² ≤ 4/3` are incompatible with the normal PMP conditions: the three stationarity identities at
`b, a, c` (in the frames of the covector calculus) and the exterior missing-control floors
(`M2Calculus.floor_out` at `b`, `floor_in` at `c`), after a reduction to the smaller neighbour,
lead to a contradiction through an integral bound and a cubic sign argument. No Casimir bound is
used.

The floor `F_x` is defined for `1/2 ≤ x < 1`; it is used here only at `x = b/(a + b)`,
`c/(a + c) ≥ 1/2`.
-/

@[expose] public section

namespace SmoothedOctagon

set_option linter.unusedVariables false in
/-- **No small forward minimum**. The proof applies the case-F scalar core (`fs_U_lt_three`,
restated without cost and cap as `sf_Dim.U_lt_three`) on the window of the costate cycle itself
(`CostateCycle.sf_act_sq_gt`), with the case-F wiring of the rows and floors localized to the four
forward switches; the calculus `K` and `3 ≤ N` are not needed. -/
theorem m2_small_forward_minimum (P : NormalPeriod) (K : P.M2Calculus) (hN : 3 ≤ P.N) {m : ℤ}
    (hf2 : P.costateCycle.m2Fwd (m - 2)) (hf1 : P.costateCycle.m2Fwd (m - 1))
    (hf0 : P.costateCycle.m2Fwd m) (hf3 : P.costateCycle.m2Fwd (m + 1))
    (hmin : ∀ j, m - 2 ≤ j → j ≤ m + 2 → P.costateCycle.act m ≤ P.costateCycle.act j)
    (hsq : P.costateCycle.act m ^ 2 ≤ 4 / 3) : False := by
  have := P.costateCycle.sf_act_sq_gt hf2 hf1 hf0 hf3 hmin
  linarith

end SmoothedOctagon

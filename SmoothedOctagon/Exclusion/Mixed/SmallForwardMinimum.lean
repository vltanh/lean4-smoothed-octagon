module

public import SmoothedOctagon.Exclusion.Mixed.Interface

/-!
# Case M2: no small forward minimum

`MIXED_GLOBAL_SMALL_FORWARD_MINIMUM` (SFM) Theorem, with its hard face replaced by the integral and
cubic argument of `SMALL_FORWARD_MINIMUM_HAND_PROOF` (accepted in
`SMALL_FORWARD_MINIMUM_HAND_AUDIT`). Five consecutive active margins `p, b, a, c, d` of a normal
vertex period with the four switches between them forward, the three interior pieces distinct, and
`0 < a ≤ min(p, b, c, d)`, `a² ≤ 4/3` (SFM (1)) are incompatible with the normal PMP conditions:
the three stationarity identities SFM (6)-(8) at `b, a, c` (CE (14) in the frames of the covector
calculus) and the exterior missing-control floors SFM (11)-(12) (`M2Calculus.floor_out` at `b`,
`floor_in` at `c`), after the smaller-neighbour reduction SFM §3 and the face signs of the hand
proof. No Casimir bound is used.

Domain remark (inventory E2, D2): SFM (10) defines `F_x` for `1/2 ≤ x < 1`; the floors are used
here only at `x = b/(a + b)`, `c/(a + c) ≥ 1/2`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **No small forward minimum** (SFM Theorem, `SMALL_FORWARD_MINIMUM_HAND_PROOF`). -/
theorem m2_small_forward_minimum (P : NormalPeriod) (K : P.M2Calculus) (hN : 3 ≤ P.N) {m : ℤ}
    (hf2 : P.costateCycle.m2Fwd (m - 2)) (hf1 : P.costateCycle.m2Fwd (m - 1))
    (hf0 : P.costateCycle.m2Fwd m) (hf3 : P.costateCycle.m2Fwd (m + 1))
    (hmin : ∀ j, m - 2 ≤ j → j ≤ m + 2 → P.costateCycle.act m ≤ P.costateCycle.act j)
    (hsq : P.costateCycle.act m ^ 2 ≤ 4 / 3) : False := by
  sorry

end SmoothedOctagon

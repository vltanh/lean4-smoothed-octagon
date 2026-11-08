module

public import SmoothedOctagon.Exclusion.Mixed.Window

/-!
# Case M2: the scalar boundary comparison `b → b*`

`MIXED_SMALLER_TURN_CONTINUATION` (19)-(20), (25)-(27) (CONT), `MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION`
(2)-(3), `MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION` (1), in the ODE-free form of inventory E2,
entry 21a. Hold `a, c, d, r` and the actual incoming secant `v` fixed and move the central margin
`b` up to `b* = K/T - a` (central factor one). The root function `R_d(u; b)` (`m2RootAt`, with
central stationarity imposed) is affine in `u` with slope `R_u(b) < 0` on `[a, b*]` (CONT (19)-(20)),
so it has the unique root `u(b)` (`m2uRoot`). Along the incident ceiling,
`G(b) = R_d(U(a/(a+b)); b)` has `G'(b) = R_u(b) a (b - a)/(a + b)³ < 0`, and on the root curve
`dw/db = d K³ G(b)/(a Q³ R_u(b)²)`. Since `G(b_act) = R_u (U - u_act) ≤ 0`, `G(b*) < 0`, the
boundary root lies strictly below the ceiling, `u* < U(aT/K)`, and `w* < w_act`.

## Main API

* `m2RootAt`, `m2uRoot`, `m2bStar`; `M2Window.bStar`, `uStar`, `hStar`, `wStar`, `tStar` (the
  boundary values of CONT (25)).
* `m2_comparison`: `G(b*) < 0`, `R_d(u*; b*) = 0`, `u* < U(aT/K)` and `w* < w`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The root function `R_d(u; b)` with central stationarity `h = m2h a b c u v` imposed. -/
noncomputable def m2RootAt (a b c d r v u : ℝ) : ℝ := m2Root a c d r u v (m2h a b c u v)

/-- The root of the affine map `u ↦ m2RootAt a b c d r v u`. -/
noncomputable def m2uRoot (a b c d r v : ℝ) : ℝ :=
  -m2RootAt a b c d r v 0 / (m2RootAt a b c d r v 1 - m2RootAt a b c d r v 0)

/-- The boundary value `b* = K/T - a` of the central margin (CONT (25)). -/
noncomputable def m2bStar (a c : ℝ) : ℝ := (a ^ 2 + 4) / (a + c) - a

namespace M2Window

variable (W : M2Window)

/-- `b* = K/T - a`. -/
noncomputable def bStar : ℝ := m2bStar W.a W.c

/-- The boundary root `u* = u(b*)`. -/
noncomputable def uStar : ℝ := m2uRoot W.a W.bStar W.c W.d W.r W.v

/-- The boundary diagonal `h* = h(u*, b*)`. -/
noncomputable def hStar : ℝ := m2h W.a W.bStar W.c W.uStar W.v

/-- The boundary transported norm `w* = w(b*)`. -/
noncomputable def wStar : ℝ := m2wOf W.a W.c W.d W.uStar W.v W.hStar

/-- The boundary next norm `t* = 𝒯(w*)`. -/
noncomputable def tStar : ℝ := m2Next W.a W.c W.d W.r W.uStar W.v W.hStar

/-- The incident ceiling at the boundary, `U* = U(a/S*) = U(aT/K)`. -/
noncomputable def ceilStar : ℝ := m2U (W.a * (W.a + W.c) / (W.a ^ 2 + 4))

end M2Window

/-- **The boundary comparison** (CONT (25)-(27); inventory E2, entries 7, 21, 21a). For the
actual smaller-nonshort window: `G(b*) = R_d(U*; b*) < 0`, the boundary root solves
`R_d(u*; b*) = 0`, lies strictly below the incident ceiling, `u* < U*`, and the boundary
transported norm is strictly below the actual one, `w* < w`. -/
theorem m2_comparison (W : M2Window) :
    m2RootAt W.a W.bStar W.c W.d W.r W.v W.ceilStar < 0 ∧
      m2RootAt W.a W.bStar W.c W.d W.r W.v W.uStar = 0 ∧ W.uStar < W.ceilStar ∧ W.wStar < W.w := by
  sorry

end SmoothedOctagon

# Internal audit of the finite mixed-minimum continuation interfaces

Date: 2026-11-07. Independent mathematical review and exact identity
replays. No Lean, Lake, typechecking or CI.

**Scope:** this audit accepts the necessary-condition reductions in
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md),
[MIXED_GENERAL_SHORT_DEFECT_INTERFACE](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md),
and [MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md).
This interface review by itself does not certify a scalar exclusion or close M2.
The imported global geometric/PMP results retain their own named inputs
and earlier reviews.

**Completion follow-up:** the smaller-short scalar exclusion passed its
full directed cover and [separate completion audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md).
Both smaller-nonshort successor alternatives are now excluded by the
[reverse boundary](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) and
[forward endpoint](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md) theorems,
with their separate source/domain and fresh-replay audits. The
[uniform M2 assembly](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md) and its
[independent audit](MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md) record the
exhaustive actual-period consequence. The interface identities reviewed
here are unchanged.

## 1. Actual-period partition and the common covector

A global smallest active margin in the remaining mixed domain is a
reverse centre. Choose the smaller of its two adjacent turn margins.
The forward run adjacent to that turn is either short or nonshort.
Reflection together with reversal of time is the established actual
symmetry of the original positive-control problem. It preserves the
physical normalization, the complete twisted endpoints and the positive
cost. Thus the two oriented descriptions in the reviewed notes cover
this choice without selecting a new local multiplier.

The current reduction does not assume that both sides of a minimum are
nonshort. It does not classify an arbitrary local window as a closed
period. Whole-period inputs enter explicitly through the global minimum,
the conserved Casimir bounds, the cost/angle budget, and continuation of
the same covector across the seam.

## 2. The nonshort side and its next actual switch

The central/turn and next-forward transport matrices in the continuation
note were checked against the actual prefix-frame conventions. The
supplementary checker independently replayed successfully, including
both determinant preservations, the coefficient of the central norm in
the first-root equation, the exact numerator comparison, and the outgoing
root derivative.

The two alternatives follow from actual switches, not an arbitrary
stationary root. If the next switch is forward, its transported norm is
at least `3/4`. If it is reverse, the turn norm is the secant average over
`[A,d]`, where the next reverse centre has `A>=a`. Positive duration gives
`A<d`, and strict turn log-concavity gives `r^2>Ad`, hence `A<r`.
The integrand `1-rx/(r+x)^2` decreases for `x<r`; the outgoing reverse
switch bounds its value at A below by the actual average. Extending the
average to `[a,d]` therefore raises it. This gives the second necessary
alternative, including equality at `A=a`.

The sign of the first-root coefficient uses all three positive factors
`K,a,Q` and the identity

`d S Q - Z(aK+SY) < (Q/W){a(ST-K)+Sc(a-d)} < 0`.

The inequality directions are correct because `q>1`, `Y>0`, `ST<K`, and
`d>a`. The monotonicity along the root curve is conditional on the stated
incident norm and derivative bounds. It does not justify continuing
through an unexamined boundary or ignoring a competing first event.

Both alternatives are excluded by the completed boundary theorems linked
above. This exact reduction applies to the next actual switch regardless
of the eventual length of the forward run, so the resulting proof uses
no word-length catalogue.

## 3. The short bridge: cost, frame, angle and slack

The two turn secants use the same actual switch norm. Substituting each
one into its own arc cost removes the corresponding logarithm. The
resulting rational cost formula was independently checked both by its
exact symbolic replay and by direct substitution into the established
vertex-flow formula. The two secants are essential to its physical
interpretation; the formula on an enlarged domain is only a scalar
expression whose actual-locus values equal the physical cost.

The determinant-one transfer is the actual product of the two vertex
propagators. The matrices P and Q have the common determinant `-2U`,
which verifies the stated relative physical frame after conjugation by
`diag(1/sqrt(3),1)`. The scalar angle expressions were checked through
the original trace formula, including the reflection of the costate,
the factor `T_kappa=2 kappa(1-rho)^2`, and `kappa^2=12 gamma^2`.

The complete period has positive polar angle exactly `pi/3`. Its actual
short-bridge subwindow therefore supplies the angle-sign filters used
in the reduction. The positive modulus of the two endpoint polar
coordinates also supplies the stated strengthened trace filters. The
reflection/time-reversal calculation in the interface note explains why
this is the angle of the original incoming window.

The stationary-control slack `3m_b-tr(Lambda_1 X)` is nonnegative along
the actual lift. The endpoint and midpoint polynomial filters are its
values after the exact transports, with explicitly positive clearing
factors. They are necessary global-PMP conditions. Their proof does
not infer a sign from a numerical continuation.

## 4. Eliminating the opposite turn and bounding the domain

The second exact turn equality may be relaxed to the displayed
one-sided inequality because every actual point still satisfies it.
No equality-dependent identity is asserted to be a physical identity
at every point of that enlarged domain.

For the eliminated opposite-turn parameter t, the derivative of its
central pairing is `(1-t+t^2-v)/t^2`. It stays nonnegative from
`t0=rho/r` to the actual t because `U(t)` decreases on `[0,1/2]`.
This proves the rational lower pairing bound.

For the stronger rational upper bound, use `log z<=z-1` and set
`K0=1-v-t0`. The bound `v<=1-t0+t0^2` gives `K0>=-t0^2`. The resulting
upper expression has derivative `1+K0/t^2>=0` for every `t>=t0`,
including points beyond the actual upper norm endpoint. Raising t to r
therefore gives the displayed stronger rational bound. The earlier
upper bound obtained by only dropping the logarithm is weaker and must
not be treated as a proved empty comparison domain.

The polynomial form of the lower pairing bound agrees exactly with the
initial stationary slack. The compact bounds `rho>=1/226`, `x<9`,
`alpha^2<675/17`, `beta<45/2`, and `|E|<23/16` follow from the named
geometric compact set, both complete-period Casimir bounds, actual
secant bounds, and the displayed elementary inequalities. Their
rational constants were independently replayed.

The root convex-chord upper bound applies on `T>=2` and
`3/4<=w<=1-1/T+1/T^2`. Its derivation does not require the central arc to
have zero duration. It therefore gives the stated necessary polynomial
and rational conditions on the entire six-variable comparison domain.

All secants have their continuous divided-difference values at a
coincident pair of endpoints. Every Taylor certificate must evaluate
the analytic functions and all derivatives on the whole enclosing
rectangle; actual-domain inequalities cannot be used to truncate an
intermediate function range unless they hold on that whole rectangle.

## 5. Verification status

Both companion symbolic checkers were independently replayed
successfully. The inspected identities and the hand implications above
are accepted as necessary-condition reductions. Numerical examples and
optimization runs in the interface note are explicitly discovery and
regression material; they are not premises of the quantified exclusions.

The completed consequences of this interface are:

- The smaller short-side domain is excluded by its separately audited
  completed cover and [theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).
- The nonshort reverse-next domain is excluded by the
  [boundary comparison and two-root cover](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md).
- The nonshort forward-next domain is excluded by the
  [concave endpoint comparison and both complete endpoint covers](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md),
  using the branch-independent [low-a theorem](MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md).

Their exhaustive whole-period passage, including all corner, seam and
boundary limits, is accepted in
[MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md)
and [its audit](MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md). The cost and affine
equality consequence is assembled separately in
[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md).

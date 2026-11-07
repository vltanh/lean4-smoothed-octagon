# Independent review of the forward and short-side hand reductions

Date: 2026-11-07 UTC. Internal mathematical review. No interval cover
or executable sign result is a premise of the accepted implications.

## 1. Forward exterior-factor concavity

[HAND_FORWARD_LEMMAS, Section 1](HAND_FORWARD_LEMMAS.md#1-exterior-factor-concavity-on-the-whole-linear-budget-domain)
is accepted. The ordered linear budget gives `z<=5/3`, `U>z` and
`H>=1` on the whole stated domain. The derivative of the cubic `P`
is positive for `h>=1`. Its factored value at `H` has the claimed sign:
`Q` decreases with `U`, and the four positive powers of `x=z-1`
are bounded by the displayed multiple of `x^2` when `x<=2/3`.
The only lower-endpoint curvature equality is the circular endpoint.

The tangent comparison is therefore valid. The larger-neighbor
monotonicity uses the original actual residual and retains the
nonnegative opposite-floor derivative; its mixed derivative has the
same sign because both relevant coefficient derivatives are positive.
The two planar domains follow from lowering the larger neighbor to
`max(z,4/3)` and preserving the linear budget.

The final negative tangent signs on those domains are not supplied by
this lemma and are not accepted as established.

## 2. Conditional forward Casimir implication

[HAND_FORWARD_LEMMAS, Section 2](HAND_FORWARD_LEMMAS.md#2-a-small-norm-sum-bound-would-replace-the-full-casimir-cover)
is accepted with all of its stated hypotheses. At fixed total norm
increment, the exact Casimir bracket is a concave quadratic in the
allocation. Its worse endpoint puts the increment at the larger
neighbor because `E0>0`. The cubic integral bounds have the correct
directions, and the second minimization over the total increment is
again justified by concavity.

At zero increment the stated fourth-power identity gives the lower
bound. At increment `1/40`, the functions `F,G` are positive and
increase with the lower comparison value of `A`; their derivatives
give the displayed positive scale derivative. The complete eleven-term
polynomial in the final one-variable comparison is checked by its two
explicit cases. Both denominator factors are positive throughout.

This is a hand proof of the implication from neighbor bound `4/3` and
norm-sum bound `1/40` to `gamma^2>23/125`. Neither of those two new
stationary-system bounds is assumed proved for actual periods. The
upstream small-forward-minimum sign argument is also still required.

The later Section 2.4 is accepted as well: its explicit bound on the
negative norm derivative, integrated over `1/39-1/40`, leaves the stated
positive margin above the sharper global cap. Thus `1/39` is a valid
weaker sufficient target. Section 3.1's product bound follows from
AM--GM and the displayed cubic completed-square estimate. It proves
the product bound only; the proposed homogeneous norm estimate is
still open.

## 3. Cost budget retaining both exterior factors

[HAND_FORWARD_LEMMAS, Section 3](HAND_FORWARD_LEMMAS.md#3-the-same-cost-argument-retains-both-exterior-factors)
is accepted. Integrating the positive mixed derivative of the edge
function over the stated rectangle gives the displayed four-corner
inequality. After keeping five consecutive margins, the seven cyclic
edges are distinct at `N=7`; larger periods add positive diagonal edges.
Applying the rectangle inequality to the two indicated edges yields
exactly `2*sum(g_U)-g_U(1)` with the correct cost normalization.

All four ratios lie in `[1,U]` by the actual strict-star products and
global minimality. At the proposed violation threshold their total
excess above one fits into a single coordinate of that interval.
Concavity therefore puts the minimum at the displayed concentrated
four-tuple. The previously proved one-variable cost contradiction
applies without a changed constant or a new polynomial sign premise.
The comparison uses a scalar cost bound and does not assert closure
of the lowered arrays.

## 4. Short-side outer-root envelope

[MIXED_SMALLER_SHORT_OUTER_ENVELOPE](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md)
is accepted as a scalar comparison of the actual short-side interface.
The definitions of the transported norm and pairing agree with the
six-variable reduction, for either sign of its bridge diagonal.

The positive factor `B_tau` is controlled at the correct endpoint of
`[0,T]`. Its numerator reduces to `beta(2x-alpha)-x>0`, using only
the stated order. Both derivative identities consequently have the
required strict signs. The root-parameter interval is fixed, so no
continuation of a changing root is invoked. Actual reverse
transversality gives a positive value of the residual immediately
before its descending root, which justifies the strict necessary
envelope condition.

The simplified endpoint residual, its concavity in the root parameter,
and the exact comparison Casimir identity have the displayed forms.
The same comparisons increase the Casimir. The note correctly transfers
only a lower bound directly and does not import the competitive upper
cap into the artificial endpoint.

The two quantitative loss identities follow by integrating the accepted
derivatives and expanding a single square. Their common derivative
ratio is positive. A bound on that ratio throughout both complete
comparison segments would give the stated corrected-cap principle;
this implication is valid, but a useful uniform bound is explicitly
left unproved. No physical two-turn cost monotonicity is claimed.

## 5. Scope and dependency pruning

These readings accept the displayed hand reductions, not the final F
or smaller-short exclusions. The separate
[nonshort gap review](MIXED_NONSHORT_UPPER_ENVELOPE_GAP_AUDIT.md)
accepts a complete replacement for the old small-parameter corner in
the actual refined nonshort route.

For the eventual M2 assembly, choose the smaller adjacent turn as soon
as the global minimum is known to be a reverse centre. Its run is short
or nonshort, exhaustively. A direct short-side exclusion handles the
first case and a nonshort exclusion handles the second. This partition
does not need the earlier theorem asserting that both adjacent runs
cannot be short. Its large polynomial tables are therefore optional
dependencies. Its elementary secant and root identities remain in use
where explicitly proved.

The indispensably large upstream static sign identity still awaiting a
new hand argument is the hard symmetric face in
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md#6-the-hard-symmetric-face-a-finite-exact-sign-certificate).
That fact also enters the mixed global-minimum classification; it is
not merely a pure-forward issue. The remaining runtime exclusions are
exactly the seven already listed in the computational baseline.

# Independent audit of normal-period sectors, switches, and forward pairings

Date: 2026-11-07 UTC. Independent internal mathematical review of
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md),
[NORMAL_SWITCH_RIGIDITY](NORMAL_SWITCH_RIGIDITY.md), and
[GLOBAL_STRUCTURE_FORWARD_ACUTE](GLOBAL_STRUCTURE_FORWARD_ACUTE.md).
No Lean, Lake, typechecking, or CI ran. This is not external peer review
or kernel validation.

## Findings and scopes

The three statements are valid under their stated hypotheses:

1. Every finite positive strict-star normal PMP period with the actual
   twisted endpoints has negative elliptic physical primary costate.
2. At any fixed strict-star normal zero-Hamiltonian phase there is at
   most one positive outgoing vertex PMP germ. Every actual switch of
   a finite normal closed period is transverse for its incident pair.
3. Every competitive entirely forward period has positive adjacent
   Jacobi Gram pairings; their corresponding angles are acute.

These conclusions retain arbitrary unequal factors. They do not close
F, M1 or M2, supply a uniform lower bound on a duration or switching
derivative, or exclude all triple ties. The whole-period statements use
the audited reverse minimum and run theorems. Germ uniqueness does not
assert existence at an arbitrary phase.

## 1. Mixed cyclic action and the actual multiplier

I checked the four factor formulas against the increasing/decreasing
margin update, including the orientation at both kinds of turn. The
periodic margin chain resolves state closure with its initial state
free. Collecting the two arc contributions adjacent to each switch
gives the nonlogarithmic coefficient
`epsilon_i(3 a_i a_(i+1)-4)`; the log-factor formula gives the remaining
terms of the cyclic action. Its derivatives give both the same-sign
formula and the opposite-sign secant formula. The displayed equation
(5) retains the required plus sign before `a^3/K`.

The actual tangent product is `F=M R^(sum epsilon)`, so the complete
endpoint makes `M=sigma I`. The state-closed variation cancels the two
initial-state terms in the frame identity; the actual cotangent twist
cancels the remaining state boundary terms. Thus the multiplier in
`J_(a_i)=tr(U V_i)` is the given primary costate divided by `sqrt(12)`.
It is not obtained from a rank assumption.

Differentiating the three affected log factors yields the four frame
columns. In one prefix frame the incoming switch vector is `-e_2/s_-`
or `-e_1/s_-`, and the outgoing one is `q e_1/s_+` or
`e_2/(q s_+)`. This independently verifies both signed Wronskians,
the antiparallel identity at turns, and the two Gram identities.
The seam columns are periodic because the monodromy is central.

## 2. Positive diagonal values and the switching signs

At a turn, the actual trace equation makes `8d_i` a secant slope of
`f(t)=t-1/t-log t`, with `d_i=d_(i-1)`. Its derivative has minimum
`3/4`, attained at only one point, and is strictly below one for
`t>1`. Positive duration makes the secant interval nondegenerate.
Integration therefore gives `3/32<d_i<1/8`.

I checked the reverse switching bracket as well as the forward one.
The reverse state bracket is `-f_0-f_2`, and the corresponding group
bracket is `[D_0,D_2]-D_0-D_2=2E_21`. The scalar cost term has the
opposite sign from the forward term. With the positive physical clock
and normalization factor `p_j/(2 sqrt(12))`, the resulting inequalities
are exactly `d_i>=j_i/2` forward and `d_i<=j_i/2` reverse. The
common physical gap derivative is nonnegative even if it vanishes.

Every reverse edge in a surviving two-switch run adjoins a turn, so
its diagonal Gram value exceeds `3/32`. Forward edges have the weak
lower bound directly. Thus every `d_i>=3/32`. This step uses both
the reverse-run theorem and exact stationarity.

## 3. Full monodromy contradicts every nonelliptic multiplier

Under `det U<=0`, the Gram identity forces `abs(e_i)>=3/32` at
same-sign indices. At `++`, the lower switching bounds and exact
action derivative give `e_i>-1/16`, hence `e_i>0`. At `--`, the
switching bounds are upper bounds. The strict centre minimum gives
`a_i(1/s_-+1/s_+)<1`, and its auxiliary `r<1`, yielding
`e_i<1/16`, hence `e_i<0`.

A rank-one or indefinite symmetric form positive on all these vectors
supplies a linear functional `h` nonzero at each vector, with adjacent
product having the sign of its Gram pairing. Choose an independent
functional `l` with positive determinant. The exact increment

\[
\frac{l(y_i)}{h(y_i)}-\frac{l(y_{i-1})}{h(y_{i-1})}
=\frac{\det(h,l)\det(y_{i-1},y_i)}{h(y_{i-1})h(y_i)}
\]

is positive at every same-sign index and zero at every turn. There
is at least one same-sign index: either all indices are forward or
there is a centre of a double reverse run. But central monodromy makes
the projective coordinate periodic, so its increments sum to zero.
This contradiction proves `det U>0`, and its positive quadratic values
select the positive triangular elliptic component. The fixed change
of orientation gives the negative physical elliptic component.

This is a full-closure argument. It assumes no projective ray coverage
from the mere cyclic order of control labels. All 32 supplementary
exact identities pass.

## 4. Unique germs and transverse closed-period switches

For any two tied candidate vertices, the same initial covector gives
the same conserved group component `m`, hence the same `mu` in
`p_w'=mu-x^2-b_i(x)p_w`. At an initial tie the first nonzero right
derivative is, in order, `mu-a^2`, then `-2a`, then `-2`. Each
candidate-dependent coefficient multiplies derivatives that have
already vanished. Thus the right sign is the same for both hypothetical
flows. Their necessary opposite signs cannot both hold. Rotation
treats every pair, including at a triple tie.

On the two sides of an actual forward switch, those derivatives
require a strictly positive first derivative. A zero derivative can
cross only with `a=mu=0`, where the negative cubic has the reverse
orientation. That local reverse possibility requires equal incident
active margins. Every reverse switch of a surviving finite closed
period adjoins a strictly smaller central margin, excluding equality.
Thus all actual incident-pair switches are transverse.

The local cubic examples remain valid: they were not complete periodic
lifts. The argument permits a phase where all three vertex tests fail,
and permits a transverse switch that is also a triple tie. It supplies
no uniform dwell time or common lower bound on a switching derivative.

## 5. Positive forward pairings below the competitive Casimir cap

Assuming `e<=0` places the two weighted diagonal variables in the
stated triangle. The determinant function there is concave: both
displayed Hessian eigenvalues are negative. Its minimum is therefore
one of its vertex values, and the two exact differences select the
vertex saturating both switching lower bounds. The argument includes
the degenerate one-point triangle.

The resulting scalar `E` is nonnegative. The factorization in equation
(8) has strictly positive right side: `d-rt>0`,
`1+r+t-d-rt>0`, and `L=log q>0`. Thus `det U>3/16`, which is
`kappa>3/2` in the physical normalization. This contradicts the assumed
cap. Hence every adjacent forward Gram pairing is positive. All nine
exact scalar identities pass.

The negative phase Laplacian has only its constant kernel. The radial
and margin variables and the full endpoint curvature remain in the
constrained cost Hessian; their index is not determined by this lemma.

## Validation boundary

The two checkers pass with Python 3.12.14 and SymPy 1.14.0. The actual
PMP interpretation, projective contradiction, triangle minimization,
and scope of transversality are the hand arguments reviewed above.
These are uniform structural results, not additional closures of the
remaining F/M1/M2 comparisons.

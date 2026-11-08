# Independent audit of the whole-forward ellipticity theorem

Date: 2026-11-07 UTC. Independent internal mathematical review of
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md).
This is neither external peer review nor Lean kernel validation. No
Lean, Lake, typechecking, or CI ran.

## Finding and scope

The theorem excludes every nonelliptic primary costate for a normal
entirely forward finite positive strict-star PMP period with the actual
twisted frame, state, and cotangent endpoints. The surviving physical
costate is negative elliptic. Unequal factors, triple ties, and zero
first switching derivatives remain in the domain. The argument does
not use endpoint rank, a period budget, or a numerical margin bound.

This is a uniform restriction on F, not its closure. A negative
constrained variation or a further complete-period cost inequality is
still required. The appendix makes that remaining index problem exact;
the indefinite Jacobi inverse has no asserted favorable sign.

## 1. Actual normal multiplier and the switching bound

The cyclic boundary identity uses the multiplier
`U=Ad_(X_0^{-1})(Lambda_1^tri(0))/sqrt(12)`. This is the primary
costate of the actual lift, not an endpoint multiplier obtained by
assuming rank. The two initial-state terms cancel when differentiating
`g_T=X_0 F X_T^{-1}` on the twisted state-closed family; the two state
cotangent terms cancel by the actual free-initial-state transversality.

I independently reconstructed the local clock calculation. In the
active state coordinates `(a,b)`, the two log-clock fields are
`f_0=(0,a+b)` and `f_1=(-(a+b),0)`. Their bracket contribution to the
derivative of the second Hamiltonian is `eta dot (f_0+f_1)`.
Substitution of the two zero active Hamiltonians leaves

\[
\operatorname{tr}\bigl(Kappa([D_0,D_1]+D_0+D_1)\bigr)
+\ell_0+\ell_1-(a+b)(\partial_a\ell_0+\partial_b\ell_1).
\]

The matrix in the trace is `2E12`; the remaining scalar expression is
`-(a^2+ab+b^2)/4`. This reproduces equation (16).

The cost normalization needs a positive factor `1/sqrt(12)`:
`widehat H_j=p_j H_j/(2 sqrt(12))` when `H_j` denotes the actual
physical Hamiltonian. The draft omitted that factor in its explanatory
clock sentence; it is now included. It does not alter the sign or any
threshold. The physical derivative of `H_1-H_0` is
`4 sqrt(12)/(ab)` times (16).

At the genuine switch, the physical gap is nonpositive on the incoming
arc and nonnegative on the outgoing arc. Its two one-sided first
derivatives agree: their difference is the self-bracket of the gap.
Therefore the common derivative is nonnegative even at a triple or
nontransverse tie. This proves exactly

\[
d_i\ge\frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}
 {8(a_i+a_{i+1})^2}\ge\frac3{32}.
\]

No strict crossing was inserted into this step.

## 2. Exact stationarity supplies the missing off-diagonal information

In the determinant-one prefix frame, the adjacent recurrence vectors
are `y_(i-1)=-e_2/s_(i-1)` and `y_i=s_(i-1)e_1/K_i`. Their
determinant is `1/K_i`, and direct trace pairing yields

\[
C_i=2(s_{i-1}d_{i-1}+s_i d_i-2a_i e_i),\qquad
d_{i-1}d_i-e_i^2=\det U/K_i^2.
\]

Combining the diagonal switching bounds with the full value of `C_i`
gives the stated estimate for `e_i`. Explicitly, with
`ell=1/(a_(i-1)+a_i)+1/(a_i+a_(i+1))`, its lower bound is

\[
-\frac1{16}\left(1-2a_i\ell+\frac{a_i^2}{K_i}-\log q_i\right).
\]

Strict star gives `a_i ell>2a_i^2/K_i`, while `log q_i>0`.
The parenthesis is strictly below one, so `e_i>-1/16`. This step
uses the exact stationarity equation, and is not a consequence of the
earlier sign-only cyclic-sector argument.

## 3. Full central monodromy contradicts a nonelliptic multiplier

The vector recurrence has two independent solutions because adjacent
vectors have nonzero determinant. The full frame endpoint makes both
solutions periodic or antiperiodic with the same sign. A trace endpoint
alone would not give this fact.

If `det U<=0`, the Gram identity and the diagonal bound imply
`abs(e_i)>=3/32`. The strict lower bound `e_i>-2/32` removes the
negative possibility. Thus every `e_i` is positive. For a rank-one
symmetric form, this propagates the sign of one linear functional on
all recurrence vectors. For an indefinite form, diagonalize it to
`u^2-v^2`: positive squared values and positive adjacent inner products
again propagate the sign of `u`. These are elementary real linear
algebra statements and include the parabolic case.

The propagated sign contradicts antiperiodicity immediately. In the
periodic case, it gives a positive kernel vector `h`. Expanding with
`Hh=0` gives the exact identity

\[
z^THz=-\sum_iK_i h_{i-1}h_i
 \left(z_i/h_i-z_{i-1}/h_{i-1}\right)^2.
\]

Every coefficient is positive. Consequently every other kernel vector
is proportional to `h`, contradicting the two independent vectors
from full monodromy. This proves `det U>0`. Its positive quadratic
values select the positive elliptic triangular component; the fixed
orientation-reversing coordinate change gives the negative physical
component claimed in the theorem.

## 4. Remaining Hessian and rank boundary

The appendix's stationarity identity is
`J_(a_i)=-tr(P H_(a_i))`. Its local Hessian has off-diagonal entries
`-beta_i`, where `beta_i=2d_i-J_(a_i a_(i+1))>=0`. The diagonal entries
follow from the same stationarity identity. Differentiation under
common scaling of all margins gives
`(Hess J a)_i-C_i=-8a_i/K_i^2`, producing the displayed weighted
square term and negative diagonal term.

On an actual closed curve of margins, differentiating `HY=0` in a
kernel-orthogonal gauge gives `Y'=-H^dagger H_vY`. A second
differentiation supplies the full curvature term
`-2 tr(P H_v H^dagger H_v)`. It cannot be omitted. The tangent
constraint is `Y^T H_vY=0`.

For the target `N>=7`, six consecutive positive forward arcs have the
rank-five fixed-initial-state endpoint map proved in LOCAL_FORWARD_RANK.
Its zero-terminal-state variations still give all three frame
directions. Extending these variations by zero proves rank three for
the full frame map on the state-closed margin family. Thus a genuinely
negative vector satisfying the tangent constraint would integrate to
a closed competitor. No such vector is claimed for every period yet.

## 5. Supplementary checks

`python explorations/global_structure_forward_ellipticity_certificate.py`
passes all ten exact local identities with Python 3.12.14 and SymPy
1.14.0. The checks independently cover the local matrix, cost,
stationarity, threshold, recurrence, and Wronskian formulas. The global
kernel contradiction and the actual PMP interpretation are the hand
arguments reviewed above; they are not replaced by sampled algebra.

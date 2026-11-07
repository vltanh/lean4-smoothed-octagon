# A uniform scale bound at every competitive reverse centre

Date: 2026-11-07 UTC. Hand proof, with supplementary exact identities.
No Lean, Lake, typechecking, or CI.

## Statement and scope

At every reverse-run centre of a competitive finite normal geometric
period, its constant active margin satisfies

\[
\boxed{\rho=\frac{a^2}{a^2+4}<\frac3{20},
\qquad a^2<\frac{12}{17}.}
\tag{1}
\]

This improves the earlier bound `a^2<4/3`. It applies to every reverse
centre, without an equal-margin assumption or a restriction on the
neighbouring forward-run lengths. In particular it applies to the
global active minimum of any remaining mixed minimizing period, whose
location at a reverse centre is proved in
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).

The argument uses the exact normal centre equation, the incident
switching inequalities, and the actual whole-period Casimir cap. It
does not exclude the remaining smaller-scale M2 domain or close F.
No endpoint rank, trajectory deformation, or positive lower duration
bound is assumed.

## 1. Retain the actual normal multiplier

Use the notation and physical normalization of
[MIXED_REVERSE_CENTRE_PHASE_BOUND, Section 1](MIXED_REVERSE_CENTRE_PHASE_BOUND.md#1-dimensionless-centre-equations).
If the two neighbouring active margins are `p,n`, put

\[
r=\frac a{a+p},\quad t=\frac a{a+n},\quad
\rho=\frac{a^2}{a^2+4},\quad
u=8\nu_-,\quad v=8\nu_+,\quad E=16e.
\]

The strict centre minimum, positive reverse factor, turn secants, and
reverse-switch inequalities give

\[
0<r,t<\frac12,\qquad 0<\rho<rt<\frac14,
\qquad \frac34<u\le U(r),\quad \frac34<v\le U(t),
\quad U(s)=1-s+s^2.
\tag{2}
\]

Weak upper bounds suffice. The exact same-lift stationarity and Gram
determinant identities are

\[
E=1+r+t-\rho+\log\frac\rho{rt}
       -\frac{1-u}{r}-\frac{1-v}{t},
\qquad
\gamma^2=\frac{4uv-E^2}{16(1-\rho)^2}.
\tag{3}
\]

Here `gamma=kappa/sqrt(12)` is the conserved normalized primary
Casimir. The complete-period bound in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD, Section 1](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md#1-a-slightly-sharper-rational-casimir-cap)
applies to all remaining negative elliptic lifts and gives

\[
\gamma^2<\frac{23}{125}.
\tag{4}
\]

Conservation by itself does not give (4); the whole-period cost budget
and actual twisted endpoint are essential inputs.

## 2. Lower both incident norms

For the following comparisons, write `Gamma` for the scalar expression
on the right of (3). The comparison points need not be trajectories or
preserve the value of the Casimir.

Throughout the rectangle `3/4<=u<=U(r)`, `3/4<=v<=U(t)`,

\[
E\le -1+2r+2t-\rho+\log\frac\rho{rt}
 <-1+2r+2t-rt<\frac32r.
\tag{5}
\]

The middle inequality follows because `-rho+log(rho/(rt))` is
strictly increasing for `rho<rt<1`; its value at `rho=rt` is `-rt`.
For the last inequality, subtract `3r/2`: the result is
`(2-r)(t-1/2)<0`. Interchanging r and t also gives `E<3t/2`.
Consequently

\[
\Gamma_u=\frac{4v-2E/r}{16(1-\rho)^2}>0,
\qquad
\Gamma_v=\frac{4u-2E/t}{16(1-\rho)^2}>0.
\tag{6}
\]

Thus lowering both norms to `u=v=3/4` lowers the scalar determinant
expression, strictly from actual data.

## 3. On large scales, raise both neighbour ratios

Suppose, for contradiction, that `rho>=3/20`. At the lower norm corner
let

\[
E_0=1+r+t-\rho+\log\frac\rho{rt}
                         -\frac1{4r}-\frac1{4t}.
\]

Its two ratio derivatives are nonnegative:

\[
(E_0)_r=\frac{(2r-1)^2}{4r^2},\qquad
(E_0)_t=\frac{(2t-1)^2}{4t^2}.
\tag{7}
\]

In particular, reducing one ratio until `rt=rho` does not increase
E0. On that boundary, with `2rho<=r<=1/2`, it becomes

\[
1-\rho+\left(1-\frac1{4\rho}\right)r
                         +\frac{\rho-1/4}{r}.
\]

This is concave in r, so its minimum is at an endpoint. Both endpoints
have the same value. Therefore

\[
E_0\ge 1+\rho-\frac1{8\rho}
\ge\frac{19}{60}>0
\qquad\left(\frac3{20}\le\rho<\frac14\right).
\tag{8}
\]

The second inequality uses the positive derivative
`1+1/(8rho^2)` of the first expression.

At the lower norm corner, `Gamma=(9/4-E0^2)/(16(1-rho)^2)`.
Equations (7)--(8) show that increasing either ratio up to `1/2`
decreases Gamma. This path preserves `rho<rt`; it is a scalar
inequality, not a variation of the actual path. Combining with (6),

\[
\boxed{\gamma^2>G(\rho):=
\frac{9/4-B(\rho)^2}{16(1-\rho)^2},
\qquad B(\rho)=1-\rho+\log(4\rho).}
\tag{9}
\]

## 4. The one-variable lower bound increases

On `3/20<=rho<1/4`, (8) gives `B(rho)>0`. The elementary inequality

\[
\log x<\frac{2(x-1)}{x+1}\qquad(0<x<1)
\tag{10}
\]

follows by differentiating their difference, whose derivative is
`-(x-1)^2/[x(x+1)^2]`, and using equality at x=1. Hence

\[
B(\rho)<\widehat B(\rho)
=\frac{-4\rho^2+11\rho-1}{4\rho+1}.
\]

Direct differentiation gives

\[
G'(\rho)=\frac{9/4-B^2-B(1-\rho)^2/\rho}
                         {8(1-\rho)^3}.
\tag{11}
\]

Its numerator decreases with B on the positive half-line. Substituting
the larger positive value `Bhat` gives the exact lower bound

\[
\frac94-\widehat B^2
 -\widehat B\frac{(1-\rho)^2}{\rho}
=\frac{(4\rho-1)^2(4\rho^2+\rho+4)}
                         {4\rho(4\rho+1)^2}>0.
\tag{12}
\]

Thus G is strictly increasing on this entire interval.

At `rho=3/20`, (10) gives `log(3/5)<-1/2`, so
`0<B(3/20)<7/20`. It follows that

\[
G(3/20)>
\frac{9/4-(7/20)^2}{16(17/20)^2}
=\frac{851}{4624}
=\frac{23}{125}+\frac{23}{578000}
>\frac{23}{125}.
\tag{13}
\]

Equations (9), (11)--(13) contradict (4). Therefore `rho<3/20`,
and the identity `a^2=4rho/(1-rho)` gives (1).

## Verification boundary

The supplementary checker
[`mixed_reverse_centre_scale_certificate.py`](../explorations/mixed_reverse_centre_scale_certificate.py)
verifies the exact derivatives, boundary reductions, rational-log
identities and rational separation displayed above. The actual-lift
interface, comparison directions, positivity and complete-period scope
are the hand proof. No sampling, new word-length comparison, or remaining
case closure is asserted.

# Compact normalized global-minimizer lifts and a uniform singular clearance

Date: 2026-11-07. Hand proof. The word "global" throughout this note refers
to a complete minimizing period, with its actual twisted endpoints.

## Result and limitation

Let A_* be the minimum cost in the Reinhardt control problem. The concrete
octagon gives A_* <= A_oct < pi. Normalize a Pontryagin multiplier at the
beginning of each minimizing period by requiring the Euclidean norm of its
cost multiplier and five actual cotangent coordinates to be one. Include
abnormal multipliers; do not divide by the cost multiplier.

The family of these normalized, complete minimizing lifts, with time scaled
to [0,1], is compact in the uniform topology on state and costate, together
with the ordinary topology on terminal time. The associated controls have
weak-star convergent subsequences. The whole family stays a positive distance
from the singular locus, uniformly over the period and over minimizers.

The singular-avoidance step uses Hales--Vajjha Theorem 16.3.1 as an
external input. [FINITE_BANG_BANG_SOURCE_AUDIT](FINITE_BANG_BANG_SOURCE_AUDIT.md)
records numerical unstable-curve and basin-containment dependencies in the
checked source that have not been independently certified here. Compactness
through Section 4 is independent of that finite-switch input; Sections 5--6
and the minimizing-family common-bound consequence retain it.

The clearance obtained here is **qualitative**: there exists epsilon_* > 0.
No numerical value for epsilon_*, no uniform dwell time, and no numerical
upper bound on the number of switches is claimed. The separate uniform local
theorem in [GLOBAL_CLOSED_VARIATION](GLOBAL_CLOSED_VARIATION.md), combined
with this compactness, proves the existence of one finite bound over all
global minimizers. That implication needs the separate theorem; pathwise
finiteness alone is not being promoted to a uniform switch count.

## 1. Published inputs and conventions

Use original half-plane coordinates z=x+iy and

\[
q=1/\sqrt3,\qquad
X=\Phi(z)=\frac1y\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix}.
\]

The strict-star domain is y>0, |x|<q, x^2+y^2>q^2. Put

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
R=\begin{pmatrix}1/2&-\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\quad
L(z)=\frac32\frac{x^2+y^2+1}{y}.
\]

The complete-period conditions are

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=R^{-1}X(0)R.
\tag{1}
\]

The initial state is free; T>0 is free. The frame equation is g'=gX.
The running cost L is independent of the control and satisfies L>=3.

We use these named results of Hales--Vajjha, *Packings of Smoothed Polygons*:

- Theorem 5.0.2: every normalized balanced disk with cost at most A_oct has
  its entire state trajectory in the explicit compact strict-star set K
  of Definition 5.0.1.
- The PMP and transversality conditions in Sections 6.2 and 6.6.
- Theorem 16.3.1: every global minimizer has a finite positive vertex-control
  representation after zero pieces are removed and equal neighbors merged.
- Lemma 8.3.4: a maximizing vertex-controlled extremal cannot meet the
  singular locus, including at an endpoint of a positive vertex arc.

The geometric/control correspondence identifies the minimum being considered
with actual worst disks. The existing P0 note records the normalization and
endpoint conventions. These are mathematical source inputs, not claims of
validated Lean code.

## 2. Explicit common bounds on states, frames, and terminal time

The compact set K removes the three open horoballs and three open boundary
neighborhoods specified in Definition 5.0.1. In particular, a point of K
satisfies

\[
y\le9/2,\quad
(x-q)^2+y^2\ge\frac8{27}y,\quad
(x+q)^2+y^2\ge\frac8{27}y.
\tag{2}
\]

The remaining boundary exclusions are essential for K to be a compact subset
of the **open** star domain; the three inequalities (2) alone are not being
substituted for the complete definition of K.

### A simple lower height bound

Suppose y<=1/5. Strict star gives
|x|>sqrt(q^2-y^2). Writing a=q-|x|, we obtain

\[
0<a<\frac{y^2}{q+\sqrt{q^2-y^2}}\le\frac{y^2}{q}.
\]

Use the nearer cusp in (2). It implies

\[
\frac8{27}\le\frac{a^2+y^2}{y}
<y+3y^3\le\frac{28}{125}<\frac8{27},
\]

a contradiction. Thus y>1/5 on K. Consequently

\[
|x/y|<5/\sqrt3,\qquad 1/y<5,\qquad
(x^2+y^2)/y<\frac{37}{6},
\]

and

\[
\|X\|_{op}\le\|X\|_F
<\sqrt{\frac{2869}{36}}<9.
\tag{3}
\]

For every minimizing period,

\[
T\le A_{oct}/3<\pi/3,
\qquad \|g(t)\|_{op}\le e^{9t}\le e^{3\pi}.
\tag{4}
\]

Gronwall gives the frame bound. Integrating g'=gX also gives
||g(T)-I|| <= e^(9T)-1. Since ||R-I||_op=1, the actual frame endpoint
implies the uniform positive lower bound

\[
\boxed{\quad \frac{\log2}{9}\le T\le\frac{A_{oct}}3.\quad}
\tag{5}
\]

All state velocities are uniformly bounded on K. This follows either from
their explicit rational formulas with denominators bounded away from zero,
or from smoothness of the three vertex fields on a neighborhood of K.
Thus normalized-time states and frames have uniform Lipschitz bounds.

## 3. An exactly equivalent control-affine formulation

For the original control matrices Z_i set gamma_i(X)=-tr(Z_i X)>0.
For a simplex control u define

\[
\theta_i=\frac{u_i\gamma_i}{\sum_j u_j\gamma_j},\qquad
u_i=\frac{\theta_i/\gamma_i}{\sum_j\theta_j/\gamma_j}.
\tag{6}
\]

These are inverse maps between the control simplices for each strict-star
state. They preserve measurability along every state trajectory. On K their
denominators have uniform positive lower bounds. The physical-time state
equations become the affine system

\[
g'=g\Phi(z),\qquad z'=\sum_{i=0}^2\theta_i f_i(z),
\qquad C=\int_0^T L(z)\,dt,
\tag{7}
\]

where f_i is the original physical vertex field. This is an exact reformulation
of the admissible trajectories and costs, not a control relaxation.

Apply the PMP to (7). In left-trivialized group cotangent coordinates write
P=(lambda,M,nu), where lambda>=0 is the nonnegative cost multiplier,
M is a traceless 2-by-2 matrix paired by trace, and nu is a covector in
the global half-plane chart. In the maximizing convention,

\[
H_i=\operatorname{tr}(M\Phi(z))+\nu f_i(z)-\lambda L(z).
\tag{8}
\]

The adjoint equations have the form

\[
P'=\sum_i\theta_i A_i(z)P,\qquad \lambda'=0,
\tag{9}
\]

for smooth matrix functions A_i on the strict-star domain. For example,
M'=[M,X] and

\[
\nu'=-D_z\operatorname{tr}(M\Phi(z))
      -\sum_i\theta_i\nu Df_i(z)+\lambda DL(z).
\]

The state-dependent control change (6) does not change the maximizing
adjoint along a maximizing trajectory. In differentiating the transformed
Hamiltonian, its extra control-derivative term vanishes: the derivative of
(6), with theta fixed, is tangent to the face supporting theta, while the
Hamiltonian is constant on that maximizing face. Equivalently, (7) may be
taken as the control problem from the outset and its cotangent covector
transported back. This also identifies the singular locus and the cited
vertex-arc lemma in the same actual cotangent coordinates.

For free time, max_i H_i=0 along the trajectory and theta is supported on
the maximizing vertices almost everywhere. If tau(z) is the half-plane
map determined by Phi(tau(z))=R^-1 Phi(z) R, the free initial state gives

\[
\nu(0)=D\tau(z(0))^t\nu(T).
\tag{10}
\]

The group covector obeys M(t)=g(t)^-1 M(0)g(t), so its twisted endpoint
follows from (1). The important independent boundary condition is (10).

## 4. Projective normalization and compactness of minimizing lifts

Choose a Euclidean norm in the finite coordinates P and normalize

\[
\|P(0)\|=1.
\tag{11}
\]

This is always possible by PMP nontriviality and positive scaling. It
includes lambda=0. No normality theorem is needed for this normalization.

Let B=max_(z in K,i) ||A_i(z)||, which is finite. The forward and backward
Gronwall inequalities give

\[
e^{-BT}\le\|P(t)\|\le e^{BT}.
\tag{12}
\]

Equation (9) also gives a uniform Lipschitz bound on normalized-time P.
The numerical value of B is not needed for compactness; finding a usable
explicit bound is a separate, finite estimate on the already explicit K.

Consider any sequence of globally minimizing periods and normalized lifts.
Use s=t/T in [0,1]. Bounds (3)--(5), (12), and Arzela--Ascoli give a
subsequence for which T converges and (g,z,P) converge uniformly. The
bounded simplex controls theta have a weak-star convergent subsequence
in L^infinity([0,1]); sequential extraction is valid because L^1([0,1])
is separable. Their limit remains simplex-valued almost everywhere.

In the normalized integral state and adjoint equations, all coefficients
depending on (g,z,P,T) converge uniformly. Weak-star convergence of theta
therefore passes every integral equation to the limit. The limiting state
remains in K, T remains positive by (5), and (1), (10), and (11) pass to the
limit by continuity. Recover an original admissible control with (6).

Since L depends only on the state, its integral converges. Every sequence
member has cost A_*, so the limit also has cost A_*. It is an actual global
minimizer, not just a trajectory satisfying necessary conditions.

To check the maximum principle in the limit, uniform convergence gives
H_i<=0 and max_i H_i=0. Moreover each nonnegative integral

\[
\int_0^1\theta_i(s)(-H_i(s))\,ds
\]

is zero before passage to the limit and remains zero afterward. Thus theta
is supported on the maximizing vertices almost everywhere. Nontriviality
persists by (11)--(12). The limit is a normalized minimizing lift of the
same type. This proves compactness of the family of state/costate curves
and terminal times; controls are understood in their weak-star topology.

## 5. Every such lift avoids the full singular locus

In these coordinates, the singular locus is

\[
z=i,\qquad \nu=0,\qquad M=-\frac32\lambda J.
\tag{13}
\]

The sign agrees with (8): at (13) the state-free Hamiltonian terms cancel.
It is the locus of Definition 8.2.4 after the positive sign convention
lambda=-lambda_cost and the cotangent-coordinate change.

Theorem 16.3.1 gives a finite positive vertex representation of the base
trajectory of **each** global minimizer. At any time, including a switch
or a period endpoint, there is a positive one-sided vertex interval having
that time in its closure. The same normalized lift solves that vertex's
analytic adjoint and state equations on the interval. Lemma 8.3.4 says that
such a maximizing arc cannot have a point of (13) in its closure. Its proof
uses the analytic expansion from the endpoint and works on either side.

Therefore no normalized lift of any global minimizer meets (13). This is
stronger than choosing one favorable lift and does not discard abnormal
limits. If lambda=0, (13) would make the whole covector zero, already
excluded by nontriviality.

## 6. Uniform qualitative clearance and the quantitative gap

The evaluation map from the compact family in Section 4 times [0,1] into
(z,P)-space is continuous. Its image is compact. It is disjoint from the
closed singular locus by Section 5. Equivalently, the continuous function

\[
D(z,P)=\left(|z-i|^2+\|\nu\|^2+
             \|M+\tfrac32\lambda J\|_F^2\right)^{1/2}
\]

is positive on that compact image. Hence

\[
\boxed{\quad\exists\epsilon_*>0\quad
D(z(t),P(t))\ge\epsilon_*
\quad\text{for every normalized global-minimizer lift and every }t.\quad}
\tag{14}
\]

The normalization is necessary: unrestricted scaling of a cotangent vector
would make any homogeneous covector distance arbitrarily small. Equation
(14) is not asserted for every local extremal or every competitive
Pontryagin trajectory; compactness was proved for actual global minimizers.

The regular-domain counting step is now effective:
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
specifies every coefficient in an O(1/epsilon) bound for a supplied
clearance, in an explicitly stated matrix-covector normalization. Its
Section 7 explains why the compactness argument also gives qualitative
clearance in precisely that normalization. The separate uniform theorem
is essential; the pathwise source theorems alone would not give it.

The remaining boundedness input is a certified numerical clearance,
or a substitute explicit global exclusion theorem with the same consequence.
Only after that input can one state a particular integer N_max and use a
fixed finite collection of closed words. No increasing-length case list is
licensed by the present qualitative theorem. A global index argument that
directly excludes all minimizing N>=6 would bypass the larger enumeration,
but it must be proved with the full period constraints.

## Sources and validation boundary

- Hales--Vajjha, [Chapter 5](https://arxiv.org/html/2405.04331v1#Ch5),
  Definition 5.0.1 and Theorem 5.0.2: the actual common compact state domain.
- [Sections 6.2 and 6.6](https://arxiv.org/html/2405.04331v1#Ch6.S6): PMP and
  the twisted costate endpoints.
- [Lemma 8.3.4](https://arxiv.org/html/2405.04331v1#Ch8.S3): vertex arcs
  cannot meet the singular locus.
- [Theorem 16.3.1](https://arxiv.org/html/2405.04331v1#Ch16.S3): finite
  bang-bang representation of every global minimizer.
- [MINIMIZER_WINDOW_AUDIT](MINIMIZER_WINDOW_AUDIT.md): normalization,
  cost and endpoint conventions, and the geometric/control bridge.

All new steps above are hand arguments. No numerical trajectory sampling,
unproved normality, bounded switch assumption, Lean compilation, Lake,
typechecking, or CI is a premise.

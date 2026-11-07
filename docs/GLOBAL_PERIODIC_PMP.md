# Global periodic lifts and rigidity of full-rank windows

Date: 2026-11-07. Hand argument; no Lean compilation, Lake, or CI.

## Result and scope

This note supplies the global bridge used by
[GLOBAL_PERIOD_BUDGET.md](GLOBAL_PERIOD_BUDGET.md): a window with a
surjective five-dimensional endpoint map forces the normal costate of
any complete minimizing trajectory containing it. A forced continuation
of that costate to the boundary of the star domain therefore excludes
the window from a closed minimizer, even when the window itself is a
global optimum for its fixed endpoints.

The free-time maximum principle, its reduced Hamiltonian, and the
spatial costate conserved by left invariance are standard ingredients
of the Reinhardt problem. They are not new exclusions of competitors.
Sections 1--3 check their precise use with a free initial state and the
coupled terminal state. Sections 4--5 prove the full-rank-window and
continuation implications needed here. Section 6 independently derives
the outgoing switching derivative used for the small padded reverse
family.

There is no assertion that first-order conditions or periodic
extendibility exclude every six-piece window. The forward examples in
[LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md) already satisfy
those conditions. A complete global plan must retain its total-period
budget and prove additional restrictions.

## 1. The actual manifold and endpoint problem

Use the original coordinates and physical cost:

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
R=\exp(\pi J/3),\qquad
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\]

\[
y>0,\quad |x|<q:=1/\sqrt3,\quad x^2+y^2>q^2.
\]

The state manifold is the five-dimensional product
\(M=\mathrm{SL}_2(\mathbb R)\times\mathfrak h^*\). Its dynamics and
cost are

\[
g'=gX,\qquad X'=[P_u(X),X],\qquad
P_u(X)=\frac{Z_u}{\operatorname{tr}(Z_uX)},\qquad
C=\int_0^T -\frac32\operatorname{tr}(JX)\,dt.
\tag{1}
\]

The control ranges over the compact simplex. At every strict-star state
all three vertex denominators are negative, so their convex combinations
are negative too. The right-hand side is smooth in the state and
continuous in state and control. On a compact trajectory its denominator
is bounded away from zero uniformly over the whole simplex. These facts
give the regularity needed for the ordinary manifold maximum principle.

The terminal time is free and positive. The initial state is free, with
the joint endpoint submanifold

\[
\mathcal B=
\{((I,X),(R,\tau X)):X\in\mathfrak h^*\},
\qquad \tau X=R^{-1}XR.
\tag{2}
\]

Applying the free-time maximum principle on this actual manifold gives
an absolutely continuous cotangent trajectory, a constant
\(\lambda\le0\), nontriviality of the cotangent class together with
\(\lambda\), Hamiltonian maximization over the entire simplex, and
zero maximized Hamiltonian almost everywhere. The version used is the
standard free-time endpoint-submanifold principle described in
Hales--Vajjha, [Sections 6.2 and 6.6](https://arxiv.org/html/2405.04331v1#Ch6.S2).
Its hypotheses have just been checked for (1)--(2).

This is a hand application of the published maximum principle. It does
not create a Lean declaration discharging the interface recorded in
[PONTRYAGIN_LIFT.md](PONTRYAGIN_LIFT.md).

### Reduction preserves the cotangent class

Identify the frame covector by the trace form with a traceless matrix
\(\Lambda_1\), using left trivialization. Represent the state covector
by a traceless matrix \(\Lambda_2\), modulo multiples of \(X\), and set

\[
\Lambda_R=[\Lambda_2,X].
\tag{3}
\]

The tangent space of the determinant-one orbit at \(X\) is
\(X^\perp\) for the trace form. Its annihilator in the traceless matrices
is \(\mathbb RX\). Since \(X^2=-I\), the centralizer of \(X\) in the
traceless matrices is exactly \(\mathbb RX\). Thus (3) vanishes exactly
when the state cotangent class vanishes. In particular the reduced pair
cannot acquire a spurious nonzero multiplier from an ambient normal.

Also \(\operatorname{tr}\Lambda_R=0\) and
\(\operatorname{tr}(\Lambda_RX)=0\). On \(X^\perp\) one has
\(\operatorname{ad}_X^2=-4I\); the perpendicular representative of the
state covector is \(\Lambda_2=\tfrac14[X,\Lambda_R]\). Hence reduction
is an invertible linear change of the two-dimensional cotangent space.

The resulting Hamiltonian is

\[
H=\operatorname{tr}\!\left((\Lambda_1-\tfrac32\lambda J)X\right)
  -\operatorname{tr}(\Lambda_RP_u(X)).
\tag{4}
\]

Indeed \(\operatorname{tr}(\Lambda_2[P,X])
=-\operatorname{tr}([\Lambda_2,X]P)\). Differentiating (3) in Hamilton's
equations gives

\[
\begin{aligned}
\Lambda_1'&=[\Lambda_1,X],\\
\Lambda_R'&=[P,\Lambda_R]
 -\operatorname{tr}(\Lambda_RP)[P,X]
 +[-\Lambda_1+\tfrac32\lambda J,X].
\end{aligned}
\tag{5}
\]

An ambient representative may add a multiple of \(X\) to
\(\Lambda_2'\); its commutator with \(X\) is zero, so (5) is
independent of that choice. On the compact trajectory the right-hand
sides in (5) are integrable. The resulting integral equations, reduced
constraints, and nontriviality are precisely the mathematical conditions
in the pinned extremal predicate.

## 2. Free-initial-state transversality and spatial conservation

The tangent vectors to (2) are
\((0,\eta;0,R^{-1}\eta R)\), where \(\eta\in T_X\mathfrak h^*\).
The endpoint transversality condition therefore gives

\[
\operatorname{tr}(\Lambda_2(0)\eta)
 =\operatorname{tr}(\Lambda_2(T)R^{-1}\eta R)
 \quad\hbox{for every such }\eta.
\]

Equivalently,
\(\Lambda_2(0)-R\Lambda_2(T)R^{-1}\in\mathbb RX(0)\).
Taking its commutator with \(X(0)\), and using the state endpoint, yields
the exact reduced closure

\[
\boxed{\Lambda_R(T)=R^{-1}\Lambda_R(0)R.}
\tag{6}
\]

This uses the variation of the initial state in the actual endpoint
graph. Independent fixed initial and terminal states would remove this
condition.

Left invariance gives a separate identity. Equations (1) and (5) imply

\[
\frac d{dt}\bigl(g\Lambda_1g^{-1}\bigr)
 =g\bigl([X,\Lambda_1]+\Lambda_1'\bigr)g^{-1}=0
\quad\hbox{almost everywhere}.
\]

The product is absolutely continuous, so

\[
\boxed{g(t)\Lambda_1(t)g(t)^{-1}=\Lambda_1(0).}
\tag{7}
\]

Consequently \(\det\Lambda_1\) is constant and

\[
\Lambda_1(T)=R^{-1}\Lambda_1(0)R.
\tag{8}
\]

There is no condition here requiring \(\Lambda_1(0)\) to commute with
\(R\). The conserved spatial matrix in (7) and the moving body matrix
\(\Lambda_1(t)\) are distinct objects. Identities (5)--(8) agree with
the published reduction in Hales--Vajjha, Sections 6.5--6.6.

## 3. The lifted trajectory extends across every seam

Let \(\sigma\) cyclically relabel a control by \(i\mapsto i+1\)
modulo three. Directly from the vertex matrices,

\[
Z_{\sigma u}=R^{-1}Z_uR,\qquad R^{-1}JR=J.
\]

For \(0\le t\le T\), extend one period by

\[
\begin{aligned}
g(t+T)&=g(t)R,& X(t+T)&=R^{-1}X(t)R,\\
\Lambda_1(t+T)&=R^{-1}\Lambda_1(t)R,&
\Lambda_R(t+T)&=R^{-1}\Lambda_R(t)R,\\
u(t+T)&=\sigma u(t).&&
\end{aligned}
\tag{9}
\]

The endpoint equations make all state and costate curves continuous at
the seam. They are absolutely continuous on each compact extended
interval. Substitution in (1), (4), and (5) proves all the equations and
the maximum condition on the next period. The cost and Hamiltonian are
unchanged by the conjugation. Iterating (9) gives a strict-star extremal
on every future time interval.

In particular, a seam cannot stop a forced continuation or replace its
costate with another one. After three periods the body state and
costates repeat, since \(R^3=-I\); the frame repeats after six periods.

## 4. A full-rank window determines the normal lift

**Lemma.** Fix the initial frame and state of a finite positive
vertex-control window. Let \(s\in\mathbb R_{>0}^n\) be its physical
arc durations, \(E(s)\in M\) its final frame and state, and \(C(s)\)
its physical cost. Suppose \(dE\) has rank five at the window. Every
free-time Pontryagin lift of this window is normal. After normalizing
\(\lambda=-1\), its cotangent trajectory is unique.

**Proof.** Let \(p_e\in T^*_{E(s)}M\) be the terminal cotangent class
of such a lift. Integrating the adjoint first-variation identity on
the smooth pieces, and using the zero active Hamiltonian for the changes
of their durations, gives

\[
(-\lambda)\,dC=p_e\circ dE.
\tag{10}
\]

All durations are positive, so each can be varied in both directions.
The variations keep the initial frame and state fixed; no endpoint
constraint is imposed when defining the map \(E\).

If \(\lambda=0\), surjectivity of \(dE\) forces \(p_e=0\). The
homogeneous adjoint equation with this terminal value has only the zero
solution. This follows, for example, from the integral equation and
Gronwall on the compact window. It contradicts cotangent nontriviality.
Thus \(\lambda<0\). After the normalization \(\lambda=-1\), (10)
determines \(p_e\) uniquely because \(dE\) is onto. Uniqueness for the
linear inhomogeneous adjoint equation then determines the entire
cotangent trajectory. \(\square\)

The same proof applies to any smooth independent arc parameters related
to positive durations by an invertible change of variables. It also
applies to a window crossing the chosen period seam, after (9).

For every positive strict-star window with word `021210`,
[LOCAL_MIXED_SIX_RANK.md](LOCAL_MIXED_SIX_RANK.md) now proves this
rank-five hypothesis on the full domain. The middle four edge arcs span
the three edge endpoint coordinates. The two outer control-0 duration
variations have independent projections to the two normal endpoint
coordinates. Together they span the whole endpoint tangent space. The
earlier Section 6.4 of
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md)
already supplies the rank needed for its padded windows \(P_{b,h}\).

That note's explicit minimizing cotangent vector \(p^{\min}\) uses the
scaled cost \(\mathcal A=(2/3)C\) and Hamiltonian
\(H^{\min}=\mathcal L+p^{\min}f\). Therefore the unique maximizing
physical-cost covector of any global occurrence is exactly

\[
p^{\max}=-\frac32p^{\min},\qquad \lambda=-1.
\tag{11}
\]

This conclusion uses its endpoint rank and explicit adjoint equations.
It is independent of the ASZ sufficient-optimality theorem and of the
subsequent all-control local replacement obstruction.

## 5. A finite escape rules out a closed extension

**Escape criterion.** Suppose a full-rank window has a given normal
lift. Suppose every maximizing forward continuation of that lift agrees
with a specified trajectory until a finite physical time at which its
state reaches the boundary of the strict-star domain. Then the window
cannot occur in any closed Reinhardt Pontryagin extremal.

**Proof.** A purported occurrence is normal and has the specified
covector by Section 4. Rebase the frame by its constant value at the
start of the window. Left invariance preserves the equations and this
cotangent identification. Section 3 extends the purported closed lift
past as many seams as needed to reach the finite escape time. The forced
continuation then reaches the star boundary, contradicting the strict
star condition of every extended period. \(\square\)

A useful uniqueness check at the first switch is valid even for
measurable simplex controls. The original rational-control Hamiltonian
is the convex combination of vertex Hamiltonians with weights
\(\theta_i=u_i\gamma_i/\sum_j u_j\gamma_j\), where
\(\gamma_i=-\operatorname{tr}(Z_iX)>0\). On the maximizing locus,
the extra term \(\sum_i H_i\,d\theta_i\) in its differential vanishes:
active vertex values are zero, and an inactive index has \(u_i=0\),
so \(\theta_i\) and its state differential are zero. The lifted field
there is consequently the corresponding convex combination of vertex
Hamiltonian fields.

Suppose exactly two minimizing vertex
Hamiltonians \(H_i,H_j\) tie and the third is strictly larger. Put
\(\Delta=H_j-H_i\). At the tie,

\[
D\Delta[\vec H_i]=D\Delta[\vec H_j],
\tag{12}
\]

because their difference is
\(D(H_j-H_i)[\vec H_j-\vec H_i]=\{\Delta,\Delta\}=0\).
A nonzero crossing derivative therefore has the same sign for every
convex combination of the two tied Hamiltonian fields. By continuity it
keeps this sign in a small neighborhood. The crossing forces the
outgoing unique vertex immediately, including among measurable mixed
controls. Thereafter strict vertex gaps and uniqueness of the smooth
active ODE force the same continuation for as long as those gaps remain
strict. Positive state-dependent changes of time preserve this argument
on the zero-Hamiltonian level.

The explicit escape test for \(P_{b,h}\) is in
[GLOBAL_PERIOD_BUDGET.md](GLOBAL_PERIOD_BUDGET.md). Its consequence is
an exclusion of that family from complete closed extremals. It is not
a uniform exclusion of every mixed six-piece word.

[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md) proves the separate
external-tie conditions when a selected window consists of six complete
positive pieces. The escape criterion applies to an occurrence with
arbitrary cuts inside the outer arcs as well. It excludes such an
occurrence through its forced future continuation, regardless of whether
its displayed outer endpoints are genuine switches.

## 6. The outgoing derivative for the small reverse family

Here is an independent calculation of the sign needed at the start of
that escape. The main escape note proves the same sign by exact
inequalities on the entire range \(0<b\le q/10000\); the limiting
calculation here is an independent check of the conventions and leading
coefficient. Retain \(q=1/\sqrt3\), the core parameter \(b>0\),
\(s=b/2\), and the notation of
`LOCAL_REVERSE_SIX_OBSTRUCTION.md`. The core ends at \(x=b\). Its last
control is 1, and the next control is 0. In the state-only clock
\(d\tau=y\,dt\), write \(w=y^{-2}\),
\(d=1-w(q^2-x^2)\), \(r=q-x\), and \(p_w=-\lambda(x)\).
The minimizing Hamiltonians at this endpoint can be written

\[
\begin{aligned}
H_1&=1+p_x+(x^2-\mu)w+\frac{2w}{r}p_w,\\
H_0&=1+p_x+(x^2-\mu)w
       -\frac2d\bigl(p_x+n+2xw^2p_w\bigr),\\
H_2-H_1&=-\frac{4qw}{q^2-x^2}p_w.
\end{aligned}
\tag{13}
\]

The exact family, after the substitution \(x=bt\) in its integrals,
has Taylor expansions at \(b=0\):

\[
w(b)=2+O(b^2),\qquad
\mu=\frac{b^2}{12}+O(b^3),\qquad
p_w(b)=-\frac{b^3}{4}+O(b^4),\qquad
L=2b+O(b^2).
\tag{14}
\]

The coefficients are analytic near zero: all rational denominators stay
nonzero after that substitution, and the intervals become fixed. Thus
the error terms in (14) give ordinary, rigorous one-sided asymptotic
estimates. For instance the leading moment ratio is
\(\int_0^{1/2}t^2dt/\int_0^{1/2}dt=1/12\), and the defining integral
for \(p_w(b)\) then gives \(-b^3(1/3-1/12)\).

For the old third-control switching function \(B=n-Q\), its terminal
derivative is

\[
B_S(L)=2b+O(b^2).
\tag{15}
\]

Indeed \(n_S=2(1+\mu)L=4b+O(b^2)\). On the last control-1 arc,
\(Q=1+(x^2-\mu)w+w(rw+1/r)p_w\), so
\(Q_x=4b+O(b^2)\) at the endpoint and \(Q_S=Q_x/w=2b+O(b^2)\).

At the tie \(H_0=H_1=0\), (12) gives

\[
\left.\frac d{d\tau}(H_1-H_0)\right|_{\mathrm{control}\ 0}
=\left.\frac d{d\tau}(H_1-H_0)\right|_{\mathrm{control}\ 1}
=\frac{2w}{d}B_S(L)=24b+O(b^2).
\tag{16}
\]

The other old gap has only an \(O(b^2)\) outgoing derivative. To check
this without differentiating a zero-level identity off its level,
differentiate the actual Hamiltonian \(H_0\) in (13). At the tie it gives

\[
\left.p_w'\right|_{\mathrm{control}\ 0}
=\mu-x^2+\frac{2w}{d}(3x-q)p_w=O(b^2).
\tag{17}
\]

The coefficient in the last line of (13) and its derivative are bounded
near the limiting state, so
\((H_2-H_1)'=O(b^2)\). Consequently

\[
\left.(H_2-H_0)'\right|_{\mathrm{control}\ 0}
=24b+O(b^2),\qquad H_2-H_0=O(b^3)>0.
\tag{18}
\]

Now conjugate by \(R^{-1}\). This sends the outgoing control 0 to
control 1, and the old controls 1 and 2 to controls 2 and 0 respectively.
At \(b=0\), the transformed state and the ratio of the two clocks are

\[
\widetilde x=a=\frac{3q}{5},\qquad
\widetilde y=\frac{4\sqrt2}{5},\qquad
\widetilde w=\frac{25}{32},\qquad
\widetilde d=\frac56,\qquad
\kappa:=\frac{y}{\widetilde y}=\frac58.
\tag{19}
\]

For a fixed physical cotangent vector the transformed tau-Hamiltonian
is \(\widetilde H=\kappa H\), while
\(d/d\widetilde\tau=\kappa\,d/d\tau\). Thus the transformed third
gap satisfies

\[
\widetilde G:=\widetilde H_0-\widetilde H_1
=\kappa(H_2-H_0),\qquad
\widetilde G'=\kappa^2(24b+O(b^2))+O(b^3).
\]

Along its outgoing control-1 arc,
\(\widetilde G=-2\widetilde B/\widetilde d\) and
\(d\widetilde S/d\widetilde\tau=\widetilde w\). Equations
(18)--(19) therefore give the exact leading sign

\[
\boxed{\widetilde B_S(0)
 =-\frac{5/6}{2(25/32)}\left(\frac58\right)^2 24b+O(b^2)
 =-5b+O(b^2)<0}
\tag{20}
\]

for every sufficiently small positive \(b\).

The other initial sign follows directly from the transverse switch.
At the transformed control-2/control-1 tie, \(\widetilde p_w=0\).
Its outgoing gap derivative is positive by (16), while

\[
(\widetilde H_2-\widetilde H_1)'
=-\frac{4q\widetilde w}{q^2-a_b^2}
       (\widetilde\mu-a_b^2).
\]

Here \(a_b\) is the actual transformed initial horizontal coordinate.
Hence \(\widetilde\mu<a_b^2\) for the positive members under
consideration. At the limiting member equality holds. For example its
physical state covector is zero and its group covector is \(J\); in
the gauge \(A=gK(a)\), \(K(a)=\begin{pmatrix}1&a\\0&1\end{pmatrix}\),
the group covector is

\[
K(a)^{-1}JK(a)=
\begin{pmatrix}-a&-(1+a^2)\\1&a\end{pmatrix},
\]

which gives \(\widetilde\mu=-1-\widetilde m=a^2\). This also checks
the rotation and costate conventions independently.

## Audit boundary

The work above proves the hand PMP interface and a general implication
from full endpoint rank to a forced global lift. Together with an actual
escape calculation it excludes the specified local family from closed
extremals. It supplies neither a uniform switch bound nor a density
comparison for all closed trajectories, and it leaves Lean kernel
validation deferred.

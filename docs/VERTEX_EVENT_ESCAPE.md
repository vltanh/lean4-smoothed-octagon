# Finite vertex events and a stronger M1 escape certificate

Hand proof, 2026-11-07 UTC. Self-reviewed; independent mathematical review
and kernel validation have not been performed. No Lean, Lake or CI.

## Results and scope

1. On any normal zero-Hamiltonian vertex arc, each of the two inactive
   Hamiltonian ties is a zero of an explicit scalar function with at most
   three zeros before the strict-star boundary. Its monotonicity intervals
   have a finite description, including possible multiple roots.
2. The sufficient escape threshold in GLOBAL_PERIOD_BUDGET improves from
   exit ratio R>=5 to **R>=16/5**, with the other stated hypotheses retained.
   A more precise endpoint test below removes even that numerical threshold.
3. The exact M1=021210 strong-local-minimum example with all factors 5/4 in
   LOCAL_L3_STRONG_MINIMUM cannot occur in **any closed twisted PMP extremal**.
   This is distinct from the previously excluded small-core padded family.
   An open neighborhood within the normal-PMP M1 domain is also excluded;
   no numerical neighborhood radius or full M1 coverage is claimed.
4. A competitive closed period must meet its actual frame endpoint at the
   **first** polar-angle section pi/3. The frame/state/costate equations
   must still be checked there; an angle match alone is not closure.

The unrestricted octagon inequality and affine rigidity remain open.
None of the five universal case-C targets is closed by these results.

## 1. Exact single-vertex coordinates

Use the minimizing convention with cost A=(2/3)C, and the state-only clock
d tau=y dt, exactly as in [GLOBAL_PERIOD_BUDGET](GLOBAL_PERIOD_BUDGET.md),
Section 2. Cyclically rotate the active vertex to 1. Write

    q=1/sqrt(3), w=y^-2, K(x)=[[1,x],[0,1]], A_frame=g K(x).

In these coordinates the active field and running cost are

    x_tau=1, w_tau=2w/(q-x), A_frame,tau=A_frame w E21,
    L=1+(1+x^2)w.

Let m,n,k be the group covector evaluated on E21,E12,diag(1,-1),
and let p_w be the w-covector. Put mu=-1-m. Along this arc,

    m'=0, k'=2wm, n'=-wk,
    p_w'+2p_w/(q-x)=mu-x^2,
    p_x=-1-(x^2-mu)w-2wp_w/(q-x).

The last equation is the zero active Hamiltonian, not a new endpoint
condition. Start at x=a in (-q,q), w=w0, and define

\[
W=(q-a)^2w_0,\quad c=\frac W{q-a},\quad
u=\frac W{q-x},\quad S=u-c,\quad r=u/c.
\]

Here the symbol in the third definition is the scalar u (not a control).
Thus x=q-W/u, w=u^2/W, and S is the accumulated integral of w dx.
The initial value is r=1. The first star boundary is at

\[
u_e=\frac{1+W}{2q},\qquad R=\frac{u_e}{c}>1.
\]

Again u_e denotes this scalar endpoint. In terms of x it is
x_e=q(1-W)/(1+W), strictly between a and q. The boundary reached is
1-w(q^2-x^2)=0; y remains positive.

The exact integrated state-covector numerator is

\[
E(u):=u^2p_w(u)
=c^2p_w(a)+W(\mu-q^2)(u-c)+2qW^2\log(u/c)
 +W^3(1/u-1/c).
\tag{1}
\]

In particular E'(u)=W(mu-x(u)^2). For the other inactive gap define

\[
Q=1+(x^2-\mu)w+w\bigl((q-x)w+(q-x)^{-1}\bigr)p_w,
\qquad B=n-Q.
\]

The two inactive-minus-active minimizing Hamiltonians are

\[
H_2-H_1=-\frac{4qwp_w}{q^2-x^2},\qquad
H_0-H_1=-\frac{2B}{1-w(q^2-x^2)}.
\tag{2}
\]

The previously derived identity B_SS=8/3-2q(W+1)/(S+c) integrates to

\[
B(S)=B_0+B_1S+\frac43S^2
 -2q(W+1)\bigl[(S+c)\log(1+S/c)-S\bigr],
\tag{3}
\]

where B_0=B(0) and B_1=B_S(0). The group covector is simultaneously

    m=m0, k=k0+2m0 S, n=n0-k0 S-m0 S^2.

For an initially identity frame the exact frame increment is
K(a) [[1,0],[S,1]] K(x)^-1. The physical elapsed time and cost are

\[
\Delta t=\sqrt W\log r,
\]
\[
\Delta C=\frac32\left[(1+W)W(1/c-1/u)
                   +\frac43(u-c)-2qW\log r\right].
\tag{4}
\]

These expressions are solutions of the state and adjoint equations, not
an ODE discretization. Numerical evaluation of them still has rounding
error and does not certify the signs of entire parameter regions.

## 2. A finite event-isolation argument

The function x(u) is strictly increasing. Consequently the only possible
critical points of E are x=+sqrt(mu) and x=-sqrt(mu) when mu>=0 and these
points lie in (a,x_e). There are at most two. On each intervening interval
E is strictly monotone. Rolle's theorem then gives at most three distinct
zeros of E. Its derivative cannot vanish identically because x varies
strictly and the coefficient of x^2 is nonzero.

For the third gap, B_S is strictly convex because

\[
B_{SSS}=\frac{2q(W+1)}{(S+c)^2}>0.
\]

More specifically B_SS vanishes only at u=u_e/2, when that point belongs
to (c,u_e). Thus B_S has at most two zeros, isolated on its two possible
monotonicity intervals. These zeros divide B into at most three monotone
intervals. B therefore has at most three distinct zeros as well.

This supplies a finite scalar procedure for the next inactive tie, rather
than relying on a time-step sign change. A zero at a critical point must
be retained as a possible multiple tie. Equal event times from E and B
must be retained as a possible triple tie. Neither is a license to choose
an arbitrary outgoing branch. The numerical implementation conservatively
returns UNKNOWN for these unresolved alternatives.

This is a per-arc result. It does not bound the number of arcs in a period
or prove that all resulting normal trajectories are minimizing.

## 3. An endpoint test and the improved escape threshold

Assume an outgoing control-1 arc has

\[
0<a<q,\quad p_w(a)\le0,\quad \mu\le a^2,\quad
B_0<0,\quad B_1\le0.
\tag{5}
\]

For x>a the source mu-x^2 is strictly negative. Multiplying the p_w
adjoint equation by its positive integrating factor proves p_w(x)<0
until the boundary.

**Endpoint test.** If B(S_e)<0, where S_e=c(R-1), then B<0 throughout
[0,S_e]. Indeed, B_S is convex and B_S(0)<=0. Its nonpositive set is an
interval containing zero, so B first decreases and then possibly increases.
Its maximum is therefore at one of the two endpoints. Both endpoint
values are strictly negative. The same conclusion follows directly from
the single minimum of B_S described in Section 2.

This endpoint test already improves on requiring B_S to stay negative.
Substitute 2q(W+1)=(4/3)cR into (3) to obtain

\[
B(S_e)=B_0+B_1c(R-1)+\frac43c^2R^2\psi(R),
\quad \psi(R)=2-3/R+1/R^2-\log R.
\tag{6}
\]

For R>2,

\[
\psi'(R)=-\frac{(R-1)(R-2)}{R^3}<0.
\]

Moreover psi(16/5)<0. Here is a finite rational logarithm certificate:
with z=11/21,

\[
\log(16/5)>2\sum_{j=0}^3\frac{z^{2j+1}}{2j+1}
=\frac{73269045344}{63038098935}
>\frac{297}{256}
=2-\frac{3}{16/5}+\frac1{(16/5)^2}.
\tag{7}
\]

The difference in the middle comparison is
34560224369/16137753327360>0. The first inequality is the finite geometric
expansion of 2 integral_0^z (1-t^2)^-1 dt with its positive remainder.
Thus (5) together with R>=16/5 gives B(S_e)<B_0<0, and the endpoint test
proves both inactive gaps strictly positive until the star boundary.

The elapsed physical time is sqrt(W) log R<infinity. A closed twisted PMP
lift extends indefinitely in strict star, using the same covector at every
seam, so this forced escape is incompatible with any such closed lift.
At an initial two-way tie one must justify the outgoing branch. In the
application below it is transverse. More generally the assertion applies
once the stated outgoing arc has begun; it does not discard unexamined
triple-tie alternatives.

## 4. Exact application to the factor-5/4 M1 example

Retain the exact input of
[LOCAL_L3_STRONG_MINIMUM](LOCAL_L3_STRONG_MINIMUM.md):

\[
f=5/4,\quad L=\log(5/4),\quad \kappa^2=448/803,
\qquad p(0)=\kappa(1,2,193/112),\quad i=021210.
\]

Its fixed-initial-state endpoint map has rank five, and its normal adjoint
and whole-arc PMP inequalities are explicitly given in that note. The rank
forces the same normal lift on any putative larger PMP occurrence, by
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md), Section 4. This application
therefore does **not** depend on the unaudited general GLOBAL_NORMALITY
claim.

At the start of the last control-0 piece its margins are
kappa(1,33/28,11/4). Rotate old vertex 0 to new vertex 1. The rotated
margins are kappa(11/4,1,33/28). Exact substitution gives

\[
a=\frac5{61\sqrt3},\quad w_0=\frac{11163}{22484},\quad
W=\frac{112}{803},\quad c=\frac{122\sqrt3}{803},\quad R=\frac{15}{4}.
\tag{8}
\]

The adjoint quantities at that switch are

\[
p_w(a)=0,\qquad
\mu-a^2=\frac{11(23440L-5363)}{55815},
\]
\[
B_0=-\frac{14884(5L-1)}{261121},\qquad
B_1=\frac{61\sqrt3(560L-167)}{20440}.
\tag{9}
\]

### 4.1 Reproducing (9) from the existing needle certificate

This avoids an unexplained numerical adjoint. The raw compensated needle
functions on the first arc in the cited note are

\[
D_{01}(s)=P_{01}(s)/392000,\quad
D_{02}(s)=P_{02}(s)/(200704s^2),
\]
\[
P_{01}=(711040L-20548)s^2+(55685-352800L)s
       -98000-294000s\log s,
\]
\[
P_{02}=-50176s^2+(894720L-247172)s
       +387365-1289200L+136640s\log s.
\]

The reflected final-arc gaps are D_52(r)=D_01(f/r) and
D_51(r)=D_02(f/r). At its beginning r=1 these give

\[
P_{01}(f)=60500(5L-1),\quad P_{02}(f)=0,
\quad P_{02}'(f)=1031360L-235972.
\]

The physical cost is sqrt(12)*kappa^2 times the raw objective. A log-factor
needle at vertex j has physical clock p_j/2. Converting to the minimizing
scaled cost and then dividing by y for the tau clock yields, on this
rotated final arc,

\[
B(r)=-\frac{4\kappa^2}{3}w_0r^2D_{01}(f/r),
\quad
p_w(r)=-\frac{\kappa^2(q-x)}{w(r)}D_{02}(f/r).
\tag{10}
\]

Use these identities at r=1 and differentiate there, with
S=c(r-1), to obtain

\[
B_1=-\frac{4\kappa^2w_0}{3c}
       [2D_{01}(f)-fD_{01}'(f)],
\quad
\mu-a^2=\frac{\kappa^2P_{02}'(f)}{200704 f w_0}.
\]

Substitution proves (9) by rational algebra. Only the value and first
right derivative at the known switch are used; no continuation of the
reflection identity beyond its proved interval is assumed.

### 4.2 Every sign is a hand inequality

The elementary bounds 2/9<L<9/40 imply

    5L-1>1/9,
    23440L-5363<5274-5363=-89,
    560L-167<126-167=-41.

Hence mu<a^2, B_0<0 and B_1<0. Also 0<a<q, p_w(a)=0, and
R=15/4>16/5. The edge tie is transverse because mu-a^2<0;
the third gap is already strict. Section 3 applies.

**Conclusion:** after the fifth switch, old control 0 is forced until the
star boundary. From the end of the original six-piece window, the remaining
physical time to that boundary is exactly

\[
\boxed{\sqrt{112/803}\,\log 3.}
\]

Thus this exact strong local minimum cannot occur even as an arbitrarily
cut subwindow of a closed twisted PMP extremal. Its fixed-endpoint strong
local minimality is not contradicted.

At partial final factor r=9/8, the new exit ratio is (15/4)/(9/8)=10/3,
still greater than 16/5. The edge gap, third gap, and mu<a^2 are strict
there. B_S remains negative up to this point since B_SS<0 for r<R/2.
All escape inequalities are therefore strict at this interior phase.
Smooth dependence of the full-rank normal covector and vertex flows gives
an open neighborhood of PMP windows with the same exclusion. No radius
or coverage of other M1 inputs is asserted.

## 5. The primary-angle return guard

Write g=aI+bJ+cH+dK and X=rho J+vH+wK, where
H=diag(1,-1), K=[[0,1],[1,0]]. Then

    a^2+b^2-c^2-d^2=1, rho>0, rho^2-v^2-w^2=1.

The nonvanishing complex polar coordinate is z(g)=2(a+ib). Directly from
g'=gX,

\[
\theta'=\rho+
 \frac{v(-ad-bc)+w(ac-bd)}{a^2+b^2}.
\]

The magnitude of the second term is at most
sqrt(rho^2-1)*sqrt((c^2+d^2)/(a^2+b^2)), strictly less than rho.
Consequently 0<theta'<2rho. With theta(0)=0 and C=3 integral rho dt,

\[
0<\theta(t)<2C(t)/3.
\]

On a competitive period C<=A_oct<pi, this lies below 2pi/3.
The exact matrix endpoint g(T)=exp(pi J/3) requires
 theta(T)=pi/3 modulo 2pi, hence exactly pi/3. Its strict monotonicity
makes this the only possible return section before budget exhaustion.
The actual frame, state and both costate endpoint equations remain
separate tests at that section. A failed numerical residual is not a
rigorous lower bound without error certification.

## Validation boundary

The proof above is algebraic and analytic. The supplemental exact
checks and high-precision continuation experiments are recorded in the
follow-up Experiment 002. Numerical roots are not interval enclosures.
No external peer review, independent reviewer, Lean elaboration,
kernel validation, or complete M1 exclusion is claimed.

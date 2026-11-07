# Exact outgoing branches at normal ties

Date: 2026-11-07 UTC. Hand proof with an
[independent internal audit](NORMAL_TIE_BRANCHING_AUDIT.md).
No Lean, Lake, typechecking or CI.

## Result and scope

At a strict-star normal zero-Hamiltonian phase, there is an exact finite
test for each of the three possible outgoing positive vertex arcs. It
uses only signs of explicitly given quantities, with derivatives of order
at most three. It includes two-way ties, triple ties, quadratic contacts
and cubic switches. It does not assume that a tie is transverse.

For each candidate vertex, rotate it to vertex 1 and use the quantities
defined below. A positive vertex-1 PMP arc starts at this phase if and
only if its active Hamiltonian is zero and both tests hold:

\[
\boxed{
\begin{split}
\mathsf E:\quad &p_w(a)<0,\quad\hbox{or}\\
&p_w(a)=0\ \hbox{and}\
 \bigl(\mu<a^2\ \hbox{or}\ (\mu=a^2\ \hbox{and}\ a\ge0)\bigr);
\end{split}}
\tag{1}
\]

\[
\boxed{
\begin{split}
\mathsf B:\quad &B_0<0,\quad\hbox{or}\\
&B_0=0\ \hbox{and}\
 \bigl(B_1<0\ \hbox{or}\ (B_1=0\ \hbox{and}\ R>2)\bigr).
\end{split}}
\tag{2}
\]

Here a positive outgoing arc means that, for some positive duration,
the actual state/costate flow with that constant vertex satisfies the
full simplex maximum principle. All inactive Hamiltonian gaps are
strict on a sufficiently short open right interval. Endpoints may tie.
The test asserts existence of this local arc, not existence of a closed
period, optimality, or a competitive total cost.

Apply the test independently to all three candidate vertices and retain
every passing branch. There is no claim that exactly one passes at every
phase. A finite positive vertex representation of an actual minimizer
must use one of the passing branches; its existence is supplied by the
existing finite-representation theorem. The result does not classify
arbitrary measurable singular arcs that have no positive vertex germ.

This gives the normal-tie branch rule required in the finite-case plan.
It excludes neither an entire F/R/M1/M2/M3 domain nor every normal tie.
Global comparisons must still cover every passing branch, including
the equality strata in (1)--(2).

## 1. Conventions and the exact vertex flow

Normalize the maximizing physical cost multiplier to \(\lambda=-1\),
which [GLOBAL_NORMALITY](GLOBAL_NORMALITY.md) permits for every global
minimizing lift under its stated inputs. To use the formulas of
[VERTEX_EVENT_ESCAPE](VERTEX_EVENT_ESCAPE.md), switch to minimizing
scaled cost \(\mathcal A=(2/3)C\), with covector
\(p^{\min}=-(2/3)p^{\max}\), and state-only clock
\(d\tau=y\,dt\). The clock factor is positive on strict star; the cotangent sign reverses
maximization into minimization. On the active zero-Hamiltonian locus, the
extra cotangent term from the state-dependent clock vanishes. These
changes preserve the selected control.

After cyclically rotating the candidate outgoing vertex to 1, put

\[
q=1/\sqrt3,\quad x(0)=a\in(-q,q),\quad w=y^{-2},
\quad W=(q-a)^2w(0)>0,\quad c=W/(q-a)>0.
\]

Along this candidate vertex flow use the increasing variables

\[
u=\frac W{q-x},\qquad S=u-c,\qquad
x(u)=q-\frac Wu,\qquad w(u)=\frac{u^2}{W}.
\tag{3}
\]

Strict star holds from \(u=c\) up to the first state boundary

\[
u_e=\frac{1+W}{2q},\qquad R=\frac{u_e}{c}>1.
\tag{4}
\]

The minimizing adjoint, expressed in the shear coordinates of
VERTEX_EVENT_ESCAPE, has a constant group coefficient \(m\); set
\(\mu=-1-m\). Its state covector and third-control numerator solve

\[
E(u):=u^2p_w(u)
 =c^2p_w(a)+W(\mu-q^2)(u-c)
  +2qW^2\log(u/c)+W^3(1/u-1/c),
\tag{5}
\]

\[
B(S)=B_0+B_1S+\frac43S^2
 -2q(W+1)\bigl[(S+c)\log(1+S/c)-S\bigr].
\tag{6}
\]

The constants \(B_0=B(0)\) and \(B_1=B_S(0)\) are obtained from
the same actual initial covector, not chosen afresh after a tie. The
active Hamiltonian is zero along this exact flow if it is zero initially.
The other minimizing Hamiltonians satisfy

\[
H_2-H_1=-\frac{4qwp_w}{q^2-x^2},\qquad
H_0-H_1=-\frac{2B}{1-w(q^2-x^2)}.
\tag{7}
\]

Both denominators are strictly positive before the state boundary.
Thus the candidate is the unique maximizing physical vertex precisely
when \(E<0\) and \(B<0\). At the initial phase, non-strict
inequalities are allowed. The maximum over the simplex is the maximum
over its vertices, by the positive fractional weights in the actual
Hamiltonian. There is no untested intermediate simplex control.

All formulas (3)--(7) solve the actual state and cotangent equations;
their derivation and the frame reconstruction are retained in
VERTEX_EVENT_ESCAPE and GLOBAL_PERIOD_BUDGET. The argument below only
differentiates these explicit functions at a strict interior state.

## 2. The incoming-edge gap: order at most three

Direct differentiation of (5) gives

\[
E'(u)=W(\mu-x(u)^2),\qquad
E''(c)=-\frac{2W^2a}{c^2}.
\tag{8}
\]

Since \(c^2>0\), \(E(c)\) has the sign of \(p_w(a)\).
If it is negative, continuity gives \(E<0\) on a short right
interval. If it is positive, the candidate is already incompatible
with maximization.

When \(p_w(a)=0\), the sign of the first derivative is the sign
of \(\mu-a^2\). A negative first derivative gives the required
right-hand strict sign; a positive one excludes the candidate.
If this derivative also vanishes, the sign of the second derivative
is the sign of \(-a\), by (8). Thus \(a>0\) is allowed and
\(a<0\) is excluded.

If \(a=0\) as well, then \(\mu=0\) and

\[
E'''(c)=-\frac{2W^3}{c^4}<0.
\tag{9}
\]

So the final equality case has a strict negative cubic right-hand
leading term. There is no fourth-order or identically zero alternative.
These alternatives prove exactly test (1), including its necessity.

The equality \(p_w(a)=\mu=a=0\) must be retained: rejecting every
zero initial switching derivative would discard this genuine cubic
possibility. Conversely, the quadratic alternative alone need not be
an actual change between two controls; it may describe a contact at
which the same vertex remains selected. The test concerns the right
arc and does not assign an incoming control that has not been checked.

## 3. The third-control gap: the cubic equality is excluded

Differentiating (6) at \(S=0\) gives

\[
B''(0)=\frac83-\frac{2q(W+1)}c
       =\frac83\left(1-\frac R2\right),\qquad
B'''(0)=\frac{2q(W+1)}{c^2}>0.
\tag{10}
\]

The identity with \(R\) uses \(q^2=1/3\) and (4).
If \(B_0<0\), continuity supplies the right strict sign. If
\(B_0=0\), the first nonzero right Taylor coefficient must be
negative. This occurs when \(B_1<0\), or when \(B_1=0\) and
\(R>2\). If \(B_1=0\) and \(R<2\), the positive quadratic
term excludes this outgoing vertex. At \(B_1=0,R=2\), the quadratic
coefficient vanishes but the cubic one is strictly positive, again
excluding this vertex. A positive initial value or first derivative
also excludes it. These are exactly the alternatives in (2).

In particular, the all-equalities case is not an unresolved higher-order
contact. It has a known positive cubic term and fails maximization for
this candidate outgoing vertex. A different vertex still has to be
tested using its own rotated data.

## 4. Sufficiency, necessity, and use at a triple tie

Suppose the active Hamiltonian is zero and (1)--(2) hold. The exact
vertex flow is analytic on a neighborhood of its initial strict-star
phase. Sections 2--3 give a positive interval on which each numerator
is strictly negative. Shrinking that interval also keeps the state
strict star. Equation (7) then makes both other controls strictly
worse, so the same analytic state/costate flow satisfies the full PMP.
This proves local sufficiency.

Conversely, a positive outgoing vertex PMP arc has both inactive gaps
nonnegative throughout a right interval. If either test failed, the
displayed first nonzero Taylor coefficient would make the corresponding
numerator positive immediately to the right. Equation (7) would violate
maximization. Thus both tests are necessary. Every zero alternative
terminates at a nonzero derivative of order at most three.

At a triple tie, both numerators initially vanish for every candidate
vertex. Apply (1)--(2) after each of the three cyclic rotations, using
the rotated state and the same transported covector. Retain all passing
vertices; discard a vertex only when its own exact sign test fails.
This is a finite branching rule covering all normal triple-tie phases
that admit positive vertex germs.

The derivative order is unchanged in physical time. Indeed
\(du/d\tau=w>0\) and \(d\tau/dt=y>0\) at the initial point,
so \(du/dt=1/y>0\). Neither a singular clock nor a zero derivative
of the clock is hidden in the cubic arguments.

For a check at the full circle singular phase, all three rotations give
\(a=\mu=p_w(a)=B_0=B_1=0\) and \(R=2\).
The edge test passes cubically, but the third-control test fails
cubically, for every vertex. This says that no positive constant vertex
arc can depart from that exact normal singular phase. It does not deny
the centroid-controlled circle solution.

## 5. What this closes and what remains

Together with global normality, the theorem provides exact treatment of
the initial multiplier and outgoing-tie alternatives for the finite
vertex search. No normal cubic or triple tie needs to be dropped by a
genericity assumption or replaced by an arbitrary outgoing label.

The result is qualitative about the size of a valid right interval.
It does not supply a uniform positive gap or a uniform duration across
nearby degenerate phases. Floating-point near-zero values do not certify
the equalities in (1)--(2); an implementation must use exact arithmetic,
verified enclosures, or return UNKNOWN when its signs are unproved.
The present theorem does not change any floating-point oracle's error
control or make its numerical roots into certificates.

Complete-period return, cost, constrained-variation and boundary
arguments must still cover every surviving branch. The five uniform
case-C exclusions, the unrestricted octagon inequality and affine
rigidity remain open.

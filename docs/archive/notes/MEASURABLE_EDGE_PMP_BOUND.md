# A direct four-piece bound for measurable edge intervals

Date: 2026-11-07. Hand proof; no Lean, Lake, typechecking, CI, numerical
trajectory, or symbolic sign calculation.

## Theorem and scope

Let a complete global minimizer of the Reinhardt control problem contain a
closed nondegenerate subinterval on which one fixed control coordinate
vanishes almost everywhere. On that subinterval its control agrees almost
everywhere with a concatenation of at most **four positive constant vertex
pieces**.

The proof permits an arbitrary measurable control at the outset. It does
not assume a finite vertex representation, isolated switches, normality of
the full-system Pontryagin lift, or a positive lower bound on piece lengths.
It proves the optimality property **(E4)** used in
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md).

More generally, the same conclusion holds for a strict-star edge trajectory
that is a strong local minimum among edge trajectories with uniformly
nearby state curves, its initial and final frame and state fixed, and its
physical terminal time free. Global
minimality is used only to obtain that local minimum. The edge problem has
its own nontrivial Pontryagin multiplier; the result is not asserted for
every extremal of the full control system.

The argument uses the ordinary fixed-time Pontryagin maximum principle on
a two-dimensional state space, followed by an integrating factor and
Rolle's theorem. The coordinate and endpoint calculations below are direct.
Neither Hales--Vajjha Theorem 8.1.4 nor Theorem 16.3.1 is needed as an input.

## 1. Reparameterizing the edge by a strictly increasing state coordinate

The cyclic rotation of the three control labels preserves cost, the strict
star, and the existence of fixed-endpoint replacements. We may therefore
take the missing coordinate to be `u_0=0`. Set

\[
q=\frac1{\sqrt3},\qquad
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix}.
\]

The strict-star conditions are

\[
-q<x<q,\qquad y>0,\qquad x^2+y^2>q^2.
\tag{1}
\]

Put

\[
\alpha=\frac{u_1-u_2}{\sqrt3}\in[-q,q].
\]

Substitution into the actual state equation
\(\dot X=[Z_u,X]/\operatorname{tr}(Z_uX)\), with
\(Z_u=\left(\begin{smallmatrix}\alpha&-2/3\\0&-\alpha\end{smallmatrix}\right)\),
gives

\[
\dot x=y,\qquad
\dot y=\frac{\alpha y^2}{\alpha x-q^2}.
\tag{2}
\]

The denominator is strictly negative on (1), uniformly over the edge on
every compact state interval. Since `y` is continuous and positive,
`x` is a continuously differentiable, strictly increasing time coordinate.
For an original physical-time interval \([t_0,t_1]\), put
\(a=x(t_0)<b=x(t_1)\). Both endpoints lie in \((-q,q)\).

Use `x` as the independent variable and define

\[
w(x)=y(x)^{-2}>0,\qquad s(a)=0,\qquad s'(x)=w(x).
\]

Equation (2) gives

\[
w'=\beta(x)w,\qquad
\beta=\frac{2\alpha}{q^2-\alpha x}.
\tag{3}
\]

For each fixed \(x\in[a,b]\), the map \(\alpha\mapsto\beta\) is
strictly increasing, because

\[
\frac{\partial\beta}{\partial\alpha}
=\frac{2q^2}{(q^2-\alpha x)^2}>0.
\]

It maps \([-q,q]\) exactly onto

\[
b_-(x):=-\frac2{q+x}\ \le\ \beta\ \le\
b_+(x):=\frac2{q-x},\qquad
b_+(x)-b_-(x)=\frac{4q}{q^2-x^2}>0.
\tag{4}
\]

Thus we may use a measurable control \(v:[a,b]\to[0,1]\) and write

\[
\beta_v(x)=b_-(x)+v(x)\bigl(b_+(x)-b_-(x)\bigr).
\tag{5}
\]

This is an equivalent control parameterization, not a relaxation. The
inverse map is

\[
\alpha=\frac{q^2\beta}{2+x\beta},
\qquad
u_1=\frac{1+\sqrt3\alpha}{2},\qquad
u_2=\frac{1-\sqrt3\alpha}{2},\qquad u_0=0.
\tag{6}
\]

Its denominator is positive throughout the interval (4); at the two
endpoints it equals \(2q/(q+x)\) and \(2q/(q-x)\), respectively.
It is affine in `beta` between them. The maps and their inverses preserve
measurability. The values `v=0` and `v=1` correspond to the vertices
\(e_2\) and \(e_1\).

The strict-star condition that remains in these coordinates is

\[
0<w(x)<\frac1{q^2-x^2}\qquad (a\le x\le b).
\tag{7}
\]

## 2. The exact physical endpoints and objective

For any solution of (3)--(7), recover physical time by

\[
t(x)=t_0+\int_a^x\sqrt{w(r)}\,dr.
\tag{8}
\]

The function `w` is positive and absolutely continuous. Its positivity
also follows directly from
\(w(x)=w(a)\exp(\int_a^x\beta_v(r)\,dr)\). Consequently (8) has a
positive continuous derivative, is invertible, and gives a positive
physical duration. The inverse change of parameter recovers (2) with
the control (6). On the compact interval, `w` has positive lower and
finite upper bounds, so this time change and its inverse are Lipschitz.
They preserve null sets and hence the almost-everywhere control identities.

Set

\[
h(x)=\begin{pmatrix}1&-x\\s(x)&1-s(x)x\end{pmatrix},
\qquad g(x)=g(t_0)h(a)^{-1}h(x).
\tag{9}
\]

One has \(\det h=1\). Direct multiplication, using `s'=w`, gives

\[
h^{-1}\frac{dh}{dx}
=\begin{pmatrix}xw&-(1+x^2w)\\w&-xw\end{pmatrix}
=\sqrt w\,\Phi(x,w^{-1/2}).
\tag{10}
\]

Equations (8)--(10) prove \(\dot g=gX\). With `a,b` fixed, the
initial state is fixed by `w(a)` and the final state by `w(b)`. The
initial frame is fixed by construction. At `x=b`, the only varying
entry in the family \(h(b)\) is determined by `s(b)`, and the map
\(s(b)\mapsto h(b)\) is injective. Hence fixing the final frame is
exactly equivalent to fixing

\[
s(b)=\int_a^b w(x)\,dx.
\tag{11}
\]

The actual segment cost transforms to

\[
\begin{aligned}
C
&=\frac32\int_{t_0}^{t_1}\frac{1+x^2+y^2}{y}\,dt\\
&=\frac32\int_a^b\bigl(1+(1+x^2)w(x)\bigr)\,dx\\
&=\frac32\left((b-a)+(s(b)-s(a))
             +\int_a^b x^2w(x)\,dx\right).
\end{aligned}
\tag{12}
\]

All terms outside the last integral are fixed by the endpoint data.
The relevant problem therefore has fixed independent-variable interval
\([a,b]\), two states `(w,s)`, dynamics

\[
w'=\beta_v(x)w,\qquad s'=w,
\tag{13}
\]

fixed initial and final values of both states, and objective

\[
M(w)=\int_a^b x^2w(x)\,dx.
\tag{14}
\]

There is no extra constraint fixing the physical duration (8). The
original physical terminal time is free.

## 3. Why the minimizer satisfies this separate edge PMP

The original state curve is continuous on a compact interval and lies
in the open region (7). Thus both inequalities in (7) have a positive
uniform margin. Every sufficiently close state curve satisfying (13)
retains (7).

For such a nearby curve with the fixed endpoint data in Section 2,
equations (6), (8), and (9) reconstruct an actual admissible edge
segment with the same initial and final `g,X`. Splicing it into the
complete trajectory preserves those state and frame values at both
seams. The frame derivatives match because both one-sided derivatives
are `gX`. The integral state equations and measurable simplex control
remain valid. The subsequent original segment is translated in time
by the change in duration (8), so the terminal frame and twisted state
endpoint are unchanged. Formula (12) shows that a decrease of (14)
would decrease the full cost.

Consequently the restriction of a global minimizer is a local minimum
of (13)--(14) with fixed endpoints. The ordinary fixed-time PMP applies:
the control set `[0,1]` is compact, the coefficients `b_-,b_+` are
smooth and bounded on `[a,b]`, and the dynamics and cost are smooth in
the states. Condition (7) is open, and the minimizing trajectory has
a positive margin from its boundary. No active state-constraint
multiplier is required.

This PMP is applied to the reduced two-state edge problem itself.
It supplies constants \(\lambda\le0\), a constant \(p_s\), and an
absolutely continuous function \(p_w\), with

\[
(\lambda,p_s,p_w)\not\equiv0,
\tag{15}
\]

such that the Hamiltonian

\[
H(x,w,s,p_w,p_s,v)
=w\bigl(p_w\beta_v(x)+p_s+\lambda x^2\bigr)
\tag{16}
\]

is maximized by the original control almost everywhere, and

\[
p_w'=-\beta_v(x)p_w-p_s-\lambda x^2,
\qquad p_s'=0.
\tag{17}
\]

We do **not** impose `H=0`: the independent-variable interval in this
edge formulation is fixed. The multiplier is not obtained by restricting
an arbitrary full-system lift, which could be abnormal and lose the
necessary edge information.

Because `w>0` and \(b_+-b_->0\), maximization of (16) forces

\[
v=\begin{cases}
1,&p_w>0,\\
0,&p_w<0
\end{cases}
\qquad\text{almost everywhere}.
\tag{18}
\]

It remains to bound the zero set of `p_w`, without assuming any initial
regularity of the control beyond measurability.

## 4. A positive integrating factor gives at most three zeros

Define

\[
\rho(x)=\exp\left(\int_a^x\beta_v(r)\,dr\right)>0,
\qquad F(x)=\rho(x)p_w(x).
\tag{19}
\]

The functions `rho` and `p_w` are absolutely continuous. Multiplication
of (17) by `rho` gives

\[
F'(x)=-\rho(x)Q(x)\quad\text{almost everywhere},
\qquad Q(x)=p_s+\lambda x^2.
\tag{20}
\]

The right-hand side is continuous: `rho` is continuous, even though
the original control is only measurable. The integral identity for
`F` therefore shows that `F` is continuously differentiable and (20)
holds at every interior point.

If the polynomial `Q` is not identically zero, it has at most two
distinct real roots. Since `rho>0`, the derivative `F'` has at most
two zeros. Four distinct zeros of `F` on `[a,b]` would give three
distinct interior zeros of `F'` by Rolle's theorem, a contradiction.
Thus `F`, and hence `p_w`, has at most three zeros.

If `Q` is identically zero, then `p_s=lambda=0`. Equation (20) makes
`F` constant. This constant cannot be zero, because that would make
`p_w=0` everywhere as well, contrary to (15). In this case `p_w` has
no zeros at all.

These alternatives also cover abnormal edge multipliers explicitly.
When `lambda=0` and `p_s` is nonzero, `F'` has constant strict sign,
so `F` has at most one zero. When both vanish, `F` is a nonzero
constant. No division by the cost multiplier is used.

## 5. Returning to physical time and counting pieces

Delete the at most three zeros of `p_w` from `[a,b]`. On every
remaining nondegenerate connected component it has one fixed sign.
Equation (18) makes the control equal almost everywhere to one fixed
endpoint of `[0,1]` there. Equation (6) then makes the original control
one fixed simplex vertex. Values at the finitely many deleted points
do not affect the integral trajectory.

There are at most four such components. The monotone time change (8)
preserves their order and maps each positive-length `x` interval to
a positive physical-time interval. Merge equal neighboring vertices
and discard zero-length pieces. The resulting physical control has
at most four positive constant vertex pieces, as claimed.

The count concerns pieces, not a positive lower bound on their
durations. It includes switches at arbitrarily close times and
possible tangencies of the switching function. No initial finite-piece
assumption, limit of longer words, or source finite-switch theorem was
used to obtain it.

## Dependency and validation boundary

- The physical equations and cyclic symmetry are those recorded in
  [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md) and
  [SWITCHING_WORDS](SWITCHING_WORDS.md).
- The reconstruction agrees with the exact endpoint calculation in
  [EDGE_SWITCH_BOUND](EDGE_SWITCH_BOUND.md), Sections 1--2. That note's
  five-arc variation remains a separate direct improvement argument.
- The sole optimal-control theorem used here is the standard fixed-time
  PMP with fixed endpoints on an open state space. Both normal and
  abnormal multipliers are retained.
- Global use requires the established geometric/control correspondence,
  which makes the reconstructed endpoint-preserving splice admissible.
  The present note does not replace that correspondence or the common
  compact-state theorem.

The four-piece statement proves the precise edge hypothesis required
by the quantitative switch theorem. It does not alone bound a complete
word using all three vertices or compare its cost with the octagon.
All arguments here are hand proofs; no kernel validation is claimed.

An independent internal hand review checked the control transformation,
its inverse, the frame reconstruction, fixed endpoints, cost, open-state
local minimum, separate PMP, both abnormal cases, and the final zero and
piece counts. It found no material gap. This is a mathematical review,
not external peer review or kernel validation.

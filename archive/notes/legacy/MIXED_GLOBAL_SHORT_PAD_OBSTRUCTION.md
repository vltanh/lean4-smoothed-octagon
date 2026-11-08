# A fixed asymmetric obstruction to a local mixed-case inference

Date: 2026-11-07 UTC. Exact hand certificate with supplementary rational
algebra and an [independent internal audit](GLOBAL_STRUCTURE_MIXED_SHORT_PAD_AUDIT.md).
No Lean, Lake, typechecking, or CI. Internal review is not external peer
review or kernel validation.

## Result and precise limitation

The following proposed inference is false:

> A strict-star normal PMP reverse-four core `2121`, with its three
> edge switching zeros, both adjoining control-0 ties, and a negative
> elliptic frame Casimir below the competitive complete-period cap,
> must enter the postcritical outgoing escape region.

There is one explicit asymmetric core satisfying all those local
conditions whose outgoing control-0 arc instead switches back to
control 1 at a factor strictly between **251/250 and 201/200**. In the
coordinates where that outgoing vertex is 1, this first return occurs
while `x<0`, before the positive critical point of its edge gap.
A positive incoming control-0 germ also exists, so these data give a
normal PMP six-piece window `021210`, with a sufficiently short cut
in its first piece and its last piece ending at the indicated tie.
The local window's cost can be kept below the octagon cost.

**This is not a closed-period or minimizing counterexample.** The
geometric sector and embedded-boundary eligibility conditions have not
been checked. Neither the complete frame/state/costate endpoints nor
local or global minimality have been established. The first piece's
external cut is not claimed to be a genuine switch. In particular this
is not a refutation of the revised complete-switch M1 target.

The concrete failure mechanism is **short outgoing padding**: the last
piece ends before the escape criterion's required postcritical point.
The core is also asymmetric and has unequal factors, but the certificate
does not claim asymmetry is essential to that failure. It shows that the
weighted moments, the two adjoining ties, and the necessary Casimir cap
alone cannot force sufficiently long padding. The padding hypothesis in
[MIXED_GLOBAL_SYMMETRIC_ESCAPE](MIXED_GLOBAL_SYMMETRIC_ESCAPE.md) must
therefore not be omitted when extending that result.

## 1. The exact core and its normal adjoint

Put

\[
q=1/\sqrt3,\quad \xi=x/q,\quad v=19/10,\quad
L=\log(7/5),\quad M=\log(6/5),\quad P=171/490.
\]

The five core abscissas, in order, are

\[
\xi_a=-1/2,\quad -2/5,\quad 0,\quad 2/5,
\quad \xi_b=4/7.
\tag{1}
\]

Prescribe controls `2121` and

\[
w(q\xi)=
\begin{cases}
P/(1+\xi)^2,&-1/2\le\xi\le-2/5,\\
v/(1+|\xi|)^2,&-2/5\le\xi\le2/5,\\
P/(1-\xi)^2,&2/5\le\xi\le4/7.
\end{cases}
\tag{2}
\]

The four factors are exactly `(6/5,7/5,7/5,7/5)`. The pieces match
continuously. On the two outer arcs the maximum values of
`w(q^2-x^2)` are `171/490` and `209/490`; on the middle arcs the
maximum is `19/30`. Thus the entire core is strictly inside the star.

Define

\[
m_0=12/5-7L,\qquad \mu=m_0/3=4/5-(7/3)L,
\]
\[
T(\xi)=\int_0^\xi w(q\eta)\,d\eta,\qquad
Z(\xi)=\int_0^\xi(m_0-\eta^2)w(q\eta)\,d\eta.
\tag{3}
\]

The weighted moment on `[0,2/5]` vanishes exactly, because

\[
2/5-2L+(1-m_0)(1-5/7)=0.
\tag{4}
\]

Consequently `0<mu<(2q/5)^2`; the zeros of `Z` are precisely
`-2/5,0,2/5`. Its signs on the successive core arcs are `+,-,+,-`.
Indeed its derivative has the sign of `mu-x^2`; on each half the
integral first increases and then decreases to its prescribed zero,
and the outer intervals lie beyond that zero. Reflection is used only
for the middle two arcs, not for the unequal whole core.

The four endpoint integrals are

\[
\begin{aligned}
T_a&=-323/490,&T_b&=38/49,\\
Z_a&=P\left((7/3)L-11/30-2M\right),&
Z_b&=P\left(16/21-(8/3)L\right).
\end{aligned}
\tag{5}
\]

Work with minimizing cost `A=(2/3)C` and shear coordinates
`A_frame=gK(x)`, `K(x)=[[1,x],[0,1]]`. Its actual normal adjoint is
specified by

\[
\begin{aligned}
m&=-1-\mu,&
k&=q\{K_0-2(1+\mu)T\},\\
n&=n_0-K_0T/3+(1+\mu)T^2/3,&
p_w&=q^3Z/w,\\
p_x&=-1-(x^2-\mu)w-b_i(x)wp_w,
\end{aligned}
\tag{6}
\]

where `b_2=-2/(q+x)` and `b_1=2/(q-x)`, and

\[
K_0=-\frac{209265L-98460M-52562}{90650},\qquad
n_0=\frac{139771961L+11224440M-11725086}{39976650}.
\tag{7}
\]

These equations solve the canonical adjoint and zero active Hamiltonian
on all four pieces. The three inner ties are exactly `p_w=0`.
For the other gap use `sigma=1` on control 2 and `sigma=-1` on
control 1, set `rho=1+sigma xi`, and write

\[
Q=1+(\xi^2-m_0)w/3
   -\sigma Z\left(\rho w/9+1/(3\rho)\right),\qquad B=n-Q.
\tag{8}
\]

The minimizing gap to control 0 is `H_0-H_active=-2B/d`, where
`d=1-w(q^2-x^2)>0`. For an explicit check of the outer ties, put

\[
Q_a=1+\frac{114}{245}(1/4-m_0)-\frac{547}{735}Z_a,
\quad
Q_b=1+\frac{19}{30}(16/49-m_0)+\frac{547}{630}Z_b.
\]

The constants (7) satisfy the two exact linear equations

\[
K_0=(1+\mu)(T_a+T_b)-3\frac{Q_b-Q_a}{T_b-T_a},
\quad n_0=Q_b+K_0T_b/3-(1+\mu)T_b^2/3.
\tag{9}
\]

Thus `B(a)=B(b)=0`: both adjoining control-0 ties hold for this same
covector. No new multiplier is chosen at either end.

## 2. Full core PMP and a positive incoming 0 germ

The edge Hamiltonian comparison is already settled by the signs of `Z`.
For the third-control gap use the exact identity

\[
B_{SS}=2\left(1-\frac{q^2}{W}
               -\sigma qx(1+1/W)\right),\qquad S=qT,
\tag{10}
\]

where `W=(q+sigma x)^2w` is constant on each arc. It gives the
following **uniform** bounds on the indicated whole arcs:

\[
B_{SS}\le-91/171<0\quad\hbox{on the first arc},\qquad
B_{SS}\le-10/133<0\quad\hbox{on the fourth arc},
\]
\[
B_{SS}\ge74/285>0\quad\hbox{on each middle arc}.
\tag{11}
\]

The endpoint slopes and center value are

\[
\begin{aligned}
qB_S(a)&=\frac{412041L+31179M-145313}{81585},\\
qB_S(b)&=-\frac{1735995L+147690M-611059}{407925},\\
B(0)&=-\frac{19(985733L-295380M-238494)}{19988325}.
\end{aligned}
\tag{12}
\]

The rational enclosures in Section 5 prove

\[
-13/1000<qB_S(a)<-12/1000,\quad
43/10^6<qB_S(b)<44/10^6,\quad
-38/1000<B(0)<-37/1000.
\tag{13}
\]

On the first arc, concavity and the negative initial slope imply `B<0`
after its initial zero. On the fourth, concavity and the positive final
slope imply `B<0` before its final zero. On each middle arc, convexity
puts `B` below the chord joining its negative endpoint values. Hence
`B<0` everywhere inside the core. Together with the edge signs, this
proves the full simplex PMP, not just the two-control edge condition.

At the left endpoint the control-1 gap is strict, since `Z_a>0`.
The physical gap `H_0-H_2` has strictly negative derivative along the
outgoing control-2 field: in the maximizing convention it is
`3y B/d`, and `B_x=wB_S<0` at the tie. The derivative of a difference
of two Hamiltonians is the same along their two Hamiltonian fields at
this tie; their difference is the Poisson bracket of the switching
function with itself, which is zero. Solve the **actual control-0
field backward** for a sufficiently short time. Its physical gap is
then strictly positive before the tie, while the remaining vertex
stays strictly inactive. Read this solution in ordinary increasing
time: it is a positive incoming control-0 PMP germ.

This is not an application of an admissible reversed control system.
It constructs the initial state of an ordinary incoming arc. Strict
star persists by continuity. Any sufficiently short positive cut of
that incoming arc supplies the first piece of the stated `021210`
window. No earlier external switch is asserted.

## 3. The outgoing 0 arc returns before its positive critical point

Rotate old vertex 0 to new vertex 1 at the right endpoint. In the
notation of VERTEX_EVENT_ESCAPE, its exact state data are

\[
a_+=-15q/547,\quad W=236883/1824760,\quad
c=q\,1383363/3649520,\quad R=3769/843>16/5.
\tag{14}
\]

The initial two-way tie gives `p_w(a_+)=0`. Transporting the group
matrix by the same cotangent rotation used in
MIXED_GLOBAL_SYMMETRIC_ESCAPE gives

\[
\mu_+=\frac{1847098680L+157142160M-650041901}{498182985},
\]
\[
\mu_+-a_+^2=
\frac{1064(1735995L+147690M-611059)}{498182985},
\]
\[
B_0=-\frac{299209(7L-2)}{5882450},\qquad
\frac{B_1}{q}=
\frac{547(4176250L+1624590M-2271733)}{534925650}.
\tag{15}
\]

Their strict bounds are

\[
212/10^6<\mu_+<213/10^6,\qquad
-39/10^6<\mu_+-a_+^2<-38/10^6,
\]
\[
-19/1000<B_0<-18/1000,\qquad -3/5<B_1/q<-1/2.
\tag{16}
\]

Thus this outgoing vertex starts as a genuine PMP arc. Also `B_0<0`,
`B_1<0`, and `R>16/5` make its third-control numerator strictly
negative all the way to the star boundary, by the exact endpoint test
in VERTEX_EVENT_ESCAPE. The only possible intervening event is its
other edge gap.

Write `c=q c_0`, where `c_0=1383363/3649520`. As a function of its
factor `r=u/c`, that numerator satisfies

\[
\frac{E(r)}q=
 W(\mu_+-1/3)c_0(r-1)+2W^2\log r
       +\frac{3W^3}{c_0}(1/r-1),
\]
\[
x(r)=q\left(1-\frac{562}{547r}\right),\qquad
\frac{dE}{dr}=cW(\mu_+-x(r)^2).
\tag{17}
\]

The same finite logarithm certificate proves

\[
-5/10^{10}<E(251/250)/q<-4/10^{10},
\quad
14/10^{10}<E(201/200)/q<15/10^{10}.
\tag{18}
\]

Both bracket points have `x<0`; at the first one,
`3/10^5<mu_+-x^2<4/10^5`. The derivative in (17) starts negative
by (16), increases in sign as `x` increases through negative values,
and has crossed zero before the first bracket point. Therefore `E`
first decreases and then increases on this interval. It has a unique
first positive zero

\[
251/250<r_*<201/200,
\tag{19}
\]

and `E'(r_*)>0`. Until that zero, both inactive gaps have the required
strict signs. At the zero the third-control gap is still strict and
the two-way edge crossing is transverse. The old control 1 is the
other tied vertex and supplies the outgoing maximizing germ, by the
same Hamiltonian switching-derivative argument used above.

This is an actual first event, rather than an arbitrary zero found
after a missed earlier event. It occurs at `x<0`, whereas the positive
critical point is `sqrt(mu_+)>0`. The hypothesized forced postcritical
continuation is therefore false for this window.

## 4. The necessary Casimir cap and the local cost do not exclude it

At the core center the minimizing group matrix is

\[
\mathsf M(0)=
\begin{pmatrix}qK_0/2&-1-\mu\\n_0&-qK_0/2\end{pmatrix}.
\]

The original physical maximizing frame costate is
`Lambda_1=-(3/2)M(0)`. Its determinant satisfies

\[
\det\Lambda_1=\frac94\left((1+\mu)n_0-K_0^2/12\right),
\qquad 213/100<\det\Lambda_1<107/50.
\tag{20}
\]

It lies in the negative elliptic component: the determinant is positive
and `M(0)` has negative upper-right entry. This component check is
necessary for the comparison with GLOBAL_COST_CASIMIR.

The determinant is even below the **actual** competitive cap, rather
than merely below the weaker rational upper bound `(313/210)^2`.
Indeed the elementary bounds

\[
\sqrt3>433/250,\quad \sqrt2<283/200,\quad
\log2<347/500
\]

give, from the exact octagon formula,

\[
A_{\rm oct}>
\frac{712718}{228750}>311/100.
\]

The classical bound `pi<22/7` follows, for example, by integrating
`x^4(1-x)^4/(1+x^2)>0` on `(0,1)`; its integral is `22/7-pi`.
Consequently

\[
\left(\frac{3A_{\rm oct}}{2(2\pi-A_{\rm oct})}\right)^2
>\left(\frac{2177}{1482}\right)^2>107/50>
\det\Lambda_1.
\tag{21}
\]

For the local cost, direct integration gives

\[
\frac{C_{\rm core}}{\sqrt3}
=\frac12\left[15/14+(1+\mu)(T_b-T_a)-(Z_b-Z_a)/3\right]
<9/7.
\tag{22}
\]

As `sqrt3<7/4`, the core costs less than `9/4`. The exact outgoing
vertex cost formula gives `Delta C(201/200)/q<1/80`; since `q<3/5`,
the last piece costs less than `3/400`. The incoming germ can be cut
with positive cost less than `1/100`. The whole six-piece window then
costs less than `907/400<A_oct`.

These are necessary local checks only. A small window cost and a
subcritical Casimir do not supply complete-period frame or cotangent
closure, a geometric embedding, or any variational minimality.

## 5. Finite rational certificate and audit boundary

For rational `z` in `(0,1)`, the identity

\[
\log\frac{1+z}{1-z}
=2\sum_{j=0}^{15}\frac{z^{2j+1}}{2j+1}+\mathcal R,
\qquad
0<\mathcal R<\frac{2z^{33}}{33(1-z^2)}
\tag{23}
\]

follows by integrating the geometric series. It gives the following
strict rational bounds; every denominator in this table is `10^18`:

| Logarithm | Lower numerator | Upper numerator |
|---|---:|---:|
| log(7/5) | 336472236621212930 | 336472236621212931 |
| log(6/5) | 182321556793954626 | 182321556793954627 |
| log(251/250) | 3992021269537452 | 3992021269537453 |
| log(201/200) | 4987541511039073 | 4987541511039074 |

Substituting these bounds into the displayed affine expressions gives
(13), (16), and (18). Expanding the quadratic determinant in (20) and
bounding each positive or negative coefficient with the corresponding
interval endpoints gives its stated bounds as well. The two cost
expressions are affine in the same logarithms. The `log 2` bound in
Section 4 uses the same series with `z=1/3` and four terms.

[The exact checker](../explorations/mixed_global_short_pad_certificate.py)
reconstructs the moments, both outer ties, the state and cotangent
rotation, the gap derivatives, the complete core concavity/convexity
bounds, the first-event bracket, and the rational budget comparisons.
Its inequalities are finite rational operations, with no sampling,
root solver, numerical ODE, or floating-point sign premise.

The reviewer and root each ran
`python explorations/mixed_global_short_pad_certificate.py`; all 71 exact
identities and rational sign checks passed with Python 3.12.14 and
SymPy 1.14.0.

The first-return factor is defined by its unique zero in the certified
rational bracket; no rounded decimal is used as an exact switch time.
No geometric sector test, embedded-boundary claim, first-pad external
switch, complete-period return, or minimality assertion is hidden in
this certificate. Universal M1, M2, M3, the remaining case-C comparisons,
the octagon inequality, and affine rigidity remain open.

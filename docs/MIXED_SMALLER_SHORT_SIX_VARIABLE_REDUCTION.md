# Six-variable necessary domain for the smaller short bridge

Date: 2026-11-07. Exact hand reduction. Its scalar exclusion is now
complete; see [the theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).
The target is the M2 branch in which the smaller turn adjacent to a
global minimum reverse centre belongs to a short bridge. Every scalar
below is reconstructed from the same actual normal multiplier.

The algebraic cost and endpoint formulas are in
[MIXED_GENERAL_SHORT_DEFECT_INTERFACE](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md).
This note specifies a compact comparison domain for those formulas.
It does not assert that every point of the comparison domain is an
actual trajectory or a complete period.

## 1. Actual hypotheses and six independent coordinates

Take a competitive geometrically eligible finite normal mixed period
with its true twisted state, frame and costate seam, free initial state,
positive arc durations and actual first-event conditions. The common
compact state bounds for the normalized balanced disk apply. Let a be
the globally smallest active margin. The established minimum structure
makes it a reverse centre.

Choose the incoming orientation so that its adjacent smaller turn has
ratio x and belongs to a short bridge. Its four active margins are
`a(alpha,beta,x,1)`. Write the other adjacent turn as ay, with `x<=y`.
The actual strict orders are

\[
1\le\alpha<x\le\beta\le\alpha x,\quad 1<x\le y,
\qquad
\alpha\ge\frac\beta x+\frac27(\beta-x).
\tag{1}
\]

Use the six scalar coordinates

\[
(x,\alpha,\beta,\rho,v,E),\qquad
\rho=\frac{a^2}{a^2+4},\quad r=\frac1{1+x}.
\]

For positive A,B,P define the continuous secant

\[
\operatorname{Sec}(A,B,P)
=1+\frac{B^2}{(A+B)(P+B)}
-\frac{B}{P-A}\log\frac{P+B}{A+B},
\]

with `Sec(A,B,A)=1-AB/(A+B)^2`. Set

\[
u=\operatorname{Sec}(1,x,\beta).
\tag{2}
\]

The actual second turn gives equality
`Sec(alpha,beta,x)=u`. The comparison domain retains only the necessary
one-sided inequality

\[
\operatorname{Sec}(\alpha,\beta,x)\le u.
\tag{3}
\]

Replacing an equality by (3) enlarges the scalar domain. The cost and
endpoint expressions remain defined algebraically on that domain. They
agree with the physical window precisely where the actual hypotheses
give the equal secants. A proof that the scalar defect is too large on
this enlarged domain would therefore exclude every actual period in
this branch. No off-locus point is used as a competing physical path.

## 2. Compact bounds and the smaller-turn estimate

The [compact geometric state domain](GLOBAL_MINIMIZER_COMPACTNESS.md),
as quantified in [SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md), gives
`a>=2/15`; the [reverse-centre scale bound](MIXED_REVERSE_CENTRE_SCALE_BOUND.md)
gives `a^2<12/17`. Thus

\[
\frac1{226}\le\rho<\frac3{20}.
\]

The smaller short turn satisfies
`u<=V(x)<3/2-log 2<13/16`, by
[MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md).
The [global mixed-angle theorem](MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md)
gives `gamma^2>27/256`, while the spectral cost bound gives
`gamma^2<23/125`. The exact normalization is

\[
\gamma^2=\frac{4uv-E^2}{16(1-\rho)^2},\qquad
\kappa=\sqrt{12\gamma^2},\qquad
\frac{27}{256}\le\gamma^2\le\frac{23}{125}.
\tag{4}
\]

Since `v<1`, these facts imply

\[
E^2<\frac{13}{4}
 -16\left(\frac{17}{20}\right)^2\frac{27}{256}
=\frac{12997}{6400}<\left(\frac{23}{16}\right)^2.
\tag{5}
\]

For the actual opposite turn, put `t=1/(1+y)<=r`. Central stationarity,
`v<=1-t+t^2`, and `rho<=rt` give

\[
E\le r+2t-\frac{1-u}{r}
\le3r-\frac{3}{16r}.
\]

Together with `E>-23/16`, this implies
`48r^2+23r-3>0`. That polynomial is increasing for `r>=0`, and its
value at `r=1/10` is `-11/50`. Consequently

\[
\boxed{r>1/10,\qquad x<9.}                       \tag{6}
\]

The preceding reverse centre has scale

\[
\rho_A=\frac{\alpha^2}{1/\rho+\alpha^2-1}<\frac3{20}.
\]

Using `rho>=1/226` gives
`alpha^2<675/17<(631/100)^2<(19/3)^2`. The strengthened order in (1) implies

\[
\beta\le\frac{x(7\alpha+2x)}{7+2x}
<\frac{561}{25}<\frac{45}{2}.
\tag{7}
\]

For (7), the displayed rational function is increasing separately in
x and alpha; evaluate it at `x=9,alpha=19/3`.
Thus a safe closed initial rectangle is

| Coordinate | Closed interval |
|---|---|
| x | [1,9] |
| alpha | [1,631/100] |
| beta | [1,45/2] |
| rho | [1/226,3/20] |
| v | [3/4,1] |
| E | [-23/16,9/20] |

The coupled inequalities below are essential; the rectangle alone is
not the actual domain.

The last rectangle bound also uses `E<=3rho<=9/20`, proved in
Section 3. The certificate uses the equivalent coordinates

\[
(r,\delta,\alpha,\rho,v,E),\qquad
x=(1-r)/r,\quad \beta=(1+\delta)x.
\]

The outgoing turn derivative gives
`u>1-(beta/x)/(1+beta/x)^2`. Combining this with `u<13/16`, and
writing `k=beta/x>=1`, gives

\[
3k^2-10k+3=(3k-1)(k-3)<0,
\quad\text{hence}\quad 0\le\delta<2.
\]

The weaker derivative is already a consequence of (3) on the enlarged
ordered domain: `Sec(alpha,beta,x)>=1-beta*x/(beta+x)^2`, since the
integrand decreases on `[alpha,x]` when `alpha<=x<=beta`.
A safe closed root box for the implemented coordinates is therefore

\[
\boxed{
[1/10,1/2]\times[0,2]\times[1,631/100]\times
[1/226,3/20]\times[3/4,1]\times[-23/16,9/20].}
\tag{7a}
\]

The strengthened order becomes `alpha>=1+delta(1+2x/7)`. The forward
turn derivative can be kept as the polynomial constraint
`(u-1)(2+delta)^2+(1+delta)>=0`. Both descriptions retain the same
actual coordinates, including their closed comparison boundaries.

## 3. Eliminating y and retaining rational pairing bounds

For fixed r,rho,u,v, admissible opposite turns obey

\[
\rho/r\le t\le r,\qquad v\le1-t+t^2.
\]

Therefore a necessary condition is

\[
\rho\le r^2,\qquad
\frac34\le v\le 1-\frac\rho r+\frac{\rho^2}{r^2}.
\tag{8}
\]

The central pairing as a function of t is

\[
\mathscr E(t)=\frac{u-1}{r}+\frac{v-1}{t}
              +1+r+t-\rho+\log\frac{\rho}{rt},
\qquad
\mathscr E'(t)=\frac{1-t+t^2-v}{t^2}\ge0.
\]

Its exact lower endpoint at `t=rho/r` is rational. For a strong rational
upper endpoint put `t0=rho/r` and `K0=1-v-t0`. The elementary bound
`log(t0/t)<=t0/t-1` gives

\[
\mathscr E(t)\le G(t):=\frac{u-1}{r}+r-\rho+t-\frac{K_0}{t}.
\]

By (8), `K0>=-t0^2`, so `G'(t)=1+K0/t^2>=0` for every `t>=t0`.
This monotonicity remains valid even beyond the true incident-norm
endpoint. Raising t to r is therefore legitimate, and `G(t0)=E_min`.
Every actual datum lies in

\[
\boxed{
\frac{u-1}{r}+\frac{(v-1)r}{\rho}
      +1+r+\frac\rho r-\rho
\ \le E\le\
\frac{u+v-2}{r}+2r-\rho+\frac\rho{r^2}.}
\tag{9}
\]

This upper endpoint improves the dropped-logarithm bound by
`1-rho/r^2>=0`. The coarser bound is insufficient for the proposed
defect exclusion and is not the bound used here. The new endpoint is
still a relaxation; the exact upper endpoint is
`mathscr E(min(r,(1-sqrt(4v-3))/2))`, as proved in the endpoint
interface note. The lower bound in (9) keeps the central zero-factor
face; neither endpoint is discarded because an actual duration is
strictly positive.

Useful additional necessary inequalities are

\[
\frac34\le u\le\frac{13}{16},\quad
u\le1-r+r^2,\quad
u\le1-\frac\alpha{\alpha+\beta}
             +\frac{\alpha^2}{(\alpha+\beta)^2},
\qquad E\le3\rho.
\tag{10}
\]

For the last bound, use both incident norm bounds to get

\[
E-3\rho\le-1+2r+2t-4\rho+\log\frac\rho{rt}.
\]

At fixed r,t the right side increases with rho for `rho<=rt<=1/4`;
at `rho=rt` it equals `-(1-2r)(1-2t)<=0`.

## 4. The rational transported outer-root condition

Define

\[
\sigma=\alpha^2-1,\quad q=1/\rho,\quad P=q+\sigma,
\quad Q=\alpha(\alpha+\beta),\quad
D=(\alpha+\beta)^2+(1+x)^2-(\beta+x)^2,
\]
\[
\lambda=q/P,\quad d=D/P,\quad T=P/Q,\quad
T_B=Q/\alpha^2,\quad \rho_A=\alpha^2/P,
\]
\[
w=\lambda^2v+d^2u-d\lambda E,
\qquad E_L=2du-\lambda E.
\tag{11}
\]

The actual outer reverse centre supplies a descending root in `(2,T)`.
Retain the necessary conditions

\[
T\ge2,\qquad \frac34\le w\le1-T^{-1}+T^{-2},
\qquad E_L\le3\rho_A.
\tag{12}
\]

Its maximum residual is bounded above by the rational convex chord in
[MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE, Section 2](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE.md).
That bound uses only T, T_B, u, w and E_L; its derivation does not
require the central zero-duration identity. Put

\[
z=\frac{T-2}{T+2},\qquad
m_0=2(1+z)+\frac23z(1+z)^2,
\]
\[
\boxed{
\overline R=m_0(w-3/4)+(u-1)T_B+1+T_B^{-1}
 -(TT_B)^{-1}-E_L-2z-\frac23z^3\ge0.}             \tag{13}
\]

The inequality follows because an actual descending root makes the
true interior maximum positive, while the convex chord and the cubic
lower bound for `log(T/2)` give this upper bound. Replacing positivity
by `>=0` enlarges the domain. Formula (13) is regular at T=2.

The strict-star condition at the two-turn switch is
`a^2 beta*x<4`. Together with the scale and T bounds, it gives the
following useful coupled restriction:

\[
\boxed{
\rho\le\min\left\{r^2,\frac3{20},
\frac3{17\alpha^2+3},
\frac1{1+\alpha^2+2\alpha\beta},
\frac1{1+\beta x}\right\}.}                    \tag{14}
\]

## 5. Hamiltonian, angle and defect tests

The central omitted-control condition in the endpoint interface gives

\[
(1-\rho-v)r^2+\rho[E-(1-\rho)]r
                  +\rho[(1-\rho)-u]\ge0.         \tag{15}
\]

The condition (15) is exactly the lower endpoint of (9): its left
side equals `rho*r*(E-E_min)`. Thus they are two algebraic forms of one
constraint. The upper endpoint of (9) and the last bound in (8) have
useful polynomial forms

\[
r^2E\le r(u+v-2)+2r^3-\rho r^2+\rho,
\qquad r^2(1-v)-\rho r+\rho^2\ge0.
\]

The actual middle switch and outer entrance also satisfy the two
stationary-slack inequalities `N_mid>=0` and `H_A>=0` established by
the exact physical-matrix identities (M)--(O) in the endpoint interface.
They involve the transported same multiplier, and are retained in the
certificate domain.

Let `mathcal A,mathcal B,C_br` be the exact rational endpoint and
cost expressions in that note. An actual competitive window also has

\[
\mathcal A>0,\qquad 0<\mathcal B<\mathcal A,
\qquad
C_{\rm br}+(\kappa+3/2)
\left(\frac\pi3-
\arctan\frac{\sqrt3\mathcal B}{\mathcal A}\right)
\le A_{\rm oct}.                                \tag{16}
\]

In addition, the determinant-one endpoint modulus gives
`mathcal A+mathcal B>=4T_kappa`, and hence
`mathcal A>=2T_kappa`, where `T_kappa=2kappa(1-rho)^2`; see (A) in
the endpoint interface. The actual angle branch and positive polar
increment justify these signs without imposing them on every point of
a comparison rectangle.

The compact comparison problem is therefore explicit: retain (1)--(4)
with weak boundary versions, the rectangle in Section 2, and
(8)--(16). It is sufficient to prove that no point satisfies all of
them. Conversely, a surviving scalar point does not prove that an actual
period exists; it would only show that these necessary conditions need further
refinement.

The proposed interval certificate may use (16) only on a full rectangle
where its denominator and analytic branches are defined. Boundary
crossings require another sign exclusion, a continuous reformulation,
or subdivision. All secants at removable zero-duration faces must use
their continuous divided-difference extension. Domain contractions
must keep all actual data, and every nonempty retained box must either
have a rigorous contradiction or remain explicitly unresolved.

## 6. Regular analytic forms for an exact checker

Every continuous secant over positive endpoints lies in `[3/4,1]`:
its integrand is `3/4+(s-B)^2/[4(s+B)^2]`. This bound holds on the
entire positive domain, including reversed endpoint order. An interval
implementation may therefore intersect the **value** enclosure for u
with `[3/4,1]` without restricting its derivatives to a feasible subset.
Combined with `v>=3/4` and `|E|<=23/16`, this gives the whole-rectangle
bound `4uv-E^2>=47/256>0`, keeping the Casimir square root regular.

A secant has a removable quotient at its zero-duration face. A form
regular there is

\[
q=\frac{P+B}{A+B},\quad c=\frac{B}{A+B},\qquad
\operatorname{Sec}(A,B,P)=1+\frac{c^2}{q}-cL(q),
\quad L(q)=\frac{\log q}{q-1},\quad L(1)=1.
\]

Put `w=(q-1)/(q+1)`. For every `q>0`,

\[
L(q)=(1-w)A(w),\qquad
A(w)=\sum_{n=0}^{\infty}\frac{w^{2n}}{2n+1}.
\]

For a truncation through n=N and `b>=|w|`, `b<1`, upper bounds for the
absolute tails of A, A' and A'' are respectively

\[
\frac{b^{2N+2}}{(2N+3)(1-b^2)},\qquad
\frac{b^{2N+1}}{1-b^2},\qquad
\frac{b^{2N}[(2N+1)-(2N-1)b^2]}{(1-b^2)^2}.
\tag{17}
\]

The A and A'' tails are nonnegative. The A' tail has the sign of w;
on an interval crossing zero it may be enclosed symmetrically. These
bounds follow by replacing each remaining coefficient by the indicated
geometric-series coefficient. The derivatives of the *actual* L are

\[
L'(q)=\frac{(1-w)^2}{2}[(1-w)A'(w)-A(w)],
\]
\[
L''(q)=\frac{(1-w)^4}{4}[(1-w)A''(w)-2A'(w)]
       -\frac{(1-w)^3}{2}[(1-w)A'(w)-A(w)].
\tag{18}
\]

Thus actual value, gradient and Hessian enclosures can be evaluated
without dividing by q-1. Derivatives of a finite truncation must not be
silently substituted for the derivatives in (18).

For the angle, (16) yields the regular transformed argument

\[
s=\frac{3\mathcal B-\mathcal A}
        {\sqrt3(\mathcal A+\mathcal B)},\qquad
\theta_{\rm br}=\frac\pi6+\arctan s,
\qquad |s|<1/\sqrt3.
\]

For `|s|<=b<1`, truncating the odd alternating series for atan through
`s^(2N+1)/(2N+1)` has absolute error at most
`b^(2N+3)/(2N+3)`. Its actual derivatives are
`1/(1+s^2)` and `-2s/(1+s^2)^2`. Consequently (16) may be checked as

\[
C_{\rm br}+(\kappa+3/2)(\pi/6-\arctan s)\le A_{\rm oct}.
\tag{19}
\]

Although the actual constraints imply q>=1 and `|s|<1/sqrt(3)`, a
covering rectangle may contain points violating those coupled
inequalities. The analytic enclosures and Taylor derivatives must cover
that entire rectangle. Internal expression intervals must not be
clamped to feasible-point-only bounds before Taylor's theorem is used.
The series in (17)--(18) also work when q<1; if a rectangle does not
provide the needed positive denominators and an argument bound b<1,
the checker must use a different valid enclosure or subdivide.

## 7. Status

The compact domain is now excluded by the completed directed-interval
cover: 107,977 nodes, 53,989 leaves, zero unresolved boxes, maximum
depth 37. The [exclusion theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md)
and [independent audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md) record
the mathematical interface, unchanged source and successful replay.

Earlier numerical searches located a two-turn defect excess near
`0.00153978`; wider searches showed that the weaker dropped-logarithm
upper bound admitted false opposite-turn data. Those probes motivated
the stronger bound (9) but are not proof premises. The completed cover
uses directed arithmetic and all stated necessary constraints. The
smaller-nonshort branch and full M2 remain open.

# The smaller-short ratio is less than twelve fifths

Date: 2026-11-08 UTC. Complete hand assembly, accepted in the
[independent interface review](MIXED_SMALLER_SHORT_LARGE_RATIO_INTERFACE_AUDIT.md).
The boundary inequalities used below
are explicit algebraic statements with separate independent reviews.
No interval cover, numerical optimization, or executable sign test
is a premise.

## 1. Statement on the original bridge

Consider the actual smaller-short bridge in
[the six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md),
with its common normal covector, two equal short secants, genuine
external reverse switch, and competitive whole-period hypotheses.
Then

\[
\boxed{x<\frac{12}{5}.}
\tag{1}
\]

Consequently the diagonal parameter and the outer pairing satisfy

\[
\boxed{D>0,\qquad E_L>0.}
\tag{2}
\]

The latter conclusion follows directly from
[the positive-pairing theorem](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md)
after (1) has been proved. It applies to the original bridge and to
the fixed-geometry root comparisons specified there.

This theorem excludes the entire large-ratio alternative. It does
not prove the remaining physical two-turn cost inequality.

## 2. Start with a strictly positive scalar test at the actual root

Suppose for contradiction that x>=12/5. The retained actual bounds
give

\[
\frac{12}{5}\le x<9,\qquad
1\le\alpha<x\le\beta,\qquad
\frac34<u\le\frac{13}{16},
\]
\[
r=\frac1{1+x},\quad
0<\rho\le r^2,\quad
q=\rho_A=\alpha^2\lambda\rho<\frac17,
\quad r_A=\frac\alpha{\alpha+\beta},\quad T=\frac{r_A}{q}.
\tag{3}
\]

The outer scale bound applies to this reverse centre even when it
is not the selected minimum; its scope is proved in
[the reverse-centre scale audit](HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT.md).
The actual incoming norm is
u=Sec(1,x,beta)=Sec(alpha,beta,x). No replacement norm is used in
the scale comparisons below.

Let tau be the actual outer descending root. Genuine reverse
transversality gives 2<tau<T. Its exact residual and norm satisfy

\[
R_\tau(t,v)=0,\qquad w(t,v)>\frac34.
\]

Define at this original geometry

\[
G_\tau(t,v):=R_\tau(t,v)+\frac12\left(w(t,v)-\frac34\right)>0.
\tag{4}
\]

The norm floor has thus been used at an actual point, before any
comparison. The positive-factor calculation in
[the floor-weighted envelope](MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md),
Section 1, permits v to increase to U(t), followed by decreasing t
to t0=rho/r. It proves

\[
0<G_\tau(t,v)\le G_\tau^*.
\tag{5}
\]

This step includes D>S and D<=S. In the former case the additional
half in the multiplier is controlled by
4Q-5(D-S)>=x(3x-5)>0, where Q=alpha(alpha+beta).
It is the combined scalar G that increases; no separate floor on
the comparison norm is needed.

## 3. Only two positive scale faces remain

Hold the original shape, incoming norm u, and p=tau*q fixed. The
exact scale identity is

\[
G^*_{p/q}(q)=C(p)+\frac18
 +q\left(L(p)-\frac{A_1}{2}\right)+\frac{q^2A_2}{2}.
\tag{6}
\]

The coefficients are those explicitly defined in
[the envelope scale theorem](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md).
Write

\[
q_c=\frac{\alpha^2}{x(x+2)+\alpha^2},\qquad
q_{\max}=\min\{q_c,1/7,p/2\}.
\tag{7}
\]

The original q lies in (0,q_max]. The
[combined scale theorem](MIXED_SMALLER_SHORT_ROOT_FLOOR_SCALE.md)
proves that (6) is bounded above by its values at 0 and q_max.
For A2>=0 this follows from convexity; for A2<0 that theorem proves
its derivative is greater than 1/10. This is an exhaustive sign
alternative, so global positivity of A2 is not assumed.

Section 5 of the floor-weighted envelope proves G*(0)<0, using the
unchanged exact shape and incoming norm. Equations (5)--(7) therefore
force

\[
G^*_{p/q_{\max}}(q_{\max})>0.
\tag{8}
\]

If q_max is either q_c or 1/7, the comparison has reached one of
the desired scale faces with 2<=tau<=T. Otherwise q_max=p/2 and
tau=2. The
[tau-two scale theorem](MIXED_SMALLER_SHORT_ROOT_FLOOR_TAU_TWO_SCALE.md)
then strictly increases G2* as q increases to

\[
\widehat q=\min\{q_c,1/7\}.
\tag{9}
\]

That theorem uses the unchanged incoming secant and its proved
uniform lower bound. It requires neither T>=2 nor an outgoing floor
at the comparison point. Thus it remains valid if this second scale
motion passes T=2.

We have obtained a positive scalar value on either q=q_c or q=1/7.
Its duration parameter is either in [2,T], or is exactly tau=2
with no restriction on T. Ties between the minima in (7) or (9)
cause no difficulty.

## 4. Incoming-norm substitution is made after the scale motions

The exact equal secants imply alpha/beta<3/4 on the present range.
The fixed geometry consequently satisfies D/Q<1. Section 4 of the
floor-weighted envelope proves

\[
\partial_uG_\tau^*>0\qquad(2\le\tau\le T)
\tag{10}
\]

at every scale under consideration. For the separate tau=2 case,
the same coefficient estimate remains valid even if T<2. Indeed,
when D>=0 it uses the direct bounds

\[
2d\le4/7<1\quad(x\ge5/2),\qquad
2d\le102/175<1\quad(12/5\le x\le5/2).
\tag{11}
\]

For D<0 the coefficient is positive directly from its grouped
formula. These are scalar derivative bounds; they do not depend on
any newly asserted incident ceiling.

At q=1/7, increase u to the proved incoming majorant

\[
\bar u=\frac34+
\frac{2(x-1)^3/[(x+1)(35x+13)]+(\beta-x)^3/(48x^2)}{\beta-1}.
\tag{12}
\]

At q=q_c use instead the larger convenient majorant

\[
\widehat u=\frac34+
\frac{2(x-1)^2}{(x+1)(35x+13)}
\frac{x-1+(\beta-x)/8}{\beta-1}.
\tag{13}
\]

The legitimacy of (13) on the central face, including the
inequality bar u<=widehat u, is proved in Section 2 of
[the central tau-two sign](MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN.md).
The comparisons (10)--(11) apply before enlarging the exact shape
domain for the boundary sign arguments. They are affine in u, so
the derivative sign continues throughout each norm substitution.

In particular the positive scalar value obtained in Section 3
remains positive after the appropriate substitution. The original
incoming norm and its ceilings were retained until all uses of the
scale theorems had ended.

## 5. Three elementary duration tests control each face

For every y>0,

\[
\log y\le\min\left\{y-1,\frac54y-\frac{11}{9}\right\}.
\tag{14}
\]

The first inequality is the tangent at 1. For the second, integrate
2/(1-z^2)>2 from 0 to 1/9 to obtain log(5/4)>2/9, and use the
tangent at y=4/5. The two displayed affine functions agree at y=8/9.

At a fixed scale face, put y=tau/T in (14). On each side of its
possible breakpoint, the resulting majorant for G* has the form
a*tau+1/tau+b. Its second derivative is 2/tau^3>0. Hence on [2,T]
its maximum is attained at one of the endpoints of these at most
two intervals: tau=2, tau=T, and tau=8T/9 if the breakpoint is
inside [2,T].

The three sufficient tests are therefore obtained by replacing
(tau,log(tau/T)) by

\[
\left(2,\frac5{2T}-\frac{11}{9}\right),\qquad
(T,0),\qquad(8T/9,-1/9).
\tag{15}
\]

At tau=2 the second line of (14) alone may exceed the minimum;
proving the larger value negative is sufficient. If T<2, no reversed
interval is used: only the standalone tau=2 value from (15) is
needed. Its logarithm bound remains valid for y>1.

## 6. Every required boundary value is strictly negative

On the central face, q_c<=1/7 implies

\[
\alpha^2\le\frac{x(x+2)}6,
\qquad
\alpha\le\frac{5x+4}{12},
\tag{16}
\]

where the second inequality follows from
((5x+4)/12)^2-x(x+2)/6=(x-4)^2/144>=0.
The exact strong short-order inequality gives

\[
x\le\beta\le x+
\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{17}
\]

These are exactly the enlarged domains of the central signs.
[The central tau-two theorem](MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN.md)
proves the first test in (15) strictly negative.
[The central duration-face theorem](MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES.md)
proves both other tests strictly negative. The latter is accepted
in its [independent review](MIXED_SMALLER_SHORT_CENTRAL_DURATION_AUDIT.md).

On the outer face, 1/7<=q_c implies

\[
\alpha^2\ge\frac{x(x+2)}6,
\qquad \alpha\ge\frac{22x+20}{55}.
\tag{18}
\]

The final inequality follows from the positive quadratic difference
printed in the outer-face theorem. The exact strong lower order
and global upper order give

\[
x+\frac{4x(\alpha-1)}{5x+4}\le\beta
\le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{19}
\]

[The outer-scale theorem](MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_SIGN.md)
proves all three tests (15) strictly negative on (18)--(19).
Its complete coefficient-norm argument is accepted in the
[independent outer-scale review](MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_AUDIT.md).

Thus every possible positive scalar value from Sections 3--4 is
strictly negative by Section 5 and the boundary signs. This is the
required contradiction. It proves (1), and hence (2).

## 7. Scope in the hand proof

The argument starts from the actual common-covector root and its
strict norm floor. All subsequent objects are explicit scalar upper
comparisons. The whole-period cost and Casimir cap are not assigned
to any artificial endpoint, and no artificial point is asserted to
be a closed or admissible trajectory. The original competitive
hypotheses supply the actual compact-domain bounds and reverse-centre
scale bound; the contradiction then uses only the displayed scalar
signs. It is independent of the number of switches in the period.

The smaller-short problem is now restricted to x<12/5 and positive
D,E_L. Its final physical-cost contradiction remains a separate
obligation in the global proof.

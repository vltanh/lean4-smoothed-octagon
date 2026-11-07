# A full symmetric M1 interval has no closed PMP occurrence

Hand proof, 2026-11-07 UTC. Self-reviewed, with exact supplementary
polynomial checks. No independent mathematical review, Lean, Lake or CI.

## Theorem

For every h in the closed interval [11/10,13/10], define

\[
z(h)=\frac{-3h^3+10h^2-7h+2}{3h-2},\qquad
\kappa(h)=\frac2{\sqrt{2+3z(h)}}.
\]

Consider the six positive vertex pieces with word **021210**, all six
factors equal to h, and initial determinant-one margins

\[
p(0)=\kappa(h)(1,2,z(h)).
\tag{1}
\]

**None of these windows can occur, even with cuts inside its outer arcs,
in a closed strict-star PMP extremal with the actual twisted endpoints.**
In particular none can occur inside a global minimizer. This conclusion
needs no total-cost assumption.

If a normal PMP lift of such a window exists, its outgoing last vertex
is forced to the strict-star boundary. From the end of the displayed
six-piece window, the remaining physical time is exactly

\[
\boxed{\frac{\kappa(h)}2\log 3.}
\tag{2}
\]

There is also an open neighborhood of this compact family within the
PMP-window domain with the same exclusion. No numerical radius or coverage
of all asymmetric M1 inputs is claimed. **The full M1 case remains open.**

The h=5/4 member is the explicit strong local minimum in
[LOCAL_L3_STRONG_MINIMUM](LOCAL_L3_STRONG_MINIMUM.md). The finite-escape
criterion used here is proved in [VERTEX_EVENT_ESCAPE](VERTEX_EVENT_ESCAPE.md).
The numerical discovery tests are not premises of this proof.

## 1. Exact states and endpoint rank

Put

    d=3h-2, U=3h^2-10h+4, V=3h^2-9h+2,
    b=(2-h)(3h-1)/d, c=h(3h-1)/d,
    e=(-3h^3+13h^2-11h+2)/d,
    f=(-6h^3+17h^2-12h+2)/(h d).

The seven raw margin triples, before multiplying by kappa, are

| Stage | Raw margins |
|---|---|
| Initial | (1,2,z) |
| After 0 | (1,3h-1,b) |
| After 2 | (e,c,b) |
| After 1 | (f,c,c) |
| After 2 | (e,b,c) |
| After 1 | (1,b,3h-1) |
| After 0 | (1,z,2) |

Each row follows from the vertex update

    (a,b,c) -> (a,(a+b)h-a,(a+c)/h-a)

in active/growing/decreasing order. The initial quadratic invariant is
2+3z, so the stated kappa makes it exactly four. All rows are positive:
d>0, h<2 and 3h-1>0; positivity of the three remaining numerators is
certified in Section 4's last three polynomial rows. Monotonicity on each
vertex arc proves strict star throughout each whole arc, not just at the
seven endpoints.

Use the triangular matrices

    D0=[[-1,0],[0,1]], D1=[[1,-2],[0,-1]], D2=[[1,0],[2,-1]],
    Ti(q)=((q+q^-1)I+(q^-1-q)Di)/2.

Let F be the chronological product of the six Ti, and use endpoint chart

    E=(F00,F01,F10,p0,end,p1,end)

with raw terminal margins. At the stated input, F00=2-h^2>0, so the three
frame entries are a valid local chart on determinant-one matrices. The two
raw state margins likewise form a chart, since their positive sum fixes
the omitted margin through the invariant.

Let J be the 5-by-6 derivative of this endpoint chart in the **six independent
log factors**, holding the initial state fixed. Deleting its second column
gives the exact minor

\[
\det J_{\widehat{2}}
=\frac{32(h-1)^2(3h-1)(h^2-2)U}{h^2d^2}>0.
\tag{3}
\]

The index here means the second chronological column. All factors except
the two displayed negative ones are positive; h^2-2<0 and U<0 on this
interval. The minor is therefore nonzero. It follows that any free-time
PMP occurrence is normal and its normalized adjoint is unique, by the
full-rank-window argument in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md), Section 4. The unaudited
claim in GLOBAL_NORMALITY is not needed.

For a hand verification of (3), differentiate the displayed Ti product
using dTi/d(log q)=-Di Ti, and differentiate the affine margin update.
Eliminate the three frame columns, then the two state columns. Appendix A
also supplies an explicit endpoint multiplier and exact identities for the
same five-coordinate system; the supplementary checker reproduces both.

## 2. The outgoing escape data

Rotate old control 0 to control 1 at the start of the last piece.
The rotated raw margins are (3h-1,1,b). In the notation of
VERTEX_EVENT_ESCAPE, with q_star=1/sqrt(3), exact substitution gives

\[
a=\frac{h(3h-4)}{\sqrt3 U},\qquad
W=\frac{\kappa^2}{4},\qquad R=3h,\qquad p_w(a)=0.
\tag{4}
\]

The tie p_w(a)=0 is the genuine preceding 1-to-0 switch in the original
labels. Define the two polynomials, affine in L=log h,

\[
\begin{aligned}
P(h,L)={}&(-30h^4+108h^3-100h^2+24h)L\\
 &+6h^6-35h^5+114h^4-245h^3+280h^2-144h+24,\\
E(h,L)={}&(-26h^3+40h^2-12h)L\\
 &+6h^5-21h^4+56h^3-87h^2+58h-12.
\end{aligned}
\tag{5}
\]

The unique adjoint of any occurrence has

\[
\mu-a^2=\frac{2(3h-1)P(h,L)}{3h(h-1)U^2},
\tag{6}
\]
\[
B_0=-\frac{4(h-1)U^2(hL-h+1)}{d^2V^2},\qquad
B_1=-\frac{\sqrt3 U E(h,L)}{3h(h-1)dV}.
\tag{7}
\]

These are exact endpoint/needle identities, not fitted formulas. Appendix A
specifies the linear multiplier and the derivative recipe proving them.
Section 4 supplies their uniform signs.

Since h<4/3 and U<0, equation (4) gives a>0. Also

a/q_star = h(3h-4)/U <1,

because U<0 and h(3h-4)-U=6h-4>0. Thus 0<a<q_star.
The exit ratio is R=3h>=33/10>16/5.

## 3. Uniform logarithm bounds

Set v=(h-1)/(h+1) in (0,1). The integral for log h, or its positive
artanh series, gives

\[
\ell(h)=\frac{2(h-1)}{h+1}<\log h<
 u(h)=\frac{(h-1)(h^2+10h+1)}{6h(h+1)}.
\tag{8}
\]

For the upper bound, the terms after the first satisfy

    2 sum_{j>=1} v^(2j+1)/(2j+1) < 2v^3/[3(1-v^2)].

Both P and E are affine in L. It therefore suffices to check their signs
at BOTH endpoints ell(h) and u(h); no assumption about the signs of their
L-coefficients is required. Direct polynomial collection gives

\[
\begin{aligned}
P(h,\ell)&=(h-1)^2 P_-/ (h+1),\\
P(h,u)&=2(h-1)^2(h+2)P_+/[3(h+1)],\\
E(h,\ell)&=(h-1)^2 E_-/ (h+1),\\
E(h,u)&=2(h-1)^2 E_+/[3(h+1)],
\end{aligned}
\tag{9}
\]

where

    P_- = 6h^5-17h^4-21h^3+120h^2-120h+24,
    P_+ = 9h^4-51h^3+105h^2-82h+15,
    E_- = 6h^4-3h^3-29h^2+46h-12,
    E_+ = 9h^4-11h^3-27h^2+56h-15.

## 4. A finite rational sign table

Let h=(11+2t)/10 with t in [0,1]. In each row below, if the listed
coefficient sequence is b_0,...,b_n and the scale is m, the identity is

\[
m\,Q((11+2t)/10)=\sum_{j=0}^n b_j\binom nj t^j(1-t)^{n-j}.
\tag{10}
\]

All Bernstein basis functions are nonnegative and sum to one. Every
coefficient in a row has the same strict sign, proving that sign over the
entire closed interval.

| Polynomial Q | Scale m | Bernstein coefficients b_0,...,b_n |
|---|---:|---|
| P_- | 25000 | -149441, -128256, -106357, -84208, -62145, -40328 |
| P_+ | 10000 | -28541, -22648, -16619, -10682, -4921 |
| E_- | 30000 | 249048, 253929, 259742, 267891, 280068 |
| E_+ | 10000 | 124659, 126952, 129381, 132518, 137079 |
| -3h^3+10h^2-7h+2 | 3000 | 7221, 8043, 8869, 9627 |
| -3h^3+13h^2-11h+2 | 3000 | 4911, 6253, 7719, 9237 |
| -6h^3+17h^2-12h+2 | 750 | 1038, 1219, 1372, 1461 |

Each row is a finite polynomial identity verifiable by expansion. This
establishes P(h,log h)<0 and E(h,log h)>0 from (8)-(9), and proves the
remaining positive state numerators used in Section 1.

The inequalities U<0 and V<0 follow without a table: both are decreasing
on the interval, and their values at 11/10 are -337/100 and -427/100.
Moreover, (8) implies

    h log h-h+1 > h ell(h)-h+1 = (h-1)^2/(h+1)>0.

Equations (6)-(7) now give

\[
\mu<a^2,\qquad B_0<0,\qquad B_1<0.
\tag{11}
\]

Together with (4), these satisfy every hypothesis of the improved escape
criterion R>=16/5. The outgoing two-way tie is transverse since mu-a^2<0,
and the third vertex has a strict gap. That same last vertex is forced
until the star boundary. A genuinely closed twisted lift could be
continued across every seam indefinitely in strict star, which is the
contradiction proving the theorem.

The final displayed arc has factor h, while the boundary factor measured
from its start is R=3h. Its remaining time is therefore
sqrt(W) log(R/h)=(kappa/2) log 3, proving (2).

## 5. Nearby asymmetric PMP inputs

At partial factor r=101/100 of the last arc, all escape inequalities are
strict, including p_w<0. This point lies inside that arc for every h in
the stated interval. The rebased exit ratio obeys

    R_new >= (33/10)/(101/100) = 330/101 > 16/5.

The derivative B_S is still negative there: B_SS<0 before r=R/2, and
101/100<R/2 throughout this interval. The other strict signs follow from
the escape proof. The selected endpoint minor (3) stays nonzero, so the
normal covector of any nearby PMP input is a smooth function of its window
parameters. State and covector transport to this interior point is smooth.

Strictness and compactness of h in [11/10,13/10] thus give an open
neighborhood of this entire family, relative to the normal-PMP M1 domain,
with the same forced escape. This is an existence statement for a common
neighborhood; it is NOT a certified numerical box or the whole M1 domain.

## Appendix A. Reproducible endpoint algebra

The raw objective for fixed initial raw margins is

    I = sum_j a_j[(a_j+b_j)(q_j-1)+(a_j+c_j)(1-q_j^-1)-a_j log q_j]/8.

The physical cost is sqrt(12)*kappa^2 I. In taking derivatives of the six
independent factors, the initial raw margins and kappa are held fixed.
Their dependence on the reference h is not differentiated.

Define a polynomial from an ascending coefficient list by
poly([c0,...,cn])=sum c_j h^j. The following table specifies
N_j=poly(constant list)+L poly(L list):

| N_j | Constant coefficients, ascending | L coefficients, ascending |
|---|---|---|
| N0 | -24,200,-622,873,-568,186,-72,27 | 0,-24,176,-432,388,-78,-18 |
| N1 | -24,192,-568,771,-553,257,-93,18 | 0,-24,172,-408,354,-90 |
| N3 | 24,-224,846,-1657,1869,-1338,660,-207,27 | 0,24,-184,524,-660,342,-54 |
| N4 | -24,208,-646,875,-518,141,-63,27 | 0,-24,176,-432,388,-78,-18 |

The endpoint multiplier, ordered as the five coordinates in Section 1, is

\[
\nu=\left(
-\frac{N_0}{8h(h-1)d^2(h^2-2)},
-\frac{hN_1}{16(h-1)d^2(h^2-2)},
\frac{hN_1}{16(h-1)d^2(h^2-2)},
-\frac{N_3}{8h^2(h-1)dU},
\frac{N_4}{8h^2(h-1)dU}
\right).
\tag{12}
\]

Differentiation of the displayed product, state update and raw cost gives
J^T nu=dI. To verify using only product rules, propagate the state derivative
columns da,db,dc on an arc with independent log-factor direction epsilon:

    db_new=(da+db)h+(a+b)h epsilon-da,
    dc_new=(da+dc)/h-(a+c)epsilon/h-da.

For the raw arc cost a M/8, where
M=(a+b)(h-1)+(a+c)(1-h^-1)-aL, use

    dM=(da+db)(h-1)+(a+b)h epsilon
       +(da+dc)(1-h^-1)+(a+c)epsilon/h-da L-a epsilon.

These recurrences, the initial zero state derivatives, and dTi=-Di Ti
verify all six equations J^T nu=dI and the minor (3) by finite algebra.

For the last arc, split its factor h into r and h/r and insert a new
factor exp(epsilon) between them. Let Delta_j(r) be the derivative of
I-nu.E with inserted old vertex j. At r=1, the same finite calculation gives

\[
\Delta_1(1)=0,\qquad
\Delta_1'(1)=-\frac{(3h-1)P(h,L)}{8h(h-1)d^2},
\]
\[
\Delta_2(1)=\frac{(h-1)(3h-1)^2(hL-h+1)}{d^2},
\]
\[
2\Delta_2(1)+\Delta_2'(1)
=\frac{(3h-1)E(h,L)}{8h(h-1)d}.
\tag{13}
\]

Here primes mean differentiation in r, not physical time. With rotated
w0=3 kappa^2(1+b)^2/16 and c=W/(q_star-a), the positive-clock conversion
in VERTEX_EVENT_ESCAPE gives

    mu-a^2 = -kappa^2 Delta_1'(1)/w0,
    B0 = -(4 kappa^2/3) w0 Delta_2(1),
    B1 = -(4 kappa^2/3)(w0/c)[2 Delta_2(1)+Delta_2'(1)].

Substitution yields (6)-(7). Thus all coefficients of the escape test are
explicitly connected to the actual unique endpoint covector, rather than
assigned independently.

## Validation and scope

[The exact checker](../explorations/m1_interval_certificate.py) reconstructs
the state and frame derivatives, verifies the explicit multiplier, the
minor, all needle identities and the seven Bernstein rows. It passed with
Python 3.13.5 and SymPy 1.14.0: 31 exact identities, including seven
uniform-sign table rows. The finite table and logarithm arguments above
are the hand proof; symbolic evaluation is supplementary.

This result is a uniform exclusion of one explicit parameter interval and
nearby PMP windows, not a classification of all eight M1 input parameters.
No radius for the nearby region, universal case-C closure, unrestricted
Reinhardt inequality, affine uniqueness, independent review, or Lean
kernel validation is claimed.

# Scale monotonicity of the negative-diagonal short residual at tau=2

Date: 2026-11-08 UTC. Scalar hand lemma. This is a further endpoint
reduction, not the full smaller-short exclusion or a physical-cost
comparison.

Use the normalized outer scale q=rho_A and fixed short geometry of
[the scale reduction](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md).
Write
\[
S=1+x,\quad \varepsilon=1-\alpha^{-2},\quad
\delta=D/\alpha^2,\quad E_0=S(u-1)+S^{-1}.
\]
The necessary short domain gives x<9, alpha>=1 and
3/4<=u<=13/16. On D<=0, the
[pairing theorem](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md)
also gives x>12/5. Thus the following enlarged closed domain suffices:
\[
\frac{17}{5}\le S\le10,\qquad
0\le\varepsilon\le1,\qquad \delta\le0,
\qquad\frac34\le u\le\frac{13}{16},
\qquad0<q\le\frac17.
\tag{1}
\]
The limiting value epsilon=1 is included only to simplify the scalar
comparison; actual finite alpha has epsilon<1.

**Theorem.** At fixed geometry and incoming norm, the upper-envelope
residual with tau=2 satisfies
\[
\boxed{\frac{d}{dq}R_2^*(q)>0.}
\tag{2}
\]
The derivative changes q with tau fixed. It is different from the
already proved affine comparison at fixed p=tau*q.

## 1. Write the derivative as a quadratic

Put a=1-epsilon and define
\[
A_{20}=\varepsilon^2+\varepsilon Sa+S^2a^2>0,
\quad K=(2S-1)a-\varepsilon E_0>0,
\]
\[
H=-E_0-u,\quad C_0=2+\varepsilon(3+E_0),\quad d=-\delta\ge0.
\tag{3}
\]
Here E_0<0, since
\(E_0\le-3S/16+1/S<0\) on (1). Also
\[
-\frac{12}{5}\le E_0<0,
\qquad H\le\frac{33}{20}.
\tag{4}
\]
Indeed \(E_0\ge-S/4+1/S\ge-12/5\), and
\(H=S(1-u)-1/S-u\) increases with S and decreases with u.
Its maximum is therefore at S=10,u=3/4.

The scale coefficients in the cited note obey
\[
A_2=A_{20}+dK+ud^2,
\qquad 2A_1+1+A_3=C_0+2dH.
\tag{5}
\]
These identities follow by collecting the terms in delta and using
\(n=S(1-\varepsilon)\). The explicit residual at tau=2 is
\[
R_2^*(q)=\frac32+\frac{u-1}{r_A}+r_A+E_0
 +\log\frac{2q}{r_A}
 -(2A_1+1+A_3)q+2A_2q^2.
\]
Consequently
\[
\boxed{
q(R_2^*)'=1-C_0q+4A_{20}q^2
 +4u(dq)^2-2(H-2Kq)dq.}
\tag{6}
\]

We will use
\[
C_0\le5-u-H,\qquad K\ge u+H>0.
\tag{7}
\]
For the first, 3+E_0>0 by (4), so epsilon<=1 applies in the
correct direction. For the second, K is the convex combination
of 2S-1 and -E_0=u+H, and
\(2S-1>-E_0\) follows directly from (1).

## 2. The range H<=5/4

If H<=0, the last two terms in (6) are nonnegative. Since C_0<=5,
\(q(R_2^*)'\ge1-5q\ge2/7>0\).

If 0<=H<=5/4, completing the square in dq gives
\[
4u(dq)^2-2(H-2Kq)dq\ge-\frac{H^2}{4u}.
\]
For H-2Kq<0 the left side is already nonnegative; otherwise use
0<=H-2Kq<=H in the usual completed-square lower bound.
Equations (1) and (7) therefore imply
\[
q(R_2^*)'\ge
1-\frac{17/4-H}{7}-\frac{H^2}{3}.
\tag{8}
\]
The right side is a concave quadratic in H, so its minimum on
[0,5/4] is at an endpoint. Those endpoint values are 11/28 and
17/336, both positive. This proves (2) in this range.

## 3. The range H>=5/4 reduces to two q endpoints

Completing the square without restricting dq gives
\[
q(R_2^*)'\ge F(q):=
1-C_0q+4A_{20}q^2-\frac{(H-2Kq)^2}{4u}.
\tag{9}
\]
The derivative of this quadratic at zero satisfies
\[
F'(0)=\frac{HK}{u}-C_0
\ge2H+u+\frac{H^2}{u}-5
\ge\frac52+\frac34+\frac{25}{13}-5
=\frac9{52}>0.
\tag{10}
\]
If its quadratic coefficient is nonnegative, F increases on q>=0.
If that coefficient is negative, F is concave and is bounded below
by the smaller of its endpoint values on [0,1/7]. In either case
it suffices to prove F(0)>0 and F(1/7)>0.

By (1) and (4),
\[
F(0)=1-\frac{H^2}{4u}\ge
1-\frac{(33/20)^2}{3}=\frac{37}{400}>0.
\tag{11}
\]

## 4. The q=1/7 endpoint reduces to two epsilon endpoints

For fixed S,u, regard F(1/7) as a quadratic in a=1-epsilon.
Its quadratic coefficient is exactly
\[
-\frac{S^2[u-U(1/S)]^2}{49u}\le0.
\tag{12}
\]
To check this identity, write
\[
K=u+H+aK_1,\qquad K_1=2S-1-u-H=S[u+U(1/S)],
\]
\[
A_{20}=1+a(S-2)+a^2(S^2-S+1),
\quad S^2-S+1=S^2U(1/S).
\]
The quadratic coefficient then follows from
\(4uU-(u+U)^2=-(u-U)^2\). Concavity reduces this endpoint
to a=0 and a=1.

At a=0, the expression is
\[
F(1/7)=\frac{18}{49}+\frac{6u}{49}
       +\frac{12H}{49}-\frac{25H^2}{196u}.
\tag{13}
\]
It increases with u, and decreases with H on
5/4<=H<=33/20, because its H derivative has numerator
24u-25H<0. Hence its minimum is bounded below by its value at
u=3/4,H=33/20, namely
\[
\frac{1569}{3920}>0.
\tag{14}
\]

At a=1, the expression is
\[
F(1/7)=\frac57+\frac{4S^2}{49}
 -\frac{[S(3-7u)+2-7u-7/S]^2}{196u}.
\tag{15}
\]
The bracket is negative. Since u<=13/16 and
7/S<=35/17<21/10, its absolute value is at most
\(43S/16+463/80\). Since 196u>=147,
\[
F(1/7)\ge\frac57+\frac{4S^2}{49}
 -\frac{(43S/16+463/80)^2}{147}.
\tag{16}
\]
Put S=17/5+z, with z>=0. The polynomial on the right becomes
\[
\frac{1223}{37632}z^2+\frac3{320}z
       +\frac{11181}{78400}>0.
\tag{17}
\]
Thus both a endpoints are positive. Equations (12)--(17) prove
F(1/7)>0; (9)--(11) finish the proof of (2).

## 5. What the monotonicity transports

The earlier fixed-p scale comparison may terminate at q=p/2,
equivalently tau=2. On the negative-D branch, (2) then permits a
further increase in q at fixed tau=2 until one of
\[
q=\frac{\alpha^2}{S^2+\alpha^2-1},\qquad
q=\frac17
\]
is reached. These are respectively the central-duration and outer-scale
bounds. The theorem does not require q<=r_A/2. If the comparison passes
that value, T<2 is allowed for this scalar residual comparison; the
changed point is not asserted to contain an actual outer reverse arc.
A subsequent logarithm bound must be valid at the resulting value of
2q/r_A, which may exceed one.

Only the scalar residual is raised by this new comparison. This note
neither proves it negative at those endpoints nor transports the
outgoing norm floor, corrected cap or physical completion cost during
that further change.

## 6. Independent mathematical review

An independent reading accepted the two derivative identities, all
bounds on C_0,K,E_0 and H, and the complete endpoint calculations.
In particular it checked the constants 17/336, 9/52, 37/400 and
1569/3920, the concavity coefficient (12), and the positive shifted
quadratic (17). It also checked that the earlier pairing theorem
excludes D<=0 for x<=12/5, justifying the closed enlargement (1).
The review accepts only the stated residual monotonicity and its
scalar endpoint reduction; the short-case exclusion remains open.

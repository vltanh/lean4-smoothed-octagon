# A decreasing scalar polynomial on the high-ratio scale face

**Lighter caller replacement:** the [new h-reduction proof](../../docs/lighter-proofs/NONSHORT_HIGH_RATIO_LOWER_REDUCTION.md)
differentiates a factored source before expansion and reduces its derivative
signs one variable at a time. Its terminal face and norm comparison prove
the original lower-shape sign and close the same caller. The negative-part
coefficient norm below is not used in that replacement.

Date: 2026-11-08 UTC. Hand derivative inequality for the constant
multiplier residual. Its endpoint value at h=1/4 is a separate sign.

Use the same rational incoming norm V, logarithm L, floor F_ell, and
transport notation as
[MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md),
but take the constant multipliers alpha=4 and M=1. Thus
\[
G_4=(5-Je^2)N(V,L)+C_*(3/4-\mathcal T_U(V))+(F_\ell-V).
\tag{1}
\]
This note makes no independent claim about transferring actual
inequalities to G_4. It proves the scalar derivative needed after that
transfer and the lowering of the shape to k=29t^2/4 have been justified.

Put
\[
t=(1-h)/2,\quad x=h+j,\quad k=29t^2/4,\quad q=1+y,
\quad W=1+x,\quad R=x^2+10x+15,
\]
and define
\[
P(h,j,y)=192q(q+1)W^3R\,G_4(t,x,q,k).
\tag{2}
\]
All denominators cancel, so P is a polynomial. Differentiation below
is performed after the displayed substitutions for t,x,k. In
particular it includes the variation of the scale k with h.

**Theorem.** At fixed j,y,
\[
\boxed{\partial_hP(h,j,y)<-237}
\tag{3}
\]
on the rectangle
\[
\frac15\le h\le\frac14,\qquad
\frac1{30}\le j\le\frac15,\qquad0\le y\le\frac14.
\tag{4}
\]
This contains the high-ratio large-gap domain, on which
\[
j\le5h/7\le5/28<1/5,
\qquad y\le\frac{h-j}{1+2j}\le\frac{13}{64}<1/4.
\]

## 1. Compact polynomial specification

For a direct check of every coefficient used below, define
\[
c=1-t,\quad p=t+x,\quad Y=x(x+2),\quad J=t+Y,
\quad B=k+2tx+x^2,
\]
\[
V=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\left(\frac{90-19x^2}{12R}-t\right),
\]
\[
L=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},\qquad
F_\ell=1+\frac{p^2q}{W^2}
 -\frac pW\frac{q^2+10q+1}{6(q+1)},
\]
\[
H_t=k(V-1+t^2)+t^2(2-t),\quad
Q_t=t(k^2-kt+t^2)+H_tY+tVY^2,
\quad E_0=q^2B+W^2-2pqW.
\]
Then
\[
\begin{aligned}
N={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
&-tBqWpL-tBqW^2V-q^2Q_t+qWp(H_t+2tVY),
\end{aligned}
\]
and the polynomial in (2) is exactly
\[
\begin{aligned}
P=48(q+1)WR\big[&4q(5W^2-Jq^2)N\\
&+(qJ-pW)\{3tE_0^2-4tVW^4
 +4q^2W^2(H_t+2tVY)-4q^4Q_t\}\\
&+4qW^2(F_\ell-V)\big],
\end{aligned}
\tag{5}
\]
followed by the substitutions before (2). This identity follows
directly from the definitions of N, C_* and the transported norm.
It involves only rational arithmetic; its displayed factors cancel
the denominators in V,L,F_ell.

## 2. One coefficient norm bounds every negative contribution

Set
\[
a=h-1/5\in[0,1/20],\qquad
b=j-1/30\in[0,1/6].
\]
Expand the negative derivative, using (5), as
\[
S(a,b,y)=-P_h(1/5+a,1/30+b,y)
=\sum_{r,m,n}s_{rmn}a^rb^my^n.
\tag{6}
\]
Its constant coefficient is
\[
s_{000}=\frac{79946460857}{284765625}>280.
\tag{7}
\]

Here is a complete norm specification for the negative part. Collect
all its coefficients, with their full weights, into the single
polynomial
\[
\mathcal R(a)=
\sum_{s_{rmn}<0}|s_{rmn}|(1/6)^m(1/4)^n a^r.
\tag{8}
\]
The integer coefficient ceilings of (8) are exactly the following
polynomial; all zero coefficients are omitted:
\[
\begin{aligned}
R_*(a)={}&1+10a+3025a^2+178114a^3+1685512a^4\\
&+2907009a^5+1889397a^6+444394a^7+3867a^8+3a^9.
\end{aligned}
\tag{9}
\]
In precise coefficient notation, (9) means
\[
[a^r]R_*
=\left\lceil
\sum_{m,n:s_{rmn}<0}|s_{rmn}|6^{-m}4^{-n}
\right\rceil.
\tag{10}
\]
Equations (5), (6), and (10) specify a direct expansion check of all
ten integers. No negative term is selected or discarded in defining
the norm, and no sign of an unprinted positive term is needed in the
estimate.

For nonnegative a,b,y in (4), each negative monomial in (6) is at
least its corresponding term in \(-\mathcal R(a)\), because
\(b\le1/6\) and \(y\le1/4\). Discarding the other nonnegative
monomials and retaining (7) gives
\[
S(a,b,y)\ge s_{000}-\mathcal R(a)
\ge s_{000}-R_*(a).
\tag{11}
\]
Every coefficient of R_* is positive, so
\[
R_*(a)\le R_*(1/20)
=\frac{21913348850943}{512000000000}<43.
\tag{12}
\]
Equations (7), (11), and (12) yield S>280-43=237, proving (3).
The margin follows from two explicitly displayed rational
comparisons, without subdivision or a computed extremum.

## 3. Reduction to h=1/4

For any point of the original high-ratio large-gap domain,
\[
\frac15\le h\le\frac14,\quad
\frac1{30}\le j\le\frac{5h}{7},\quad
0\le y\le\frac{h-j}{1+2j},
\]
increase h to 1/4 while keeping j,y fixed. The entire segment stays
inside (4). Thus (3) proves
\[
\boxed{P(h,j,y)\ge P(1/4,j,y).}
\tag{13}
\]
At the endpoint one has
\[
1/30\le j\le5/28,\qquad
0\le y\le\frac{1/4-j}{1+2j}.
\tag{14}
\]
A positive sign for P on (14) therefore proves positivity on the
entire high-ratio scale face. This is a scalar comparison of the
polynomial already defined in (2); no actual floor or covector is
transported along the segment in h.

# The displacement-weighted zero-scale face is negative

Date: 2026-11-08 UTC. Analytic zero-scale exclusion for the weight in
[the displacement reduction](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md).
The proof retains the original incident ceiling \(u\le U(r_A)\).
It needs two explicitly displayed univariate polynomial identities,
with 25 coefficients in total, and elementary termwise sign arguments.

## 1. The zero-scale function and its incident-norm comparison

Write \(a=\alpha\), \(r=r_A\), \(S=1+x\), and \(k=5a-1\).
The actual candidate excluded shape satisfies

\[
2\le x\le13/6,\quad 1<a\le x,\quad
\beta\ge b_0:=\frac{x(9x+8a)}{9x+8},\quad
\frac13<r\le\frac{13}{30},\quad u\le U(r)=1-r+r^2.
\tag{1}
\]

The last inequality is the original incoming-turn ceiling retained in
[the normalized scale identity](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md).
It is used before replacing the incoming norm by any looser ceiling.
The weight reduction also proves \(D/Q<1\), where
\(Q=a(a+\beta)\); its proof uses only the shape inequalities in
(1), and so applies on all scalar comparison segments below.

At fixed normalized duration \(y=\tau/T\in(0,1]\), the
zero-scale endpoint of the weighted residual is

\[
Z_u(y)=E_0+(u-1)/r+r+1-yrA_1+\log y+\frac{4-3y}{k}.
\tag{2}
\]

Its derivative with respect to \(u\) is

\[
(Z_u)_u=\frac1r+S\left(1-y\frac DQ\right)>0.
\tag{3}
\]

Thus it suffices to insert \(u=U(r)\) into this scalar function.
Set

\[
H=Sr(1-r)-1/S,\quad
C=2+\frac{x-1}{a^2},\quad
d_0=\frac DQ=2-\frac{2x}{a}
 +r\left(-1+\frac{2x}{a}+\frac{1+2x}{a^2}\right).
\tag{4}
\]

Since \(S\ge3\) and \(1/3\le r\le13/30<1/2\), one has
\(H\ge1/3>0\). The resulting explicit function is

\[
\boxed{Z(y)=-H(1-yd_0)+r(2-yC)
                  +\frac{4-3y}{k}+\log y.}
\tag{5}
\]

We shall prove \(Z(y)<0\) throughout (1).

## 2. Raise the active margin r to its explicit endpoint

At fixed \(a,x,y\), the function (5) strictly increases with
\(r\) on the interval in (1). To prove this, put

\[
A=2x/a-1,\qquad B=A+(1+2x)/a^2.
\]

The derivative \(Z_r\) is affine in \(y\). At \(y=0\), its
algebraic value is

\[
2-S(1-2r)\ge2-S/3\ge17/18>0.
\tag{6}
\]

Here the derivative has a continuous extension to \(y=0\), even
though \(Z\) itself contains \(\log y\). At \(y=1\),

\[
Z_r(1)=-\frac{x-1}{a^2}-S(1-2r)A
                        +SB(2r-3r^2)-B/S.
\tag{7}
\]

This expression increases with \(r\), because

\[
\frac{d}{dr}Z_r(1)=2S[A+B(1-3r)]
\ge\frac{S}{5a^2}
       [7(2ax-a^2)-3(1+2x)]>0.
\]

For the last sign use \(1\le a\le x\), which gives
\(2ax-a^2\ge2x-1\); the bracket is then at least
\(8x-10>0\). At \(r=1/3\), (7) is exactly

\[
\frac{3(a-x)^2+(x-1)(x+1)(2x-1)}{3a^2(x+1)}>0.
\tag{8}
\]

Both endpoint values of the affine function \(Z_r(y)\) are
therefore positive. This proves the monotonicity for all
\(0<y\le1\).

The lower bound on \(\beta\) in (1) is precisely

\[
r\le r_0(a,x):=
\frac{a(9x+8)}{a(17x+8)+9x^2}.
\tag{9}
\]

Hence \(Z(y)\) can be raised to \(r=r_0\). Throughout this
segment \(r\le13/30\), because
\(b_0/a\ge17x/(9x+8)\ge17/13\). This is a scalar
comparison with \(u=U(r)\); it does not assert the equal secants
at its endpoint.

## 3. Reduce to two one-dimensional shape edges

At fixed \(a,r,y\), the function (5) strictly decreases with
\(x\). Indeed,

\[
H_x=r(1-r)+S^{-2}>0,\quad C_x=a^{-2}>0,
\quad (d_0)_x=\frac{2[(a+1)r-a]}{a^2}<0.
\]

For the last inequality use
\(r\le a/(a+2)\), which follows from \(\beta\ge x\ge2\).
Thus, since \(d_0<1\),

\[
Z_x=-H_x(1-yd_0)+yH(d_0)_x-yr/a^2<0.
\tag{10}
\]

The endpoint (9) itself decreases with \(x\):

\[
(r_0)_x=
-\frac{a(81x^2+144x+64a)}{[a(17x+8)+9x^2]^2}<0.
\tag{11}
\]

Equations (6)--(11) show that
\(Z(a,x,r_0(a,x),y)\) decreases with \(x\). It is enough to
lower \(x\) to \(\max\{2,a\}\), giving the two edges

\[
x=2,\quad1<a\le2;
\qquad x=a,\quad2\le a\le13/6.
\tag{12}
\]

Every bound used in the comparison remains valid: lowering \(x\)
increases \(r_0\), so the lower bound \(r_0>1/3\) is retained,
and (9) gives the upper bound \(r_0\le13/30\). The inequalities
\(a\le x\), \(x\ge2\), and \(d_0<1\) hold all along the
segment.

## 4. A quadratic logarithm bound removes the duration

At either edge, write

\[
L=rC-d_0H+3/k,\qquad
E=Z(1)=-H+2r+4/k-L.
\tag{13}
\]

For \(t=1-y\in[0,1)\), integration of
\((1-t)^{-1}\ge1+t\) gives
\(\log y\le-t-t^2/2\). Therefore

\[
Z(y)=E+Lt+\log(1-t)
\le E+(L-1)t-t^2/2
\le E+\frac{(L-1)^2}{2}.
\tag{14}
\]

No sign of \(L-1\) is needed: the second inequality is just
completion of a square. We now prove that its right side is negative
at both edges, by displaying the complete numerators.

### Edge x=2

Here \(r_0=13a/[3(7a+6)]\). Direct substitution in (13) gives

\[
L=\frac{11135a^5+16944a^4+49572a^3+37214a^2+7122a-1152}
        {9a(5a-1)(7a+6)^3},
\]
\[
E=\frac{2200a^5+4797a^4-15912a^3-7622a^2+6a+1152}
        {9a(5a-1)(7a+6)^3}.
\tag{15}
\]

Put \(z=a-1\in[0,1]\). The exact identity is

\[
-[2E+(L-1)^2]
=\frac{P(z)}{81a^2(5a-1)^2(7a+6)^6},
\tag{16}
\]

where, in ascending powers of \(z\), the complete coefficient
list of \(P\) is

\[
\begin{split}
(&690233687,\ 10582593086,\ 37156604316,\ 52283775388,\
&20843672122,\ -28806946584,\ -44038758296,\
&-26501707700,\ -8351204733,\ -1342243990,\ -86404000).
\end{split}
\tag{17}
\]

The coefficients through degree four are positive and all later
coefficients are negative. For \(0<z\le1\), each positive term
is at least its coefficient times \(z^4\), and each negative
term is also at least its coefficient times \(z^4\). Hence

\[
P(z)\ge z^4P(1)=12429613296z^4>0.
\tag{18}
\]

At \(z=0\), its displayed constant is positive. This proves
the required edge sign without a root count or a sampled minimum.

### Edge x=a

Here \(r_0=(9a+8)/(26a+8)\), and

\[
L=\frac{-6885a^6+29322a^5+136684a^4+101398a^3
                 +16449a^2-1904a+64}
        {8a(5a-1)(13a+4)^3},
\]
\[
E=\frac{-13005a^7-21199a^6+72156a^5+40656a^4
                 -4703a^3+2415a^2+2352a-64}
        {8a(a+1)(5a-1)(13a+4)^3}.
\tag{19}
\]

Put \(v=a-2\in[0,1/6]\). Exactly,

\[
-[2E+(L-1)^2]
=\frac{Q(v)}{64a^2(a+1)(5a-1)^2(13a+4)^6},
\tag{20}
\]

where the complete coefficient list of \(Q\), in ascending
powers of \(v\), is

\[
\begin{split}
(&335599558992,\ 18835981373520,\ 81208201479192,\
&164345667026256,\ 201771400623165,\ 166252659646707,\
&96321280676760,\ 39931801595520,\ 11787954152298,\
&2403930238142,\ 314562058520,\ 21728950216,\
&199528065,\ -47403225).
\end{split}
\tag{21}
\]

Every coefficient except the last is positive. The two highest
terms combine as

\[
v^{12}(199528065-47403225v)
\ge\frac{383255055}{2}v^{12}\ge0.
\tag{22}
\]

The constant is positive, so \(Q(v)>0\) throughout the interval.
This proves the second edge sign.

## 5. Conclusion and comparison scope

The two exact identities (16), (20) and their explicit sign arguments
make the last bound in (14) strictly negative. Sections 2--3 extend
that sign to the original shape. Section 1 then extends it from the
incident ceiling back to the original incoming norm. Consequently

\[
\boxed{Z_u(y)<0\qquad(0<y\le1).}
\tag{23}
\]

Together with fixed-normalized-duration convexity and the
[tau-two continuation](MIXED_SMALLER_SHORT_DISPLACEMENT_SCALE_CONTINUATION.md),
this removes both extra scale faces. A positive value of the actual
weighted residual must therefore produce a positive scalar value at
\(q=\min\{q_c,1/7\}\), with the same incoming norm. The two
duration tests at that terminal scale still require their own signs;
this note supplies no global displacement or cost conclusion.

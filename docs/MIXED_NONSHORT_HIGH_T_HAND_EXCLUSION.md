# A hand exclusion of the larger incoming ratio in the nonshort case

Date: 2026-11-07 UTC. Accepted independent internal hand review.
See [NONSHORT_HAND_SCALE_AUDIT](NONSHORT_HAND_SCALE_AUDIT.md).

This note proves a uniform necessary bound for the actual smaller-nonshort
continuation at a global minimum reverse centre:

\[
\boxed{t:=a/(a+c)<2/5.}
\tag{1}
\]

It is not an exclusion of the whole nonshort case. Together with
[the conditional scale argument](MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md),
it strengthens the actual nonshort scale bound to `a<4/5`.

## 1. Retained necessary inequalities

Use the normalized notation and residual `N=tBqW R` of
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md):

\[
W=1+x,\quad p=t+x,\quad Y=x(x+2),\quad B=k+2tx+x^2,
\quad Z=qB/W.
\]

Here `0<t<1/2`, `x>0`, `q>1`, `k>=1`. The already proved scale
`a^2<2/3` implies `k>7t^2`. The upper-envelope centre gap is

\[
x^2+2x+2t>k.
\tag{2}
\]

The actual incoming norm satisfies

\[
v=1+\frac{(1-t)^2}{W}-(1-t)\frac{\log(1+x)}x,
\quad v>g:=1-\frac{(1-t)p}{W^2},
\]
\[
v\ge F_{p/W}(q),\qquad
F_\eta(q)=1+\eta^2q-\eta q\frac{\log q}{q-1}.
\tag{3}
\]

The strict secant comparison in (3) follows from the genuine turn and
was retained in the upper-envelope gap note. The second inequality is
the actual next missing-control inequality. The necessary incident root
ceiling gives `N<0`.

Suppose, for contradiction, that `t>=2/5`. The proved strict increase of
N with k allows lowering k to `7t^2`, still greater than one, so its
residual must remain negative. From now on set `k=7t^2`.

## 2. Two elementary logarithm bounds and a short x interval

The first two positive terms of the atanh expansion and the elementary
Padé upper bound give

\[
v<\bar v:=1+\frac{(1-t)^2}{W}
 -\frac{2(1-t)}{x+2}\left(1+\frac{x^2}{3(x+2)^2}\right),
\]
\[
\log q< L(q):=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},
\quad
F_{p/W}(q)>\underline F
:=1+(p/W)^2q-\frac{p(q^2+10q+1)}{6W(q+1)}.
\tag{4}
\]

Each logarithm comparison follows by differentiating from one, or by
integrating its positive remainder; the same bounds are proved in
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md).
In particular, `bar v-underline F>0` by (3).

The inequality `bar v>g` factors exactly as

\[
\bar v-g=
\frac{x(t-1)\{3t(x+2)^3+2x^3+x^2-10x-12\}}
 {3(1+x)^2(x+2)^3}>0.
\tag{5}
\]

Consequently

\[
t<T(x):=\frac{-2x^3-x^2+10x+12}{3(x+2)^3}.
\]

But the numerator of `T(x)-2/5`, with positive denominator
`15(x+2)^3`, is `12-22x-41x^2-16x^3`. It decreases on x>0 and
equals `-13/27` at x=1/3. Therefore `x<1/3`.

On the other hand, (2) gives
`x^2+2x>7t^2-2t>=8/25`. If `x<=1/7`, the left side is at most
`15/49<8/25`, a contradiction. Thus

\[
\boxed{\frac17<x<\frac13,\qquad \frac25\le t<\frac12.}
\tag{6}
\]

## 3. A rational lower residual and its cubic comparison

In the formula for N, substitute `v=bar v` and `log q=L(q)`; call
the resulting expression `bar N`. Both replacements decrease N.
The logarithm coefficient is negative. The other derivative is

\[
R_v=-\frac{xI}{tWB}<0,
\]
\[
I=k+tx+tW(k-2t)
 +(q-1)\{k(x+2)+tx(x+2)^2\}>0.
\tag{7}
\]

Indeed `k>=1` and `t<1/2`, so every term in I is positive.
It suffices to prove `bar N>0`.

Here are full rational definitions, to fix the algebraic calculation:

\[
\bar H=\frac{k}{t}(\bar v-1+t^2)+t(2-t),\qquad
\bar w=\frac{k^2-kt+t^2+\bar H Y+\bar vY^2}{B^2},
\]
\[
\bar R=1-t+Z-p^2/W-p^2/Z+p^3/B-pL(q)
 -W\bar v-Z\bar w+p(\bar H+2\bar vY)/B,
\quad \bar N=tBqW\bar R.
\]

Define the stronger comparison

\[
P(t,x,y):=6(q+1)W^2(x+2)^3
 \{\bar N-(q-1)(\bar v-\underline F)\},\quad q=1+y.
\tag{8}
\]

Since y>0 and `bar v-underline F>0`, positivity of P implies the
required positivity of `bar N`. Cancellation in the displayed rational
expressions makes P a cubic in y:

\[
P=C_0(t,x)+C_1(t,x)y+C_2(t,x)y^2+C_3(t,x)y^3.
\tag{9}
\]

The elementary derivative lemma in the appendix gives

\[
\partial_t C_j(t,x)>0\quad(0<x\le1/3,\ 2/5\le t\le1/2,
\ j=0,1,2,3).
\tag{10}
\]

Thus every coefficient can be lowered to its value at t=2/5.
Those four complete one-variable polynomials are

\[
C_0=-\frac{72x^2(x+1)}{625}
 (15x^4+68x^3+94x^2+20x-48),
\]
\[
C_1=\frac{12x}{625}
 (84+2086x-395x^2-8726x^3-11540x^4
 -6493x^5-1647x^6-140x^7),
\]
\[
C_2=-\frac6{625}H(x),
\quad H(x)=144-1444x-3342x^2+25127x^3+75813x^4
 +88565x^5+54334x^6+18396x^7+3270x^8+250x^9,
\]
\[
C_3=\frac{x+2}{625}J(x),
\quad J(x)=2680+17612x+33046x^2+3121x^3-42903x^4
 -45902x^5-20182x^6-3790x^7-250x^8.
\tag{11}
\]

All remaining signs concern only these displayed polynomials on (6).

## 4. Three rational estimates finish the cubic sign

First `C0>0`: the positive terms inside its parentheses increase with
x, and their sum at x=1/3 is strictly less than 48.

The derivative `C1'(x)/x` is a positive multiple of a sum consisting
of a positive multiple of `1/x`, a constant, and negative multiples of
positive powers of x. It is strictly decreasing. Thus C1 has at most
one interior critical point, a maximum; its minimum on any closed
subinterval occurs at an endpoint.

Similarly `H'(x)/x` is strictly increasing: its terms are a negative
multiple of `1/x`, a constant, and positive multiples of positive
powers of x. Therefore H has at most one interior critical point, a
minimum, and its maximum on a closed subinterval occurs at an endpoint.

Finally J and C3 are increasing on `0<x<=1/3`. For an explicit check,

\[
J'=17612+66092x+9363x^2
 -171612x^3-229510x^4-121092x^5-26530x^6-2000x^7.
\]

The five negative terms have absolute sum less than `30000x`, because
`171612/9+229510/27+121092/81+26530/243+2000/729<30000`.
Hence `J'>0`, and `J(0)>0` proves the same monotonicity for C3.

Evaluation of (11) at the four rational endpoints, with the preceding
monotonicities, gives the following deliberately weakened estimates:

| x interval | C1 lower bound b | C3 lower bound c | C2 lower bound -M | 4bc-M^2 |
| --- | ---: | ---: | ---: | ---: |
| [1/7,1/5] | 9/10 | 20 | -1 | 71 |
| [1/5,3/10] | 3/2 | 26 | -10 | 56 |
| [3/10,1/3] | 77/50 | 194/5 | -771/50 | 3079/2500 |

The table uses only substitution into the four fixed polynomials, not
a subdivision algorithm. Each last entry is strictly positive. Thus for
y>=0 in any row,

\[
C_1y+C_2y^2+C_3y^3
 \ge y(b-My+cy^2)\ge0,
\]

since the quadratic has positive leading coefficient and negative
discriminant. Together with C0>0, this proves P>0. It contradicts
the necessary negative residual in Section 1, proving (1).

## Appendix: the elementary coefficient derivative lemma

This appendix proves (10) using explicit polynomial lower bounds. Define

\[
D_0=\frac{\partial_tC_0}{4x^2(x+1)},\quad
D_1=\frac{\partial_tC_1}{2x},\quad
D_2=\frac{\partial_tC_2}{2},\quad
D_3=\frac{\partial_tC_3}{2}.
\tag{A1}
\]

Every coefficient of x in these four polynomials is a cubic or lower
degree polynomial in t. The following four elementary bounds suffice
for all of them on `2/5<=t<=1/2`:

\[
\frac45t-\frac4{25}\le t^2\le\frac9{10}t-\frac15,
\qquad
\frac{12}{25}t-\frac{16}{125}\le t^3
 \le\frac{61}{100}t-\frac9{50}.
\tag{A2}
\]

Their four nonnegative remainders are, respectively,

\[
(t-2/5)^2,\quad (t-2/5)(1/2-t),\quad
(t-2/5)^2(t+4/5),\quad
(t-2/5)(1/2-t)(t+9/10).
\]

Here is the complete rule for checking the ensuing coefficient bounds.
For a coefficient `A t^3+B t^2+C t+D`, substitute the lower bound in
(A2) when A or B is positive and the upper bound when it is negative.
This leaves an affine function of t, whose minimum is the smaller of
its values at 2/5 and 1/2. Expanding the rational definition (8),
differentiating, collecting powers of x and applying this rule gives

\[
\begin{aligned}
D_0\ge{}&1+14x+15x^2+4x^3+x^4/3,\\
D_1\ge{}&70+300x+560x^2+550x^3+290x^4
          +72x^5+7x^6+3x^7/10,\\
D_2\ge{}&34+270x+610x^2+640x^3+170x^4
          -321x^5-368x^6-165x^7-35x^8-3x^9,\\
D_3\ge{}&39+234x+545x^2+690x^3+482x^4+147x^5
          -18x^6-26x^7-7x^8-x^9/2.
\end{aligned}
\tag{A3}
\]

For transparency, two coefficient calculations illustrate the sign
rule, including one of the negative tail bounds. The constant term of
D0 is

\[
336t^3-576t^2+264t-24
 \ge-\frac{24(485t-251)}{125}
 \ge\frac{204}{125}>1.
\]

The coefficient of x^5 in D2 is

\[
-5880t^3+4710t^2+2648t-1757
 \ge\frac{14146t-7261}{5}
 \ge-\frac{8013}{25}>-321.
\]

The remaining entries of (A3) follow by exactly the same affine
substitution rule from (8) and (A1); all resulting lower polynomials
are displayed in (A3). Thus (A3) is a finite elementary multiplication
and endpoint check, not an executable sign assertion or an omitted
coefficient-count certificate.

The first two lower polynomials in (A3) are positive for x>0. For the
last two, discard the displayed positive nonconstant terms and use
`x<=1/3`:

\[
D_2\ge34-321x^5-368x^6-165x^7-35x^8-3x^9
 \ge\frac{23396}{729}>0,
\]
\[
D_3\ge39-18x^6-26x^7-7x^8-x^9/2
 \ge\frac{1533791}{39366}>0.
\]

All prefactors removed in (A1) are positive for x>0. Therefore every
partial derivative in (10) is strictly positive, completing the
coefficient derivative lemma and the high-t exclusion.

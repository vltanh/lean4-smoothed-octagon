# The S1 outer A branch: the upper-shape F0 terminal

This proves the terminal estimate
\[
 \boxed{F_0\left(x,x,x+\frac{24}{43}(x-1),\frac34\right)>
 \frac3{500}}
 \qquad\left(\frac32\le x\le2\right).
 \tag{1}
\]
The immediate caller is Section 7 of
[SHORT_OUTER_LARGE_SHAPE_REDUCTION](SHORT_OUTER_LARGE_SHAPE_REDUCTION.md).
Its reciprocal-shape concavity leaves a=x and a=6/5; on the a=x face it
proves norm monotonicity, then slope monotonicity, reducing exactly to (1).
The other F0 face is supplied by
[the shared a=6/5 terminal](SHORT_OUTER_UPPER_SHAPE_TERMINAL.md).
This note proves its one face and does not independently assert the entire
A-row conclusion or the other S1 signs.

The original c=7/96, g=9193/50000, and cubic logarithm majorant are retained:
\[
 \ell(y)=2\frac{y-1}{y+1}
       +\frac23\left(\frac{y-1}{y+1}\right)^3,
 \qquad\log y\le\ell(y)\quad(0<y\le1).
 \tag{2}
\]
We prove strict concavity in the sole remaining variable x, then check its two
endpoints with explicitly rounded scalar fractions. There is no subdivision.

## 1. A degree-eight source with its linear pole kept separate

In this note always set
\[
 a=x,\quad \beta=(67x-24)/43,\quad u=3/4,\quad
 S=x+1,\quad K=6x^2+1,\quad L=55x-12,\quad
 B=a+\beta=2L/43,
\]
\[
 y=2B/(7a)=4L/(301x).
 \tag{3}
\]
The original transport polynomial D simplifies to \(D=S^2\), independent of
beta on this shape face. Put \(J_n=4SJ\), where
\(J=K[-S/4+1/S]+2S-1\), and \(M=K^2-SK+S^2\). Their complete polynomials are
\[
\begin{aligned}
M(x)={}&36 x^{4} - 6 x^{3} + 7 x^{2} + x\\
&{}+ 1
\end{aligned}
\]
This polynomial has 5 monomials, degree 4, and largest cleared coefficient 36.

\[
\begin{aligned}
J_n(x)={}&- 6 x^{4} - 12 x^{3} + 25 x^{2} + 10 x\\
&{}+ 7
\end{aligned}
\]
This polynomial has 5 monomials, degree 4, and largest cleared coefficient 25.

The three original source functions become
\[
 \Gamma_* =\frac{N_\Gamma(x)}{9216x^4S^2},\qquad
 w=\frac{N_w(x)}{196x^3},\qquad
 E_L=\frac{N_E(x)}{28x^2S},
 \tag{4}
\]
with the individually checkable source identities
\[
\begin{aligned}
 N_\Gamma&=48S^2M-J_n^2,\\
 xN_w&=4M+3S^4-SJ_n,\\
 N_E&=6S^3-J_n.
\end{aligned}
\tag{5}
\]
The outer x factor in the second identity is canceled before using (4);
it is positive on this face. Here are all three expanded polynomials:
\[
\begin{aligned}
N_\Gamma(x)={}&- 36 x^{8} - 144 x^{7} + 1884 x^{6} + 3888 x^{5}\\
&{}+ 1187 x^{4} + 100 x^{3} + 30 x^{2} + 4 x\\
&{}-1
\end{aligned}
\]
This polynomial has 9 monomials, degree 8, and largest cleared coefficient 3888.

\[
\begin{aligned}
N_w(x)={}&6 x^{4} + 165 x^{3} - 25 x^{2} + 11 x\\
&{}-1
\end{aligned}
\]
This polynomial has 5 monomials, degree 4, and largest cleared coefficient 165.

\[
\begin{aligned}
N_E(x)={}&6 x^{4} + 18 x^{3} - 7 x^{2} + 8 x\\
&{}-1
\end{aligned}
\]
This polynomial has 5 monomials, degree 4, and largest cleared coefficient 18.

The largest of (5) has nine monomials and degree eight, in x alone.

Define the source with its elementary linear pole removed:
\[
 \widetilde Q(x)=F_0+c\ell(y)+g+c\frac aB.
\]
Substituting the original residual before any common-denominator expansion gives
\[
 \widetilde Q=
 \Gamma_*-\frac7{48}w+\frac3{64}
 +\frac7{384}\frac Ba+\frac7{96}E_L
 =\frac{N(x)}{2774016x^4S^2}.
 \tag{6}
\]
\[
\begin{aligned}
N(x)={}&- 10836 x^{8} - 12384 x^{7} + 634524 x^{6} + 1098408 x^{5}\\
&{}+ 307391 x^{4} + 60700 x^{3} - 16770 x^{2} + 3268 x\\
&{}-301
\end{aligned}
\]
This polynomial has 9 monomials, degree 8, and largest cleared coefficient 1098408.

Every separate source contribution in (6) has degree at most eight after
clearing that displayed denominator. The largest uncollected coefficient is
1170288. Its useful partial-fraction identity is
\[
\begin{aligned}
 \widetilde Q={}&-\frac{x^2}{256}+\frac{3x}{896}+\frac{6529}{28896}
 -\frac7{72S}-\frac{49}{576S^2}\\
 &+\frac{3289}{86688x}-\frac{563}{64512x^2}
 +\frac5{3584x^3}-\frac1{9216x^4}.
\end{aligned}
\tag{7}
\]
This source comparison also has nine monomials and degree eight. Its largest
individual coefficient before collection is 1253568.

To restore the pole use only
\[
 c\frac aB=\frac{301x}{192L}
 =\frac{301}{10560}+\frac{301}{880L}.
 \tag{8}
\]
After multiplying by L this is a two-monomial linear identity. Thus
\[
 F_0(x)=\widetilde Q(x)-g-\frac{301}{10560}
       -\frac{301}{880L}-c\ell(y).
 \tag{9}
\]
Do not collect (9) over its joint denominator: adjoining the extra factor L to
(6) would create an unnecessary degree-nine numerator. The proof differentiates
the already verified reciprocal terms in (7)--(9) separately.

## 2. A small bound for the logarithm and pole curvature

The same majorant (2) satisfies
\[
 \ell'(y)\le1/y,\qquad \ell''(y)\ge-1/y^2\qquad(0<y\le1).
 \tag{10}
\]
For completeness, the cleared error numerators are
\[
 -y^4+4y^3-6y^2+4y-1=-(y-1)^4,
\]
\[
 y^5-11y^4+26y^3-22y^2+5y+1
 =(1-y)^3(1+8y-y^2).
\]
They have five and six monomials, of degrees four and five. The positive
respective denominators are \(y(y+1)^4\) and \(y^2(y+1)^5\).

Here y increases, \(y''<0\), and \(188/301\le y\le196/301<1\).
The chain rule with (10) bounds the second derivative of the negative
logarithm term by
\[
 [-c\ell(y(x))]''\le
 c\left[(y'/y)^2-y''/y\right]
 =\frac{7(55x-6)}{4x^2L^2}.
\]
Adding the pole term in (9) therefore gives the upper bound
\[
 U(x)=\frac{7(55x-6)}{4x^2L^2}-\frac{182105}{88L^3}.
 \tag{11}
\]
We have
\[
 \frac1{160}-U(x)=\frac{P(x)}{160x^2L^3}.
 \tag{12}
\]
The source identity is the small sum of products
\(P=x^2L^3-280(55x-6)L+331100x^2\). Its full polynomial and positive shift are:
\[
\begin{aligned}
P(x)={}&166375 x^{5} - 108900 x^{4} + 23760 x^{3} - 517628 x^{2}\\
&{}+ 277200 x -20160
\end{aligned}
\]
This polynomial has 6 monomials, degree 5, and largest cleared coefficient 517628.

\[
\begin{aligned}
32P(3/2+z)={}&5324000 z^{5} + 36445200 z^{4} + 99641520 z^{3} + 119497544 z^{2}\\
&{}+ 52029222 z + 744669
\end{aligned}
\]
This polynomial has 6 monomials, degree 5, and largest cleared coefficient 119497544.

All shifted coefficients are positive for z=x−3/2≥0. Thus U<1/160
throughout the interval. Each identity (12) and its shift has six monomials
and degree five; the largest coefficient before collecting the shifted
monomial contributions is 179685000.

## 3. The remaining reciprocal powers give negative curvature

Differentiating (7) gives a constant term \(-1/128\), together with
\[
 -\frac7{36S^3}-\frac{49}{96S^4}
 +\frac{6578}{86688x^3}-\frac{3378}{64512x^4}
 +\frac{60}{3584x^5}-\frac{20}{9216x^6}.
 \tag{13}
\]
Keep these powers separate. Since x≥3/2, \(S\le5x/3\), so the first four
terms are at most
\[
 \frac{p}{x^3}-\frac{q}{x^4},
 \quad
 p=\frac{6578}{86688}-\frac{21}{500}=\frac{183569}{5418000}>0,
 \quad
 q=\frac{3378}{64512}+\frac{49}{96}\left(\frac35\right)^4
   =\frac{796403}{6720000}.
\]
The exact scalar comparison is
\[
 q-2p=\frac{43993907}{866880000}>\frac6{125}.
 \tag{14}
\]
Because x≤2 and \(x^4\le16\),
\[
 \frac{p}{x^3}-\frac{q}{x^4}
 =\frac{px-q}{x^4}< -\frac{6}{125x^4}\le-\frac3{1000}.
\]
The remaining positive reciprocal term satisfies
\[
 \frac{60}{3584x^5}\le\frac5{2268}<\frac9{4000}.
\]
Discard the last negative term in (13). Combining these bounds with Section 2,
\[
 \boxed{F_0''< -\frac1{128}+\frac1{160}-\frac3{1000}+\frac9{4000}
       =-\frac{37}{16000}<0.}
 \tag{15}
\]
The derivative sign is therefore a separate small claim: it follows from the
six-term positive polynomial P and scalar rational comparisons. No high-degree
common numerator of the full second derivative has been formed.

## 4. The two endpoint signs

The following fractions are direct substitutions in (3)--(5) and (2).
At x=3/2,
\[
\begin{aligned}
 \Gamma_*&=\frac{3457319}{18662400}\ge\frac{37}{200},&
 w&=\frac{1093}{1323}\le\frac{827}{1000},\\
 E_L&=\frac{691}{1260}\ge\frac{137}{250},&
 \ell(y)&=-\frac{165009832}{350790507}\le-\frac{47}{100},\\
 a/B&=43/94,& (u-1)B/a&=-47/86.
\end{aligned}
\tag{16}
\]
These rounding directions give an upper bound for the original residual
\(\overline R_2=2w-1/2+(u-1)B/a+a/B-1/7-E_L+\ell(y)\), and hence
\[
\begin{aligned}
 F_0(3/2)&\ge\frac{37}{200}
 -\frac7{96}\left[
 \frac{1654}{1000}-\frac12-\frac{47}{86}+\frac{43}{94}
 -\frac17-\frac{137}{250}-\frac{47}{100}\right]-\frac{9193}{50000}\\
 &=\frac{205493}{25262500}>\frac3{500}.
\end{aligned}
\tag{17}
\]
At x=2, the analogous exact values and roundings are
\[
\begin{aligned}
 \Gamma_*&=\frac{237263}{1327104}\ge\frac{357}{2000},&
 w&=\frac{191}{224}\le\frac{853}{1000},\\
 E_L&=\frac{227}{336}\ge\frac{27}{40},&
 \ell(y)&=-\frac{153480}{357911}\le-\frac{107}{250},\\
 a/B&=43/98,& (u-1)B/a&=-49/86.
\end{aligned}
\tag{18}
\]
Consequently,
\[
\begin{aligned}
 F_0(2)&\ge\frac{357}{2000}
 -\frac7{96}\left[
 \frac{1706}{1000}-\frac12-\frac{49}{86}+\frac{43}{98}
 -\frac17-\frac{27}{40}-\frac{107}{250}\right]-\frac{9193}{50000}\\
 &=\frac{1709137}{240800000}>\frac3{500}.
\end{aligned}
\tag{19}
\]
Every comparison is scalar; the largest integer required by an individual
cross-multiplication in (16) or (18) is 16500983200, eleven digits.
Concavity (15) places F0 above the chord joining its two endpoint values.
Equations (17) and (19) therefore prove (1).

## 5. Caller and size boundary

The large-shape reduction's Section 7 first lowers the norm to 3/4 and then
lowers C to 24/43 on a=x. Its final requested premise is precisely (1).
Thus this result closes that F0 terminal, with a stronger quantitative margin
than the caller needs. The separate a=6/5 terminal is still invoked at its
own norm endpoints; nothing in this note substitutes one shape face for the
other.

The largest source identity has nine monomials and degree eight in one variable.
The only nonconstant sign polynomial beyond the printed source functions is
the six-term, degree-five pole-curvature numerator P. All polynomial expansions,
including individual contributions before collection and shifting, have
coefficients at most 179685000. Every scalar rounding also stays within twelve
digits. This is a hand proof; no Lean source change, Lean check, or CI measurement
is claimed here.

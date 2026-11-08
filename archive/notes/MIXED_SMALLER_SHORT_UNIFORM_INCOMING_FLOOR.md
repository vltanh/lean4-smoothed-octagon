# A uniform rational floor for the incoming short secant

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 11, and used in the combined residual's tau=2 scale comparison.

For
\[
1<x\le9,\qquad \beta\ge x,\qquad
u=\operatorname{Sec}(1,x,\beta),
\]
one has
\[
\boxed{u>\frac34+\frac1{28}
                  \left(\frac{x-1}{x+1}\right)^2.}
\tag{1}
\]
No upper bound on beta, no second-secant equality and no scale
condition are required.

## 1. A rational logarithm bound

Put
\[
r=\frac{\beta-1}{\beta+2x+1}\in(0,1),\qquad
\ell(r)=2r+\frac{2r^3}{3}+\frac{2r^5}{5(1-r^2)}.
\]
The positive atanh series, with every denominator after its cubic
term bounded below by five, gives
\[
\log\frac{x+\beta}{x+1}=2\operatorname{atanh}r<\ell(r).
\tag{2}
\]
For example this also follows by integrating the geometric-series
identity for 1/(1-r^2); the omitted denominator comparison is strict
for r>0.

Define the rational lower bound
\[
u_-=1+\frac{x^2}{(x+1)(x+\beta)}
                 -\frac{x}{\beta-1}\ell(r).
\]
Then u>u_-. We will prove that u_- exceeds the right side of (1).

## 2. An explicit polynomial identity

Set
\[
z=x-1\in(0,8],\qquad t=\frac{\beta-x}{x-1}\ge0.
\]
Direct substitution gives
\[
u_--\frac34-\frac{(x-1)^2}{28(x+1)^2}
=\frac{z^2\{z^4F_4(t)+z^3F_3(t)+z^2F_2(t)+zF_1(t)+F_0(t)\}}
 {210(\beta+x)(x+1)^2(\beta+2x+1)^3},
\tag{3}
\]
where
\[
\begin{aligned}
F_4(t)={}&24t^4+61t^3-131t^2-289t+239,\\
F_3(t)={}&147t^4+728t^3+202t^2-1672t+1587,\\
F_2(t)={}&4(42t^4+413t^3+537t^2-1077t+917),\\
F_1(t)={}&80(14t^3+49t^2-64t+45),\\
F_0(t)={}&320(7t^2-7t+4).
\end{aligned}
\tag{4}
\]
The sign below is proved by elementary grouping, rather than by
listing signs of all coefficients.

## 3. The last three terms are positive

For t>=0,
\[
537t^2-1077t+917
 \ge500(t-11/10)^2+312>0,
\]
\[
49t^2-64t+45=32(t-1)^2+17t^2+13>0,
\]
\[
7t^2-7t+4=7(t-1/2)^2+9/4>0.
\]
Thus F_2,F_1,F_0 are strictly positive.

## 4. Pair the first two terms

First F_3(t)>0 for every t>=0. On [0,1], discard its cubic and
quartic terms; the remaining quadratic decreases there and is 117
at one. On [1,infinity), F_3''>0 and F_3'(1)=1504>0, so
F_3(t)>=F_3(1)=992.

Next put
\[
P(t)=8F_4(t)+F_3(t)
 =339t^4+1216t^3-846t^2-3984t+3499.
\]
At t=1+s its expansion is
\[
P(1+s)=339s^4+2572s^3+4836s^2-672s+224.
\tag{5}
\]
For s>=0, this is at least
\[
4800(s-7/100)^2+5012/25>0.
\]
For -1<=s<=0, put v=-s in [0,1]. Equation (5) is at least
\[
2264v^2+672v+224>0,
\]
because -2572v^3>=-2572v^2. Therefore P(t)>0 for all t>=0.

At fixed t, the function zF_4(t)+F_3(t) is affine in z. Its values
at z=0 and z=8 are the positive quantities F_3(t) and P(t),
respectively. Hence it is positive throughout [0,8]. Consequently
\[
z^4F_4(t)+z^3F_3(t)=z^3[zF_4(t)+F_3(t)]>0
\qquad(0<z\le8).
\]
Together with Section 3 this proves positivity of (3), and (1)
follows from u>u_-.

This lemma concerns only the unchanged incoming secant. Replacing
u by its lower bound in a different expression requires that
expression's own monotonicity or endpoint argument.

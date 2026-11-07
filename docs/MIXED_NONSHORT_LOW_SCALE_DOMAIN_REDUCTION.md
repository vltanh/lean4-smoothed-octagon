# Two hand bounds in the common low-scale nonshort domain

Date: 2026-11-07 UTC. Hand necessary-domain reduction, independently
accepted in [HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).
The common low-scale exclusion itself remains open.

Use the actual smaller-nonshort data and the normalized coordinates of
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md):
\[
t=\frac a{a+c},\qquad
x=\frac{d-a}{a+c},\qquad
k=\frac{a^2+4}{(a+c)^2},\qquad W=1+x.
\]
The already proved smaller-turn shape and centre gap give
\[
k\ge1,\qquad k<2t+x(x+2).
\tag{1}
\]
Assume the proposed common low-scale region \(a\le1/2\).
Since
\[
a^2=\frac{4t^2}{k-t^2},
\]
this is exactly the additional restriction
\[
k\ge17t^2.
\tag{2}
\]

**Theorem.** Every such actual configuration satisfies
\[
\boxed{t<\frac7{20},\qquad x>\frac3{13}.}
\tag{3}
\]
No next-switch alternative or Casimir cap is used in this refinement.

## 1. A strictly decreasing upper bound for t

The exact incoming secant and its actual turn derivative satisfy
\[
v=1+\frac{(1-t)^2}{1+x}
 -(1-t)\frac{\log(1+x)}x
 >g:=1-\frac{(1-t)(t+x)}{(1+x)^2}.
\]
The elementary two-term logarithm lower bound
\[
\log(1+x)>
\frac{2x}{x+2}+\frac{2x^3}{3(x+2)^3}
\]
follows by integrating the first two terms of the positive expansion of
\(2/(1-z^2)\), with \(z=x/(x+2)\).
Thus \(v<\bar v\), where
\[
\bar v=1+\frac{(1-t)^2}{1+x}
 -\frac{2(1-t)}{x+2}\left(1+\frac{x^2}{3(x+2)^2}\right).
\]
Direct subtraction gives
\[
\bar v-g=\frac{(1-t)x}{(1+x)^2}\,[T(x)-t],
\]
\[
T(x)=\frac{-2x^3-x^2+10x+12}{3(x+2)^3}.
\tag{4}
\]
Every factor outside the bracket is positive, so the actual derivative
inequality implies \(t<T(x)\).
The derivative of this explicit upper envelope is
\[
T'(x)=-\frac{11x^2+24x+16}{3(x+2)^4}<0.
\tag{5}
\]

Suppose \(t\ge7/20\). Equations (1)--(2) imply
\[
x^2+2x>17t^2-2t\ge\frac{553}{400},
\]
because \(17t^2-2t\) increases for \(t\ge7/20\).
But \(x\le8/15\) would give
\[
x^2+2x\le\frac{304}{225}<\frac{553}{400}.
\]
Therefore \(x>8/15\). Equations (4)--(5) now give the contradiction
\[
t<T(x)<T(8/15)=\frac{14129}{41154}<\frac7{20}.
\]
The last comparison has positive cross-product difference
\(7\cdot41154-20\cdot14129=5498\).
This proves the first bound in (3).

## 2. A rational lower bound for the duration ratio

Suppose instead that \(x\le3/13\). Then
\(x^2+2x\le87/169\).
The two bounds in (1) imply
\[
1<2t+\frac{87}{169},
\quad\text{hence}\quad t>\frac{41}{169}.
\]
The function
\[
17t^2-2t-\frac{87}{169}
\]
is strictly increasing for \(t\ge41/169\), and its value at that
rational endpoint is \(16/28561>0\). Consequently
\[
17t^2>2t+\frac{87}{169},
\]
contradicting (1)--(2). This proves \(x>3/13\).

## 3. The remaining common sign

The existing strict increase of the incident-upper residual numerator
\(N(k)\) with k gives a precise two-face sufficient target:
\[
k_0=\max\{1,17t^2\},\qquad
N(k_{\rm actual})<0\Longrightarrow N(k_0)<0.
\]
The exact incoming secant, its derivative inequality, and the incoming
missing-control inequality are independent of k and remain available.
The centre gap also survives lowering k. Thus a common low-scale hand
exclusion may be proved on these two lower faces, now with
\(0<t<7/20,\ x>3/13\).

Constraints that change with k, such as the next normalized active
margin or compact inactive-margin bounds, cannot be attached to a lower
face without a further comparison. The statement above does not do so.
The genuine incoming missing-control inequality is retained; it is not
replaced by its turn-derivative specialization at q=1.

The strict residual sign on those faces has not been proved in this
note. These two necessary bounds are a reproducible hand increment,
not an assertion of completion of the common low-scale or forward-next
case.


## 4. Subsequent closure of the d<=c part

The [unit-shape hand theorem](MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md)
and its [independent audit](MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md)
now exclude every point of this common low-scale region with d<=c.
Indeed t<7/20<13/35, d<=c is exactly x<=1-2t, and the actual
centre gap with k>=1 implies 1<2t+2x+x^2. The exact incoming secant
and its missing-control floor are unchanged when k is lowered to one.
Strict shape monotonicity sends N(k)<0 to N(1)<0, contrary to that
theorem. This application uses no reverse-next hypothesis.

The part with d>c remains open; the present low-scale domain bounds
continue to apply there.

The later [complete reverse hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md),
Section 5, strengthens this conclusion without any low-scale assumption:
every common nonshort window has a<=r<c<=b*<d and
q<(1+x)/(2t+x). Its scalar proof uses the successor sign only to contradict
the opposite order. The low-scale d>c residual signs remain separate.

# A quantitative swapped-secant bound

Date: 2026-11-07 UTC. Complete hand proof, accepted in the
[endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 16.

This note strengthens the common incoming-floor bound when
\(t\ge1/4\). The secant comparison itself is an elementary statement
independent of an extremal, a successor sign, or a Casimir.

Write
\[
\operatorname{Sec}(A,B,P)
=1+\frac{B^2}{(A+B)(P+B)}
-\frac{B}{P-A}\log\frac{P+B}{A+B}.
\]

## 1. The stronger secant comparison

**Lemma.** Let
\[
t+c=1,\qquad \frac14\le t<c,\qquad
c<p<2c-t.
\]
Then
\[
\boxed{\operatorname{Sec}(t+p-c,p,c)>
       \operatorname{Sec}(t,c,p).}
\tag{1}
\]

Put
\[
h=1-2t=c-t,\qquad j=p-c,\qquad
0<j<h\le1/2,\qquad \delta=h-j.
\]
Also set
\[
c=\frac{1+h}{2},\quad p=c+j,\quad
A=1+2j,\quad C=1+h+j,\quad B=1+2h+j,\quad
E=\frac{1-h^2}{2}+j.
\]
For the difference \(\Delta\) in (1), direct subtraction of the
two secant formulas gives
\[
\frac{h^2-j^2}{j}\Delta
=\frac{p(h+j)}j\log A-B\log C+
\frac{(h^2-j^2)E}{AC}.
\]
Since \(p(h+j)/j-B=c(h-j)/j\), this is equivalently
\[
\frac{h+j}{j}\Delta
=\frac cj\log A-\frac B\delta\log(C/A)
+\frac{(h+j)E}{AC}.
\tag{2}
\]
All factors multiplying \(\Delta\) are positive.

Use the elementary rational logarithm bounds
\[
\log(1+2j)>
\frac{2j}{1+j}+\frac{2j^3}{3(1+j)^3},
\]
\[
\log z<
\frac{(z-1)(z^2+10z+1)}{6z(z+1)}
\qquad(z>1).
\]
The first follows from two positive atanh terms.
For the second, the derivative of the right side minus \(\log z\)
is \((z-1)^4/[6z^2(z+1)^2]>0\), with value zero at \(z=1\).

Applying the lower bound to the positive log term in (2), and the
upper bound to the negative one, gives
\[
\frac{h+j}{j}\Delta>
\frac{\mathcal P(h,j)}
 {6(1+j)^3AC(A+C)},
\tag{3}
\]
where the full cleared numerator is
\[
\begin{aligned}
\mathcal P={}&
2(1+h)\{3(1+j)^2+j^2\}AC(A+C)\\
&-B(1+j)^3(C^2+10CA+A^2)\\
&+3(h+j)(1-h^2+2j)(1+j)^3(A+C).
\end{aligned}
\tag{4}
\]

There is a short hand sign proof for (4). Its expansion in \(j\) is
\[
\begin{aligned}
\mathcal P={}&
h^2(2-2h-3h^2)
+h(2+9h-12h^2-9h^3)j\\
&+h(10+14h-28h^2-9h^3)j^2\\
&+(-1+20h+8h^2-28h^3-3h^4)j^3\\
&+(-7+14h-8h^2-12h^3)j^4
+(-13-9h^2)j^5-7j^6.
\end{aligned}
\tag{5}
\]
Every monomial of (4) is accounted for in (5).

The first two terms have the lower bounds
\[
h^2(2-2h-3h^2)\ge h^2/4,\qquad
h(2+9h-12h^2-9h^3)j
\ge h(2+3h/4)j.
\]
For the quadratic and the negative part of the cubic term, use
\(h\le1/2\) and \(j\le h\):
\[
\begin{aligned}
&h(10+14h-28h^2-9h^3)j^2
 -(1+28h^3+3h^4)j^3\\
&\hspace{12mm}\ge
\frac{71}{8}h j^2-\frac{75}{16}j^3
\ge\frac{67}{16}j^3.
\end{aligned}
\]
Here \(14h-28h^2\ge0\), \(9h^3\le9/8\), and
\(1+28h^3+3h^4\le75/16\).

The remaining negative terms are absorbed by \(20h j^3\):
\[
\begin{aligned}
&20h j^3-(7+8h^2+12h^3)j^4
 -(13+9h^2)j^5-7j^6\\
&\hspace{12mm}\ge
\left(20-\frac{21}{2}-\frac{61}{8}-\frac74\right)j^4
=\frac18j^4.
\end{aligned}
\]
The positive \(8h^2j^3\) and \(14h j^4\) may be dropped.
Thus (5) gives the explicit positive lower bound
\[
\mathcal P\ge
\frac{h^2}{4}+h(2+3h/4)j+
\frac{67}{16}j^3+\frac18j^4>0.
\tag{6}
\]
Equations (2)--(6) prove the lemma.

## 2. The actual derivative floor supplies the interval hypothesis

For the common smaller-nonshort coordinates let
\[
c=1-t,\qquad p=t+x,\qquad W=1+x,\qquad X=x+2.
\]
Suppose \(t\ge1/4\) and retain the exact secant derivative floor
\(v=\operatorname{Sec}(t,c,p)>g_c(p)\).
The usual two-atanh upper secant \(\bar v\) satisfies
\[
\bar v-g_c(p)
=\frac{(1-t)x}{W^2}\{T(x)-t\},\qquad
T(x)=\frac{12+10x-x^2-2x^3}{3X^3}.
\]
Therefore \(t<T(x)\). Since \(T\) is decreasing and
\(T(1)=19/81<1/4\), one has \(x<1\).
For \(0<x\le1\), the exact identity
\[
3X^3\left(\frac{2-x}{4}-T(x)\right)
=\frac{x}{4}(8+4x-4x^2-3x^3)>0
\]
holds; the last brace is at least \(8-3x\ge5\).
It follows that \(4t+x<2\).

The common strict-order theorem gives \(p>c\).
In terms of \(h=1-2t\) and \(j=p-c=2t+x-1\), the preceding bound
is exactly \(0<j<h\). Thus every hypothesis of the lemma holds.

## 3. The strengthened first-event factor bound

Keep the original incoming missing-control floor and the actual
star bound:
\[
v\ge F_{p/W}(q)
=\operatorname{Sec}(W/q-p,p,c),\qquad
1<q<W/p.
\]
Its secant first argument lies in \((0,c)\).
For middle \(p\ge c\) and endpoint \(c\), this secant is strictly
decreasing in its first argument. Combining (1) with the retained
floor therefore gives
\[
W/q-p>t+p-c.
\]
Consequently
\[
\boxed{
q<\frac{W}{p+t+(p-c)}
  =\frac{1+x}{4t+2x-1}.
}
\tag{7}
\]
The denominator is positive because the common strict order gives
\(2t+x>1\).

The exact incoming secant and its floor have stayed at their original
coordinates. No artificial next-switch assertion is used.
This strengthens the earlier common bound \(q<W/(2t+x)\) when
\(t\ge1/4\), and is independent of the sign of the actual next switch.

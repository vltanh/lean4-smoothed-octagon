# The outer-scale envelope is negative at large short ratio

**Replacement status, 2026-11-08:** the [new two-shape proof](../../docs/lighter-proofs/SHORT_SCALE_OUTER_LARGE_RATIO.md)
proves all three signs (7) on the unchanged closed domain (1)--(2).
A cubic beta comparison, beta convexity and two boundary
derivatives replace the coefficient tables below. Every expanded
identity has degree at most eight and at most 44 monomials; the
original scale and duration callers are preserved.

Date: 2026-11-08 UTC. Hand polynomial derivation, accepted in the
[independent outer-scale review](MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_AUDIT.md).
This note proves the three outer-scale signs used by the
[floor-weighted envelope reduction](MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md).
The reduction from an actual bridge remains the responsibility of that
theorem and the final contraction assembly.

The proof uses one explicitly specified polynomial, a finite coefficient
extraction rule, and the complete group norm table below. It does not use
an interval cover or an executable sign test as a premise.

## 1. The scalar domain and the three expressions

Assume

\[
\frac{12}{5}\le x\le9,\qquad
\frac{22x+20}{55}\le\alpha\le x,
\tag{1}
\]
\[
x+\frac{4x(\alpha-1)}{5x+4}\le\beta
 \le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{2}
\]

The beta interval is the combination of the proved
[global upper order](MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER.md) and
[strong lower order](MIXED_SMALLER_SHORT_STRONG_ORDER.md).
The alpha interval is a harmless enlargement of the actual outer-scale
face. Indeed q=1/7<=q_c is equivalent to
alpha^2>=x(x+2)/6, and

\[
\frac{x(x+2)}6-\left(\frac{22x+20}{55}\right)^2
 =\frac{121x^2+770x-2400}{18150}>0
 \qquad(x\ge12/5).
\tag{3}
\]

The numerator increases on this range and its value at 12/5 is 3624/25.

Set S=1+x, r_A=alpha/(alpha+beta), q=1/7, T=7r_A, and use the
[incoming rational norm bound](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)

\[
\bar u=\frac34+
 \frac{1}{\beta-1}\left\{
 \frac{2(x-1)^3}{(x+1)(35x+13)}
 +\frac{(\beta-x)^3}{48x^2}\right\}.
\tag{4}
\]

All the following quantities are scalar expressions at this fixed
shape. Define

\[
\varepsilon=1-\alpha^{-2},\quad n=S/\alpha^2,
\quad D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\quad d=D/\alpha^2,
\]
\[
E_0=S(\bar u-1)+S^{-1},
\]
\[
\begin{split}
A_1&=2\varepsilon+n+dE_0,\\
A_2&=\varepsilon^2+\varepsilon n+n^2+d^2\bar u
       +d\varepsilon E_0-d(2S-1)/\alpha^2,\\
A_3&=2d\bar u+\varepsilon E_0-(2S-1)/\alpha^2,
\end{split}
\tag{5}
\]
\[
w=1-qA_1+q^2A_2,\qquad E_L=-E_0+qA_3.
\]

For an independent logarithm value ell put

\[
F(\tau,\ell)
 =(w-1)\tau+\tau^{-1}
 +\frac{\bar u-1}{r_A}+r_A+1-q-E_L+\ell
 +\frac12(w-3/4).
\tag{6}
\]

The three claims proved below are

\[
\boxed{
F_T:=F(T,0)<0,\qquad
F_8:=F(8T/9,-1/9)<0,\qquad
F_2:=F\left(2,\frac5{2T}-\frac{11}{9}\right)<0.}
\tag{7}
\]

They hold on the entire closed scalar domain (1)--(2). No separate
outgoing floor or upper Casimir cap is assumed after this comparison.

## 2. Why these three signs control every eligible tau

For y>0 the elementary tangent inequalities give

\[
\log y\le\min\left\{y-1,\frac54y-\frac{11}{9}\right\}.
\tag{8}
\]

For the second line, concavity gives the tangent at y=4/5, while

\[
\log(5/4)=2\int_0^{1/9}\frac{ds}{1-s^2}>\frac29.
\]

Thus log(4/5)<-2/9 and that tangent is strictly below
5y/4-11/9. The two displayed upper lines intersect at y=8/9.

Substitute y=tau/T in (8) and in (6). On each of the resulting two
tau intervals, the upper expression has second derivative 2/tau^3>0:
all its other tau dependence is affine. A convex function on an
interval is bounded above by the larger endpoint value. Consequently,
on 2<=tau<=T, its maximum is controlled by tau=2,T, and the interior
breakpoint 8T/9 when that breakpoint is present.

At tau=2 the second line alone, used in F_2, may be larger than the
minimum in (8); proving its negative sign is therefore sufficient.
At T and 8T/9 the values in (7) are the stated upper endpoint values.
Thus (7) implies

\[
F(\tau,\log(\tau/T))<0\qquad(2\le\tau\le T).
\tag{9}
\]

If T<2 the last interval is empty. Proving all three expressions in
(7), even when their tau values are not eligible, is a scalar sign
argument and does not assert the existence of an artificial trajectory.

## 3. One polynomial specification for all three faces

The common positive denominator used below is

\[
\mathcal D=4704\alpha^4x^2(\alpha+\beta)(\beta-1)
                  (x+1)(35x+13).
\tag{10}
\]

For f in {T,8,2} define

\[
P_f(x,\alpha,\beta)=-\mathcal D F_f.
\tag{11}
\]

Equations (4)--(7), (10)--(11) are the complete definition of these
three polynomials over the rationals. In particular, their degree in
beta is at most six. The normalization in (10) is common to all three
faces; the 8 and 2 polynomials need not have integral coefficients.
No additional face-dependent rescaling is implicit.

Write

\[
Q=4x^2+11x+1,\qquad L=(5x+4)Q,
\]
\[
x=\frac{12}{5}+X,\qquad
\alpha=\frac{22x+20+(33x-20)z}{55},
\tag{12}
\]
\[
\beta=\frac{xQ(5x+4\alpha)
                +x^2(19x-11)(\alpha-1)t}{L}.
\tag{13}
\]

The scalar domain is contained in X>=0, 0<=z<=1, 0<=t<=1.
Equation (13) runs exactly from the lower beta endpoint in (2) to its
upper endpoint. Let

\[
\widehat P_f(X,z,t)
 =L^6P_f(x,\alpha,\beta)
\tag{14}
\]

after these substitutions. This is a polynomial of degree at most six
in t, eight in z, and 29 in X. The following specifies every coefficient
used in the proof:

\[
\widehat P_f
 =\sum_{i=0}^6\binom6i t^i(1-t)^{6-i}
       \sum_{k=0}^{29}X^k\sum_{j=0}^8c_{fijk}z^j.
\tag{15}
\]

Equivalently, using ordinary monomial coefficient extraction,

\[
\boxed{
c_{fijk}=\sum_{\ell=0}^i
 \frac{\binom i\ell}{\binom6\ell}
 [X^kz^jt^\ell],\widehat P_f.}
\tag{16}
\]

Formula (16), together with the short rational definitions (4)--(14),
makes the finite arithmetic below independently reconstructible.

## 4. Complete grouped coefficient bounds

For each k, the following table gives integers e,A,B,C,M. Its meaning
is the four exact rational inequalities

\[
c_{fi0k}\ge10^eA,\qquad c_{fi1k}\ge10^eB,
\qquad c_{fi2k}\ge10^eC,
\tag{17}
\]
\[
\boxed{
\sum_{j=3}^8\max\{0,-c_{fijk}\}\le10^eM,}
\tag{18}
\]

simultaneously for every f in {T,8,2} and every i in {0,...,6}.
These are grouped bounds for the complete negative part of the
remaining six z coefficients, including zeros. There are no other
coefficient groups to check.

| k | e | A | B | C | M |
|---:|---:|---:|---:|---:|---:|
| 0 | 21 | 134 | 40377 | 46525 | 45070 |
| 1 | 22 | 240 | 43581 | 52099 | 48682 |
| 2 | 23 | 172 | 22556 | 27914 | 25278 |
| 3 | 23 | 753 | 74403 | 95337 | 84025 |
| 4 | 24 | 233 | 17582 | 23327 | 20088 |
| 5 | 24 | 539 | 31817 | 43569 | 36788 |
| 6 | 24 | 955 | 45857 | 64616 | 53674 |
| 7 | 25 | 136 | 5405 | 7620 | 6407 |
| 8 | 25 | 160 | 5309 | 7481 | 6373 |
| 9 | 25 | 157 | 4405 | 6203 | 5358 |
| 10 | 25 | 130 | 3120 | 4389 | 3845 |
| 11 | 24 | 925 | 19002 | 26706 | 23735 |
| 12 | 24 | 563 | 10005 | 14049 | 12679 |
| 13 | 24 | 295 | 4560 | 6414 | 5882 |
| 14 | 24 | 134 | 1806 | 2548 | 2376 |
| 15 | 23 | 529 | 6235 | 8818 | 8363 |
| 16 | 23 | 180 | 1874 | 2658 | 2567 |
| 17 | 22 | 512 | 4903 | 6971 | 6859 |
| 18 | 22 | 125 | 1113 | 1586 | 1592 |
| 19 | 21 | 265 | 2186 | 3121 | 3198 |
| 20 | 20 | 481 | 3692 | 5278 | 5528 |
| 21 | 19 | 741 | 5321 | 7614 | 8161 |
| 22 | 18 | 963 | 6480 | 9275 | 10187 |
| 23 | 18 | 103 | 657 | 940 | 1061 |
| 24 | 16 | 914 | 5461 | 7802 | 9035 |
| 25 | 15 | 639 | 3612 | 5150 | 6135 |
| 26 | 14 | 341 | 1830 | 2601 | 3192 |
| 27 | 13 | 131 | 667 | 944 | 1195 |
| 28 | 11 | 320 | 1555 | 2191 | 2860 |
| 29 | 9 | 376 | 1744 | 2443 | 3290 |

For clarity, one exact way to verify the table is to expand the
explicit polynomial (14), apply (16), and for each k take the minima
of the three coefficients in (17) over the 21 pairs (f,i), and the
maximum of the six-term sum in (18). The table rounds these rational
minima down and the rational maximum up after division by 10^e.
Its entries are finite arithmetic bounds, not results of testing
points of the continuous shape domain.

## 5. The quadratic lower bounds prove all three signs

For 0<=z<=1 and j>=3, a negative coefficient obeys
c*z^j>=c*z^2. Positive terms of those degrees can be discarded in a
lower bound. Equations (17)--(18) therefore give, for every f,i,k,

\[
\sum_{j=0}^8c_{fijk}z^j
 \ge10^e\{A+Bz+(C-M)z^2\}>0.
\tag{19}
\]

To check the last sign by hand, every row has A>0, B>0 and
A+B+C-M>0. If C>=M the quadratic is visibly positive. If C<M,
it is concave and lies above the chord between its positive endpoint
values A and A+B+C-M. Thus every row of (19) is positive on [0,1].

All powers X^k in (15) are nonnegative. The seven Bernstein basis
terms in t are nonnegative and sum to one. The k=0 row is already
strictly positive, so (15) gives

\[
\widehat P_f>0\qquad(f=T,8,2)
\]

on the whole scalar domain. The factors L and mathcal D are positive.
Undoing (14) and (11) proves precisely (7). Section 2 then proves the
uniform outer-scale sign (9).

The proof does not change the actual PMP covector, identify an
artificial endpoint with a trajectory, or infer an outgoing floor after
a deformation. Those issues belong to the actual floor-weighted
comparison and scale reduction to which this scalar lemma is applied.

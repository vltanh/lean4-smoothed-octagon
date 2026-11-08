# Completed outer upper-ratio caller replacement

This collection replaces the large signs (11)--(18) in
[the archived outer-ratio proof](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md).
It proves that the original outer comparison endpoint cannot carry
the positive variable-floor duration test when
\(13/6\le x\le12/5\). The norm substitutions and duration
conclusion are exactly those of the source caller.

The proof uses reciprocal-shape convexity, a beta comparison only at
the lower shape, and three terminal families. All polynomial signs are
proved after reducing to one or two variables. At larger shapes it
retains the original condition \(a\le x\); this closes the actual
caller and removes the need for the source's larger scalar rectangle
in (17).

## 1. Original domain and transport

Write \(a=\alpha,b=\beta\). The actual outer endpoint satisfies

\[
\frac{13}{6}\le x\le\frac{12}{5},\quad
1\le a\le x,\quad a^2\ge\frac{x(x+2)}6,
\tag{1}
\]
\[
x+\frac{8x(a-1)}{9x+8}\le b\le
x+\frac{x(7x+1)(a-1)}{4x^2+11x+1}.
\tag{2}
\]

The outer scale remains \(q=1/7\). For an incoming norm scalar u,
put

\[
S=x+1,\quad B=a+b,\quad M=6a^2+1,
\quad D=a^2+2ab+1+2x-2bx,
\]
\[
N=M\{S(u-1)+S^{-1}\}+2S-1,
\]
\[
w=\frac{M^2-MS+S^2+D^2u-DN}{49a^4},
\qquad E_L=\frac{2Du-N}{7a^2},
\qquad k=\frac{B}{7a}=1/T.
\tag{3}
\]

The original variable-floor test is

\[
\begin{aligned}
G_\tau={}&(w-1)\tau+\tau^{-1}+(u-1)B/a+a/B+6/7-E_L
+\log(\tau k)\\
&+\left(2-\frac{7\tau k}{4}\right)(w-3/4),
\qquad 2\le\tau\le T.
\end{aligned}
\tag{4}
\]

The [accepted variable-floor reduction](../../archive/notes/MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md)
gives strict positivity of the incoming-norm coefficient at the original
outer endpoint. Thus the original incoming norm may be raised to the
proved ceiling used below before any scalar shape comparison.

The duration calculation is unchanged. For either sign of
\(w-3/4\),

\[
G_\tau'=(1-7k/4)(w-3/4)-\frac{(\tau-2)^2}{4\tau^2}
\le(1-7k/4)(w-3/4).
\]

Integration therefore gives

\[
G_\tau\le\max\{H_0,H_1\},
\tag{5}
\]

where

\[
\begin{aligned}
H_0={}&6/7+(u-1)B/a+a/B-E_L
+\left(4-\frac{B}{2a}\right)(w-3/4)+\log(2k),\\
H_1={}&6/7+(u-1)B/a+a/B-E_L
+\left(\frac{7a}{B}+\frac14\right)(w-3/4)+\log(2k).
\end{aligned}
\tag{6}
\]

The first is \(G_2\); the second is the endpoint of the affine
upper bound for \(G_\tau\). In particular (5) remains valid after
raising the norm even when the continued scalar w is below \(3/4\).

## 2. Domain bounds and norm ceilings

The actual domain implies

\[
a\ge a_f(x):=\frac{36x+25}{84}>\frac65,
\qquad b=x+c(a-1),
\qquad \frac58\le c\le c_+(x):=\frac{24x+51}{128}<\frac78.
\tag{7}
\]

For the shape bound, the difference between the squared bounds has
numerator

\[
84^2x(x+2)-6(36x+25)^2=-720x^2+3312x-3750.
\]

This concave quadratic has endpoint values \(46,258/5\).
For the lower c bound, use \(19x\ge40\). For the upper one,
with \(h=x-2\ge0\), the positive-denominator numerator of the
difference between \(c_+\) and the upper slope in (2) is

\[
96h^3+148h^2-103h+21
=96h^3+148\left(h-\frac{103}{296}\right)^2+\frac{1823}{592}>0.
\tag{8}
\]

All scalar paths below have \(a\ge1,c<x\), hence \(b\le ax\)
and \(0<2k\le2S/7\le34/35<1\). Their logarithms and duration
intervals are valid.

We retain the two proved incoming bounds from source Section 3:

\[
u_{\rm actual}\le u_s:=\frac34+
\frac{17(x-1)^3/(240S^2)+(b-x)/1200}{b-1}
\qquad(a\le3/2),
\tag{9}
\]
\[
u_{\rm actual}\le u_v:=\frac34+
\frac{2(x-1)^2}{S(35x+13)}
\qquad(a\ge3/2).
\tag{10}
\]

Bound (9) uses the Gauss incoming estimate and the tail bound
\((b-x)^3/(48x^2)\le(b-x)/1200\) at the original smaller shape.
Bound (10) uses the original equal-secant incoming comparison followed
by the rational bound for its symmetric norm. These are unchanged
dependencies; the larger polynomial derivative and terminal signs in
source Sections 4--6 are not used.

The norm is raised only at the original outer endpoint. Subsequent
steps compare the explicit rational expressions (3),(6), with their
logarithm, on stated scalar paths.

## 3. Smaller shapes

Assume \(a_f(x)\le a\le3/2\) and use norm \(u_s\). At fixed
\(x,c\), the [reciprocal proof](SHORT_RATIO_OUTER_RECIPROCAL.md)
gives

\[
\frac{d^2}{dr^2}H_j(x,1/r,x+c(1/r-1);u_s)>\frac25,
\quad r=1/a.
\]

The interval \(2/3\le r\le1/a_f<5/6\) lies entirely in its
proved domain. Convexity therefore bounds each test by the larger of
its two endpoint values.

At \(a=a_f\), the [beta proof](SHORT_RATIO_OUTER_BETA.md) gives a
strictly positive total beta derivative at the moving norm. It reaches
\(c=c_+(x)\), where the
[lower-shape terminal proof](SHORT_RATIO_OUTER_TERMINAL_AF.md)
gives both strict negative signs. That proof also records a margin
\(1/5000\) for the first comparison on \([13/6,9/4]\), and
\(1/1000\) on \([9/4,12/5]\).

At \(a=3/2\), the beta proof gives \(u_s\le u_v\), and the
reciprocal proof gives \((H_j)_u>0\) along that norm interval.
Thus this endpoint is bounded by the
[middle terminal at norm \(u_v\)](SHORT_RATIO_OUTER_OTHER_TERMINALS.md),
which is strictly negative for every \(5/8\le c\le7/8\).

Both endpoints are strictly negative. Convexity proves
\(H_0,H_1<0\) throughout the original smaller-shape branch.

## 4. Larger shapes

Assume \(3/2\le a\le x\) and use norm \(u_v\), which is
constant during the reciprocal-shape comparison and lies in
\((3/4,4/5)\). The reciprocal proof gives

\[
(H_j)_{rr}>1/2\qquad(1/x\le r\le2/3).
\]

Its two endpoints are \(a=3/2\) and \(a=x\). The
[two larger-shape terminal proofs](SHORT_RATIO_OUTER_OTHER_TERMINALS.md)
give both negative signs on the entire c interval at each endpoint.
Convexity again yields \(H_0,H_1<0\) throughout this branch.
The common shape \(a=3/2\) is included in both arguments.

## 5. Caller closure and verification boundary

In either branch, the proved incoming-norm ceiling followed by (5)
gives \(G_\tau<0\) for every original outer endpoint and every
\(2\le\tau\le T\). This excludes the original positive
variable-floor test (4). The conclusion is exactly the outer terminal
required by the source upper-ratio assembly, with its domain (1),(2)
and actual incoming norm preserved.

The proof has one shape split at \(a=3/2\) and one ratio split at
\(x=9/4\) in the lower terminal. The middle and upper terminals
need no ratio subdivision. Every expanded sign or source identity is
printed in the linked notes and has at most two remaining variables,
degree at most eight, at most 150 monomials, and coefficient numerators
and denominators of at most twelve digits. Norm affinity, reciprocal
differentiation, or the actual terminal substitution occurs before
expansion; factored source contributions are included in the size audit.

The elementary incoming ceilings and original variable-floor norm
monotonicity remain dependencies. No outgoing physical floor, upper
Casimir cap, or equal-secant relation is reassigned to the continued
scalar comparisons. Exact symbolic calculations check transcription and
the identity sizes; the displayed identities and inequalities provide
the mathematical proof. No Lean compilation, Lake, typechecking or CI
has been run.

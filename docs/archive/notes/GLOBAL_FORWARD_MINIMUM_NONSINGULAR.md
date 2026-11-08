# The forward minimum's three-arc system has no interior rank defect

Date: 2026-11-07. Hand algebra with an exact symbolic checker.
No Lean, Lake, typechecking, or CI.

## Purpose and scope

This note records a uniform simplification for the remaining F cost–Casimir
problem. At a global active-margin minimum above the circular scale, the
two equations determining the same primary multiplier from the three
interior arcs are nonsingular. Consequently an exact scalar certificate
may safely use their Cramer formulas throughout the interior domain. The
only common zero-duration corner where the stated lower bound vanishes is
handled separately by a limit or a corner estimate.

This is **not** a proof of the F exclusion. The needed uniform cost–Casimir
inequality remains open. In particular, one cannot justify reducing the
five variables to the symmetric outer-minimum face merely by asserting
monotonicity in the exterior factors.

## 1. Dimensionless variables and the actual system

Use the common-covector equations (7)–(9) of
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).
Let the five actual consecutive margins be `(p,b,a,c,d)`, with `a` the
smallest. Set

\[
U=4/a^2,\qquad z=b/a,\qquad w=c/a,\qquad
S=1+z,\quad T=1+w,\quad L=1+U,
\]
\[
q=ST/L,\qquad H=h-1,\quad K=k-1,
\]

where `h,q,k` are the three actual positive arc factors. In the remaining
F domain,

\[
11/5<U<3,\qquad 1\le z,w<U,\qquad q>1,\qquad H,K>0.
\tag{1}
\]

The bounds on `U` come from the minimum scale bounds; `z,w<U` are the
strict-star inequalities. Write `Mhat=M/a` for the coefficient matrix
in that note. Its entries are

\[
\widehat M_{11}=\frac{S^2(U-z)H}{z^2+U},\qquad
\widehat M_{12}=\frac{L^2[(q-1)+H(Sq-1)]}{S(z^2+U)},
\]
\[
\widehat M_{22}=\frac{T^2(U-w)K}{w^2+U},\qquad
\widehat M_{21}=\frac{L^2[(q-1)+K(Tq-1)]}{T(w^2+U)}.
\tag{2}
\]

Every entry is positive.

## 2. A positive factorization of the negative determinant

Define

\[
\begin{aligned}
P(U,z,w)={}&w^2(z+1)(U-z)\\
&+w\{U(z+1)(z+3)-z^2+1\}\\
&+Uz(z+3)-U^2+z.
\end{aligned}
\tag{3}
\]

Then direct multiplication gives

\[
\boxed{\begin{aligned}
&-\det\widehat M\;ST(z^2+U)(w^2+U)\\
&=L^4\bigl[(q-1)^2+(q-1)\{H(Sq-1)+K(Tq-1)\}\bigr]\\
&\quad+HK(ST-L)(ST+L)P(U,z,w).
\end{aligned}}
\tag{4}
\]

Here `P>0` on (1). Its first term is positive. In its second term,
`U>z` gives

\[
U(z+1)(z+3)-z^2+1>(z+1)^3>0.
\]

Its last line is `U[z(z+3)-U]+z>0`, because `z>=1` and `U<3`.
Also `Sq-1,Tq-1>0`, and `ST-L=L(q-1)>0`. Thus every term on the
right of (4) is positive, proving

\[
\boxed{\det\widehat M<0,\qquad\det M=a^2\det\widehat M<0.}
\tag{5}
\]

A useful explicit estimate follows by retaining the first square:

\[
-\det\widehat M\ge
\frac{L^4(q-1)^2}{ST(z^2+U)(w^2+U)}>0.
\tag{6}
\]

The same argument permits `H=0` or `K=0` in the closure of the comparison
domain as long as `q>1`. On the closed scale-and-neighbour domain
`11/5<=U<=3`, `1<=z,w<=U`, the equation `q=1` implies
`U=3,z=w=1`, since `ST>=4>=L`. Thus the only exceptional central
zero-duration corner is explicitly identified. This is a statement about
the displayed local normal system; it does not replace or change the
separate full endpoint-rank theorem.

## 3. Boundary on an exterior-factor reduction

In the scalar relaxed domain, lowering `p,d` to `a` need not lower the
Casimir supplied by the three actual stationarity equations. A diagnostic
is obtained by fixing

\[
a=13/10,\qquad b=c=3611/2600,
\]

and moving the two exterior factors together from

\[
h=k=\frac{(a+b)^2}{b^2+4}
\]

to `h=k=H0+(Hmax-H0)/100`, where
`H0=(a+b)^2/(b^2+4)` and `Hmax=1+a/b`. The local stationarity
solution's physical squared Casimir decreases from approximately
`2.234982592` to `2.234758425`. All four weak switching-derivative
inequalities and all four missing-control inequalities in the existing
five-active diagnostic remain positive at both endpoints. This numerical
example is discovery evidence only: it is neither a global closed period
nor an exactly certified counterexample to the still-open F theorem.
It explains why a proposed rigorous symmetric-face reduction must use a
combined cost–Casimir comparison rather than that unqualified
monotonicity assertion.

## Verification boundary

The companion
[global_forward_minimum_rank_certificate.py](../explorations/global_forward_minimum_rank_certificate.py)
verifies (4), the exact formula (3), and the determinant normalization.
The inequalities and common-covector interpretation are the hand argument
above. No new global competitor class is excluded. The determinant
factorization provides a safe interior denominator for the finite
continuous-domain certificate sought in F1.

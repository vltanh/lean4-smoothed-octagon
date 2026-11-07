# The opposite norm floor cannot occur alone when the short diagonal is nonpositive

Date: 2026-11-07. Hand proof, accepted in independent internal review.
See [HAND_FURTHER_REFINEMENTS_AUDIT](HAND_FURTHER_REFINEMENTS_AUDIT.md).

This removes the nonpositive-diagonal part of one stopping face in
[MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
It does not exclude the remaining positive-diagonal part or the other
boundary faces. The argument is a scalar inequality; no runtime
certificate or large coefficient table is used.

## 1. Statement

Use the actual short-bridge geometry, retained throughout the scalar
comparison:

\[
1\le\alpha<x\le\beta\le\alpha x,\qquad
\alpha\ge\frac\beta x+\frac27(\beta-x),\qquad
r=\frac1{1+x},\quad 0<\rho\le rt,\quad 0<t\le r.
\]

Its fixed incoming norm satisfies

\[
\tfrac34<u\le V(x):=\operatorname{Sec}(1,x,x).
\]

The order and the bound u<=V(x) use only the integral/secant arguments
in Sections 1--2 of
[MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md).
The later polynomial comparison in that note is not used here.

Define

\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad
\lambda=[1+\rho(\alpha^2-1)]^{-1},\quad d=\lambda\rho D,
\]
\[
E=\frac{u-1}{r}+\frac{v-1}{t}
 +1+r+t-\rho+\log\frac{\rho}{rt},
\qquad w=\lambda^2v+d^2u-d\lambda E.
\]

**Lemma.** If D<=0 and v=3/4, then

\[
\boxed{E-\rho Du<0,\qquad w\le\tfrac34.}
\tag{1}
\]

The last inequality is strict if D<0, or if alpha>1. In particular,
within a comparison retaining w>=3/4, the face v=3/4 with D<=0 is
either impossible or already belongs to the face w=3/4.

Neither the upper Casimir cap nor the outer root is needed for this
lemma.

## 2. A short rational bound for the incoming norm

The secant integral gives

\[
V(x)-\frac34
=\frac1{4(x-1)}\int_1^x\frac{(s-x)^2}{(s+x)^2}\,ds
\le\frac{(x-1)^2}{12(x+1)^2}.
\]

Indeed \(s+x\ge1+x\), and the remaining integral of \((s-x)^2\)
is \((x-1)^3/3\). Put

\[
S=1+x,\qquad \bar u=\frac34+\frac{(x-1)^2}{12S^2}.
\tag{2}
\]

Thus u<=ubar by a single integral bound.

## 3. Move the central scalar expression to its upper endpoint

Write \(F_0=E-\rho Du\) and set v=3/4. At fixed rho,

\[
\frac{\partial F_0}{\partial t}
=\frac{(t-1/2)^2}{t^2}>0\qquad(0<t\le r<1/2).
\]

Raise t to r; this preserves rho<=rt. Then, holding t=r,

\[
\frac{\partial F_0}{\partial\rho}
=\frac1\rho-1-Du>0\qquad(0<\rho\le r^2<1/4, D\le0).
\]

Raise rho to r^2. These are comparisons of a scalar expression, with
all short-bridge ratios and u fixed. They yield

\[
F_0\le u\left(S-\frac D{S^2}\right)
       -\frac54S+1+\frac2S-\frac1{S^2}.
\tag{3}
\]

Since D<=0, the coefficient of u in (3) is positive. We may therefore
replace u by ubar from (2) when obtaining an upper bound.

## 4. One quadratic shape bound and one univariate sign

Put \(k=\beta/x\ge1\). The strengthened short order says

\[
\alpha\ge \frac{(7+2x)k-2x}{7}.
\]

D is strictly increasing in alpha, because its alpha derivative is
\(2(\alpha+\beta)>0\). Substituting this lower endpoint gives

\[
D\ge A k^2+B k+C,
\]
\[
A=\frac{(2x+7)(16x+7)}{49}>0,
\quad B=-\frac{2x(67x+14)}{49},
\quad C=1+2x+\frac{4x^2}{49}.
\tag{4}
\]

First, D<=0 forces x>2. If 1<x<=2, the derivative of the quadratic
in (4) is positive for k>=1: at k=1 it is

\[
2A+B=\frac{2(-35x^2+112x+49)}{49}>0.
\]

The numerator is a concave quadratic, positive at x=1 and x=2, hence
positive throughout [1,2]. The minimum over k>=1 is then at k=1,
where the quadratic is \(2+4x-2x^2\ge2>0\), a contradiction.

For x>=2, complete the square in (4):

\[
D\ge C-\frac{B^2}{4A}.
\tag{5}
\]

Insert (2) and (5) into the right side of (3). Collecting the displayed
quadratic expressions gives the following single-variable identity:

\[
\bar u\left(S-\frac{C-B^2/(4A)}{S^2}\right)
 -\frac54S+1+\frac2S-\frac1{S^2}
=-\frac{P(x)}{12S^4(2x+7)(16x+7)},
\tag{6}
\]
\[
\begin{aligned}
P(x)={}&160x^7+284x^6+1003x^5-141x^4\\
       &-4310x^3-5566x^2-2653x-441.
\end{aligned}
\]

The sign of this polynomial does not require a coefficient table. Divide
it by x^5:

\[
\frac{P(x)}{x^5}
=160x^2+284x+1003-\frac{141}x-\frac{4310}{x^2}
 -\frac{5566}{x^3}-\frac{2653}{x^4}-\frac{441}{x^5}.
\]

Every nonconstant term is strictly increasing on x>0. At x=2 its value
is \(6005/32>0\). Hence P(x)>0 for all x>=2. The denominator in (6)
is positive, so (3)--(6) prove \(F_0<0\).

Finally the exact transport identity is

\[
w=\lambda^2v-d\lambda F_0.
\]

For D<0, both d and F0 are negative, so
\(w<\lambda^2v\le v=3/4\). For D=0,
\(w=\lambda^2v\le v\), with strictness when alpha>1. This proves
(1) and the stated stopping-face consequence.

## 5. The remaining positive-diagonal floor question

In the root-preserving comparison, if \(1-\tau d\le0\), then
\(v'\ge0\), so the path cannot reach v=3/4 from an actual v>3/4.
Combined with the lemma above, a separate v-floor endpoint could only
remain when

\[
D>0,\qquad 0<\tau d<1.
\]

Writing
\(C_0=-f(\tau)+u/r_A-f(1/r_A)-h(1/\rho_A)\), the fixed-root
equation gives

\[
(1-\tau d)w=\lambda^2v-d^2u+dC_0.
\]

Thus a sufficient further face-collapse inequality would be

\[
\tfrac34(1-\tau d-\lambda^2)+d^2u-dC_0\ge0.
\]

It is not proved here on the remaining positive-diagonal domain. That
case and the other stopping faces remain open.

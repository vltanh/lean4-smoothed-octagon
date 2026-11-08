# A nonnegative short diagonal has positive outer pairing

Date: 2026-11-07. Complete hand lemma, accepted in the
[independent pairing review](MIXED_SMALLER_SHORT_PAIRING_HAND_AUDIT.md).

This proves a uniform sign on the actual short geometry retained by the
root-preserving comparison. It does not exclude the remaining short
faces. In particular it does not establish that the diagonal is
nonnegative, or settle the physical completion-cost comparison.

The proof uses only the integral equal-secant continuation in Section 1
of [MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md).
It does not use the polynomial certificate later in that note.

## 1. Statement

Retain
\[
1\le\alpha<x\le\beta\le\alpha x,\qquad x>1,\qquad
u=\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x),
\]
\[
r=(1+x)^{-1},\qquad 0<\rho\le r^2,\qquad
\rho/r\le t\le r,\qquad v\le U(t),\qquad U(s)=1-s+s^2.
\]
Define the central pairing and short transport by
\[
E=\frac{u-1}{r}+\frac{v-1}{t}
 +1+r+t-\rho+\log\frac{\rho}{rt},
\]
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad
\lambda=[1+\rho(\alpha^2-1)]^{-1}>0,
\]
\[
E_L=\lambda(2\rho Du-E).
\]
Then
\[
\boxed{D\ge0\quad\Longrightarrow\quad E_L>0.}
\tag{1}
\]
In fact the following more precise statements hold:
\[
\boxed{1<x\le12/5\quad\Longrightarrow\quad D>0\text{ and }E_L>0,}
\tag{2}
\]
\[
\boxed{x\ge12/5\quad\Longrightarrow\quad E<0.}
\tag{3}
\]
Consequently a point with \(E_L\le0\) necessarily has both
\(x>12/5\) and \(D<0\).

These statements need neither an outer reverse root nor a Casimir cap.
Thus they apply throughout the fixed-geometry root comparison, whose
central upper norm and duration inequalities are retained.

## 2. A central envelope and a rational secant bound

Put \(S=1+x\). Raising \(v\) to \(U(t)\) raises \(E\), and
\[
\frac{d}{dt}E(t,U(t))=2-1/t<0
\qquad(\rho S\le t\le1/S<1/2).
\]
Hence
\[
E\le E_*:=S(u-1)+S^{-1}+\rho(2S-1).
\tag{4}
\]
The incoming short secant decreases along the exact equal-secant branch,
so \(u\le V(x):=\operatorname{Sec}(1,x,x)\). The elementary integral
identity
\[
V(x)-\frac34
=\frac1{4(x-1)}\int_1^x\frac{(s-x)^2}{(s+x)^2}\,ds
\le\frac{(x-1)^2}{12(x+1)^2}
\]
gives
\[
u\le\bar u(x):=\frac34+\frac{(x-1)^2}{12S^2}.
\tag{5}
\]
Only \(s+x\ge1+x\) and integration of \((s-x)^2\) were used.
Also \(u\le U(1/S)\), by the same integral bounds already retained
in the short-root interface.

## 3. Large incoming ratio

Since \(2S-1>0\), (4), \(\rho\le S^{-2}\), and (5) imply
\[
E\le S(\bar u-1)+3/S-1/S^2
=-\frac{Q(x)}{6S^2},
\]
\[
Q(x)=x^3+5x^2-13x-11.
\tag{6}
\]
For \(x>1\),
\[
Q'(x)=3x^2+10x-13=(x-1)(3x+13)>0.
\]
At \(x=12/5\), \(Q=53/125>0\). This proves (3).
If also \(D\ge0\), then \(2\rho Du\ge0>E\), proving (1)
on this range.

## 4. Small incoming ratio: monotonicity along the short secants

Assume \(1<x\le12/5\). Hold \(x,\rho\) fixed and continue
\(\beta\) from \(x\) to its actual value along the exact
short equal-secant branch. Write its functions as \(u(\beta)\) and
\(\alpha(\beta)\). At the starting point \(\alpha=1\) and
\(u=V(x)\). The integral continuation gives
\[
u_\beta<0,\qquad \alpha_\beta>\alpha/\beta,
\qquad \beta\le\alpha x
\tag{7}
\]
on the complete segment. For clarity, with
\[
g(z)=1-z/(1+z)^2,\quad
\eta=u-g(x/\beta)>0,\quad
\xi=g(\alpha/\beta)-u>0,
\]
the exact derivatives are
\[
u_\beta=-\frac\eta{\beta-1},\qquad
\alpha_\beta=\frac\alpha\beta+
 \frac\eta\xi\left(\frac x\beta+
                      \frac{x-\alpha}{\beta-1}\right).
\]
The uniqueness and existence of this continuation, and the order in
(7), are proved by the two-average comparison cited at the start.

Along it,
\[
D_\beta=2(\alpha+\beta)\alpha_\beta+2\alpha-2x
>\frac{2\alpha^2}{\beta}+4\alpha-2x
\ge\frac2x+4-2x.
\]
The last function decreases in \(x\). At \(x=12/5\), it is
\(1/30>0\). Thus \(D_\beta>0\) throughout this range, and
\[
D\ge D_0:=2+4x-2x^2\ge D_0(12/5)=2/25>0.
\tag{8}
\]
The last comparison uses \(D_0'(x)=4-4x<0\).

Furthermore \(D\le S^2\): at fixed \(\beta,x\), the expression
for \(D\) increases in \(\alpha\), and its value at \(\alpha=x\)
is \(S^2\). Define
\[
F_2:=E_*-2\rho Du
=S(u-1)+S^{-1}+\rho(2S-1-2Du).
\]
Its branch derivative is
\[
(F_2)_\beta=(S-2\rho D)u_\beta-2\rho uD_\beta<0,
\tag{9}
\]
since
\(S-2\rho D\ge S-2>0\), \(u>0\), and (7)--(8) supply
the two derivative signs.
It is therefore enough to bound \(F_2\) at \(\beta=x,\alpha=1\),
with the original \(x,\rho\) unchanged.

## 5. The two affine scale endpoints are negative

At this equal-centre starting point, \(F_2\) is affine in \(\rho\).
It suffices to prove strict negativity at \(\rho=0\) and
\(\rho=S^{-2}\).

At zero,
\[
F_2(0)=S(V(x)-1)+S^{-1}
\le S(U(1/S)-1)+S^{-1}=-1+2/S<0.
\tag{10}
\]
At \(\rho=S^{-2}\), the coefficient of \(V(x)\) is positive:
\[
S-2D_0/S^2
=\frac{(x-1)(x^2+8x+3)}{S^2}>0.
\]
Thus replacing \(V(x)\) by \(\bar u(x)\) from (5) gives
\[
F_2(S^{-2})
\le\bar u\,(S-2D_0/S^2)-S+3/S-1/S^2
=-\frac{P(x)}{6S^4},
\tag{11}
\]
\[
P(x)=x^5-13x^4+6x^3+32x^2+37x+9.
\]
To check the sign without a coefficient table, divide by \(x^4\):
\[
\frac{P(x)}{x^4}
=x-13+\frac6x+\frac{32}{x^2}+\frac{37}{x^3}+\frac9{x^4}.
\]
Its derivative is
\[
1-\frac6{x^2}-\frac{64}{x^3}-\frac{111}{x^4}-\frac{36}{x^5}<0
\quad(1\le x\le12/5),
\]
because \(x^2\le144/25<6\). At the upper endpoint,
\(P(12/5)=41817/3125>0\). Therefore \(P(x)>0\) throughout
this interval, and (11) is strictly negative.

Affinity in \(\rho\), (9), and (4) now give
\[
E-2\rho Du\le E_*-2\rho Du=F_2<0.
\]
Multiplication by \(-\lambda<0\) proves \(E_L>0\), completing
(2) and the uniform assertion (1).

## 6. Consequence and remaining boundary obligation

On the \(w=3/4\) face, the positive-pairing comparison in
[MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION](MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION.md)
therefore applies throughout the entire \(D\ge0\) branch. A remaining
nonpositive-pairing point must instead satisfy
\[
x>12/5,\qquad D<0.
\]
This is a genuine sign restriction on that branch, and uses the same
fixed physical short geometry as the earlier root comparison. It does
not transport an actual lower Casimir bound to an artificial point.
The \(D<0\) branch and the endpoint cost signs still require exclusion;
no smaller-short closure is asserted here.

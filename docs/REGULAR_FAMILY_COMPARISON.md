# The octagon uniquely minimizes the standard regular smoothed-polygon family

## Result and scope

For every positive integer \(k\), consider the standard regular smoothed
\((6k+2)\)-gon constructed in Hales–Vajjha, Chapter 7. It has
\(N=3k+1\) equal positive control arcs in cyclic order. Its physical cost
\(C_N\) satisfies

\[
\boxed{C_4<C_7<C_{10}<\cdots<\pi,\qquad
\lim_{k\to\infty}C_{3k+1}=\pi.}
\tag{1}
\]

Here \(C_4=A_{\rm oct}\). Thus the octagon uniquely minimizes cost within
this entire infinite family. The argument proves strict monotonicity of
the natural continuous interpolation for all real \(N\ge4\), so it does
not rest on checking finitely many integers.

This family has equal factors and a specific initial shape. It does not
include arbitrary asymmetric trajectories with the same cyclic word, or
all smoothed polygons with \(6k+2\) sides. No restriction of an arbitrary
minimizer to this family is assumed or proved.

The construction and endpoint condition are from Hales–Vajjha,
[Lemma 7.5.5 and Theorem 7.5.6](https://arxiv.org/html/2405.04331v1#Ch7.S5).
The same state and cost conventions occur in the pinned reference's
[SmoothedPolygon.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/SmoothedPolygon.lean),
including its explicit one-arc cost primitive. The cost integration and
strict inequality below are displayed as hand arguments. No Lean
compilation, numerical optimization, or computer certificate is used.

## 1. Exact cost of the standard family

Put

\[
\theta_k=\frac{\pi k}{3k+1},\qquad
r=2\cos\theta_k,\qquad
y_0^2=\frac{4/r-1}{3},\qquad
\tau=\frac{\log r}{\sqrt3\,y_0}.
\tag{2}
\]

For \(k\ge1\), one has
\(1<r\le\sqrt2\) and \(1/\sqrt3<y_0<1\).
On one constant-control arc, the actual upper-half-plane state is

\[
x(t)=\frac{e^{at}-1}{\sqrt3},\qquad
y(t)=y_0e^{at},\qquad
a=\sqrt3\,y_0,\qquad 0\le t\le\tau.
\tag{3}
\]

For
\[
X=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\qquad
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
\]
substitution into the cost density gives

\[
-\operatorname{tr}(JX(t))
=\frac{x(t)^2+y(t)^2+1}{y(t)}
=\frac{(1+3y_0^2)e^{at}+4e^{-at}-2}{3y_0}.
\tag{4}
\]

Integrate (4), multiply by \(3/2\), and use
\(e^{a\tau}=r\), \(1+3y_0^2=4/r\). The physical cost of one arc is

\[
\begin{aligned}
C_{\rm arc}
&=\frac{(1+3y_0^2)(r-1)+4(1-r^{-1})-2\log r}
{2\sqrt3\,y_0^2}\\
&=\sqrt3\,\frac{4r-4-r\log r}{4-r}.
\end{aligned}
\tag{5}
\]

Successive arcs are conjugate by the fixed Euclidean rotation \(R\).
Since \(R\) commutes with \(J\), their costs agree. The \(N=3k+1\)
arcs therefore have total cost

\[
\boxed{C_N=N\sqrt3\,f(r),\qquad
f(r)=\frac{4r-4-r\log r}{4-r}.}
\tag{6}
\]

The published endpoint condition in (2) ensures the actual frame and
twisted state endpoints, with the primary winding. It is not merely a
trace condition imposed on an arbitrary word.

## 2. A continuous parameter and the exact second derivative

Let

\[
z=\frac{\pi}{3N}\in(0,\pi/12].
\]

Because \(k=(N-1)/3\), equation (2) becomes

\[
r(z)=2\cos(\pi/3-z)=\cos z+\sqrt3\sin z.
\tag{7}
\]

Define \(F(z)=f(r(z))\), with \(F(0)=f(1)=0\). Then

\[
C_N=\frac{\pi}{\sqrt3}\frac{F(z)}z.
\tag{8}
\]

We prove that \(F\) is strictly concave on this interval. The needed
derivatives are

\[
f'(r)=\frac{8+r-4\log r}{(4-r)^2},
\qquad
f''(r)=\frac{24+r-16/r-8\log r}{(4-r)^3}.
\tag{9}
\]

Also \(r''(z)=-r(z)\) and \(r'(z)^2=4-r(z)^2\).
The chain rule and (9) give

\[
F''(z)=
\frac{4\,D(r(z))}{(4-r(z))^3},
\tag{10}
\]
where
\[
D(r)=24-3r-\frac{16}r-5r^2
 +(r^2+4r-8)\log r.
\tag{11}
\]

For a direct algebraic check of (10), its numerator before cancellation is

\[
(4-r^2)(24+r-16/r-8\log r)
-r(4-r)(8+r-4\log r).
\]

Its nonlogarithmic part is
\(96-12r-64/r-20r^2\), and its logarithmic coefficient is
\(4(r^2+4r-8)\), exactly \(4D(r)\).

## 3. A rational sign certificate for strict concavity

Differentiating (11) twice gives

\[
\begin{aligned}
D'(r)&=1-9r-\frac8r+\frac{16}{r^2}
 +(2r+4)\log r,\\
D''(r)&=-7+\frac4r+\frac8{r^2}-\frac{32}{r^3}
 +2\log r.
\end{aligned}
\tag{12}
\]

At \(r=1\), both \(D(1)\) and \(D'(1)\) vanish.
On the whole interval \(1\le r\le\sqrt2<3/2\), use
\(\log r\le r-1\le1/2\). Each term in (12) is then bounded explicitly:

\[
D''(r)
\le -7+4+8-\frac{256}{27}+1
=-\frac{94}{27}<0.
\tag{13}
\]

The negative reciprocal term has the displayed direction because
\(r^3\le27/8\). Integrating the strict sign in (13) from \(1\)
shows \(D'(r)<0\) and \(D(r)<0\) for every \(r>1\) in the domain.
Equation (10) therefore gives

\[
F''(z)<0\qquad(0<z\le\pi/12).
\tag{14}
\]

All denominators are positive on the closed interval. In particular
there is no singular endpoint hidden in the differentiations at \(z=0\).

## 4. Strict comparison, equality, and the circular limit

Since \(F(0)=0\), integration by parts gives

\[
zF'(z)-F(z)=\int_0^z tF''(t)\,dt<0.
\tag{15}
\]

Thus \(F(z)/z\) is strictly decreasing for positive \(z\).
In (8), increasing \(N\) decreases \(z\), so \(C_N\) is strictly
increasing for real \(N\ge4\). This proves the strict inequalities
between successive members in (1).

At \(z=0\), equations (7) and (9) give
\[
F'(0)=f'(1)r'(0)=1\cdot\sqrt3.
\]
Hence (8) has limit
\[
\lim_{N\to\infty}C_N
=\frac{\pi}{\sqrt3}F'(0)=\pi.
\tag{16}
\]
Strict concavity gives \(F(z)<zF'(0)\) for every positive \(z\),
so each finite member has cost strictly below \(\pi\).

For \(N=4\), one has \(r=\sqrt2\). Formula (6) gives
\[
\frac{C_4}{\sqrt{12}}
=2\,\frac{4\sqrt2-4-(\sqrt2/2)\log2}{4-\sqrt2}
=\frac{8-4\sqrt2-\log2}{2\sqrt2-1}
=\delta_{\rm oct}.
\tag{17}
\]
Together with strict monotonicity, this proves that \(k=1\) is the
unique minimizing member of the standard family. It does not classify
equality for arbitrary asymmetric or measurable competitors.

## Why the first-order conditions do not bound word length

The same primary source proves that every member of this family has a
normal Pontryagin lift satisfying the Hamiltonian maximum and endpoint
transversality conditions. Its control labels follow the same cyclic
direction at every switch, including the twisted seam. Consequently
these words avoid the forbidden forward two-vertex alternation, while
their lengths \(3k+1\) are unbounded.

This is an exact limitation of combining those necessary conditions:
Pontryagin extremality and the forward-pattern exclusion alone cannot
imply a uniform word-length bound. The strict comparison above removes
this particular infinite family at every \(k>1\). A proof covering
arbitrary longer words still needs a quantitative comparison, a stronger
variation, or a justified general reduction.

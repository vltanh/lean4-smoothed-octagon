# A shear and cost reduction for a smaller-short bridge

Date: 2026-11-07. Hand derivation, accepted in an
[independent internal review](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).
The final short-case exclusion remains open.

The [fixed-root and angle-circle reduction](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md)
retains a necessary relaxed completion-cost inequality. This note makes
its dependence on physical scale explicit. At fixed short shape, the
relative endpoint matrix has a scale-independent lower row; its
remaining freedom is one shear, and physical cost is affine in that
shear. The resulting fixed-kappa minimization has explicit endpoints and
at most one interior local-minimum candidate. An unconditional
endpoint-only minimization is not asserted.

All physical interpretations use the same actual equal-secant bridge
and the [rational physical interface](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md).
No interval cover or runtime sign test is a premise.

## 1. The physical matrix and its fixed lower row

Keep the short shape and common actual turn norm fixed:

\[
1\le\alpha<x\le\beta\le\alpha x,\qquad
r=(1+x)^{-1},\qquad r_A=\frac{\alpha}{\alpha+\beta},
\]
\[
\tfrac34<u\le\min\{U(r),U(r_A)\},\qquad U(s)=1-s+s^2.
\]

Write

\[
S=1+x,\quad A_0=\alpha+\beta,\quad B_0=\beta+x,
\]
\[
K_x=x^2+x+1,\qquad
K_A=\alpha^2+\alpha\beta+\beta^2.
\]

The physical scale is \(\rho=a^2/(a^2+4)\). For the physical-frame
calculation let \(U_0=(1-\rho)/\rho\); this symbol is distinct from
the function U. The exact interface gives

\[
n=\frac{U_0-x}{S},\qquad z=\frac{U_0-\alpha\beta}{A_0},
\]
\[
P=\begin{pmatrix}-n-2&x+2\\n&x\end{pmatrix},\qquad
Q=\begin{pmatrix}-z-2\beta&\alpha+2\beta\\z&\alpha\end{pmatrix},
\]
\[
F=\begin{pmatrix}
S/A_0&0\\(S^2-B_0^2)/(SA_0)&A_0/S
\end{pmatrix},\qquad
M=D_3PFQ^{-1}D_3^{-1},\quad
D_3=\operatorname{diag}(1/\sqrt3,1).
\tag{1}
\]

Here det P=det Q=-2U_0 and det F=1, so det M=1. The physical
two-turn factors are B_0/S and B_0/A_0, both greater than one.

Use the rotation already chosen in the angle-circle proof:

\[
O=\frac1{2\sqrt{K_x}}
\begin{pmatrix}x+2&-\sqrt3x\\\sqrt3x&x+2\end{pmatrix},
\qquad M'=O^TMO=(m_{ij}).
\]

Its lower row is independent of rho:

\[
\boxed{
m_{21}=\frac{\sqrt3S(\beta x-\alpha)}{2A_0K_x},\qquad
m_{22}=\frac{S[(2x+1)\alpha+(x+2)\beta]}{2A_0K_x}.}
\tag{2}
\]

This cancellation follows directly from the factors in (1). The lower
row of \(O^TD_3P\) is \((U_0/\sqrt{K_x},0)\).
After multiplying by F and \(Q^{-1}\), it is

\[
\frac{S}{2A_0\sqrt{K_x}}(-\alpha,\alpha+2\beta).
\]

Multiplication by \(D_3^{-1}O\) gives (2).

Set

\[
L=m_{21}^2+m_{22}^2,\qquad V=m_{22}+im_{21},\qquad
\psi=\arg V.
\]

Squaring the two displayed numerators gives

\[
\boxed{L=\frac{S^2K_A}{A_0^2K_x}
=\frac{U(r_A)}{U(r)}\le1.}
\tag{3}
\]

Indeed beta<=alpha*x implies r_A>=r, and U decreases on (0,1/2).
Both entries in (2) are positive. Also
\(m_{21}/m_{22}<\sqrt3\), because

\[
(2x+1)\alpha+(x+2)\beta-(\beta x-\alpha)
=2S\alpha+2\beta>0.
\]

Thus \(0<\psi<\pi/3\). Write

\[
A=L^{-1}-1
=\frac{(\beta x-\alpha)(\alpha x-\beta)}{S^2K_A}\ge0.
\tag{4}
\]

## 2. The shear is affine in scale, and cost is affine in shear

Since det M'=1 and its lower row is fixed, there is a unique real h
such that its upper row is

\[
(m_{11},m_{12})
=\frac1L(m_{22},-m_{21})+h(m_{21},m_{22}).
\tag{5}
\]

Equivalently \(h=(m_{11}m_{21}+m_{12}m_{22})/L\).
Using the factors in (1), this scalar simplifies to

\[
\boxed{
h=h_0-\frac{2\sqrt3}{3}U(r)Q_0\frac{\rho}{1-\rho},}
\tag{6}
\]
\[
Q_0=2\beta x-x-\alpha\beta>0,
\qquad
h_0=
\frac{\sqrt3(\beta x-\alpha)[(x+2)\alpha+(2x+1)\beta]}
     {3S^2K_A}.
\]

Equation (6) can be checked by inserting (1) in the dot-product
definition following (5); its only scale dependence is \(U_0^{-1}\).
The positivity of Q_0 follows from
\(Q_0=x(\beta-1)+\beta(x-\alpha)\), the sum of two positive
turn contributions.

The exact equal-secant physical cost is

\[
C_{\rm br}=
\sqrt3\left[\frac{\rho u}{1-\rho}Q_0
               +\frac{\beta x-\alpha}{SA_0}\right].
\]

Define the fixed shape quantities

\[
J_0=\frac{3u}{2U(r)},\qquad
C_0=\frac{\sqrt3(\beta x-\alpha)}{SA_0},\qquad
H_0=C_0+J_0h_0.
\]

Multiplying (6) by J_0 now proves the exact cost-shear identity

\[
\boxed{C_{\rm br}=H_0-J_0h.}
\tag{7}
\]

In particular h strictly decreases as rho increases. The identity uses
both actual turn secants through the physical cost formula; it is not
an arbitrary off-secant cost replacement.

## 3. The maximal angle in shear coordinates

Fix kappa>0. In the angle-circle notation,

\[
s=\frac{J_0}{\kappa},\qquad
D_0=(m_{11}-m_{22})-i(m_{12}+m_{21}).
\]

Equation (5) immediately gives

\[
D_0=V(A-ih).
\]

Thus, after dividing the angle circle by V, its centre and radius are

\[
1+\frac{s}{2(s+1)}(A-ih),\qquad
\frac{s}{2(s+1)}\sqrt{A^2+h^2}.
\]

Put

\[
K=A+2+\frac{2\kappa}{J_0},\qquad
\mathscr D=\sqrt{K^2-A^2}>0.
\tag{8}
\]

The symbol \(\mathscr D\) here denotes this positive radical; it is
unrelated to the signed short diagonal D in the root-comparison note.
The supremal endpoint angle has the form
\(\Theta=\psi+\delta\), where

\[
\boxed{
\delta=2\arctan
 \frac{\sqrt{h^2+A^2}-h}{K+\mathscr D}.}
\tag{9}
\]

For A>0 this is a continuous angle in (0,pi). The upper supporting
ray of the divided circle satisfies

\[
K\sin\delta+h\cos\delta=\sqrt{h^2+A^2};
\]

the half-angle substitution gives (9). Equivalently,

\[
\boxed{
h=\frac{K\cos\delta-\mathscr D}{\sin\delta},\qquad
\frac{dh}{d\delta}
=\frac{\mathscr D\cos\delta-K}{\sin^2\delta}<0.}
\tag{10}
\]

The branch is the one obtained from the disk containing 1. The
angle-circle proof supplies a common continuous argument branch, since
every disk lies inside a fixed limiting disk that avoids the origin.

The case A=0 is also explicit. For h>=0 one has delta=0. For h<0,
one has \(\delta=2\arctan(-h/K)\). The limiting formulas agree at
h=0; no division by A is used.

## 4. Exact critical points of the completion score

Put

\[
c=\kappa+\tfrac32,\qquad b=\pi/3-\psi>0.
\]

Equations (7)--(9) turn the relaxed completion lower bound into

\[
\boxed{\mathcal F
=H_0-J_0h+c\max\{0,b-\delta\}.}
\tag{11}
\]

The score remains nondecreasing in kappa at fixed physical geometry,
by the nested-disk argument in the root-and-angle note. The present
section studies its dependence on shear when kappa is fixed.

On the active interval 0<delta<b, differentiation using (10) gives

\[
\frac{d\mathcal F}{d\delta}
=\frac{P(\cos\delta)}{\sin^2\delta},
\]
\[
P(z)=cz^2-J_0\mathscr D z+(J_0K-c).
\tag{12}
\]

The discriminant has a particularly simple factorization:

\[
\boxed{
\Delta=(2J_0-3)[2J_0(A+1)-3]
=9\left(1-\frac{u}{U(r)}\right)
   \left(1-\frac{u}{U(r_A)}\right)\ge0.}
\tag{13}
\]

It is independent of kappa. The two roots are

\[
z_\pm=\frac{J_0\mathscr D\pm\sqrt\Delta}{2c}.
\tag{14}
\]

They lie in (0,1], and their angles admit a useful exact description.
Let

\[
a_1=\frac{u}{U(r)},\qquad a_2=\frac{u}{U(r_A)},\qquad
\theta_i=\arcsin\sqrt{\frac{3(1-a_i)}{2\kappa+3}}.
\]

Here 3/4<a_i<=1, so 0<=theta_i<pi/6. The definitions give

\[
J_0\mathscr D
=\sqrt{(2\kappa+3a_1)(2\kappa+3a_2)},\qquad
\sqrt\Delta=3\sqrt{(1-a_1)(1-a_2)}.
\]

The cosine addition and subtraction identities therefore yield

\[
\boxed{
z_-=\cos(\theta_1+\theta_2),\qquad
z_+=\cos(\theta_1-\theta_2).}
\tag{15}
\]

This proves the asserted root range without a separate quadratic
estimate. In particular,

\[
\boxed{\delta_{\min}=\theta_1+\theta_2.}
\tag{16}
\]

As delta increases, cos delta decreases. Since P is an upward
quadratic, the first critical angle
\(|\theta_1-\theta_2|=\arccos z_+\) can only be a local maximum;
the second angle \(\delta_{\min}=\arccos z_-\) can be a local
minimum. In a coincident-root case the same finite candidate list
remains valid, without an assertion of a strict extremum.

On delta>=b, the score is just H_0-J_0h, and it strictly increases
with delta by (10). It follows that on any closed physical-scale
interval, with shape and kappa fixed, a minimum occurs among:

- the two scale endpoints;
- a point delta=b, if that clipping point lies in the interval;
- delta=delta_min, if it lies in the interval and is below b.

For A=0 also include the join h=0, if present. On its h>=0 piece,
delta=0 and the score is affine in h, so no additional interior
candidate is needed.

This is a finite analytic reduction, not an endpoint-only theorem.
For example, a sufficient condition for endpoint-only minimization is
that the largest allowed scale angle is at most
min(delta_min,b): the only interior critical point then available is
a local maximum. When kappa itself varies with scale, this fixed-kappa
classification may be applied only after justifying the relevant
comparison in kappa; the actual Casimir is not assumed constant.

## 5. Curvature and the precise remaining use

For A>0, differentiating the angle formula gives

\[
\delta_h=-\frac{\sin\delta}{\sqrt{h^2+A^2}},\qquad
\delta_{hh}
=\frac{\sin\delta\,[h+\sqrt{h^2+A^2}\cos\delta]}
       {(h^2+A^2)^{3/2}}.
\tag{17}
\]

The sign changes exactly at

\[
\boxed{h=-\sqrt{\frac{A(K-A)}2}
       =-\sqrt{A(1+\kappa/J_0)}.}
\tag{18}
\]

To see the location directly, set the bracket in (17) to zero.
Then \(h=-\sqrt{h^2+A^2}\cos\delta\). Combine this with the
supporting-ray equation preceding (10), giving
\((K+A)\sin^2\delta=2A\), and substitute back. The negative
solution is (18); it is the unique sign change. The angle is concave
below this shear and convex above it, while the active score has the
opposite curvature. For A=0, its h<0 angle branch is concave and its
h>=0 branch is constant, as follows directly from (9).

Thus a blanket claim of concavity throughout the physical scale range
would lose a possible interior minimum. The exact shear identity,
critical angles and candidate list provide a controlled way to retain
that possibility. They do not establish the sign at the candidate
points, exclude the remaining short boundary faces, or replace the
107,977-node smaller-short cover by a complete hand argument.

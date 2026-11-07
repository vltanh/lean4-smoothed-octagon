# Retain both stationary slacks in the short root comparison

Date: 2026-11-07 UTC. Hand reduction, accepted in independent internal review.
See [HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).
This note strengthens the necessary domain of the remaining short
faces. It does not exclude those faces.

The [physical short-window interface](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md),
equations (M) and (O), supplies two nonnegative stationary-control
slacks from the same actual normal multiplier. Both survive the first
[root-preserving comparison](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
Their retention requires no sign restriction on the transported
diagonal coefficient.

## 1. Exact slack expressions

Keep the fixed short geometry \(x,\alpha,\beta,\rho,u\), with
\(1\le\alpha<x\le\beta\le\alpha x\) and the actual equal secants.
Use the root-comparison notation
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad
\lambda=[1+\rho(\alpha^2-1)]^{-1},\quad d=\lambda\rho D,
\]
\[
Q=\alpha(\alpha+\beta),\quad
r_A=\frac{\alpha}{\alpha+\beta},\quad
\rho_A=\alpha^2\lambda\rho,\quad
T=\frac{r_A}{\rho_A}=\frac1{\lambda\rho Q}.
\]
Introduce
\[
B_{\rm mid}=\beta x-2x-1,\qquad
J=D+B_{\rm mid}=Q-\beta(x-\alpha).
\tag{1}
\]
Here \(J\) is a scalar and is not the complex-structure matrix.

The middle slack is
\[
N_{\rm mid}=C_{\rm geo}-v-\rho B_{\rm mid}E,
\tag{2}
\]
where all entries of \(C_{\rm geo}\) stay fixed in the comparison:
\[
C_{\rm geo}
 =(1-\rho)\{1+\rho(\beta^2+\beta x+x^2-1)\}
   -\rho u P_{\rm mid},
\]
\[
\begin{aligned}
P_{\rm mid}={}&\beta^2\rho x^2-\beta^2\rho+\beta^2
 -4\beta\rho x^2-4\beta\rho x+2\beta x\\
 &+3\rho x^2+4\rho x+\rho+x^2.
\end{aligned}
\]
The outer entrance slack is
\[
H_A=(1-\rho_A-w)r_A^2
 +\rho_A(E_L-1+\rho_A)r_A+\rho_A(1-\rho_A-u).
\tag{3}
\]
Actual data have \(N_{\rm mid}\ge0\) and \(H_A\ge0\). The positive
physical prefactors and their common-covector interpretation are those
of the linked physical interface.

## 2. Both slacks increase along the first root path

The first comparison fixes the actual outer root parameter
\(2<\tau<T\) and increases the central opposite ratio \(t\). Write
\[
\nu=1-t+t^2-v,\qquad B=1+\tau(\lambda t-d)>0.
\]
On every interior part of the path, \(\nu>0\), and the proved exact
derivatives are
\[
v'=-\frac{(1-\tau d)\nu}{tB},\qquad
E'=\frac{\tau\lambda\nu}{tB},\qquad
w'=-\frac{\lambda^2\nu}{tB},\qquad E_L'=\tau w'.
\tag{4}
\]
The prime in this section denotes differentiation with respect to \(t\).

Differentiate (2) using (4):
\[
\boxed{
N_{\rm mid}'
 =\frac{\nu}{tB}\{1-\tau\lambda\rho J\}>0.}
\tag{5}
\]
The strict sign follows from the short ordering and the positive
outer duration, without assuming \(J\ge0\). Indeed,
\[
J=Q-\beta(x-\alpha)<Q,\qquad
\tau\lambda\rho Q=\frac{\tau}{T}<1,
\]
and hence
\[
1-\tau\lambda\rho J>1-\frac{\tau}{T}>0.
\]

Likewise (3)--(4) give
\[
\boxed{
H_A'=r_A(\tau\rho_A-r_A)w'>0,}
\tag{6}
\]
because \(\tau<T=r_A/\rho_A\) and \(w'<0\).
Continuity gives the corresponding weak monotonicity at terminal
points with \(\nu=0\).

Consequently every endpoint of a nontrivial first comparison has both
slacks strictly larger than their original values. If no motion is
needed, their original weak signs remain valid. In particular the
three remaining faces
\[
t=r,\qquad v=1-t+t^2,\qquad w=3/4
\]
may all retain \(N_{\rm mid}\ge0\) and \(H_A\ge0\), together with
the previously retained root, norm, scale and cost conditions.
No new stopping face is needed to preserve these two inequalities.

The comparison is still a scalar necessary-condition relaxation:
the retained slack signs do not assert that an artificial endpoint
is a physical Pontryagin trajectory.

## 3. A short exact form on the outer-norm floor

On \(w=3/4\), put \(\xi=E_L\). The solved transport equations are
\[
E=\frac{2du-\xi}{\lambda},\qquad
v=\frac{3/4+d^2u-d\xi}{\lambda^2}.
\tag{7}
\]
With
\[
\sigma=\alpha^2-1,\quad M=\beta^2+\beta x+x^2-1,\quad
B_0=\beta+x,
\]
substitution into (2) yields the compact necessary inequality
\[
\boxed{
N_{\rm mid}=N_0+\frac{\rho J}{\lambda}\xi\ge0,}
\tag{8}
\]
\[
\boxed{
N_0=\frac14
 +\rho\{M-1-\tfrac32\sigma-uB_0^2\}
 +\rho^2\{-M-\tfrac34\sigma^2+uB_0^2-uJ^2\}.}
\tag{9}
\]

For a direct algebraic check, write
\[
P_{\rm mid}=B_0^2+\rho P_1.
\]
The displayed expression for \(P_{\rm mid}\) gives
\[
P_1-B_{\rm mid}^2=-B_0^2.
\]
Since \(D^2+2DB_{\rm mid}=J^2-B_{\rm mid}^2\), the coefficient of
\(u\rho^2\) after (7) is exactly \(B_0^2-J^2\).
The constant and linear coefficients then give (9).
Thus no polynomial table or executable check is needed for (8)--(9).

## 4. Scope during the further outer-floor deformation

The [nonnegative-pairing outer-floor comparison](MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION.md)
keeps \(w=3/4\), increases \(\xi\), and varies \(\tau\).
Equations (3) and (8) imply
\[
\frac{dH_A}{d\xi}=\rho_A r_A>0,\qquad
\frac{dN_{\rm mid}}{d\xi}=\frac{\rho J}{\lambda}.
\tag{10}
\]
Therefore \(H_A\ge0\) persists on that entire comparison.
The middle slack also persists if the fixed shape satisfies \(J\ge0\);
a simple sufficient condition is \(x\le2\alpha\), since then
\(J=\alpha^2+\beta(2\alpha-x)>0\).

No uniform sign of \(J\) is asserted. If \(J<0\), retaining the middle
slack in this further comparison requires stopping at \(N_{\rm mid}=0\)
if it is reached before the other listed endpoints. The earlier
outer-floor reduction remains valid when this additional constraint
is dropped. The negative-pairing branch and the required endpoint
cost exclusions remain open.

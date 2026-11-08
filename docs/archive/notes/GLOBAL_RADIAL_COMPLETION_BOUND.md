# A radial lower bound for the cost of completing a window

Date: 2026-11-07 UTC. Hand proof and supplementary exact identities.
No Lean, Lake, typechecking, or CI.

## Result and scope

Use a competitive complete normal PMP lift with the actual twisted frame
and costate endpoints, negative elliptic primary costate, and physical
normalization `lambda=-1`. Let

\[
0<\kappa<3/2,\qquad c=\kappa+3/2,\qquad
A=3/(2\kappa)>1,\qquad z_*=(A+A^{-1})/2.
\]

The primary costate itself determines the scalar radial coordinate

\[
z(t)=\frac{\operatorname{tr}(J\Lambda_1(t))}{2\kappa}\ge1.
\tag{1}
\]

Define a nonnegative, continuously differentiable function on `z>=1` by

\[
W_\kappa(z)=
\begin{cases}
0,&1\le z\le z_*,\\
c\bigl(\eta-\arctan\eta\bigr),&z\ge z_*,\quad
\eta=\sqrt{\dfrac{z-z_*}{z_*+1}}.
\end{cases}
\tag{2}
\]

For every actual contiguous window `I=[s,t]` with `0<=t-s<=T`, including a window crossing
the chosen seam after cyclic continuation, the completion budget improves
to

\[
\boxed{
 C_I+c\left(\frac\pi3-\Delta\theta_I\right)
 +\left|W_\kappa(z(t))-W_\kappa(z(s))\right|
 \le A_{\rm oct}.}
\tag{3}
\]

Here `Delta theta_I` is the same increasing polar angle used in
[GLOBAL_SPECTRAL_COST_CASIMIR](GLOBAL_SPECTRAL_COST_CASIMIR.md). Its endpoint
formula is in [GLOBAL_ENDPOINT_DEFECT_TEST](GLOBAL_ENDPOINT_DEFECT_TEST.md).
Thus both the angle and the new endpoint penalty are computable from the
same actual costate and frame, without integration of the adjoint flow.

The proof gives a necessary cost for the omitted part of the actual
period. It uses no new multiplier, selected word, endpoint-rank assumption,
or competitor. It strengthens a continuation test; a uniform exclusion
of all remaining M2 data is a separate obligation.

## 1. Exact singular-value coordinates

Choose the constant matrix `h` so that
`Lambda_1(0)=-kappa h J h^{-1}`, and put `B=h^{-1}g`. Conservation gives

\[
\Lambda_1=-\kappa B^{-1}JB.
\]

The trace identity

\[
-\tfrac12\operatorname{tr}(JB^{-1}JB)
=\tfrac12\operatorname{tr}(B^TB)
\]

proves (1). Write the singular values of B as `exp(s),exp(-s)`, with
`s>=0`; then `z=cosh(2s)`. All following pointwise calculations are on
`s>0`. The final bound extends through `s=0` because (2) is constant
on a neighborhood of it.

Choose an oriented orthonormal basis that diagonalizes `B^TB` as
`diag(exp(2s),exp(-2s))`. In that basis write

\[
Q=-JX=\begin{pmatrix}m_b+n&m\\m&m_b-n\end{pmatrix}>0,
\qquad \det Q=1.
\]

Consequently

\[
m_b^2-n^2-m^2=1.
\tag{4}
\]

The equation `B'=BX` gives
`(B^TB)'=X^TB^TB+B^TBX`. Its first diagonal entry gives `s'=-m`: the derivative of a simple
eigenvalue is its unit eigenvector paired with the matrix derivative.
Equivalently, the moving orthonormal basis adds a commutator with zero
diagonal. Set `xi=n/m_b`, so `-1<xi<1`. The exact relations are

\[
m_b^2(1-\xi^2)=1+(s')^2,\qquad
r:=m_s/m_b=z-\xi\sinh(2s),
\tag{5}
\]

where `m_s` has the definition in the spectral cost theorem. In
particular this retains the determinant-one term in (4).

The actual stationary-control inequality is `r<=A`. The polar-angle
identity and the physical cost density give

\[
\theta'=m_b(1-\xi\tanh s),\qquad C'=3m_b.
\tag{6}
\]

Define the nonnegative defect density `D'=C'-c theta'`. With
`b=3/2-kappa>0` and `H=tanh s`,

\[
D'=m_b(b+cH\xi).
\tag{7}
\]

## 2. Minimize the defect per radial displacement

Let `s_*=(log A)/2`, so `z_*=cosh(2s_*)` and
`b/c=tanh s_*`. If `s>=s_*`, the stationary comparison in (5) gives

\[
\xi\ge \xi_0:=\frac{z-A}{\sqrt{z^2-1}}\ge-1.
\]

For `-1<\xi<1`, the derivative of the relevant scalar ratio is

\[
\frac{d}{d\xi}\frac{b+cH\xi}{\sqrt{1-\xi^2}}
=\frac{cH+b\xi}{(1-\xi^2)^{3/2}}\ge0,
\]

because `cH>=b`. Its minimum on the permitted interval is therefore
its value at `xi_0`, interpreted by the limit at `s=s_*`. Direct algebra
using `kappa A=3/2` gives

\[
\frac{b+cH\xi_0}{\sqrt{1-\xi_0^2}}
=\sqrt{3\kappa}\,\tanh s\,\sqrt{z-z_*}
=:w_\kappa(s)\ge0.
\tag{8}
\]

At `s=s_*` the right side is zero. The left limiting value is also zero,
since then `H=b/c` and the ratio is
`b sqrt((1+xi)/(1-xi))` as `xi` tends to -1 from above.
Equations (5), (7), and (8) now yield the stronger pointwise statement

\[
D'\ge w_\kappa(s)\sqrt{1+(s')^2}
\ge w_\kappa(s)|s'|\qquad(s\ge s_*).
\tag{9}
\]

For `s<s_*`, retain only `D'>=0` from the spectral theorem.

The identities `c^2=3 kappa(z_*+1)` and `z'=2sinh(2s)s'` show that
(2) is exactly the integral of (8):

\[
\frac{dW_\kappa}{dz}
=\frac{\sqrt{3\kappa}\sqrt{z-z_*}}{2(z+1)},\qquad
\frac{dW_\kappa}{ds}=w_\kappa(s)\quad(s\ge s_*).
\]

Both derivatives tend to zero at `z=z_*`. Combining the two regions,

\[
\boxed{D'\ge\left|\frac{d}{dt}W_\kappa(z(t))\right|}
\tag{10}
\]

almost everywhere. The argument is valid on measurable-control lifts:
the state and frame are absolutely continuous, and the displayed
composition is continuously differentiable across its joining value.

## 3. The omitted part must restore the radial coordinate

The actual costate twist is
`Lambda_1(T)=R^{-1} Lambda_1(0) R`, with `RJ=JR`. Therefore
`z(T)=z(0)`. The costate extended over the seam has the same periodic
radial coordinate. For any actual window, integrate (10) on the
complementary portion of that period to obtain

\[
D_{I^c}\ge
\left|W_\kappa(z(t))-W_\kappa(z(s))\right|.
\]

The competitive spectral theorem proves that the complete continuous
polar angle is exactly `pi/3`; extra turns are excluded by `C<=A_oct<pi`.
Hence

\[
D_I+D_{I^c}=C-c\pi/3\le A_{\rm oct}-c\pi/3.
\]

Combining these two inequalities with `D_I=C_I-c Delta theta_I` proves
(3). The complementary path need not be reconstructed or chosen; it is
the omitted part of the same actual minimizing-period lift.

## Verification boundary

[`global_radial_completion_certificate.py`](../explorations/global_radial_completion_certificate.py)
checks the trace identity, singular-value relations, ratio derivative,
radial coefficient, and potential derivative exactly. The pointwise
comparison, absolute-continuity argument and actual twisted endpoint
are the hand proof above. The result does not imply that every locally
eligible M2 window consumes too much budget.

Independent review reran all 11 exact checks and verified the spectral
trace convention, oriented singular-value basis, signs in the scalar
minimization, the continuously differentiable joining value, and the
absolute-continuity and twisted-complement arguments. No substantive
gap was found. This is a hand-proof review with exact algebra checks,
not Lean kernel verification or a uniform M2 exclusion.

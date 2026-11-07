# One signed scalar dual for every remaining normal period

Date: 2026-11-07 UTC. Hand proof of a uniform scalar and index reduction.
No Lean, Lake, typechecking, or CI.

## Result and scope

The scalar dual in
[GLOBAL_STRUCTURE_FORWARD_DUAL_HESSIAN](GLOBAL_STRUCTURE_FORWARD_DUAL_HESSIAN.md)
extends to every remaining mixed geometric minimizing period. Its
auxiliary variables may be negative, but every adjacent auxiliary
sum is strictly positive. Thus all logarithms remain real and smooth.
No division by an individual auxiliary variable is needed.

For the actual sign pattern `epsilon_i`, set

\[
\delta_i=(\epsilon_{i-1}+\epsilon_i)/2,\quad
P=N-2m,\quad n=(N-m-1)/3,
\]

where `m` is the number of double reverse runs. The state-closed
factor map is denoted `ell_epsilon(a)=(log q_i(a))_i`. Its symmetric
derivative is `B_epsilon(a)`.

The complete normal period supplies a critical point of a real scalar
function `Psi_epsilon(a,b,c)` in `2N+1` variables. Its auxiliary
Jacobi block `D=B_epsilon(b)` has the exact inertia

\[
\boxed{(n_+(D),n_0(D),n_-(D))=(2n-1,2,N-2n-1).}
\tag{1}
\]

On the full-rank remaining domain `N>=6`, the actual closed cost
Hessian satisfies

\[
\boxed{\operatorname{ind}_-(Q_{\rm closed})
=\operatorname{ind}_-(\operatorname{Hess}\Psi_\epsilon)
 -(N-2n-1)-3.}
\tag{2}
\]

An `N`-dimensional negative subspace of this scalar Hessian would
give `2(n-1)` negative closed directions. That sign theorem remains
unproved. Equations (1)--(2) are uniform bridges, not a closure of
F, M1, or M2.

## 1. The signed factor map has a scalar potential

For a real sequence `x` with `x_i+x_(i+1)>0`, put

\[
s_i(x)=x_i+x_{i+1},\qquad K_i(x)=x_i^2+4,
\]

\[
\ell_{\epsilon,i}(x)
=\epsilon_{i-1}\log s_{i-1}(x)
 +\epsilon_i\log s_i(x)-\delta_i\log K_i(x).
\tag{3}
\]

The actual margins `a_i` are positive and give the ordinary positive
vertex factors `q_i(a)=exp(ell_(epsilon,i)(a))>1`. Define

\[
\Phi_\epsilon(x)
=\sum_i\epsilon_i s_i(x)\log s_i(x)
 -\sum_i\delta_i\bigl[x_i\log K_i(x)+4\arctan(x_i/2)\bigr].
\tag{4}
\]

Direct differentiation gives

\[
\nabla\Phi_\epsilon=\ell_\epsilon,\qquad
B_\epsilon=\operatorname{Hess}\Phi_\epsilon,
\]

\[
(B_\epsilon)_{ii}
=\frac{\epsilon_{i-1}}{s_{i-1}}+\frac{\epsilon_i}{s_i}
 -\frac{2\delta_i x_i}{K_i},\qquad
(B_\epsilon)_{i,i+1}=\frac{\epsilon_i}{s_i}.
\tag{5}
\]

All these formulas are smooth even when an individual `x_i` is zero
or negative. The only logarithmic arguments are the positive adjacent
sums and `x_i^2+4`.

## 2. Positive ellipticity produces the auxiliary sequence

Use the actual prefixes and multiplier of
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md):

\[
P_{i+1}=P_iT_0(q_i)R^{-\epsilon_i},\quad
Z_i=\operatorname{Ad}_{P_i}\operatorname{diag}(1,-1),\quad
c=\sqrt{\det U}>0,
\]

\[
\boxed{b_i=\operatorname{tr}(UZ_i)/c.}
\tag{6}
\]

The full central monodromy makes `b` periodic. Positive ellipticity
allows the prefix representative to be written

\[
P_i^{-1}UP_i
=c\begin{pmatrix}b_i/2&-h_i\\k_i&-b_i/2\end{pmatrix},
\qquad h_i,k_i>0,\qquad h_i k_i=1+b_i^2/4.
\tag{7}
\]

Direct conjugation by `T_0(q_i)R^(-epsilon_i)` gives

\[
\begin{array}{c|c|c}
\epsilon_i& (b_i+b_{i+1})/2&\text{next incoming component}\\ \hline
+1&q_i^2 k_i&h_{i+1}=(b_i+b_{i+1})/2\\
-1&h_i/q_i^2&k_{i+1}=(b_i+b_{i+1})/2.
\end{array}
\tag{8}
\]

In particular every adjacent sum of `b` is positive. Combining
the incoming and outgoing identities with (7) treats all four
incident sign pairs:

\[
\boxed{\ell_\epsilon(b)=2\ell_\epsilon(a).}
\tag{9}
\]

For example, at `++` the product of the incoming `h_i` and outgoing
`k_i` gives `q_i^2=s_(i-1)(b)s_i(b)/(b_i^2+4)`; at `--` it gives
the reciprocal. At the two turns, the same incoming and outgoing
component gives respectively the ratio or reciprocal of adjacent
sums. No third-margin interpretation of `b` is asserted.

The actual frame-column identity also gives

\[
\boxed{\nabla J(a)=cB_\epsilon(a)b,\qquad J=C/\sqrt{12}.}
\tag{10}
\]

Indeed differentiating each logarithmic factor pairs its prefix
generator `Z_i` with the same actual frame covector `U`. The signed
derivative matrix (5) is symmetric, so the resulting vector is
exactly the right-hand side of (10). This uses the established actual
state/costate endpoint cancellation.

## 3. The angle equation and one scalar critical point

The Euler identity of (4) is

\[
\Phi_\epsilon(b)-b\cdot\ell_\epsilon(b)
=-4\sum_i\delta_i\arctan(b_i/2).
\tag{11}
\]

At a same-sign index the actual cross pairing is
`e_i=c b_i/(2K_i)`. For the collapsed, positively gauged switch
vectors, the angle on that edge therefore satisfies

\[
\theta_i=\frac\pi2-\delta_i\arctan(b_i/2),
\qquad 0<\theta_i<\pi.
\]

There are `P` such edges. The proved geometric winding gives

\[
\sum_i\delta_i\arctan(b_i/2)=(P-2n)\pi/2.
\tag{12}
\]

This uses the principal real arctangent; the displayed angle formula
is valid for either sign of `b_i`.

Consequently the actual period supplies a critical point of

\[
\boxed{
\Psi_\epsilon(a,b,c)
=J(a)-c\,b\cdot\ell_\epsilon(a)
 +\frac c2\Phi_\epsilon(b)+c(P-2n)\pi.
}
\tag{13}
\]

The `a,b` equations are (9)--(10); the `c` equation is (12).
This is a necessary stationary representation. Arbitrary critical
points of (13) are not claimed to meet the complete PMP, geometric,
or endpoint conditions.

## 4. A complex-column proof of the signed kernel winding

Holding the prefixes fixed, vary `U` within its two-dimensional
determinant level. Equation (9) gives a pair of kernel sequences for
`D=B_epsilon(b)`. Their exact signs and winding can be checked without
positivity of the individual auxiliary variables.

Make one determinant-one change of coordinates so that `U=cJ_0`,
with `J_0=[[0,-1],[1,0]]`. Write the two columns of the transformed
prefix as complex numbers `u=A+iC` and `v=B+iD_0`, with
`det(u,v)=1`. The two determinant-preserving variations
`delta U=c[[x,y],[y,-x]]` give the kernel pair

\[
\zeta_i=(2(AD_0+BC),\,2(CD_0-AB)),
\qquad \zeta_i^{\mathbb C}=-2iuv.
\tag{14}
\]

Thus its lifted angle is the sum of the two column angles minus
`pi/2`. A positive diagonal factor rescales the columns by reciprocal
positive numbers, and changes neither their angles nor their product.

After this rescaling write their lifted angles as
`alpha<beta<alpha+pi`, and let `gamma` be the angle of `u+v`.
Positive linear combination gives `alpha<gamma<beta`. The two
canonical rotation factors act as follows:

\[
\begin{array}{c|c|c}
\text{factor}&\text{new columns}&\text{kernel angle increment}\\ \hline
R^{-1}&(u+v,-u)&\pi+\gamma-\beta\in(0,\pi)\\
R&(-v,u+v)&\gamma-\alpha-\pi\in(-\pi,0).
\end{array}
\tag{15}
\]

The canonical elliptic paths select exactly these branches: the first
moves both column directions forward, and the second moves them
backward. Their orientation-preserving prefixes preserve those lifts.
One also obtains directly

\[
\boxed{\det(\zeta_i,\zeta_{i+1})
=2\epsilon_i(b_i+b_{i+1}).}
\tag{16}
\]

For example, the forward determinant is `4|u|^2` after the diagonal
rescaling, while the reverse determinant is `-4|v|^2`; equation (8)
gives exactly (16).

The geometric lift of the full cyclic prefix is `k pi`, where
`sum epsilon=3k+1`. Each column therefore moves by `k pi`, and
the raw kernel pair in (14) moves by `2k pi`. Gauging the `2m`
negative switch edges makes every adjacent determinant positive and
adds `2m pi`. Its resulting winding is precisely `2(k+m)pi=2n pi`.
The gauge is periodic because there are an even number of negative
edges.

The gauged off-diagonal entries of `D` are
`1/(b_i+b_(i+1))`. By (16), these are twice the canonical
inverse-Wronskian coefficients. Its kernel has dimension exactly two:
the pair is independent, and its nonzero off-diagonal recurrence
is determined by two initial values. The positive-Wronskian homotopy
therefore proves (1), including the factor-two normalization. This
argument requires no acute-angle lemma for the individual mixed arcs.

## 5. Full scalar Hessian and actual endpoint curvature

Put `B=B_epsilon(a)`, `D=B_epsilon(b)`, `C=grad J`, and

\[
M=J''(a)-c\,D B_\epsilon(a)[b].
\]

At the actual critical point the complete scalar Hessian is

\[
\boxed{
\operatorname{Hess}\Psi_\epsilon=
\begin{pmatrix}
M&-cB&-C/c\\
-cB&(c/2)D&0\\
-C^T/c&0&0
\end{pmatrix}.}
\tag{17}
\]

All third derivatives in the contraction of `B_epsilon` are symmetric
because it is the Hessian of (4).

The actual full frame tangent is characterized by

\[
C\cdot v=0,\qquad Bv\perp\ker D.
\tag{18}
\]

The original multiplier `U` and its two independent determinant-level
variations span all traceless frame covectors, so (18) pairs the frame
derivative with all three, rather than adding an artificial cost
constraint. Rank three is proved for the remaining `N>=6` periods
in [MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md).

Along an actual closed variation keep `U` fixed as the multiplier of
the central frame constraint. The varying prefixes determine `b'`,
and (9) gives `D b'=2Bv`. Differentiating the normal frame gradient
`cB(a)b(a)` then yields the exact curvature-corrected form

\[
\boxed{
Q_{\rm closed}(v)=v^TMv-2c(Bv)^TD^\dagger Bv,
\qquad v\text{ satisfying (18)}.
}
\tag{19}
\]

The range inverse `D^dagger` is generally indefinite. Its two kernel
directions drop out of (19) by (18). The same fixed-multiplier argument
as in the independently audited forward dual note applies; the moving
prefixes and frame curvature have not been suppressed.

Eliminating the nonzero part of `(c/2)D` in (17) contributes
`N-2n-1` negative directions by (1). Its two kernel directions and
the scalar `c` coordinate pair with the three independent constraints
(18), contributing three further negative and three positive
directions. This proves (2). There is no additional rotation coordinate
in this scalar formulation.

## 6. Exact signs available for a uniform negative-subspace proof

Let `s_i=a_i+a_(i+1)` and `t_i=b_i+b_(i+1)>0`. For every sign,

\[
d_i=\frac{ct_i}{2s_i^2},\qquad
j_i=\frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}{4s_i^2},\qquad
\beta_i=\epsilon_i(2d_i-j_i)>0.
\]

The adjacent coupling block of (17), in node ordering `(a_i,b_i)`,
is

\[
R_i=\epsilon_i\begin{pmatrix}
j_i+2d_i&-c/s_i\\-c/s_i&c/(2t_i)
\end{pmatrix},
\qquad
\det R_i=-\frac{\epsilon_i c\beta_i}{2t_i}.
\tag{20}
\]

Thus a forward coupling block is indefinite, while a reverse coupling
block is negative definite. These are coupling blocks between adjacent
nodes, not principal submatrices whose indices may simply be added.

The ratio graph `delta b_i=(2b_i/a_i)delta a_i` is well-defined
because the physical `a_i` remain positive. Its off-diagonal entry is

\[
G_{i,i+1}=-\beta_i
-\frac{2\epsilon_i c a_i a_{i+1}}{s_i^2t_i}
 \left(\frac{b_i}{a_i}-\frac{b_{i+1}}{a_{i+1}}\right)^2.
\tag{21}
\]

Its scaling row is `delta_i` times the forward expression:

\[
(Ga)_i=\delta_i\frac{
16c b_i(a_i^4+8a_i^2-4b_i^2)-8a_i^2(b_i^2+4)}
{a_i(a_i^2+4)^2(b_i^2+4)}.
\tag{22}
\]

In particular this row vanishes at every turn. The identities follow
from `B_epsilon(a)a=8delta/K` and its directional derivative.
Neither (20) nor (21)--(22) proves a full negative subspace.

The uniform remaining sufficient target is an `N`-dimensional
negative subspace for (17), with the actual full-period conditions
retained. For M2 beyond the through-five class one has `n>=2`, so
that target would exclude the entire remaining M2 domain by (2).
The present note supplies the common signed scalar system and its
correct index transfer; it leaves that substantive sign open.

## Supplementary exact checker

Run

```
python3 explorations/mixed_global_scalar_dual_certificate.py
```

All 19 exact identities pass with Python 3.12.14 and SymPy 1.14.0.
They check both conjugation signs, the four signed factor formulas,
the potential and scaling derivatives, the two kernel Wronskians,
and the signed adjacent-block and ratio-graph identities. The
geometric lifted branches, actual normal/endpoints interface, rank,
and bordered-Hessian inertia are the displayed hand arguments. The
checker supplies no negative-subspace or cost-comparison sign.

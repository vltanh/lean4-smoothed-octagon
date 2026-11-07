# Exact local descent on the short equal-factor forward six-window family

Date: 2026-11-07. A constrained local calculation with both endpoints
preserved; no closed-word comparison or numerical search.

## Result and scope

For every \(1<q\le5/4\), consider the local word `012012` with all
six factors equal to \(q\), initial frame \(I\), and physical margins

\[
(a,a(2/q-1),a),\qquad a^2={4q\over4-q}.                    \tag{1}
\]

There is a strictly cheaper six-positive-piece path of the **same word**
with precisely the same initial and final frame and state. The original
initial state is held fixed in the variation; elapsed time may change.
The source and replacement remain strictly in the star domain.

The proof computes the actual constrained Hessian, including the frame
endpoint multiplier and curvature of the constraint. It is strictly
negative on the one-dimensional endpoint tangent throughout this
interval. The comparison neither assumes a closed endpoint \(F=R\)
nor varies the initial shape to obtain its decrease.

All standard forward polygon six-windows with
\(q=2\cos(\pi k/(3k+1))\), \(k\ge2\), lie in this interval.
Those known windows satisfy the complete-switch PMP and eligibility
conditions. Thus this is a nonempty subfamily result inside the revised
L1 domain, not just a test on inputs already excluded by external gaps.

The same local descent holds on an unspecified open neighborhood of
each fixed reference input in its full eight-dimensional initial-state/
factor domain. No radius is uniform as \(q\downarrow1\), and no
coverage of the entire asymmetric PMP family is claimed. L1 and the
other revised universal analytic targets remain open.

## 1. Constant active margins and the exact endpoint tangent

Use [LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md). For a forward word,
the active chain \(a_{-1},\ldots,a_6\) gives

\[
q_i={(a_{i-1}+a_i)(a_i+a_{i+1})\over a_i^2+4}.
\]

The data (1) have \(a_i=a\) for every index: after one arc the margin
triple is cyclically relabeled, with the next active margin again
\(a\). Indeed \(q=4a^2/(a^2+4)\). Positivity of the remaining margin
\(a(2/q-1)\) requires only \(q<2\), so every reference in the asserted
range is strict-star throughout its six arcs.

For the local variation, fix the four outer active margins
\(a_{-1},a_0,a_5,a_6\). This fixes both states and leaves the four
variables \(a_1,\ldots,a_4\). The remaining frame endpoint is

\[
F=A(q_0)\cdots A(q_5),\qquad
A(q)=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix}.
\]

Write \(V_i=F_{a_i}F^{-1}\). At the constant chain,

\[
V_i=\operatorname{Ad}_{A^i}V_*,\qquad
V_*={1\over a}
\begin{pmatrix}-q/2&q^2\\-1&q/2\end{pmatrix}.              \tag{2}
\]

The adjoint action of \(A\), whose determinant is one and trace is
\(q\), satisfies

\[
(\operatorname{Ad}_A)^3-r(\operatorname{Ad}_A)^2
 +r\operatorname{Ad}_A-I=0,
\qquad r=q^2-1.
\]

This follows from its eigenvalues \(1,e^{2i\theta},e^{-2i\theta}\),
where \(q=2\cos\theta\), or directly from the two-by-two
Cayley--Hamilton identity. Hence

\[
v=(-1,r,-r,1),\qquad \sum_{i=1}^4v_iV_i=0.                \tag{3}
\]

The full-domain rank theorem proves that the four columns have rank
three. Thus (3) is a nonzero tangent spanning the actual fixed-state,
fixed-frame endpoint fiber, not merely a formal direction annihilating
part of the endpoint equations.

## 2. The stationary frame multiplier

Let \(J=C/\sqrt{12}\), with the exact active-margin action from
LOCAL_FORWARD_RANK. Its four interior derivatives at the constant
chain are all

\[
G={a\over16}(8+q-4\log q).                               \tag{4}
\]

Put

\[
B_*=A-{q\over2}I,
\qquad
\mu(W)={8+q-4\log q\over2(4-q)^2}
          \operatorname{tr}(B_*W).                       \tag{5}
\]

Since \(B_*\) commutes with \(A\), the value of \(\mu(V_i)\)
is independent of \(i\). Direct multiplication gives

\[
\operatorname{tr}(B_*V_*)={q(4-q)\over2a}.
\]

Using \(a^2=4q/(4-q)\), this makes \(\mu(V_i)=G\) for all four
columns. Every reference in (1), in fact every \(1<q<2\) in this
equal-factor family, is therefore stationary on its endpoint fiber.
Rank three makes (5) the unique frame multiplier. This is the
three-dimensional multiplier after fixing the two states; it is not
an arbitrarily chosen full-control costate.

## 3. The complete constrained Hessian

Write \(L=\log q\) and \(U=1+r^2\). The nearest-neighbor action has
the following ambient Hessian entries at the constant chain:

\[
8J_{a_i a_i}=D:=-2L+{5q\over2}-{q^2\over4}-3,
\qquad 8J_{a_i a_{i+1}}={3\over2}.                         \tag{6}
\]

All other off-diagonal entries are zero. Thus

\[
v^{\mathsf T}(\operatorname{Hess}J)v
 ={2DU-6r-3r^2\over8}.                                  \tag{7}
\]

The endpoint-curvature correction must also be subtracted. Extend
\(v_{-1}=v_0=v_5=v_6=0\), and let \(z_j,w_j\) be the first and
second derivatives of \(\log q_j\) along the straight active-margin
variation with velocity (3). The explicit derivatives are

\[
z_j={v_{j-1}+(2-q)v_j+v_{j+1}\over2a},
\]
\[
w_j=-{(v_{j-1}+v_j)^2+(v_j+v_{j+1})^2\over4a^2}
       +{2(a^2-4)v_j^2\over(a^2+4)^2}.                    \tag{8}
\]

Set \(E=\operatorname{diag}(1,-1)\) and
\(Z_j=\operatorname{Ad}_{A^j}E\). On an endpoint-tangent direction,
the second right-trivialized frame variation is

\[
\mathcal K(v)=\sum_{j=0}^5w_jZ_j
 +\sum_{0\le m<j\le5}z_mz_j[Z_m,Z_j].                    \tag{9}
\]

The square of the first right-trivialized variation vanishes because
(3) fixes the endpoint to first order. Formula (9) is the finite-product
derivative proved in LOCAL_FORWARD_RANK; it includes the noncommuting
prefix derivatives. The actual constrained second derivative is

\[
Q(q)=v^{\mathsf T}(\operatorname{Hess}J)v-\mu(\mathcal K(v)).
                                                                    \tag{10}
\]

### 3.1 The second-log terms

Summing (8) gives

\[
a^2\sum_jw_j
=W:=-\bigl(1+(r-1)^2\bigr)
       +{q(q-2)\over2}(1+r^2).                           \tag{11}
\]

For example,
\(\sum_{i=0}^4(v_i+v_{i+1})^2=2+2(r-1)^2\) and
\(\sum_{i=1}^4v_i^2=2+2r^2\), which give (11) directly.
Also \(\operatorname{tr}(B_*Z_j)=q\) for every \(j\).

### 3.2 The commutators without a large matrix expansion

Put \(t=q^2-2\). The numbers

\[
k_d=\operatorname{tr}(B_*[E,\operatorname{Ad}_{A^d}E])
\]

have \(k_0=0\), \(k_1=4q\), and satisfy
\(k_{d+1}=t k_d-k_{d-1}\). One can obtain this recurrence from the
adjoint eigenvalues in Section 1: the fixed component is proportional
to \(B_*\), and its contribution to this commutator trace is zero.
The value \(k_1\) also follows immediately from
\([E,AEA^{-1}]=4q^2E_{12}\).

Write \(z_j=d_j/(2a)\). Equation (8) gives

\[
(d_0,\ldots,d_5)=(-1,B,-C,C,-B,1),
\quad B=q^2+q-3,\quad C=q^3-q^2-q+2.                     \tag{12}
\]

For the convolution in (9), set \(u_0=0\), \(u_1=d_0=-1\),
and \(u_{j+1}=tu_j-u_{j-1}+d_j\). Its entire short table is

\[
(u_0,\ldots,u_6)=(0,-1,q-1,1-q,1,0,0).
\]

Consequently the scalar commutator sum is

\[
\sum_{m<j}z_mz_j
 \operatorname{tr}(B_*[Z_m,Z_j])
 ={q\over a^2}S,
\qquad
S=\sum_{j=1}^5d_ju_j=-2B-2(q-1)C.                        \tag{13}
\]

Every entry in the table follows by one substitution using
\(B=t+q-1\) and \(C=(q-1)t+q\). No vanishing symbolic
determinant or sampled identity is a premise.

### 3.3 The exact scalar formula

Combine (5), (7), (11), and (13). With \(P=W+S\), one obtains

\[
Q(q)={1\over8}
 \left(2DU-6r-3r^2-{8+q-4L\over4-q}P\right),              \tag{14}
\]

where the polynomial needed for a direct expansion is

\[
P={q^6\over2}-q^5-4q^4+6q^3+3q^2-10q+5.
\]

Equivalently,

\[
\boxed{Q(q)={\mathcal A(q)+\mathcal B(q)\log q\over8(4-q)},}
                                                                    \tag{15}
\]

with

\[
\begin{aligned}
\mathcal A(q)&=-10q^6+40q^5+4q^4-102q^3+20q^2+124q-76,\\
\mathcal B(q)&=2q^6-32q^4+16q^3+44q^2-32q-12.
\end{aligned}
\]

For checking the expansion, the numerator in (14), after multiplying
by \(4-q\), is

\[
(4-q)\bigl((5q-q^2/2-6)U-6r-3r^2\bigr)
 -(8+q)P+4L\bigl(P-(4-q)U\bigr).
\]

This gives exactly the two polynomials in (15). As a consistency check
outside the descent interval, (15) specializes at \(q=3/2\) to
\(Q=(29/640)(23-51\log(3/2))\), agreeing with the earlier
fixed-endpoint calculation after its tangent rescaling. That check
is not a proof premise, and no sign on the whole interval \(1<q<2\)
is asserted.

## 4. A short hand certificate for the negative sign

Set \(x=q-1\), so \(0<x\le1/4\). The two shifted polynomials are

\[
\begin{aligned}
\mathcal A(1+x)
 &=14x-12x^2+114x^3+54x^4-20x^5-10x^6,\\
\mathcal B(1+x)
 &=-14-12x-70x^2-72x^3-2x^4+12x^5+2x^6<0.
\end{aligned}                                             \tag{16}
\]

For instance the strict last sign follows already by discarding the
other negative terms and bounding
\(-14+12x^5+2x^6\le-14+12/4^5+2/4^6<0\).
The elementary logarithmic inequality

\[
\log(1+x)>{2x\over2+x}\qquad(x>0)
\]

follows by differentiation from equality at zero: the derivative of
the difference is \(x^2/((1+x)(2+x)^2)>0\).
Because the logarithm coefficient is negative,

\[
\mathcal A+\mathcal B\log(1+x)
 <{(2+x)\mathcal A+2x\mathcal B\over2+x}
 =-{2x^2\over2+x}
 \bigl(17-38x-39x^2-5x^3+8x^4+3x^5\bigr).                \tag{17}
\]

On the stated interval the bracket is at least

\[
17-{38\over4}-{39\over16}-{5\over64}={319\over64}>0.
\]

Since \(8(4-q)>0\), equations (15)--(17) prove

\[
\boxed{Q(q)<0\qquad(1<q\le5/4).}                         \tag{18}
\]

## 5. Exact endpoint-preserving replacements and nearby inputs

Rank three of the fixed-state frame map gives a smooth local
one-dimensional endpoint fiber through every reference. It has a
smooth curve with velocity (3). On this curve the first cost derivative
is zero by (4)--(5), and its second derivative is exactly (18).
For sufficiently small nonzero curve parameter, the cost is therefore
strictly smaller. Both states and the tangent endpoint remain exactly
fixed, so \(g_{\rm end}=X_0FX_{\rm end}^{-1}\) fixes the actual final
frame as well.

All six factors are initially greater than one and every margin is
strictly positive. These are open inequalities, so a sufficiently small
variation retains them and gives an actual six-positive-piece
strict-star path. The initial state is never changed. No sector test
on the replacement is assumed: for an actual minimizing source, the
existing P0 finite-piece splice supplies the geometric comparison.

The conclusion extends to an open neighborhood of each fixed reference
in the full eight-dimensional initial-state/factor space. Here is the
precise local argument. The triple \((V_2,V_3,V_4)\) is independent,
so the implicit function theorem solves \(a_2,a_3,a_4\) smoothly in
terms of the four outer margins, the three frame endpoint coordinates,
and the remaining fiber coordinate \(a_1\). These form a local chart
of all eight active-margin variables. At the reference its fiber
tangent is the negative of (3), whose first coordinate is one; its
restricted cost second derivative is again \(Q(q)<0\).

By continuity that second derivative stays negative on an open
neighborhood. A neighboring input with nonzero first fiber derivative
descends in the appropriate direction at first order. A stationary
neighbor descends at second order. The same local chart preserves its
own initial state and full endpoint, and sufficiently small changes
preserve the positive factors and margins. This proves the claimed
open-neighborhood comparison without assuming stationarity, PMP, or
sector eligibility for every neighbor.

The neighborhood and the size of the improvement may depend on the
reference \(q\). They have not been bounded uniformly as \(q\to1\).
The statement does not cover every asymmetric input, or all of the
five-dimensional asymmetric PMP family in
LOCAL_FORWARD_ENDPOINT_FILTER.

## 6. Application to the standard complete-switch PMP windows

For the known standard forward family, write

\[
q_k=2\cos\left({\pi k\over3k+1}\right),\qquad k\ge2.
\]

Since \(k/(3k+1)\) increases from \(2/7\) to \(1/3\),

\[
1<q_k\le2\cos(2\pi/7)<5/4.                               \tag{19}
\]

For the strict rational bound, let \(z=2\cos(2\pi/7)>1\).
Pairing the seventh roots of unity gives
\(z^3+z^2-2z-1=0\). This polynomial is strictly increasing on
\([1,\infty)\), and its value at \(5/4\) is \(1/64>0\).
This proves the last inequality in (19) without a decimal estimate.

[LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md), using the
published standard-polygon Pontryagin lift, establishes that these
six-complete-piece windows have full local PMP, genuine external
switches, strict-star states, the required sectors, and window cost
below the octagon budget. Their factors and margins are exactly (1).
Equations (18)--(19) now give a cheaper same-word local replacement
for every one of them, and the preceding section gives unspecified
open neighborhoods with the same conclusion.

This local calculation does not use a comparison of the whole closed
polygon's cost. An arbitrary equal-factor \(q\) is not being declared
a globally closed polygon or a full-PMP reference: the broad local
descent theorem needs none of those properties. They are invoked only
for the already established standard values in (19).

## Dependencies and validation boundary

- LOCAL_FORWARD_RANK supplies the active coordinates, full-domain rank,
  exact cost action, and endpoint-curvature formula.
- LOCAL_FORWARD_PMP_LIMIT and its cited Hales--Vajjha results supply
  the standard family's complete-switch PMP and input eligibility.
- MINIMIZER_WINDOW_AUDIT supplies the finite-piece geometric splice
  when this comparison is applied to an actual minimizing window.

All new Hessian identities, logarithmic signs, and continuation
arguments are hand calculations. No optimizer, sampled Hessian,
computer algebra assertion, Lean, Lake, typecheck, or CI is a premise.
The result excludes this explicit subfamily and nearby inputs; it does
not close the revised universal L1 target or prove a global complexity
bound.

Independent internal hand reviews on 2026-11-07 checked the active-margin
tangent, unique endpoint multiplier, both contributions to the constrained
Hessian, the exact logarithm estimate on the whole interval, and the
implicit-function passage to exact endpoint-preserving replacements.
A separate review checked standard-family inclusion and persistence for
nearby unequal-factor inputs. No material gap was found. These are
mathematical reviews, not external peer review or Lean kernel validation.

# Full endpoint rank for the mixed six-piece word 021210

Date: 2026-11-07. Hand proof on the entire positive strict-star domain.

## Theorem and exact scope

Fix any initial frame and determinant-one strict-star state. For the word

\[
0,\ 2,\ 1,\ 2,\ 1,\ 0,
\]

let the six physical durations be positive, and suppose the resulting
trajectory stays in the strict-star domain. The map from these six
durations to the **full terminal frame and state** has rank five.
The same assertion holds in the repository's six positive-factor
coordinates.

No symmetry, small-duration, cost, sector, stationarity, or Pontryagin
hypothesis is used. In particular, this is not restricted to the
small padded reverse-edge examples. The initial state is fixed
throughout the differentiation.

The proof separates the four-piece edge core from the two outer
control-\(0\) arcs. The edge endpoint map has rank three. In its
two-dimensional normal quotient, the two outer columns have an
explicit strictly nonzero determinant.

The resulting one-dimensional endpoint fibers do not imply descent.
The original broad L3 replacement target is refuted by
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md).
This rank theorem instead removes abnormality and normalized-multiplier
ambiguity for any proposed restriction of L3 to genuine minimizing
windows. It does not repair the uniform reduction or exclude a
competitor class.

## 1. Coordinates and the edge core

Use the original half-plane coordinates from
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md):

\[
q=\frac1{\sqrt3},\qquad
X=\Phi(x,y)=\frac1y
 \begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\qquad w=y^{-2}.
\]

The strict-star domain is

\[
-q<x<q,\qquad y>0,\qquad x^2+y^2>q^2.
\]

The frame is \(g\in\mathrm{SL}_2(\mathbb R)\), with \(g'=gX\).
Thus the full frame/state manifold has dimension \(3+2=5\).

Temporarily consider only a positive four-piece core with controls
\(2,1,2,1\). Left-normalize its initial frame to \(I\) by one fixed
linear map. Write its initial state as \((a,y_a)\), its terminal state
as \((b,y_b)\), and its three interior switch abscissas as

\[
a<\xi_1<\xi_2<\xi_3<b.
\]

All inequalities are strict because on either edge control

\[
\frac{dx}{dt}=y>0.
\]

In the \(x\) coordinate,

\[
\frac{dw}{dx}=\beta_i(x)w,\qquad
\beta_2(x)=-\frac2{q+x},\qquad
\beta_1(x)=\frac2{q-x}.                                    \tag{1}
\]

Set

\[
S(x)=\int_a^x w(r)\,dr,\qquad S_b=S(b)>0.
\]

Direct integration of the frame equation gives

\[
g(x)=
\begin{pmatrix}
1+aS(x)&a-x-axS(x)\\
S(x)&1-xS(x)
\end{pmatrix}.                                            \tag{2}
\]

For example, put \(K(x)=\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)\).
Then \((gK)_x=gK\,wE_{21}\) and the initial value is \(K(a)\);
multiplying \(K(a)(I+S E_{21})K(x)^{-1}\) gives (2).

In particular the full terminal frame/state is determined by the three
edge endpoint coordinates

\[
(b,\log w_b,S_b),\qquad w_b=y_b^{-2}.                       \tag{3}
\]

Conversely the terminal state recovers \(b,w_b\) and the frame entry
\(g_{21}\) recovers \(S_b\). Thus (3) is a smooth coordinate system on
the three-dimensional family of edge endpoints.

## 2. The four edge durations give rank three

The four physical durations and the four ordered abscissas
\((\xi_1,\xi_2,\xi_3,b)\) are locally smoothly equivalent.
The map from durations to these abscissas is triangular, and its
diagonal entries are the positive terminal values of \(y\) on the four
arcs. Hence its derivative is invertible. All the nearby flows exist
in the strict-star domain because the reference consists of finitely
many compact arcs in that open domain.

At fixed \(b\), let

\[
k_j=\beta_{\text{left}}(\xi_j)
      -\beta_{\text{right}}(\xi_j),\qquad
R_j=\int_{\xi_j}^b w(r)\,dr .
\]

For the control order \(2,1,2,1\), the \(k_j\) have signs
\(-,+,-\), and none is zero, since

\[
\beta_1(x)-\beta_2(x)=\frac{4q}{q^2-x^2}>0.
\]

Moving switch \(\xi_j\) changes \(\log w(x)\) by \(k_j\,d\xi_j\)
for \(x>\xi_j\), and makes no change for \(x<\xi_j\). Therefore

\[
\frac{\partial(\log w_b,S_b)}{\partial\xi_j}
   =k_j(1,R_j).                                          \tag{4}
\]

There is no extra moving-boundary term in the integral derivative:
the two formulas for \(w\) agree at the switch. Since \(w>0\),

\[
R_1>R_2>R_3>0.
\]

For any two different switch indices \(j<\ell\), the corresponding
two-by-two determinant is

\[
k_jk_\ell(R_\ell-R_j)\ne0.                               \tag{5}
\]

Thus the fixed-\(b\) map has rank two. Adding the output coordinate
\(b\), whose derivative in the variable \(b\) is one and whose switch
derivatives are zero, proves rank three for the full four-duration
edge endpoint map.

This proof works for arbitrary unequal positive edge arcs; it makes no
reference to an edge extremal, its costate, or the sign of a Hessian.

## 3. Two exact normal coordinates

Fix the core's baseline initial state and frame. Put

\[
c_i=e_1,\qquad v_i=X(a,y_a)e_1=\frac1{y_a}(a,1).
\]

For a variable terminal frame/state \((g_e,X_e)\), define

\[
N_1=\det(v_i,g_eX_e e_1),\qquad
N_2=\det(v_i,g_e e_1-e_1).                                \tag{6}
\]

On every edge path beginning at this fixed initial pair, both quantities
are zero. In fact they describe the full edge endpoint submanifold.

To check the converse, write \(c_e=g_e e_1\). From \(N_2=0\),

\[
c_e=(1+aS,S)
\]

for a unique real \(S\). If the terminal state is \((b,y_b)\), then
\(N_1=0\) says \(g_eX_e e_1=\rho_b v_i\) for some scalar \(\rho_b\).
The condition \(\det g_e=1\) forces

\[
\rho_b=\frac{y_a}{y_b}.
\]

The second column is consequently

\[
g_e e_2=(a,1)-b c_e=(a-b-abS,1-bS),
\]

which is exactly (2). No additional sign or endpoint branch occurs.

The differentials \(dN_1,dN_2\) are independent at every such endpoint.
For example, vary the terminal \(b\) while holding \(g_e,y_b\) fixed.
Then

\[
\frac{\partial N_1}{\partial b}
=\frac{\det(v_i,c_e)}{y_b}
=-\frac1{y_a y_b}\ne0,\qquad
\frac{\partial N_2}{\partial b}=0.                          \tag{7}
\]

The differential of \(N_2\) is nonzero on frame variations: the first
column of a tangent vector to \(\mathrm{SL}_2\) can vary in any direction,
and \(v_i\ne0\). Thus \(N=(N_1,N_2)\) is a rank-two normal chart.

Combining this with Section 2, the four middle duration columns span
exactly the three-dimensional kernel of \(dN\).

## 4. Normal columns for arbitrary asymmetric edge data

Consider a control-\(0\) piece inserted at a point \(x\in[a,b]\)
of the baseline edge core, with small physical duration \(\varepsilon\).
All four old edge durations remain fixed. Let

\[
\nu(x)=\left.\frac{d}{d\varepsilon}N\right|_{\varepsilon=0}
\]

be its projected endpoint column.

The required formula is

\[
\boxed{\displaystyle
\nu(x)=
\frac{2y(x)^2}{\gamma_0(x)y_a y_b}
 \left(1,\ y_b\int_x^b w(r)\,dr\right),\qquad
\gamma_0(x)=\frac{x^2+y(x)^2-q^2}{y(x)}>0.}                 \tag{8}
\]

All quantities refer to the unperturbed edge path. The two heights
\(y_a,y_b\) need not agree.

### Derivation of the prefactor

Write \(c=ge_1\) and \(v=gXe_1\). From (2),

\[
v(x)=\frac1{y(x)}(a,1)=\rho(x)v_i,
\qquad \rho(x)=\frac{y_a}{y(x)}>0,\qquad
\rho_b=\frac{y_a}{y_b}.
\]

Because \(X^2=-I\),

\[
\det(v,v')
=\det\!\left(Xe_1,-e_1+X'e_1\right)
=\frac{y-x'}{y^2}.
\]

On edge controls \(x'=y\), so \(v'\) is parallel to \(v\);
more precisely,

\[
v'=-\frac{y'}{y}v.                                        \tag{9}
\]

For control \(0\),

\[
x'=y-\frac{2y^3}{x^2+y^2-q^2},
\]

and hence

\[
\det(v,v')=\frac2{\gamma_0}.                              \tag{10}
\]

The inserted piece therefore creates the instantaneous normal tangent
variation

\[
\det(v_i,\delta v)=\frac2{\gamma_0(x)\rho(x)}.
\]

The simultaneous position variation is \(\delta c=v(x)\), whose
normal projection is zero.

Along the subsequent edge path, linearize (9). The term involving the
variation of \(-y'/y\) is parallel to the baseline \(v\), and vanishes
after taking its determinant with \(v_i\). Thus the normal tangent
variation at later time \(t\) is multiplied by \(\rho(t)/\rho(x)\).
Its terminal value is

\[
\delta N_1
=\frac{2\rho_b}{\gamma_0(x)\rho(x)^2}
=\frac{2y(x)^2}{\gamma_0(x)y_a y_b}.                        \tag{11}
\]

Since \(c'=v\), the terminal normal position variation is the integral
of this transported normal tangent variation. Dividing by (11) gives

\[
\frac{\delta N_2}{\delta N_1}
=\int_{t(x)}^{t(b)}\frac{\rho(t)}{\rho_b}\,dt
=y_b\int_x^b y(r)^{-2}\,dr.
\]

Here \(dt=dx/y\) on the reference edge. This proves (8), including its
precise asymmetric prefactor.

At the two ends, (8) becomes

\[
\nu(a)=\frac{2y_a}{\gamma_0(a)y_b}(1,y_bS_b),\qquad
\nu(b)=\frac{2y_b}{\gamma_0(b)y_a}(1,0).                    \tag{12}
\]

Therefore

\[
\boxed{\displaystyle
\det\bigl(\nu(a),\nu(b)\bigr)
=-\frac{4y_bS_b}{\gamma_0(a)\gamma_0(b)}<0.}                \tag{13}
\]

This is the required uniform nondegeneracy statement in the sense of
pointwise rank throughout the domain. It is not a positive uniform
lower bound: the determinant may tend to zero along degenerating
families.

## 5. Arbitrary positive outer arcs give the same normal directions

Return to a full \(\mathtt{021210}\) trajectory. Let its baseline first
and last physical durations be \(d_0,d_5>0\), of any allowed size.
Let \(\varphi_0^t\) denote the smooth control-\(0\) flow on the full
frame/state manifold.

The initial frame and state of the full six-piece path remain fixed.
Postcompose the endpoint map by the inverse of the **fixed baseline**
last flow \(\varphi_0^{-d_5}\). This is a local diffeomorphism near the
baseline endpoint. Such an inverse exists on a neighborhood because
the baseline last arc is a compact trajectory in the open strict-star
domain.

Next left-multiply every nearby frame by the inverse of the **fixed
baseline** frame at the beginning of the middle edge core. This is
another fixed diffeomorphism. We do not renormalize separately for each
varied first duration: doing so would incorrectly remove part of that
duration's frame variation.

In these coordinates the baseline core starts at \(g=I\), so Sections
1–4 apply. The four middle duration columns span \(\ker dN\).

Autonomy gives the exact flow identities

\[
\varphi_0^{d_0+\varepsilon}
=\varphi_0^\varepsilon\circ\varphi_0^{d_0},
\qquad
\varphi_0^{-d_5}\circ\varphi_0^{d_5+\varepsilon}
=\varphi_0^\varepsilon.                                   \tag{14}
\]

Consequently varying the first outer duration, after these fixed
coordinate changes, is exactly a control-\(0\) insertion at the core
entrance. Varying the last duration is exactly such an insertion at
its exit. Their normal columns are therefore \(\nu(a)\) and \(\nu(b)\)
from (12), even when the already existing outer arcs are long or
unequal.

By (13), these two columns span the entire two-dimensional normal
quotient. Together with the rank-three middle columns, the full
endpoint differential has rank five. Postcomposition by the two
fixed diffeomorphisms preserves rank, proving the theorem for physical
durations at the original fixed initial state.

The proof has not varied the initial shape and has not substituted
preservation of only a tangent product or only a state endpoint for the
full endpoint condition.

## 6. Positive factors and consequences for necessary conditions

In the repository's factor convention, the duration of arc \(j\) is

\[
d_j=\frac{p_{i_j}^{\rm start}}2\log q_j .
\]

The positive active margin at the start of arc \(j\) depends only on
the initial state and the preceding factors. Therefore the map from
the six factors to the six physical durations is smooth and triangular,
with diagonal entries

\[
\frac{\partial d_j}{\partial q_j}
=\frac{p_{i_j}^{\rm start}}{2q_j}>0.
\]

It is locally a diffeomorphism everywhere on the positive strict-star
domain. Rank five consequently holds for the six-factor endpoint map
as well.

The regular-level-set theorem gives a smooth one-dimensional local
endpoint fiber at every input in this domain. It gives neither a
uniform conditioning estimate near the boundary nor a cheaper point
on that fiber.

There is also a direct PMP consequence. On a free-time extremal,
the first-variation identity for the six independent durations is

\[
\lambda_0\,dJ=\lambda_e\circ d\mathcal E,
\]

where \(\mathcal E\) is the full five-dimensional endpoint map. If the
cost multiplier were zero, surjectivity would force the reduced
endpoint covector \(\lambda_e=0\), and then the adjoint equation would
force the covector to vanish throughout the window. This violates PMP
nontriviality on the actual state manifold. Thus a free-time minimizing
window of this type is normal. Normalizing the cost multiplier to one,
the same surjectivity makes its endpoint covector unique; the adjoint
equation then makes its full normalized lift unique on the window.

This is the same rank-based argument used for L1, now on the **entire**
positive L3 domain. At a stationary L3 input, full-control inequalities
and external switch ties can therefore be checked against one uniquely
determined normalized multiplier. No abnormal or alternative normal
lift can be invoked to evade a failed test.

## Dependencies and validation boundary

The proof uses the explicit half-plane vertex fields and frame equation,
the edge-coordinate differentiation in (4), and the displayed normal
projection (8). It does not use the small-core estimates, symmetry,
optimality theorem, or finite-piece comparison from the padded-family
obstruction.

The coordinate formulas agree with the pinned project conventions.
No Lean, Lake, typecheck, or CI command was run. No numerical search
or symbolic computation is a premise of the hand proof.

An independent hand review checked the edge rank, asymmetric normal
prefactor, strict determinant sign, fixed-coordinate outer-flow transport,
and the reduced-cotangent normality argument. No material gap was found.


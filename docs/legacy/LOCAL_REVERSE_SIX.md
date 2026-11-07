# An exact needle improvement for the uniform reverse six-arc family

## Result and scope

This note proves an endpoint-preserving strict improvement for a concrete
one-parameter subfamily of the local template **L2 = 021021** in
[BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md).

For every \(q>1\), take six equal factors \(q\), with fixed initial star
margins
\[
(p_0,p_1,p_2)=\frac2{\sqrt{4q-1}}(1,1,2q-1).
\tag{1}
\]
There is a strict-star replacement with the **same initial and final frame
and state**, free elapsed time, seven positive vertex pieces, and strictly
smaller cost. Its word is
\[
\boxed{0121021.}
\]
It inserts a short control-1 arc after the first control-0 arc and adjusts
five original factors. The initial state is not varied.

**This is not a proof of the full L2 statement.** It assumes the equal
factors and the state in (1). Arbitrary initial states and six unequal
factors form the open eight-dimensional domain of L2. Also, seven pieces
exceed the at-most-six replacement count in the current formulation of
that target. A universal seven- or eight-piece improvement for an entire
template would still exclude that template from a global minimizer, but
this note establishes such an improvement only for (1).

The number of fully proved universal local inputs remains **zero of five**.
No longer closed-word classification, switch bound, or unrestricted
Reinhardt comparison follows from this subfamily result.

## 1. Exact trajectory and endpoint conventions

Use the triangular coordinates of
[BOUNDED_REDUCTION.md, Sections 4–6](BOUNDED_REDUCTION.md). Write
\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]
\[
T_0(x)=\begin{pmatrix}x&0\\0&x^{-1}\end{pmatrix},\quad
T_1(x)=\begin{pmatrix}x^{-1}&x-x^{-1}\\0&x\end{pmatrix},\quad
T_2(x)=\begin{pmatrix}x^{-1}&0\\x^{-1}-x&x\end{pmatrix}.
\tag{2}
\]
The scalar-free state half-factors are
\[
M_0(x)=\begin{pmatrix}1&0\\0&x\end{pmatrix},\quad
M_1(x)=\begin{pmatrix}x&1-x\\0&1\end{pmatrix},\quad
M_2(x)=\begin{pmatrix}x&0\\x-1&1\end{pmatrix}.
\tag{3}
\]
Each \(M_i(x)/\sqrt x\) is the actual determinant-one state conjugator.
Its scalar cancels in the conjugation.

For a chronological word \(i_0,\ldots,i_{n-1}\), define
\[
F=T_{i_0}(x_0)\cdots T_{i_{n-1}}(x_{n-1}),\qquad
H=M_{i_{n-1}}(x_{n-1})\cdots M_{i_0}(x_0).
\]
Then
\[
X_{\rm end}=HX_0H^{-1},\qquad
g_{\rm end}=X_0F X_{\rm end}^{-1}
\tag{4}
\]
when \(g_0=I\). Thus fixing \(F\) and the terminal state fixes both
actual endpoints. Left multiplication restores any prescribed initial
frame. No condition \(F=R\) is imposed on this local window.

It is convenient to retain the raw margins
\[
(r_0,r_1,r_2)=(1,1,2q-1),\qquad I=4q-1,
\]
and the raw state
\[
Z_0=\frac12\begin{pmatrix}-1&2q\\-2&1\end{pmatrix}.
\tag{5}
\]
Physical margins and states are obtained by multiplying by \(2/\sqrt I\).
The normalization \(I=r_0r_1+r_1r_2+r_2r_0\) remains fixed throughout
every variation below.

On an arc of label \(i\), with raw margins
\((a,b,c)=(r_i,r_{i+1},r_{i-1})\), the update and normalized cost are
\[
a\longmapsto a,\qquad
b\longmapsto(a+b)x-a,\qquad
c\longmapsto(a+c)/x-a,
\tag{6}
\]
\[
J_i=\frac{a}{2I}
\left[(a+b)(x-1)+(a+c)(1-x^{-1})-a\log x\right].
\tag{7}
\]
Here \(J_i\) is physical cost divided by \(\sqrt{12}\).

For the original word 021021 and \(x=q\), the raw margin triples are
\[
(1,1,2q-1)\longmapsto(1,2q-1,1)
\longmapsto(2q-1,1,1)\longmapsto(1,1,2q-1),
\]
and then repeat. Every raw margin is positive. On each arc the active
margin is \(1\), one other margin increases from \(1\) to \(2q-1\),
and the remaining one decreases from \(2q-1\) to \(1\).
Consequently the entire trajectory is strict star for every \(q>1\).

Its final state equals its initial state, but its final frame is the
actual local endpoint in (4), not an imposed Reinhardt endpoint. The
total normalized cost is
\[
J_6(q)=\frac{3\left[4(q-1)-\log q\right]}{4q-1}.
\tag{8}
\]

## 2. The endpoint map has rank five

The proof needs actual endpoint solvability, not a dimension count.
All parameters in this section vary with \(q\) fixed as the base point.

Let \(F_*,H_*\) be the base products for 021021 with every factor \(q\).
Because the base state returns to \(Z_0\), \(H_*\) commutes with \(Z_0\).
Normalize endpoint coordinates by
\[
\mathcal F=FF_*^{-1},\qquad
\mathcal Z=H_*^{-1} Z_{\rm end}H_*.
\]
Use the following five scalar coordinates near the base point:
\[
\mathcal F_{11}-1,\quad \mathcal F_{12},\quad
\mathcal F_{21},\quad
\operatorname{tr}(D_0\mathcal Z)-1,\quad
\operatorname{tr}(D_1\mathcal Z)-1.
\tag{9}
\]
These are genuine local endpoint coordinates. Since \(\det\mathcal F=1\),
the first three being zero imply \(\mathcal F=I\). The raw determinant
\(\det\mathcal Z=I/4\) is fixed. The last two coordinates fix \(r_0,r_1\);
the invariant
\[
r_0r_1+r_1r_2+r_2r_0=I
\]
then fixes \(r_2\), because \(r_0+r_1>0\). Thus (9) being zero is
equivalent to preserving \(F\) and the terminal state.

Differentiate (9) with respect to the first five original factors,
holding the sixth factor at \(q\). The resulting \(5\times5\) matrix
has determinant
\[
\boxed{-\frac{16(q-1)^2(4q-1)}{q^{12}}\ne0.}
\tag{10}
\]
Here and below matrix entry indices are \(1,2\).

The following gives a short algebraic certificate for (10). For column
\(j\), let \(P_j\) be the product of tangent factors strictly before that
arc, and let \(K_j\) be the reverse product of the scalar-free half-factors
strictly before it. Set
\[
U_j=-\frac1q P_jD_{i_j}P_j^{-1},\qquad
V_j=\frac1{2q}K_j^{-1}D_{i_j}K_j.
\]
The column is exactly
\[
\left(
(U_j)_{11},(U_j)_{12},(U_j)_{21},
\operatorname{tr}(D_0[V_j,Z_0]),
\operatorname{tr}(D_1[V_j,Z_0])
\right)^{\mathsf T}.
\tag{11}
\]
These formulas follow by differentiating (2)–(3); the scalar derivative
of \(H\) drops out of the commutator.

The first three columns of the upper three rows are
\[
\begin{pmatrix}
q^{-1}&-q^{-1}&(q^2-2)q^{-3}\\
0&0&2q^{-1}\\
0&-2q^{-3}&2(q^2-1)q^{-5}
\end{pmatrix},
\]
whose determinant is \(4/q^5\). Eliminating those three columns from
the two state rows leaves
\[
\begin{pmatrix}
-\dfrac{2(q-1)(3q-1)}{q^4}
&
\dfrac{2(q-1)(8q^3-6q^2-2q+1)}{q^6}
\\[5pt]
\dfrac{2(q-1)(5q^2-5q+1)}{q^5}
&
-\dfrac{2(q-1)(12q^4-19q^3+3q^2+4q-1)}{q^7}
\end{pmatrix}.
\tag{12}
\]
Its determinant is \(-4(q-1)^2(4q-1)/q^7\), by the elementary identity
\[
\begin{aligned}
&(3q-1)(12q^4-19q^3+3q^2+4q-1)\\
&\qquad-(8q^3-6q^2-2q+1)(5q^2-5q+1)
=-q^4(4q-1).
\end{aligned}
\]
Multiplying the two block determinants proves (10).

The normalized tangent coordinates matter: an unnormalized chart using
\(F_{11},F_{12},F_{21}\) degenerates when \(F_{11}=0\). Formula (10)
has no such artificial singularity and holds for every \(q>1\).

## 3. An exact first-order endpoint-preserving insertion

Insert a label-1 factor \(1+\varepsilon\) after the first label-0 arc.
The seven-factor word is
\[
0,\ 1,\ 2,\ 1,\ 0,\ 2,\ 1.
\]
At \(\varepsilon=0\) the inserted factor is one and the trajectory is
the original six-piece trajectory.

Write the six old factors as
\[
x_j(\varepsilon)=q+d_j\varepsilon+O(\varepsilon^2).
\]
The following derivatives cancel the first variation of both endpoints:
\[
\begin{aligned}
d_0&=\frac{q^4(2q-1)}{4q-1},\\
d_1&=\frac{q(4q^4-5q^3-q^2+5q-1)}{4q-1},\\
d_2&=-\frac{q^2(3q^2-q+1)}{4q-1},\\
d_3&=-\frac{q^3(4q^2-q-2)}{4q-1},\\
d_4&=-\frac{2q^5}{4q-1},\qquad d_5=0.
\end{aligned}
\tag{13}
\]
The factor indices here refer to the original chronological word
021021; the inserted factor has its own derivative \(1\).

Here are explicit checks of the endpoint cancellation. Put
\[
G=T_0(q)T_2(q)T_1(q)
=\begin{pmatrix}
q^{-1}&q-q^{-1}\\
(1-q^2)q^{-3}&(2q^2-1)q^{-3}
\end{pmatrix}.
\]
Its three separate factor derivatives are
\[
A_0=
\begin{pmatrix}
q^{-2}&1-q^{-2}\\
(q^2-1)q^{-4}&(1-2q^2)q^{-4}
\end{pmatrix},
\]
\[
A_1=
\begin{pmatrix}
-q^{-2}&q^{-2}-1\\
-(q^2+1)q^{-4}&q^{-4}
\end{pmatrix},\qquad
A_2=
\begin{pmatrix}
-q^{-2}&1+q^{-2}\\
(q^2-1)q^{-4}&q^{-4}
\end{pmatrix}.
\]
If
\[
B=\begin{pmatrix}-1&2q^2\\0&1\end{pmatrix},
\]
the inserted factor contributes \(BG^2\) to the tangent-product
derivative. Substitution of (13) gives the \(2\times2\) identity
\[
(A_0d_0+A_1d_1+A_2d_2+BG)G
+G(A_0d_3+A_1d_4)=0.
\tag{14}
\]
Thus \(F'=0\).

For the state check, differentiate (6). The derivatives of the active
raw margins on the six original arcs are, in order,
\[
\left(
0,\
-\frac{2q(2q^3-q^2-4q+1)}{4q-1},\
\frac{2q^2(q-2)}{4q-1},\
\frac{4q^4}{4q-1},\
0,\
0
\right).
\tag{15}
\]
This follows by substituting (13) into
\[
b'_{\rm end}=(a'+b')x+(a+b)x'-a',\qquad
c'_{\rm end}=(a'+c')/x-(a+c)x'/x^2-a'.
\]
Immediately before the last original arc, both its active margin and
the preceding active margin have derivative zero by (15). The fixed
quadratic invariant forces the third derivative to be zero as well.
Since \(d_5=0\), all terminal state derivatives vanish.

Now apply the implicit function theorem to the five endpoint
coordinates (9), with the first five old factors as dependent variables,
the sixth fixed at \(q\), and \(\varepsilon\) as the free parameter.
The nonzero determinant (10) gives smooth functions \(x_0,\ldots,x_4\)
that preserve the endpoints **exactly**, not only to first order.
Their derivatives are precisely (13), because (14)–(15) give the
unique linear correction for this five-column Jacobian.

For sufficiently small \(\varepsilon>0\), all six old factors remain
greater than one and the new factor is greater than one. Every switching
state remains strictly positive by continuity. Formula (6) then gives
strict-star membership throughout each closed arc, because one margin
is constant and the other two vary monotonically. This constructs an
actual seven-piece integral trajectory with both original endpoint pairs.

## 4. Exact strict decrease of cost

All cost derivatives in this section are evaluated at \(\varepsilon=0\).
Write \(L=\log q\). On each original arc, the active margin is \(1\),
the increasing margin starts at \(1\), and the decreasing margin starts
at \(2q-1\).

Let \(a'\) be the active-margin derivative on one of those arcs and
\(d\) its factor derivative. Differentiating the fixed invariant gives
\[
c'=-q(a'+b').
\]
Substitution into (7) therefore gives
\[
J_i'=
\frac1{2(4q-1)}
\left[
\left(4q-3-q^{-1}-2L\right)a'
+\left(2+q^{-1}\right)d
\right].
\tag{16}
\]
The two sums needed from (13) and (15) are particularly simple:
\[
\sum_{j=0}^5d_j=-q(2q^2-1),\qquad
\sum_{j=0}^5a_j'=
\frac{2q(2q^2+2q-1)}{4q-1}.
\tag{17}
\]
The inserted arc has zero length at the base point. Its active raw margin
is \(2q-1\), its two other raw margins are \(1,1\), and its factor
derivative is \(1\). Its contribution to the first cost derivative is
\[
\frac{(2q-1)(2q+1)}{2(4q-1)}
=\frac{4q^2-1}{2(4q-1)}.
\tag{18}
\]
Adding (16)–(18) yields the exact derivative of the endpoint-corrected
seven-piece path:
\[
\boxed{
J'(0)=
-\frac{
2q(2q^2+2q-1)\log q-8q^3+9q^2-1
}{(4q-1)^2}.}
\tag{19}
\]

Its sign has an elementary uniform certificate. For \(q>1\),
\[
\log q>\frac{2(q-1)}{q+1},
\tag{20}
\]
because the difference vanishes at one and its derivative is
\((q-1)^2/[q(q+1)^2]>0\). Also,
\[
8q^3-9q^2+1=(q-1)(8q^2-q-1).
\]
Consequently the numerator in (19) is strictly greater than
\[
\begin{aligned}
(q-1)\left[
\frac{4q(2q^2+2q-1)}{q+1}-(8q^2-q-1)
\right]
&=\frac{(q-1)^3}{q+1}\\
&>0.
\end{aligned}
\]
Thus
\[
\boxed{
J'(0)<-\frac{(q-1)^3}{(q+1)(4q-1)^2}<0.}
\tag{21}
\]
The smooth exact endpoint correction therefore has smaller normalized,
and hence physical, cost for all sufficiently small positive
\(\varepsilon\). This proves the result stated at the start.

## 5. Limits and the boundary of the result

The improvement is pointwise in \(q>1\). It does not assert one positive
insertion size that works for every \(q\), nor a cost decrease bounded
away from zero over the whole family.

As \(q\downarrow1\), all six original factors collapse, the chosen
endpoint Jacobian determinant in (10) tends to zero quadratically, and
the cost derivative in (19) tends to zero cubically. More precisely,
the elementary logarithm expansion gives
\[
J_6(q)=3(q-1)+O((q-1)^2),\qquad
J'(0)=-\frac19(q-1)^3+O((q-1)^4).
\]
The theorem does not include the zero-duration point \(q=1\).

The subfamily contains geometrically eligible low-cost windows. Its cost
tends to zero by (8), and its physical state tends to the circle state.
For \(q\) sufficiently close to one, the whole frame path remains close
to the identity. The second sector determinants remain positive by
continuity from their initial value one. The first sector determinants
become positive immediately: the star condition gives a strictly positive
angular derivative for each contact curve, and closeness to its initial
ray prevents an extra turn. Thus the nonvacuity does not depend on ignoring
the sector restriction. The improvement itself does not need a sector
assumption, and its endpoint-preserving replacement need not separately
satisfy that restriction, as explained in BOUNDED_REDUCTION.

The equal-factor, cyclic-state assumptions are essential to the proof
presented here. For arbitrary L2 factors the endpoint Jacobian, correcting
direction, active-margin sums, and switching defect are different.
Neither their rank nor their signs are inferred from (10) or (21).
Singular ranks and boundary limits in the full eight-dimensional domain
remain part of the open problem.

This result also explains why one should not insist on a decreasing
same-word direction. In this family, insertion of the missing control is
a direct way to violate the necessary Hamiltonian maximizing condition.
The proof uses the explicit endpoint correction and cost calculation;
it does not assume a Pontryagin multiplier or a PMP classification.

## Sources and validation boundary

The constant-control update, tangent product, half-factor, and cost
conventions are the existing hand formulas in
[WORD_HOLONOMY.md](WORD_HOLONOMY.md) and
[BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md). Their pinned upstream source is
[SmoothedPolygons at 8ce7328](https://github.com/vltanh/lean4-smoothed-polygon/tree/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f);
the corresponding control system is developed in
[Hales–Vajjha, Chapter 7](https://arxiv.org/html/2405.04331v1#Ch7).

The rank reduction (11)–(12), exact correction (13)–(15), cost derivative
(16)–(19), and logarithmic inequality (20)–(21) provide the hand certificate.
An independent hand review rederived the four Schur-complement entries and
the inserted-factor column, checked the correcting vector against both
endpoint equations, and verified the cost sign and exact-IFT conclusion.
No numerical optimization, sampled signs, or symbolic zero-output premise
is used. No Lean compilation, Lake run, typechecking, CI, or kernel
validation is claimed.


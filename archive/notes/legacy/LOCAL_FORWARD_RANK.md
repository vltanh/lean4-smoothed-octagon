# Active margins and uniform endpoint rank for the local word 012012

Date: 2026-11-07. Hand proof, independently reviewed.

## Result and scope

This note proves two exact facts about the **entire positive strict-star
domain** of the local template L1 = 012012 in
[BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md):

1. Fixing the initial and terminal states leaves four active-margin
   variables, with an explicit nearest-neighbor formula for the cost.
2. The remaining frame endpoint map has rank three everywhere. Therefore
   the five original frame-and-state endpoint constraints have rank five,
   and each local endpoint fiber is a smooth one-dimensional manifold.

The rank theorem includes arbitrary initial state and all six unequal
positive factors. It has no additional cost, sector, equal-factor, or
Pontryagin hypothesis. In particular, no rank-zero or rank-one exceptions
remain for the reduced L1 endpoint map.

**No local cost exclusion is proved.** The exact eligible example in
[LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md) has a strict same-word local
minimum, so universal nearby same-word descent is false. The cost along
the endpoint fiber need not have the sign of the unconstrained Hessian.
The missing step is a different-word or nonlocal endpoint-preserving
improvement, or an additional restriction on actual minimizers. L1 remains open, and
the number of fully proved universal local inputs remains zero of five.
Nothing here compares a new closed-word family or bounds the total number
of pieces of a minimizer.

## 1. The active-margin coordinates resolve the state endpoints

Use the determinant-one physical margins of BOUNDED_REDUCTION:

\[
p_0p_1+p_1p_2+p_2p_0=4,\qquad p_j>0.
\]

Number the six arcs by \(i=0,\ldots,5\), with label \(i\pmod3\).
Let \(a_i\) be the active margin at the start of arc \(i\), and put
\(a_{-1}=p_2(0)\), \(a_0=p_0(0)\). After a forward switch, the old
active margin is the next decreasing margin. Thus the three initial
margins on arc \(i\), in active/growing/decreasing order, are

\[
(a_i,b_i,a_{i-1}),\qquad
b_i=\frac{4-a_{i-1}a_i}{a_{i-1}+a_i}.
\tag{1}
\]

For compact notation write

\[
s_i=a_i+a_{i+1},\qquad K_i=a_i^2+4.
\]

The growing-margin update gives
\(a_{i+1}=(a_i+b_i)q_i-a_i\). Since
\(a_i+b_i=K_i/s_{i-1}\), it follows that

\[
\boxed{q_i=\frac{s_{i-1}s_i}{K_i}
=\frac{(a_{i-1}+a_i)(a_i+a_{i+1})}{a_i^2+4}.}
\tag{2}
\]

The remaining margin after this update equals \(b_{i+1}\): indeed,

\[
\frac{a_i+a_{i-1}}{q_i}-a_i
=\frac{K_i}{a_i+a_{i+1}}-a_i
=\frac{4-a_ia_{i+1}}{a_i+a_{i+1}}.
\]

Consequently the exact positive strict-star domain in these coordinates is

\[
\begin{gathered}
a_{-1},a_0,\ldots,a_6>0,\\
a_{i-1}a_i<4\quad(0\le i\le6),\\
(a_{i-1}+a_i)(a_i+a_{i+1})>a_i^2+4
\quad(0\le i\le5).
\end{gathered}
\tag{3}
\]

The last line is precisely \(q_i>1\). Together with the adjacent-product
conditions it guarantees positive endpoint margins and hence strict-star
membership along every complete arc. Conversely every strict-star
012012 window supplies exactly this chain.

For fixed initial state, the map from \((q_0,\ldots,q_5)\) to
\((a_1,\ldots,a_6)\) is a smooth change of coordinates on its positive
domain. It is obtained successively from the growing-margin update;
the inverse (2) is smooth, and
\(\partial q_i/\partial a_{i+1}=s_{i-1}/K_i>0\).
There is no rank or branch assumption in this change of coordinates.

At the terminal time the label for the next arc is again zero. Therefore

\[
(p_0,p_1,p_2)_{\rm end}=(a_6,b_6,a_5).
\]

It follows that fixing both states is exactly the condition that
\(a_{-1},a_0,a_5,a_6\) are fixed. The only free active margins are
\(a_1,a_2,a_3,a_4\).

One optional bounded-angle description makes the inequalities particularly
simple. If \(\alpha_i=\arctan(a_i/2)\in(0,\pi/2)\), then (3) says

\[
\alpha_{i-1}+\alpha_i<\frac\pi2,
\qquad
\alpha_{i-1}+\alpha_i+\alpha_{i+1}>\frac\pi2.
\tag{4}
\]

For the second equivalence, divide (2) by the positive cosines and use

\[
\sin(\alpha_i+\alpha_{i-1})
\sin(\alpha_i+\alpha_{i+1})
-\cos\alpha_{i-1}\cos\alpha_{i+1}
=-\cos\alpha_i\cos(\alpha_{i-1}+\alpha_i+\alpha_{i+1}).
\]

The adjacent-sum inequalities keep the triple sum below \(\pi\), so
the stated cosine sign has no extra angular branch.

## 2. Exact cost as a nearest-neighbor action

Let \(J\) denote physical cost divided by \(\sqrt{12}\). The arc formula is

\[
8J_i=a_i\left[(a_i+b_i)(q_i-1)
 +(a_i+a_{i-1})(1-q_i^{-1})-a_i\log q_i\right].
\]

Using the two endpoint updates, this becomes

\[
8J_i=a_i(a_{i-1}+a_{i+1}-b_i-b_{i+1})-a_i^2\log q_i.
\tag{5}
\]

For every interior pair, the nonlogarithmic terms combine as

\[
2a_i a_{i+1}-(a_i+a_{i+1})b_{i+1}
=3a_i a_{i+1}-4.
\]

Also \(\log q_i=\log s_{i-1}+\log s_i-\log K_i\). Summing (5) therefore
gives

\[
\boxed{
8J=C_{\rm end}
 +\sum_{i=0}^{4}\left[3a_i a_{i+1}
 -(a_i^2+a_{i+1}^2)\log(a_i+a_{i+1})\right]
 +\sum_{i=1}^{4}a_i^2\log(a_i^2+4),}
\tag{6}
\]

where the fixed boundary term is

\[
\begin{aligned}
C_{\rm end}={}&-20+a_0(a_{-1}-b_0)+a_5(a_6-b_6)\\
&-a_0^2\log(a_{-1}+a_0)-a_5^2\log(a_5+a_6)\\
&+a_0^2\log K_0+a_5^2\log K_5.
\end{aligned}
\]

All terms in \(C_{\rm end}\) depend only on the two fixed states. No frame
endpoint condition has been used to obtain (6).

## 3. The remaining frame endpoint map

Use

\[
R=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\qquad
A(q)=T_0(q)R^{-1}=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix}.
\]

The relation \(T_i(q)=R^{-i}T_0(q)R^i\), and \(R^6=I\), give the exact
tangent endpoint

\[
\boxed{F=A(q_0)A(q_1)\cdots A(q_5).}
\tag{7}
\]

This is an arbitrary local endpoint. There is no condition \(F=R\).
Since both states are already fixed, preserving (7) preserves the actual
terminal frame by \(g_{\rm end}=X_0F X_{\rm end}^{-1}\).

Put \(P_i=A(q_0)\cdots A(q_{i-1})\), with \(P_0=I\), and
\(E=\operatorname{diag}(1,-1)\). The right-trivialized derivative with
respect to \(\log q_i\) is \(Z_i=P_iEP_i^{-1}\).
For an interior active margin \(a_i\), define

\[
V_i=\frac{\partial F}{\partial a_i}F^{-1},\qquad 1\le i\le4.
\]

Differentiating (2) gives

\[
V_i=\frac{Z_{i-1}+Z_i}{s_{i-1}}
 +\frac{Z_i+Z_{i+1}}{s_i}-\frac{2a_i}{K_i}Z_i.
\]

The two elementary identities

\[
A(q)^{-1}EA(q)+E=\begin{pmatrix}0&0\\-2&0\end{pmatrix},\qquad
E+A(q)EA(q)^{-1}=\begin{pmatrix}0&2q^2\\0&0\end{pmatrix}
\]

therefore yield the explicit formula

\[
\boxed{
V_i=P_i\,2\begin{pmatrix}
-a_i/K_i&q_i^2/s_i\\
-1/s_{i-1}&a_i/K_i
\end{pmatrix}P_i^{-1}.}
\tag{8}
\]

In particular

\[
\det V_i=
\frac{4(s_{i-1}s_i-a_i^2)}{K_i^2}>\frac{16}{K_i^2}>0.
\tag{9}
\]

The individual columns are nonzero elliptic matrices. The next section
proves the stronger assertion that three consecutive columns are always
linearly independent.

## 4. A sign certificate for every consecutive triple

For a trace-zero matrix, use coordinates \((M_{11},M_{12},M_{21})\), and
write \(\det(U,V,W)\) for the determinant of three such column vectors.
Conjugation preserves this determinant: its determinant on the full
matrix algebra is one, it fixes the scalar line, and it preserves the
trace-zero complement.

Consider any consecutive five active margins

\[
(x,a,b,c,d).
\]

They supply three consecutive frame-gradient columns. Set

\[
K=b^2+4,\quad K_a=a^2+4,\quad K_c=c^2+4,\quad
s=a+b,\quad t=b+c,\quad q=\frac{st}{K}>1.
\tag{10}
\]

Strict star implies \(ab<4\), \(bc<4\). The first and third factors
being greater than one imply

\[
x>x_0:=\frac{4-ab}{a+b},\qquad
d>d_0:=\frac{4-bc}{b+c}.
\tag{11}
\]

Conjugate all three columns by the inverse prefix immediately before the
middle arc. Formula (8) then gives the three columns, in order, as

\[
\frac2{K_a}(U_0+\lambda N_L),\qquad
\frac2K U_1,\qquad
\frac2{K_c}(U_2+\mu N_R),
\tag{12}
\]
where

\[
\begin{aligned}
U_0&=(-b,s,-K/s),\\
U_1&=(-b,sq,-K/s),\\
U_2&=(-b,sq,-K/(sq)),\\
N_L&=(-1,1,-1),\\
N_R&=(-1,q^2,-q^{-2}),
\end{aligned}
\qquad
\lambda=\frac{(x-x_0)s^2}{K_a}>0,\quad
\mu=\frac{(d-d_0)t^2}{K_c}>0.
\tag{13}
\]

These formulas can be checked without a large determinant expansion.
For the first column, conjugating the local matrix in (8) by the inverse
first transfer gives, after division by two,

\[
\begin{pmatrix}
a/K_a-z&z\\
2a/K_a-1/s-z&-a/K_a+z
\end{pmatrix},\qquad z=\frac{(x+a)s^2}{K_a^2}.
\]

At \(x=x_0\), this is \(U_0/K_a\), and its change is exactly
\(\lambda N_L/K_a\). For the third column, before conjugation the only
entry depending on \(d\) is the upper-right entry
\(t^2(c+d)/K_c^2\). The conjugate of its matrix unit is

\[
A(q)\begin{pmatrix}0&1\\0&0\end{pmatrix}A(q)^{-1}
=\begin{pmatrix}-1&q^2\\-q^{-2}&1\end{pmatrix}.
\]

At \(d=d_0\) the conjugated column is \(U_2/K_c\), giving (12).
The middle column follows directly from \(q=st/K\).

By multilinearity, the determinant in (12), after multiplication by the
positive factor \(K_a K K_c/8\), is

\[
d_{00}+\lambda d_{10}+\mu d_{01}+\lambda\mu d_{11},
\tag{14}
\]
with the following four small determinants:

\[
\begin{aligned}
d_{00}&=\det(U_0,U_1,U_2)
       =-\frac{bK(q-1)^2}{q},\\
d_{10}&=\det(N_L,U_1,U_2)
       =\frac{K(q-1)}{sq}(b-sq),\\
d_{01}&=\det(U_0,U_1,N_R)
       =\frac{s(q-1)}{q^2}(b-tq),\\
d_{11}&=\det(N_L,U_1,N_R)
       =\frac{q^2-1}{q^2}\bigl[b(q^2+1)-q(s+t)\bigr].
\end{aligned}
\tag{15}
\]

For example, subtracting the first column from the second, then the
second from the third, immediately gives \(d_{00}\). The same subtractions
give \(d_{10}\) and \(d_{01}\). Expanding the last determinant and using
\(K/s=t/q\) gives its displayed expression.

All four numbers are strictly negative. This is immediate for the first
three, since \(s,t>b\) and \(q>1\). For the fourth, the two adjacent
strict-star inequalities give

\[
bq=\frac{bst}{b^2+4}<s,\qquad bq<t.
\]

Consequently

\[
b(q^2+1)-q(s+t)
<b(q^2+1)-2bq^2=b(1-q^2)<0.
\]

Equations (14)–(15) prove the full-domain sign theorem

\[
\boxed{\det(V_i,V_{i+1},V_{i+2})<0.}
\tag{16}
\]

For the four free L1 margins, both triples \((V_1,V_2,V_3)\) and
\((V_2,V_3,V_4)\) are therefore independent. The frame endpoint map has
rank three everywhere. Combined with the globally resolved state
coordinates in Section 1, the original five endpoint constraints have
rank five throughout the full positive L1 domain.

This is a rank statement at every interior input, not a positive uniform
lower bound for a Jacobian singular value. The displayed determinants may
approach zero as factors collapse or star margins degenerate at the boundary.
No boundary rank or uniform conditioning estimate is asserted.

The implicit function theorem now gives an exact local one-dimensional
endpoint fiber at every input. A nonzero kernel vector can be chosen as

\[
v=(-\det(V_2,V_3,V_4),\ \det(V_1,V_3,V_4),
   -\det(V_1,V_2,V_4),\ \det(V_1,V_2,V_3)).
\tag{17}
\]

In this orientation \(v_1>0\) and \(v_4<0\). No sign for the middle two
components is asserted. In particular, either end active margin is a
valid local coordinate on the endpoint fiber, and the two end active
margins vary in opposite directions.

## 5. Cost derivatives and the constrained second variation

The action (6) has a tridiagonal ambient Hessian. Its neighboring
off-diagonal entries, before division by eight, are

\[
8J_{a_i a_{i+1}}
=1+\frac{a_i^2+a_{i+1}^2}{(a_i+a_{i+1})^2}>0.
\tag{18}
\]

For \(1\le i\le4\), its diagonal entries are

\[
\begin{aligned}
8J_{a_i a_i}={}&-2\log q_i
 +\frac{10a_i^2}{K_i}-\frac{4a_i^4}{K_i^2}\\
&-4a_i\left(\frac1{s_{i-1}}+\frac1{s_i}\right)
 +\frac{a_{i-1}^2+a_i^2}{s_{i-1}^2}
 +\frac{a_i^2+a_{i+1}^2}{s_i^2}.
\end{aligned}
\tag{19}
\]

For completeness, the corresponding gradient is

\[
4J_{a_i}=a_{i-1}+a_i+a_{i+1}
 -a_i^2\left(\frac1{s_{i-1}}+\frac1{s_i}\right)
 +\frac{a_i^3}{K_i}-a_i\log q_i.
\tag{20}
\]

These follow by differentiating the two neighboring summands of (6).
They are ambient derivatives, **not** the second derivative after the
frame endpoint is fixed.

There is an exact formula for the required correction. At a stationary
point of the endpoint fiber, rank three gives a unique linear functional
\(\lambda\) on the trace-zero matrices such that

\[
J_{a_i}=\lambda(V_i),\qquad 1\le i\le4.
\tag{21}
\]

For a tangent vector \(v\) satisfying \(\sum_i v_i V_i=0\), extend
\(v_{-1}=v_0=v_5=v_6=0\), and set

\[
\begin{aligned}
z_j&=\frac{v_{j-1}+v_j}{s_{j-1}}
 +\frac{v_j+v_{j+1}}{s_j}-\frac{2a_jv_j}{K_j},\\
w_j&=-\frac{(v_{j-1}+v_j)^2}{s_{j-1}^2}
 -\frac{(v_j+v_{j+1})^2}{s_j^2}
 +\frac{2(a_j^2-4)v_j^2}{K_j^2},\qquad 0\le j\le5.
\end{aligned}
\tag{22}
\]

Along the straight active-margin variation, these are the first and
second derivatives of \(\log q_j\). The second right-trivialized frame
variation, evaluated on an endpoint-tangent direction, is

\[
\mathcal K(v)=\sum_{j=0}^5 w_j Z_j
 +\sum_{0\le m<j\le5}z_mz_j[Z_m,Z_j].
\tag{23}
\]

Indeed, the first right-trivialized frame variation is
\(\sum_j z_jZ_j\), and
\(Z_j'=[\sum_{m<j}z_mZ_m,Z_j]\). Its square term in
\(F''F^{-1}\) vanishes at an endpoint-tangent direction.
The exact constrained second derivative is therefore

\[
\boxed{v^{\mathsf T}(\operatorname{Hess}J)v
       -\lambda(\mathcal K(v)).}
\tag{24}
\]

A negative value in (24), or a nonzero first variation away from a
stationary point, produces a cheaper exact same-word local replacement
by the already-proved rank theorem. However, a universal negative sign
at stationary points is false: LOCAL_FORWARD_SIX supplies a strictly
positive constrained second variation on an eligible stationary fiber.
Neither ellipticity (9), the signs in (16), nor the positive neighboring
entries (18) justify dropping the correction term in (24).

The rank theorem eliminates interior rank exceptions from L1, not its
stationary minima. Further work must allow different-word or nonlocal
replacements, or use necessary conditions for windows in actual global
minimizers. Repeating a universal negative-Hessian search would contradict
the exact obstruction already proved.

## Validation boundary

The state recursion, cost, and tangent conventions are the hand formulas
in [WORD_HOLONOMY.md](WORD_HOLONOMY.md) and BOUNDED_REDUCTION. The coordinate
inversion, action telescoping, and four small determinant calculations
above supply a complete hand proof of the new rank result. No expanded
symbolic polynomial, floating-point sign, optimization output, or numerical
sample is a proof premise. Two independent hand reviews rederived the
coordinate inverse, cost telescoping, four determinant identities and
strict signs, and the constrained second-variation correction; neither
found a material issue. No Lean, Lake, typecheck, CI, or kernel validation
was performed. The universal L1 improvement remains an open analytic input.

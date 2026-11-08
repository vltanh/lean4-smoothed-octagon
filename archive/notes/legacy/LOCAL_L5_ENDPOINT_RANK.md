# Endpoint rank for the prefix 02101 and the full L5 window

Date: 2026-11-07. Hand proof on the entire positive strict-star domain.

## Theorem and scope

Fix the initial frame and determinant-one strict-star state. For the
positive five-piece word \(\mathtt{02101}\), the map from its five
logarithmic factors to the full terminal frame and state has rank five.
Consequently the six-piece L5 word \(\mathtt{021012}\) has full endpoint
rank five everywhere on its positive strict-star domain: its first five
factor columns already suffice.

There is no symmetry, cost, sector, stationarity, or PMP assumption.
The proof does not require the six-dimensional paired-product
determinant to be nonzero. It proves that a particular five-dimensional
paired image is transverse to the one-dimensional state stabilizer.

This removes abnormal lifts and normalized-multiplier ambiguity for
free-time minimizing L5 windows. It does not prove a cost improvement,
close L5, or repair the refuted original L3 replacement target.

## 1. Paired products and the actual endpoint quotient

Use the triangular generators

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix}.
\]

For logarithmic factor \(s=\log q\), put

\[
T_i(q)=e^{-sD_i},\qquad
\overline Q_i(q)=e^{sD_i/2}.
\]

For a word \(i_1,\ldots,i_m\), define

\[
F=T_{i_1}(q_1)\cdots T_{i_m}(q_m),\qquad
G=\overline Q_{i_1}(q_1)^{-1}\cdots
  \overline Q_{i_m}(q_m)^{-1}.
\]

Left-normalize the fixed initial frame to \(I\), using one fixed
invertible linear map; this does not change endpoint rank or \(X_0\).
At that fixed initial state,

\[
X_e=G^{-1}X_0G,\qquad
g_e=X_0FX_e^{-1}.                                        \tag{1}
\]

Thus preserving \((F,X_e)\) preserves the actual full endpoint, and
the change between these endpoint coordinates is a smooth
diffeomorphism at fixed \(X_0\).

If \(F_k,G_k\) are the products before factor \(k\), the paired
differential in the coordinates \((\delta F F^{-1},\delta G G^{-1})\)
has logarithmic-factor columns

\[
\left(-\operatorname{Ad}_{F_k}D_{i_k},
      -\tfrac12\operatorname{Ad}_{G_k}D_{i_k}\right).        \tag{2}
\]

The differential of the actual state projection is

\[
\delta X_e=G^{-1}[X_0,\delta G G^{-1}]G.
\]

Its kernel in the paired six-dimensional tangent space is

\[
\mathcal K=\{(0,tX_0):t\in\mathbb R\}.                     \tag{3}
\]

Indeed, the trace-zero centralizer of the elliptic matrix \(X_0\),
with \(X_0^2=-I\), is \(\mathbb R X_0\). For an elementary verification,
choose any nonzero vector \(v\). The vectors \(v,X_0v\) are independent.
A commuting matrix is determined by its value on \(v\), so it is a
linear combination of \(I,X_0\); trace zero removes its \(I\) component.

A five-dimensional paired image therefore gives actual endpoint rank
five if and only if it does not contain the line (3).

## 2. Remove only fixed block conjugations

Consider the first five labels \(0,2,1,0,1\), and write

\[
a=q_2,\qquad b=q_3,\qquad c=q_4.
\]

All three exceed one. The first factor may be arbitrary and positive;
the fifth factor does not enter the prefixes in (2).

At the chosen baseline, conjugate the top and bottom blocks in (2)
by the inverses of their first-factor matrices. These are **fixed
linear changes of tangent coordinates** for the rank calculation,
not parameter-dependent normalizations being differentiated.
Since \(D_0\) commutes with the two first-factor matrices, this has
the same effect on every column as setting the first factor to one.

In the lower block, the stabilizer line (3) becomes

\[
\{(0,tY):t\in\mathbb R\},\qquad
Y=\overline Q_0(q_1)X_0\overline Q_0(q_1)^{-1}.             \tag{4}
\]

Crucially, \(Y\) is the actual state **after the first arc**, so it is
strict star. It need not equal the initial state.

Remove the minus signs and the factor \(1/2\) in (2) by an invertible
block scaling, and call the resulting six-by-five matrix \(M\).
These scalar changes preserve the stabilizer line as a line.

For checking lower-block conjugations without square roots, use

\[
S_i(q)=\frac{(q+1)I-(q-1)D_i}{2}
      =\sqrt q\,\overline Q_i(q)^{-1}.
\]

The scalar \(\sqrt q\) has no effect on conjugation. Explicitly,

\[
S_0(q)=\begin{pmatrix}q&0\\0&1\end{pmatrix},\quad
S_1(q)=\begin{pmatrix}1&q-1\\0&q\end{pmatrix},\quad
S_2(q)=\begin{pmatrix}1&0\\1-q&q\end{pmatrix}.              \tag{5}
\]

We identify a trace-zero matrix with \((x,y,z)=(M_{00},M_{01},M_{10})\).

## 3. A three-column pivot and its exact elimination map

The top three columns of \(M\) are

\[
D_0=(-1,0,0),\qquad D_2=(1,0,2),\qquad
\operatorname{Ad}_{T_2(a)}D_1
=\left(\frac2{a^2}-1,-\frac2{a^2},\frac2{a^2}-2\right).
\]

Their determinant is

\[
-\frac4{a^2}\ne0.                                        \tag{6}
\]

The corresponding lower columns replace \(a^2\) by \(a\) in the
third vector and keep the first two vectors unchanged. The unique
linear map carrying these three top columns to the lower ones is

\[
\boxed{\mathcal L_a(x,y,z)=
 \bigl(x-(a-1)y,\ ay,\ z-(a-1)y\bigr).}                   \tag{7}
\]

This is checked by substitution into the three displayed vectors.

Subtract \(\mathcal L_a\) of the upper block from the lower block.
The first three lower columns become zero. Let \(u,v\) denote the
remaining two lower columns.

For a compact expression put

\[
A_0=a^2+a-1,\qquad
P=A_0-(a-1)b,\qquad
Q=(c+1)A_0-(a-1)b.
\]

Then

\[
\boxed{\begin{aligned}
u&=-\frac2{ab^2}
 \begin{pmatrix}
 (a-1)(b-1)\\ b-1\\ (a-1)P
 \end{pmatrix},\\[3pt]
v&=-\frac{2(c-1)}{ab^2}
 \begin{pmatrix}
 (a-1)(b-c-1)\\ b-c-1\\ (a-1)Q
 \end{pmatrix}.
\end{aligned}}                                           \tag{8}
\]

These two finite identities have a short direct matrix recipe. The
upper fourth and fifth columns before elimination are

\[
\operatorname{Ad}_{T_2(a)T_1(b)}D_0,\qquad
\operatorname{Ad}_{T_2(a)T_1(b)T_0(c)}D_1,
\]

and the lower columns replace the \(T_i\) by the \(S_i\) of (5).
Use

\[
T_2(a)=\begin{pmatrix}a^{-1}&0\\a^{-1}-a&a\end{pmatrix},
\quad
T_1(b)=\begin{pmatrix}b^{-1}&b-b^{-1}\\0&b\end{pmatrix},
\quad
T_0(c)=\operatorname{diag}(c,c^{-1}),
\]

multiply these two-by-two matrices, and subtract (7). Collection of
the three coordinates gives (8). No large determinant or generic
nonvanishing assertion is needed.

## 4. Two independent residual columns

The first coordinate of each vector in (8) is \(a-1\) times its
second. The second/third coordinate minor, however, is strictly positive.
Its simplification rests on the elementary identity

\[
\begin{aligned}
(b-1)Q-(b-c-1)P
&=\bigl((b-1)(c+1)-(b-c-1)\bigr)A_0\\
&\quad +(a-1)b\bigl((b-c-1)-(b-1)\bigr)\\
&=bc\bigl(A_0-(a-1)\bigr)=a^2bc.
\end{aligned}
\]

Consequently

\[
\boxed{\det
 \begin{pmatrix}u_2&v_2\\u_3&v_3\end{pmatrix}
=\frac{4c(a-1)(c-1)}{b^3}>0,}                             \tag{9}
\]

where the subscripts \(2,3\) refer to the second and third entries of
these three-vectors. The residual columns are independent. Together
with (6), this proves that \(M\) has rank five.

The unique annihilator direction of their lower plane is

\[
n(x,y,z)=x-(a-1)y.                                       \tag{10}
\]

After the row elimination, a full annihilating functional is simply
\(n\) on the lower block. Before elimination it is
\(n(\text{lower}-\mathcal L_a(\text{upper}))\).
Its upper part will not be needed, because the stabilizer vectors
have zero upper block.

## 5. Strict star makes the stabilizer transverse

For the actual state \(Y\) after the first arc, write its positive
triangular margins as \((p_0,p_1,p_2)\). Then

\[
Y=\frac12
\begin{pmatrix}-p_0&p_0+p_2\\-p_0-p_1&p_0\end{pmatrix},
\qquad p_j>0.
\]

Its evaluation under (10) is

\[
\boxed{n(Y)=
-\frac12\left[p_0+(a-1)(p_0+p_2)\right]<0.}                \tag{11}
\]

Thus no nonzero vector of the line (4) belongs to the paired
five-dimensional image. The passage from paired products to the
actual endpoint loses no rank on that image. By (1), the five-piece
full frame/state endpoint map has rank five.

This argument uses the state after the first arc, not an untransformed
initial state in a new basis. It is valid because the input trajectory
is strict star at that junction. No later-state equality or special
shape is assumed.

For the full L5 word \(\mathtt{021012}\), the paired differential's
first five columns are identical: a column depends only on its prefix,
not on later factors. The kernel description (3) is also unchanged.
Therefore those same five columns have independent images in the
actual endpoint tangent space for every allowed sixth factor. The
six-variable L5 endpoint map has rank five throughout its positive
strict-star domain.

## 6. Consequences and limits

For L5 the endpoint fiber is locally a smooth one-dimensional manifold,
and a compensated variation can use five independent old factors
everywhere in the positive domain. The rank statement gives no uniform
conditioning as factors collapse or star margins degenerate.

If a positive L5 window belongs to a free-time Pontryagin extremal,
the six-duration first-variation identity is

\[
\lambda_0\,dJ=\lambda_e\circ d\mathcal E,
\]

on the actual five-dimensional endpoint manifold. Logarithmic factors
and physical durations are smoothly equivalent, with positive
triangular diagonal, so the proved rank applies to this identity.

If \(\lambda_0=0\), surjectivity forces \(\lambda_e=0\); the adjoint
then vanishes, violating nontriviality. A minimizing L5 window is
therefore normal. After normalizing \(\lambda_0=1\), surjectivity
makes the endpoint covector unique, and the adjoint equation makes its
whole normalized lift unique.

Accordingly full-control Hamiltonian inequalities and genuine external
switch ties must hold for that one multiplier. An abnormal or alternate
normal lift cannot repair a failed test. This is a necessary-condition
result, not a full-domain cost comparison or proof of local descent.

The analogous L2 word is not covered by this particular annihilator
calculation. No assertion about its full-domain rank is inferred from
the L5 result.

## Dependencies and validation boundary

The paired-product derivative and stabilizer quotient are the exact
endpoint formulas of
[LOCAL_SIX_VARIATION.md](LOCAL_SIX_VARIATION.md), Section 1.
Equations (5)–(11) supply the finite hand elimination and sign proof.

An exact symbolic calculation helped identify the two residual columns.
The proof uses their displayed two-by-two matrix derivation, the short
identity leading to (9), and the strict-star sign (11); no symbolic-zero
output, sampled sign, or optimizer is a proof premise. No Lean, Lake,
typecheck, or CI command was run.

Two independent hand reviews checked the finite conjugations, pivot,
residual minor, transformed stabilizer state, strict-star sign, and
the passage from the five-piece prefix to the full six-piece endpoint.
No material issue was found.


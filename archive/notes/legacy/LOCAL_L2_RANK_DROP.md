# An exact rank-four point for the full L2 endpoint map

Date: 2026-11-07. Hand certificate at one fixed positive strict-star
input. This point is **above the competitive cost sublevel**.

## Result and scope

The six-piece word \(\mathtt{021021}\) has positive factors and a fixed
determinant-one strict-star initial state at which its **actual full
frame-and-state endpoint differential has rank exactly four**.

This is not merely a zero paired-product determinant or a deficient
five-piece prefix. Section 3 proves paired rank five, and Section 4
proves that its image contains the actual one-dimensional state
stabilizer, causing exactly one further rank loss.

All six whole arcs are strict star. However, Section 5 proves that
this input's physical cost exceeds \(\pi\). It therefore lies outside
the minimizer-eligible sublevel \(C\le A_{\rm oct}<\pi\). It does not
show a rank drop in the competitive L2 domain, an abnormal minimizing
trajectory, a cost obstruction there, or a counterexample to Reinhardt.

The certificate rules out an everywhere-rank-five theorem on the full
positive strict-star L2 domain. The corresponding theorem for the
cost-restricted domain remains unsettled.

## 1. Exact fixed input and all seven states

Let

\[
\kappa=\sqrt{\frac{200}{253}},\qquad
d=\frac{1597}{247}.
\]

Use the fixed initial physical margins

\[
p^{(0)}=\kappa
\left(\frac{197}{300},\frac{11893}{3300},\frac{3793}{6000}\right),
\]

initial frame \(g(0)=I\), and the six factors

\[
\boxed{\quad
(q_1,\ldots,q_6)
=\left(\frac{11}{10},\,3,\,2,\,3,\,d,\,\frac{11}{10}\right),
\qquad i=(0,2,1,0,2,1).
\quad}                                                    \tag{1}
\]

The initial state is held fixed when any factor is differentiated.

Write \(P=p/\kappa\) for the raw margins and put

\[
A=\frac{3221}{494},\qquad B=\frac{2443}{3194}.
\]

The exact states are:

| After piece | Raw margins \((P_0,P_1,P_2)\) |
|---|---|
| Before all pieces | \(\left(197/300,\ 11893/3300,\ 3793/6000\right)\) |
| \(0\), factor \(11/10\) | \(\left(197/300,\ 403/100,\ 103/200\right)\) |
| \(2\), factor \(3\) | \(\left(3,\ 1,\ 103/200\right)\) |
| \(1\), factor \(2\) | \(\left(1,\ 1,\ 203/100\right)\) |
| \(0\), factor \(3\) | \(\left(1,\ 5,\ 1/100\right)\) |
| \(2\), factor \(d\) | \(\left(A,\ B,\ 1/100\right)\) |
| \(1\), factor \(11/10\) | \(\left((10A-B)/11,\ B,\ B/10+11/1000\right)\) |

Each row follows from the exact active/growing/decreasing update

\[
(a,b,c)\longmapsto
\bigl(a,(a+b)q-a,(a+c)/q-a\bigr).                          \tag{2}
\]

For example, at the fifth piece,

\[
P_0=\frac{101d-1}{100}=\frac{3221}{494},\qquad
P_1=\frac{501-d}{100d}=\frac{2443}{3194}.
\]

All entries are positive. In the final row,
\(A>6\) and \(0<B<1\), so \(10A-B>0\) without an approximation.

The invariant is particularly simple at the state after the fourth
piece:

\[
P_0P_1+P_1P_2+P_2P_0=5+\frac5{100}+\frac1{100}
=\frac{253}{50}.
\]

The update preserves this invariant, and
\(\kappa^2(253/50)=4\). Thus the physical initial state has exactly
the required determinant-one normalization.

Every factor in (1) exceeds one. Along a vertex arc its active margin
is constant, the growing margin increases, and the decreasing margin
decreases. Positivity of both endpoint rows therefore proves positivity
throughout every entire arc. All physical durations are strictly
positive.

## 2. The actual endpoint quotient

Use the triangular \(D_i,T_i,\overline Q_i\) conventions of
[LOCAL_SIX_VARIATION.md](LOCAL_SIX_VARIATION.md), Section 1:

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]
\[
T_i(e^s)=e^{-sD_i},\qquad
\overline Q_i(e^s)=e^{sD_i/2},
\]
\[
F=\prod_{j=1}^6T_{i_j}(q_j),\qquad
G=\prod_{j=1}^6\overline Q_{i_j}(q_j)^{-1}.
\]

With \(X_0\) fixed,

\[
X_e=G^{-1}X_0G,\qquad g_e=X_0FX_e^{-1}.                    \tag{3}
\]

For products \(F_j,G_j\) before factor \(j\), the paired differential
columns in logarithmic factors are

\[
\left(-\operatorname{Ad}_{F_j}D_{i_j},
      -\tfrac12\operatorname{Ad}_{G_j}D_{i_j}\right).
\]

The kernel of the actual endpoint projection from paired tangent space
is the line

\[
\{(0,tX_0):t\in\mathbb R\}.                               \tag{4}
\]

This follows from
\(\delta X_e=G^{-1}[X_0,\delta G G^{-1}]G\) and the
one-dimensional trace-zero centralizer of an elliptic \(X_0\).

At the fixed input (1), remove the first-factor block conjugations and
the harmless block signs and factor \(1/2\), as in
[LOCAL_L5_ENDPOINT_RANK.md](LOCAL_L5_ENDPOINT_RANK.md).
These are fixed linear coordinate changes at the point under study.
The resulting paired columns have the same expression as when the
first factor is one.

Under this change, (4) becomes

\[
\{(0,tY):t\in\mathbb R\},
\]

where \(Y\) is the **actual state after the first arc**, with physical
margins

\[
\kappa\left(\frac{197}{300},\frac{403}{100},\frac{103}{200}\right).
                                                               \tag{5}
\]

It is essential to transform this stabilizer state together with the
paired columns.

## 3. A complete paired-rank certificate

Represent a trace-zero matrix by its entries
\((x,y,z)=(M_{00},M_{01},M_{10})\).

The first three upper columns, for the labels \(0,2,1\), are

\[
(-1,0,0),\quad (1,0,2),\quad
\left(-\frac79,-\frac29,-\frac{16}{9}\right),
\]

with determinant \(-4/9\). The linear map taking them to the first
three lower columns is

\[
\mathcal L_3(x,y,z)=(x-2y,3y,z-2y).                       \tag{6}
\]

Subtract (6) of the upper block from the lower block, and eliminate
the upper entries of the final three columns using the first three
pivots. The remaining three lower columns are

\[
u=\begin{pmatrix}-1/3\\-1/6\\-7/3\end{pmatrix},\qquad
v=-\frac43u,
\]
\[
w=-\frac2{9d^2}
\begin{pmatrix}
2(d^2+2d-6)\\
d^2+8d-12\\
2(7d^2-d+54)
\end{pmatrix}.                                           \tag{7}
\]

Here is an explicit two-by-two recipe for these identities. Before
columns \(4,5,6\), the upper prefix matrices are respectively

\[
M=\begin{pmatrix}1/6&1/2\\-4/3&2\end{pmatrix},\qquad
N=\begin{pmatrix}1/2&1/6\\-4&2/3\end{pmatrix},
\]
\[
P=\begin{pmatrix}
(4-d^2)/(6d)&d/6\\
-(10+2d^2)/(3d)&2d/3
\end{pmatrix}.
\]

The corresponding lower prefix matrices can be taken, up to irrelevant
nonzero scalar multiples, as

\[
M_h=\begin{pmatrix}1&1\\-2&4\end{pmatrix},\qquad
N_h=\begin{pmatrix}3&1\\-6&4\end{pmatrix},\qquad
P_h=\begin{pmatrix}4-d&d\\-2-4d&4d\end{pmatrix}.
\]

Conjugate \(D_0,D_2,D_1\), respectively, by these three prefix pairs,
and subtract \(\mathcal L_3\) of the upper conjugate from the lower
one. This gives (7) using only ordinary two-by-two multiplication.
For example the fourth upper and lower conjugates have coordinates

\[
(1/3,1/6,16/3),\qquad (-1/3,1/3,8/3);
\]
their difference after (6) is exactly \(u\).

The first two coordinate rows of \(u,w\) have minor

\[
\det\begin{pmatrix}u_1&w_1\\u_2&w_2\end{pmatrix}
=\frac{4(d-1)}{9d^2}>0.                                  \tag{8}
\]

Thus the three residual columns have rank exactly two. Together with
the first three pivots, the full paired differential has rank exactly
five.

A convenient annihilator of the residual plane is

\[
n(x,y,z)=(46-19d)x+(10d-64)y+(2d-2)z.                    \tag{9}
\]

It annihilates \(u,v\) by direct substitution. For \(w\), the required
polynomial identity is

\[
\begin{aligned}
&2(46-19d)(d^2+2d-6)
 +(10d-64)(d^2+8d-12)\\
&\qquad+4(d-1)(7d^2-d+54)=0.
\end{aligned}
\]

The cubic, quadratic, linear, and constant coefficients each cancel.
Hence before the block elimination the full annihilator is
\(n(\mathrm{lower}-\mathcal L_3(\mathrm{upper}))\).

## 4. The actual rank is four

For physical margins \(\kappa(x_0,x_1,x_2)\), the state matrix is

\[
Y=\frac\kappa2
\begin{pmatrix}-x_0&x_0+x_2\\-x_0-x_1&x_0\end{pmatrix}.
\]

Using the actual after-first-arc values in (5), equation (9) gives

\[
\begin{aligned}
n(Y)
&=\frac\kappa2\left[
 27(d-4)\frac{197}{300}
 -2(d-1)\frac{403}{100}
 +(10d-64)\frac{103}{200}\right]\\
&=\frac{3\kappa}{100}(247d-1597)=0.                       \tag{10}
\end{aligned}
\]

The last equality is the exact chosen value \(d=1597/247\), not a
numerical root.

The paired image has dimension five, hence is exactly the kernel of
its nonzero annihilator. Equation (10) says that the transformed
stabilizer vector \((0,Y)\) lies in this image. It is nonzero. The
state projection has precisely the one-dimensional kernel (4), so its
restriction to this image loses exactly one dimension:

\[
\boxed{\operatorname{rank}d(F,X_e)=5-1=4.}                \tag{11}
\]

By the endpoint diffeomorphism (3), this is the rank of the actual
\((g_e,X_e)\) map. Positive factors, logarithmic factors, and physical
durations are related by smooth local diffeomorphisms, so (11) does not
depend on that choice of input coordinates.

This is a rank statement at the one displayed input. It does not claim
that its singular endpoint fiber is a smooth two-dimensional manifold.

## 5. The exact point is cost-ineligible

The point disproves an unrestricted strict-star rank-five assertion.
It does **not** disprove such an assertion under the minimizer's
competitive cost constraint.

Indeed,

\[
\kappa>\frac89,
\]

because \(200/253>64/81\), with cross-product difference
\(16200-16192=8>0\). The elementary series
\(2\operatorname{artanh}z=2\sum_{m\ge0}z^{2m+1}/(2m+1)\)
gives the strict bounds

\[
\log(11/10)>\frac2{21},\qquad
\log3>\frac{13}{12},\qquad
\log2>\frac23.
\]

For \(\log3\), retain its first two terms at \(z=1/2\);
for the other two bounds retain the first positive term.

The first four physical durations alone sum to

\[
T_4=\frac\kappa2
 \left[\frac{197}{300}\log(11/10)
       +\frac{303}{200}\log3+\log2\right].
\]

Therefore

\[
\begin{aligned}
T_4
&>\frac49\left(\frac{197}{3150}
                 +\frac{1313}{800}+\frac23\right)\\
&=\frac{119471}{113400}
 >\frac{22}{21}.
\end{aligned}                                             \tag{12}
\]

The final rational comparison has numerator gap \(671\) over
denominator \(113400\).

For determinant-one strict-star margins,
\((p_0+p_1+p_2)^2\ge3(p_0p_1+p_1p_2+p_2p_0)=12\).
The physical running cost is
\(\frac{\sqrt3}{2}(p_0+p_1+p_2)\), and is consequently at least three.
Thus the full trajectory satisfies

\[
C\ge3T>3T_4>\frac{22}{7}>\pi>A_{\rm oct}.                 \tag{13}
\]

For a self-contained strict comparison \(\pi<22/7\), one may use

\[
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=\frac{22}{7}-\pi.
\]

Hence this point cannot itself belong to the competitive L2 domain.
No sector eligibility is asserted or needed for this rank certificate.

## Interpretation and validation boundary

The L1, L3, L4, and L5 full-domain rank arguments cannot simply be
extended by asserting the same conclusion for every positive L2 input:
(11) is an exact exception. A theorem restricted to the competitive
L2 sublevel would require a separate argument that this certificate
does not settle.

The proof displays the fixed initial state, all positive factors,
every switching state, the paired rank, and the actual stabilizer
intersection. Its derivation uses finite matrix arithmetic and the
strict inequalities shown above. Exact symbolic calculations were
used to discover the candidate; no numerical optimization or sampled
rank is used as a proof premise.

No Lean, Lake, typecheck, or CI command was run.

Independent hand reviews checked the assembled certificate, including
the transformed stabilizer and the exact budget exclusion, without a
material finding. A separate reverse active-margin calculation also
confirmed that the four fixed-state frame columns have rank two at
this same input, hence that the full endpoint rank is four. That
independent calculation was checked by explicit two-by-two conjugations
and rational arithmetic; it is a review cross-check, not an additional
premise of the paired-product proof above.

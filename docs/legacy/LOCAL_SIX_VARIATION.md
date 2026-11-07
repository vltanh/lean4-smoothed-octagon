# Local six-piece variations: rank and a switch-only obstruction

**Status (2026-11-07).** This note proves two reusable endpoint-variation
lemmas and a precise failure of one proposed L4 method. The actual endpoint
map of `010201` has rank five at **every** positive-factor tuple and every
strict-star initial state. A negative compensated needle therefore gives an
actual endpoint-preserving cheaper replacement. However, it is false that a
stationary `010201` window must have a negative missing-control needle at one
of its five switches: an explicit analytic family below has all five such
variations strictly positive, even with the competitive cost and geometric
sector restrictions.

This does **not** disprove the universal L4 replacement claim. Insertions
inside arcs, higher variations, or a distant different-word replacement are
not settled by the counterexample to the switch-only test. No universal
L1–L5 gate is closed here. The equal-factor reverse-family improvement is a
separate result in [LOCAL_REVERSE_SIX.md](LOCAL_REVERSE_SIX.md).

## 1. Endpoint derivatives without a matrix-entry chart

Use the triangular matrices and state convention of
[WORD_HOLONOMY.md](WORD_HOLONOMY.md):

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]

\[
T_i(e^s)=e^{-sD_i},\qquad
\overline Q_i(e^s)=e^{sD_i/2}.
\]

The scalar-free matrices `Q_i` used in the existing endpoint formulas satisfy
`Q_i(q)=sqrt(q) overline Q_i(q)` and induce the same conjugation. For a word
`i_1,...,i_m`, put

\[
F=T_{i_1}(q_1)\cdots T_{i_m}(q_m),\quad
G=\overline Q_{i_1}(q_1)^{-1}\cdots
  \overline Q_{i_m}(q_m)^{-1}.
\]

Then

\[
X_e=G^{-1}X_0G,\qquad g_e=X_0F X_e^{-1}.                 \tag{1}
\]

Fix `X_0`; both frame and state endpoints are being preserved. Let `F_k,G_k`
be the corresponding products **before** factor `k`, and identify a
traceless matrix with its three coordinates `(A_00,A_01,A_10)`. In logarithmic
factor variables `s_k=log q_k`, the left-trivialized derivative of `(F,G)` has
columns

\[
B_k=\left(-\operatorname{Ad}_{F_k}D_{i_k},
          -\tfrac12\operatorname{Ad}_{G_k}D_{i_k}\right). \tag{2}
\]

This uses all of the tangent space of `SL(2)` and does not fail when a chosen
matrix entry, such as `F_00`, vanishes.

The kernel of the derivative of

\[
(F,G)\longmapsto(F,G^{-1}X_0G)
\]

is

\[
\{(0,cX_0):c\in\mathbb R\}.                             \tag{3}
\]

Indeed, its second component is `G^{-1}[X_0,delta G G^{-1}]G`. A traceless
matrix commuting with the nonzero elliptic matrix `X_0` is a scalar multiple
of `X_0`. Thus a rank-six paired map gives a rank-five actual endpoint map.
Conversely, a rank-five paired map need not lose another rank on passing to
the actual endpoints: its image can be transverse to the line (3). A zero
paired determinant alone does not produce an extra endpoint-fiber direction.

## 2. Universal regularity of the L4 endpoint map

**Lemma.** For the word `010201`, the map from its six logarithmic factors to
`(F,X_e)`, with `X_0` fixed, has rank five whenever all six factors exceed one.

Here is a short determinant proof. Remove the common block conjugations
from the first factor in (2), and write

\[
a=q_2,\quad b=q_3,\quad c=q_4,\quad d=q_5.
\]

The sixth factor does not enter any prefix. Temporarily replace the minus
signs and the factor `1/2` in (2) by one, and call the resulting matrix `M`.
Its determinant is

\[
\det M=-\frac{32ad(a-1)(c-1)^2(cd-c+d)}{b^3c}.            \tag{4}
\]

For a hand elimination certificate, pivot on columns `1,2,4` in the first
three rows. Their determinant is `4a^2/b^2`. The Schur complement on remaining
columns `3,5,6` has first column

\[
(0,-2(a-1)/a^2,0)^t.
\]

The first and third entries of its second column are, respectively,

\[
-2c(a-1)(c-1)/b,\qquad -2ac(c-1)/b.
\]

Subtract `(a-1)/a` times its third row from its first row. That first row
becomes

\[
\left(0,0,\frac{2d(c-1)(cd-c+d)}{c^2}\right).
\]

The three displayed pivots multiply to the Schur determinant. The column
permutation `1,2,4,3,5,6` has negative sign, giving (4). These operations are
valid for `a,b,c,d>1`. Also `cd-c+d=c(d-1)+d>0`, so (4) never vanishes.
Returning to (2) multiplies the determinant by `1/8`. The paired map is
therefore a local diffeomorphism, and (3) proves the lemma.

This is a full-domain statement, not a generic dimension count. The initial
state, first factor, and last factor are arbitrary subject to admissibility.
It supplies regularity, but no sign of the cost variation.

## 3. Compensating a needle while preserving both endpoints

Let `E` be a smooth five-dimensional local chart for `(F,X_e)` near a regular
six-piece window, and let `J` be its normalized cost. Suppose first that
`dJ` is nonzero on `ker dE`. The submersion theorem gives a smooth exact
endpoint fiber; choosing the decreasing orientation gives an actual
strictly cheaper nearby window with the same word.

The remaining case is stationarity:

\[
dJ=\lambda\,dE.                                        \tag{5}
\]

Insert a new control with logarithmic factor `epsilon` at a switch, retaining
the original six factors as variables. At `epsilon=0` the original window
is recovered. Five independent old-factor columns allow the implicit
function theorem to preserve `E` exactly while `epsilon` varies. The
compensated derivative is

\[
N=J_\epsilon-\lambda E_\epsilon.                         \tag{6}
\]

If `N<0`, take small `epsilon>0`. The old factors remain greater than one,
the inserted factor is greater than one, and the cost is strictly lower.
All strict-star conditions persist on the finitely many compact arcs. This
is a **seven-piece replacement of one of the fixed six-piece input
windows**, not an enumeration of longer closed words. A needle strictly
inside an arc splits that arc and normally gives eight pieces instead.
The splice preserving actual `(g,X)` is justified in
[MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md).

For L4, (4) gives an especially useful stronger correction. Preserve the
entire pair `(F,G)` using all six old factors. Let `j` be the six-component
column of cost derivatives and solve

\[
B^t\ell=j.                                             \tag{7}
\]

The cost derivative of a needle with paired endpoint column `b_new` and
uncompensated cost derivative `k_new` is

\[
N=k_{\rm new}-\ell^t b_{\rm new}.                        \tag{8}
\]

The correcting vector is `-B^{-1}b_new` and depends only on the factor tuple,
not on the initial state. Actual endpoint stationarity is exactly

\[
\ell^t(0,X_0)=0.                                        \tag{9}
\]

At (9), (8) also equals the derivative under **any** correction preserving
only the actual five endpoint coordinates. Two corrections differ, after
application of `B`, by `(0,cX_0)`, and (9) annihilates the difference. Thus
preserving the stronger paired endpoint does not conceal a different
first-order improvement at a stationary point.

A convex combination of switch needles has the corresponding sum of the
values (8). If all five values are positive, no nonzero nonnegative mixture
of those five insertions, with arbitrary first-order endpoint corrections,
is a descent direction.

## 4. An exact obstruction to a universal switch-only L4 test

### 4.1 A stationary base point with zero outer factors

Use the factors

\[
q=(1,11/10,11/10,6/5,11/10,1),\qquad
p=\frac{2(r,1,3)}{\sqrt{4r+3}}.                           \tag{10}
\]

The two outer zero-duration arcs will be made positive in Section 4.4. The
paired map is already nonsingular at (10): formula (4) does not involve the
two outer factors.

Write

\[
L=\log(11/10),\qquad M=\log(6/5).
\]

For this computation, use the unnormalized margin vector `(r,1,3)`. The
normalizing factor multiplies every cost and needle derivative by
`4/(4r+3)>0`, and multiplies the stationarity expression by a further
positive factor. Hence it does not change any zero or sign below.

Define `C(r)=P(r)/25935653040`, where

\[
\begin{aligned}
P(r)={}&(-32491470000L-371910000M+2936513500)r^3\\
 &+(3472586700L+6428934600M-2948372700)r^2\\
 &+(130343616810L+278114063040M-64645729575)r\\
 &+97189929342L+142474761000M-31921153839.
\end{aligned}                                          \tag{11}
\]

Equation (9), with the matrices (2) and cost formula below, is precisely
`C(r)=0`. There is a unique such root in

\[
I=\left(\frac{10249705}{10^7},
         \frac{10249706}{10^7}\right).                   \tag{12}
\]

The verification of this assertion and all signs uses only rational
arithmetic and the following elementary log bounds:

\[
\begin{aligned}
\frac{9531017980432485}{10^{17}}
 &< L <\frac{9531017980432487}{10^{17}},\\
\frac{18232155679395461}{10^{17}}
 &< M <\frac{18232155679395464}{10^{17}}.
\end{aligned}                                          \tag{13}
\]

For completeness, use

\[
\log\frac{1+z}{1-z}
 =2\sum_{k=0}^{n-1}\frac{z^{2k+1}}{2k+1}+R_n,\qquad
0<R_n<\frac{2z^{2n+1}}{(2n+1)(1-z^2)}.
\]

Take `(z,n)=(1/21,6)` for `L` and `(1/11,8)` for `M`. Substitution into
(11), in Horner order, gives the rational bounds

| Expression | Lower bound | Upper bound |
| --- | ---: | ---: |
| `C(10249705/10^7)` | `6/10^9` | `7/10^9` |
| `C(10249706/10^7)` | `-14/10^9` | `-13/10^9` |
| `C'(r)` for `r` in (12) | `-201/1000` | `-1/5` |

The intermediate value theorem and strict derivative sign prove the claim.
The decimal `r≈1.024970533409` is only a convenient identification of this
exactly specified root.

### 4.2 All five compensated switch needles are positive

Number the switches from left to right. Insert, at each switch, the unique
third control absent from its two adjacent labels. In (10), the five
inserted controls are `2,2,1,1,2`. Formula (8) gives `N_k=A_k(r)/d_k`, with
the following explicit polynomials:

\[
\begin{aligned}
A_1={}&(406708500L-36762000M-25961800)r^2\\
 &+(-4188448935L+1493924520M+163164240)r\\
 &+6555239163L-4325607000M+361504455,\\[2pt]
A_2={}&(-132000L-6000M+13100)r^2\\
 &+(-467280L+203160M+4860)r+48048L+819000M-140493,\\[2pt]
A_3={}&-(11L-1)(r+1)(5r-6),\\[2pt]
A_4={}&(52364950L+719950M-4599750)r^2\\
 &+(24074930L-27422835M+5005130)r\\
 &-21193128L+15926625M-2501049,\\[2pt]
A_5={}&(42900000L+1800000M-4617500)r^2\\
 &+(176550000L-60948000M-6668700)r\\
 &+74234160L-245700000M+41137209,
\end{aligned}                                          \tag{14}
\]

\[
(d_1,d_2,d_3,d_4,d_5)
 =(7132304586,638880,242,235778664,177156100).
\]

Here is a direct derivation recipe for (11) and (14), which also fixes the
endpoint convention and the differentiation variables. On a control `i`
with cyclic margins `(A,B,C)`, use

\[
\begin{aligned}
p_i'&=A,&p_{i+1}'&=(A+B)q-A,&p_{i-1}'&=(A+C)/q-A,\\
J_i&=\frac A8\big((A+B)(q-1)+(A+C)(1-q^{-1})-A\log q\big).
\end{aligned}                                          \tag{15}
\]

Propagate the three linear margin updates, differentiate their sum of costs
with respect to `log q_k`, and solve (7), whose matrix is rational at (10).
For the new factor, the immediate state derivative is

\[
(\delta p_i,\delta p_{i+1},\delta p_{i-1})
 =(0,A+B,-A-C),
\]

and its immediate cost derivative is `A(A+B+C)/8`. Propagate this state
variation through the unchanged suffix and apply (8). These finite linear
operations give the displayed polynomials. They preserve both endpoint
matrices; no scalar matrix-entry chart or terminal condition `F=R` is used.

Using (12)–(13) in (14), with the quadratic polynomials evaluated in Horner
order, yields the following simpler strictly positive rational bounds:

| Needle | Lower bound for its unnormalized compensated derivative |
| --- | ---: |
| `N_1` | `1/30` |
| `N_2` | `3/200` |
| `N_3` | `7/20000` |
| `N_4` | `1/200` |
| `N_5` | `1/80` |

In particular these are open inequalities, with substantial room for the
padding argument. Normalizing the margins multiplies them by the positive
factor `4/(4r+3)`.

### 4.3 Star, cost, and geometric sector checks

This example is not obtained by dropping an eligibility condition. Apply
(15) to the four positive middle arcs. The unnormalized switching margins
fall in the following rational boxes; the two zero outer factors merely
duplicate the end states.

| State | First margin | Second margin | Third margin |
| --- | --- | --- | --- |
| Initial | `(1.0249,1.0251)` | `1` | `3` |
| After `1(11/10)` | `(.8408,.8410)` | `1` | `17/5` |
| After `0(11/10)` | `(.8408,.8410)` | `(1.1840,1.1842)` | `(3.0144,3.0146)` |
| After `2(6/5)` | `(1.6118,1.6121)` | `(.4842,.4845)` | `(3.0144,3.0146)` |
| After `0(11/10)` | `(1.6118,1.6121)` | `(.6938,.6941)` | `(2.5937,2.5941)` |

Every margin is positive. The endpoint positivity criterion for each arc
therefore proves strict-star membership throughout, including after
normalization.

The unnormalized total cost is

\[
\begin{aligned}
J_{\rm raw}={1\over1932612000}\big[&
 (-478500000L-1650000M+88396250)r^2\\
 &+(-225192000L+123750000M+337113375)r\\
 &-306590460L-2320312500M+1134919431\big].
\end{aligned}                                          \tag{16}
\]

Equations (12)–(13) give

\[
0.3130752<\frac{4J_{\rm raw}}{4r+3}<0.3130753<\frac13.
\]

This is below `delta_oct`: the elementary bounds `sqrt(2)<3/2` and
`log 2<1` already give `delta_oct>1/2` in the formula of
[BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md).

Here is also a finite full-arc sector certificate. For a frame
`g=[[A,B],[C,D]]`, the three upper sector brackets are

\[
A,\qquad D-B,\qquad C+D.                                \tag{17}
\]

All three exceed `1/2` throughout this base window. One can verify this
without sampling as follows. Let `z` be the running factor on each of its
four middle arcs. Use (1) and the rational, scalar-free `Q_i`; then for any
bracket `U` in (17),

\[
(4r+3)z\,(U-1/2)
\]

is a polynomial of degree at most two in each of `r,z`. Substitute
`r=1+v/20`, `z=1+(q-1)u`, so `0<=u,v<=1`. Expand in the tensor product
Bernstein basis of degree two. The minima of its coefficients, in the
order of the three brackets (17), are the following positive rationals:

| Arc | `A` | `D-B` | `C+D` |
| --- | ---: | ---: | ---: |
| `1(11/10)` | `7/2` | `7/2` | `7/2` |
| `0(11/10)` | `75/22` | `351/110` | `17/5` |
| `2(6/5)` | `214977/73205` | `89307/73205` | `230806/73205` |
| `0(11/10)` | `1914962/831875` | `3767403/7320500` | `115403/43923` |

For a power expansion `sum a_kl u^k v^l`, the coefficient with indices
`i,j` is explicitly

\[
\sum_{k\le i,\ l\le j}
 a_{kl}\frac{\binom{i}{k}\binom{j}{l}}
               {\binom{2}{k}\binom{2}{l}}.
\]

Thus the table is a reproducible rational polynomial identity and positivity
check. Nonnegative Bernstein basis functions sum to one, proving (17).
The root interval (12) is contained in `1<r<21/20` used here.

The remaining three, lower sector brackets begin at zero and become
positive immediately by the strict-star condition. Each radial contact
angle is strictly increasing in the chosen orientation. It cannot reach
its successor ray while its corresponding upper bracket in (17) is
positive, and cannot return to its initial ray before reaching that
successor. Hence all lower brackets are strictly positive at positive
times. This proves the complete sector condition, not just endpoint
membership.

### 4.4 Genuine six-positive-factor stationary windows

The zero outer factors in (10) are only a device for specifying simple
exact coefficients. Replace them by

\[
q_1=q_6=e^\varepsilon.
\]

Continue to use the normalized initial-state chart
`2(r,1,3)/sqrt(4r+3)`. Define the actual stationarity function by (7)–(9)
for this new tuple. It is smooth near the base point. At `epsilon=0` it
is (11), up to the positive normalization factor, and its `r` derivative
is nonzero by the table following (13). The implicit function theorem
gives a smooth root `r(epsilon)` with `r(0)` equal to (12).

For every sufficiently small `epsilon>0`, all six factors now exceed one.
Stationarity is exact. Every inequality in Sections 4.2–4.3 is open:
strict-star margins, the cost gap below `1/3`, the positive switch-needle
values, and the upper sector margins. They persist. Positive radial speed
then supplies the strict lower sector inequalities, including on the two
new short outer arcs.

Consequently there are eligible, strictly positive L4 windows for which

\[
dJ|_{\ker dE}=0,\qquad N_1,N_2,N_3,N_4,N_5>0.             \tag{18}
\]

This disproves the proposed necessary condition “every stationary L4
window has a negative missing-control insertion at one of its five
switches,” throughout the explicit domain relevant to that proposal.

## 5. What remains open

The endpoint rank issue for L4 is settled by Section 2. The compensated
needle and splice argument is settled by Section 3. The switch-only sign
shortcut is refuted by Section 4. Neither the nonstationary descent lemma
nor the rank calculation supplies the missing inequality at the remaining
stationary points.

In particular, (18) is not a proof that its window is a full-control local
minimum, a global endpoint minimum, or an irreplaceable six-piece window.
A positive constrained Hessian and nonnegative samples of interior needle
values would still require a genuine sufficiency or calibration theorem.
The five-gate package remains conditional, with **0/5 universal analytic
gates proved**.

The companion `explorations/local_l4_switch_obstruction.py` reproduces the
finite exact arithmetic above. Its symbolic and numerical operations are
verification aids; the matrices, polynomial identities, log-series
remainders, rational sign bounds, and continuity argument stated in this
note are the certificate. No Lean, Lake, typechecking, or CI was run.

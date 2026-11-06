# Every reverse five-arc trajectory costs more than the circle

This note concerns the word `02102`, all five durations positive, with no
equal-duration or Pontryagin hypothesis. It proves an exact two-parameter
classification and the uniform bound

\[
\boxed{\frac{\operatorname{cost}}{\sqrt{12}}
>\frac{10}{11}>\frac{\pi}{\sqrt{12}}.}
\]

Thus every admissible reverse cyclic five-arc trajectory costs strictly
more than the circle and cannot improve the octagon. All unequal durations
and initial shapes are covered. The bound is not asserted to be sharp.
Together with the other two word classes in
[FIVE_ARC_PROGRESS.md](FIVE_ARC_PROGRESS.md), this closes the comparison for
at most five positive vertex-control arcs. It supplies no bound on the
number of arcs of an unrestricted minimizing trajectory.

The equations are the actual determinant-one state equations used in
[WORD_HOLONOMY.md](WORD_HOLONOMY.md) and the pinned
[reference definitions](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
The constant-control solution is given in
[Hales–Vajjha, Section 7.1](https://arxiv.org/html/2405.04331v1#Ch7.S1).
The hand algebra below supplies the new word-specific reduction. The
noncyclic five-arc orbit has a separate complete comparison in
[FIVE_ARC_PROGRESS.md](FIVE_ARC_PROGRESS.md). No Lean source was added,
compiled, or kernel checked for this note.

Use the rational matrices and notation of `WORD_HOLONOMY.md`. Indices of the
five arcs below are in `Z/5Z`; their control labels are `j_i=-i mod 3` for
`i=0,1,2,3,4`. Write their factors as

\[
(Q_0,Q_1,Q_2,Q_3,Q_4)=(p,q,r,s,z),\qquad Q_i>1.
\]

Matrix entries use row and column numbers `1,2`, distinct from the
zero-based arc and control indices.

## 1. Complete positive tangent-factor parameterization

Isolating the central two factors in the tangent closure gives

\[
T_2(q)T_1(r)=T_0(1/p)R T_2(1/z)T_0(1/s).
\]

The left matrix is upper triangular, with entries

\[
\begin{pmatrix}
r/q&2/(qr)-r/q-q/r\\0&q/r
\end{pmatrix}.
\]

Before multiplying by the final `T_0(1/s)`, the right matrix is

\[
\begin{pmatrix}
z/(2p)&z/(2p)-(p+p^{-1})/z\\
z/(2p)&z/(2p)+(p-p^{-1})/z
\end{pmatrix}.
\]

Its lower-left entry after that multiplication is zero exactly when

\[
z^2=(p^2-1)(s^2-1).
\]

Under this equation, the right matrix simplifies to

\[
\begin{pmatrix}
\dfrac{p(s^2-1)}{sz}&-\dfrac{p^2+s^2}{psz}\\[4pt]
0&\dfrac{s(p^2-1)}{pz}
\end{pmatrix}.
\]

Set `D=p²s²-p²-s²=z²-1`. Comparing the diagonal and then the upper-right
entry gives

\[
\frac rq=\frac{pz}{s(p^2-1)},\qquad qr=\frac{psz}{D},
\]

and therefore

\[
\boxed{
z=\sqrt{(p^2-1)(s^2-1)},\quad
q^2=\frac{s^2(p^2-1)}D,\quad
r^2=\frac{p^2(s^2-1)}D.}
\]

The complete domain is `p>1`, `s>1`, `D>0`. These conditions make all
three recovered factors strictly greater than one: `z²=D+1`,
`q²=1+p²/D`, and `r²=1+s²/D`. Conversely every positive tangent solution
satisfies these formulas. All divisions have positive denominators.

An alternative uses completely free `q,r>1`. Put

\[
A=\sqrt{q^2-1},\quad B=\sqrt{r^2-1},\quad
W=\sqrt{q^2+r^2-1}.
\]

Then the same family is

\[
\boxed{(p,q,r,s,z)=(W/B,\ q,\ r,\ W/A,\ qr/(AB)).}
\]

These formulas impose tangent closure only; state feasibility is treated
below. They do not silently discard an initial-state condition.

Equivalently, the five positive quantities `x_i=Q_i²-1` satisfy the cyclic
pentagon identities

\[
x_{i-1}x_{i+1}=1+x_i.
\]

For example `x_4 x_1=p²`, `x_0 x_2=q²`, `x_1 x_3=r²`,
`x_2 x_4=s²`, and `x_3 x_0=z²` follow from the displayed formulas.
Multiplying the five identities gives

\[
\prod_i(Q_i^2-1)=\prod_i Q_i.
\]

## 2. A polynomial trace formula for half-holonomy

Let `H_i(Q)=exp((log Q)D_i/2)`, let `H` be their chronological state
product (later factors on the left), and let `K=RH`. The initial-state
condition is `[K,X_0]=0`.

Since `D_{-i}=R^i D_0 R^{-i}` and `R^6=I`, `K` is conjugate to

\[
(H_0(Q_4)R^{-1})(H_0(Q_3)R^{-1})\cdots(H_0(Q_0)R^{-1}).
\]

Conjugate by `L=[[1,1],[1,-1]]`. In that basis

\[
R'=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\qquad
H_0(Q)R'^{-1}=Q^{-1/2}C(Q),\quad
C(Q)=\begin{pmatrix}1&-1\\Q&0\end{pmatrix}.
\]

Define

\[
\mathcal C=C(Q_4)C(Q_3)C(Q_2)C(Q_1)C(Q_0),\quad
P=\prod_iQ_i,
\]

\[
F=1-\sum_iQ_i+\sum_iQ_iQ_{i+2},\qquad N=P-F^2/4.
\]

Every `C(Q_i)` has determinant `Q_i`, so `det C=P`. Direct multiplication
gives `tr C=F`. For an explicit short check, the first three factors have
product

\[
C(Q_2)C(Q_1)C(Q_0)=
\begin{pmatrix}
1-Q_0-Q_1&Q_1-1\\
Q_2(1-Q_0)&-Q_2
\end{pmatrix}.
\]

Multiplying on the left by `C(Q_3)` and then `C(Q_4)`, the two diagonal
entries sum to

\[
1-\sum_iQ_i+
Q_0Q_2+Q_0Q_3+Q_1Q_3+Q_1Q_4+Q_2Q_4=F.
\]

Thus `tr K=F/sqrt P`. The same multiplication gives

\[
\mathcal C_{12}=Q_2-(Q_1-1)(Q_3-1)>0.
\]

The strict sign follows from
`Q_2²=(Q_1²-1)(Q_3²-1)` and `Q_1,Q_3>1`: its positive square root is
strictly greater than `(Q_1-1)(Q_3-1)`. Therefore `C`, and hence `K`,
is never central. The elliptic condition is exactly `N>0`; all data with
`N<=0` are impossible by `WORD_HOLONOMY.md`. There is no omitted central
exception for this particular family.

## 3. Active margins without a matrix expansion

For `N>0`, let

\[
Y=K-\tfrac12\operatorname{tr}(K)I,
\quad \sigma=\operatorname{sign}(Y_{21}),
\quad X_0=\sigma Y/\sqrt{1-(\operatorname{tr}K)^2/4}.
\]

Here `Y_21` is in the original rational basis, not the `L` basis.
It is nonzero because `det Y>0`. This is the sole orientation compatible
with a positive lower-left entry. Let `a_i` be the active margin on arc `i`.
Define, cyclically,

\[
B_i=2Q_i(Q_{i+2}+Q_{i+3}-1)-F.
\]

Then

\[
\boxed{a_i=\frac{\sigma B_i}{\sqrt N}.}
\]

In fact the orientation is always `sigma=+1` in this reverse family.
The companion product also has

\[
\mathcal C_{21}=Q_4\bigl((Q_0-1)(Q_2-1)-Q_1\bigr)<0,
\]

again by the pentagon relation. If `N>0`, its traceless part is elliptic;
the quadratic form `v -> det(v,Yv)` is negative definite because its
lower-left coefficient is negative and its determinant is positive.
Conjugation by `L`, whose determinant is negative, reverses that sign;
conjugations by `R` preserve it. Thus the corresponding traceless part
of `K` in the original rational basis has positive lower-left entry.
The formulas can therefore use `a_i=B_i/sqrt N` and the feasibility test
below can use `B_i>0`.

To prove the active-margin formula, temporarily regard the five `Q_i` as independent variables.
If `H^{(i)}` is the product of the state factors before arc `i`, cyclic
invariance of trace and differentiation of its half-factor give

\[
\frac{\partial\operatorname{tr}K}{\partial\log Q_i}
=\frac12\operatorname{tr}
\bigl(D_{j_i}H^{(i)}K(H^{(i)})^{-1}\bigr).
\]

The scalar part of `K` has zero trace against `D_{j_i}`. Substituting
`X_0` identifies the right side with
`sqrt(1-(tr K)²/4) a_i/(2 sigma)`.
On the other hand differentiation of `F/sqrt P` gives `B_i/(2 sqrt P)`.
These two equalities prove the boxed formula. The trace identity itself
holds for independent factors, so this differentiation does not assume
an invalid variation transverse to the endpoint constraint.

The five margins `a_i` do not by themselves certify the strict star
condition. At the start of arc `i`, the growing coordinate is `a_{i-1}`:
it was active on the preceding arc. The third coordinate is

\[
c_i=\frac{4-a_i a_{i-1}}{a_i+a_{i-1}}.
\]

The same statement holds across the twisted seam, because `-5=1 mod 3`.
Consequently full strict-star feasibility is exactly the finite test

\[
\sigma B_i>0,\qquad B_iB_{i-1}<4N\qquad(i\bmod5),
\]

provided `N>0` and the orientation `sigma` is as defined above. Positivity
at all switching states implies positivity along each entire arc by the
monotone margin formulas. Under this test, tangent closure and holonomy
commutation recover the actual group endpoint as well. The durations are
`a_i log Q_i/2`.

## 4. Exact scalar cost

The decreasing coordinate at the end of arc `i` is `a_{i+1}`. Therefore

\[
\boxed{Q_i=\frac{a_i^2+4}
{(a_i+a_{i-1})(a_i+a_{i+1})}.}
\]

The growing coordinate at the end is

\[
b_i^+=\frac{4-a_i a_{i+1}}{a_i+a_{i+1}}.
\]

The exact constant-control integral gives

\[
8\delta_i=a_i\bigl((b_i^+-a_{i-1})+(c_i-a_{i+1})\bigr)
-a_i^2\log Q_i.
\]

Group its algebraic terms by each adjacent pair `(a_i,a_{i+1})`. The two
coefficients of their common third coordinate add to `a_i+a_{i+1}`, so
that pair contributes

\[
(a_i+a_{i+1})\frac{4-a_i a_{i+1}}{a_i+a_{i+1}}
-2a_i a_{i+1}=4-3a_i a_{i+1}.
\]

Summing all five pairs proves

\[
\boxed{\delta=
\frac{20-3\sum_i a_i a_{i+1}-\sum_i a_i^2\log Q_i}{8}
=\frac{20N-3\sum_iB_iB_{i+1}-\sum_iB_i^2\log Q_i}{8N}.}
\]

This is an exact two-variable objective after the parameterization in
Section 1. Section 6 will show that its finite feasibility test is satisfied
on the whole positive tangent-factor family. Section 7 proves the uniform
lower bound. The central cases have already been excluded in Section 2.

## 5. A global constraint and a failed coarse bound

There are two useful exact simplifications of the cyclic data. First,

\[
\boxed{P=\prod_iQ_i=\sum_iQ_i^2-2.}
\]

To check the nontrivial equality, write `x_0=a`, `x_1=b`. The pentagon
identities give

\[
(x_0,x_1,x_2,x_3,x_4)=
\left(a,b,\frac{1+b}{a},\frac{1+a+b}{ab},\frac{1+a}{b}\right).
\]

Both `prod x_i` and `3+sum x_i`, when multiplied by `ab`, equal
`(1+a)(1+b)(1+a+b)`. Since `prod x_i=P` and `Q_i²=1+x_i`, the stated
identity follows.

Second, each quantity

\[
e_i=Q_iQ_{i+2}-Q_{i+1}-1
\]

is nonnegative. Indeed the pentagon relation shows

\[
(Q_iQ_{i+2})^2-(Q_{i+1}+1)^2
=\left(\sqrt{Q_i^2-1}-\sqrt{Q_{i+2}^2-1}\right)^2\ge0.
\]

Both quantities being compared are positive. Therefore

\[
\boxed{F=6+\sum_i e_i\ge6.}
\]

Equality forces `Q_i=Q_(i+2)` for every index, hence all five factors
are equal. The pentagon relation then gives their common value
`varphi=(1+sqrt5)/2`.

The pentagon product identity gives

\[
\sum_i\log(2\sinh(\log Q_i))=0.
\]

The function `t -> log(2 sinh t)` is strictly concave for `t>0`.
Jensen's inequality therefore gives

\[
\frac15\sum_i\log Q_i\ge\operatorname{arsinh}(1/2)=\log\varphi,
\qquad \prod_iQ_i\ge\varphi^5,
\quad\varphi=(1+\sqrt5)/2.
\]

Equality forces every `Q_i=varphi`. This controls a real parameter of the
whole asymmetric family, but is not alone a cost comparison.

At that symmetric point,

\[
a_i^2=\frac4{1+2\sqrt5},\qquad
\delta=\frac{5(2\sqrt5-2-\log\varphi)}{2(1+2\sqrt5)}.
\]

The elementary upper bound `log Q<=(Q-Q^{-1})/2` is too coarse for the
desired comparison. Even at this point it gives only

\[
\delta\ge\frac{5(4\sqrt5-5)}{4(1+2\sqrt5)},
\]

This is below the octagon's density by rational bounds alone. The estimate
`sqrt5<161/72` gives a value less than `355/394<451/500`. On the other
hand, `sqrt2<99/70` and `log2<6932/10000` give

\[
\delta_{\rm oct}>\frac{144345}{160000}>\frac{451}{500}.
\]

For the logarithmic estimate, expand
`log2=2 atanh(1/3)` and bound the remaining positive terms to obtain

\[
\log2<2\left(\frac13+\frac1{81}+\frac1{1215}+\frac1{13608}\right)
<\frac{6932}{10000}.
\]

The square-root estimates follow by squaring; the rational comparisons
follow by clearing positive denominators. This failure concerns the
proposed coarse certificate, not a smaller admissible cost.

## 6. Exact normalization identities and full feasibility

Write

\[
S=\sum_iQ_i,\quad Z=\sum_iQ_iQ_{i+2},\quad
U=\prod_i(Q_i-1)>0,\quad D=2S+F+1,
\qquad w_i=\sqrt{\frac{Q_i+1}{Q_i-1}}.
\]

The three identities needed below are

\[
\boxed{B_i=2\sqrt U\,w_i>0,\qquad
N=UD,\qquad \sum_i w_iw_{i+1}=D-2.} \tag{A}
\]

Here are independent finite certificates for them. Their order avoids
assuming the normalization identity while proving it.

### 6.1 A positive square-root formula for every active numerator

Use the free parameters `q,r>1` from Section 1 and its radicals `A,B,W`.
Define additional scalars

\[
L=qr-AB>0,\quad M=qr+AB,\quad k=(q+1)(r-1)>0,
\]
\[
E=(q+1)B-(r-1)A,\qquad V=k+AB.
\]

The following short identities use only
`A²=q²-1`, `B²=r²-1`, and `W²=q²+r²-1`:

\[
W^2=LM,\qquad
EV=2k(A+B),\qquad
E^2+V^2=4qrk,\qquad
E^2-V^2=4k(1-AB). \tag{B}
\]

For the middle product, group the coefficients of `A` and `B` after
expansion: they are respectively `2k` and `2k`. For the last two identities,
the square sums factor as

\[
E^2+V^2=((q+1)^2+A^2)(B^2+(r-1)^2),
\]
\[
E^2-V^2=((q+1)^2-A^2)(B^2-(r-1)^2)-4kAB.
\]

Substitution of the five factors into the definition of `B_1` gives

\[
AB\,B_1=WE-LV. \tag{C}
\]

For an entry-by-entry check of (C), its terms containing `W` collect to
`W((q+1)B-(r-1)A)`, while its remaining terms are
`L(q-r+1)-W²=-L((q+1)(r-1)+AB)`.
Now (B) gives

\[
\begin{aligned}
(WE-LV)^2
&=L(ME^2+LV^2-2WEV)\\
&=4kL\bigl(W^2+AB-W(A+B)\bigr)\\
&=4kL(W-A)(W-B).
\end{aligned} \tag{D}
\]

Also the five-factor product is explicitly

\[
U=\frac{(q-1)(r-1)(W-A)(W-B)L}{A^2B^2}.
\]

Equations (C)–(D) prove

\[
B_1^2\frac{q-1}{q+1}=4U.
\]

The sign is positive as well. Indeed
`E=k(B/(r-1)-A/(q+1))>0`, since its two ratios are respectively greater
and less than one. Both `WE` and `LV` are positive, and (B) gives

\[
(WE)^2-(LV)^2=L(ME^2-LV^2)=4qrkL>0.
\]

Thus `WE-LV>0`, so `B_1>0`. The pentagon relations and their positive
parameterization are cyclic; the same argument after a cyclic rotation
proves, for every index,

\[
B_i^2\frac{Q_i-1}{Q_i+1}=4U,\qquad B_i>0,
\qquad B_i=2\sqrt U\,w_i. \tag{E}
\]

### 6.2 An adjacent-product identity from finite symmetric sums

Let `E_j` denote the elementary symmetric sum of degree `j` in the five
factors. Put

\[
A_i=Q_i(Q_{i+2}+Q_{i+3}-1),\qquad
T=\sum_iQ_iQ_{i+1}Q_{i+3}^2.
\]

The following expansions are useful:

\[
\sum_i A_i=2Z-S,\qquad
\sum_i A_iA_{i+1}=3E_4+T-2E_3+E_2-Z, \tag{F}
\]
\[
Z^2=3P+1+2E_4+2T. \tag{G}
\]

In the second identity of (F), the three kinds of products with four
distinct indices each sum to `E_4`; the repeated-index terms sum to `T`;
the negative triple products give `-2E_3`; and the remaining adjacent
quadratic products sum to `E_2-Z`. For (G), the pentagon relation gives

\[
\sum_i(Q_iQ_{i+2})^2=3\sum_iQ_i^2-5=3P+1.
\]

The ten cross terms in `Z²` split into five distinct fourfold products
and five repeated-index products, giving `2E_4+2T`.
Using `B_i=2A_i-F`, (F)–(G), and `Z=F+S-1`, collection now gives

\[
\begin{aligned}
\sum_iB_iB_{i+1}
&=4\sum_iA_iA_{i+1}-4F(2Z-S)+5F^2\\
&=-F^2-8P+4S^2-8S+8(E_4-E_3).
\end{aligned}
\]

Finally,

\[
E_4-E_3=P+S-1-E_2-U,\qquad
2E_2=S^2-P-2.
\]

The first follows from `prod(1-Q_i)=-U`, and the second from
`sum Q_i²=P+2`. Substituting them proves the exact identity

\[
\boxed{\sum_iB_iB_{i+1}=4P-F^2-8U=4N-8U.} \tag{H}
\]

No ellipticity, star feasibility, or `N=UD` was assumed in this calculation.

### 6.3 An independent adjacent-product identity from the pentagon

Set `x_i=Q_i²-1` as before. The pentagon relations, with positive square
roots, imply

\[
x_i=\frac{Q_iQ_{i-1}Q_{i+1}}{Q_{i-2}Q_{i+2}},\qquad
\sqrt{x_ix_{i+1}}=\frac{Q_iQ_{i+1}}{Q_{i-2}}.
\]

For the first formula, square the right side and use
`Q_j²=x_(j-1)x_(j+1)`; all factors cancel except `x_i²`. The second
then follows by multiplying adjacent instances. Consequently

\[
w_iw_{i+1}=Q_{i-2}
\left(1+\frac1{Q_i}\right)\left(1+\frac1{Q_{i+1}}\right). \tag{I}
\]

On the other hand the squared pentagon relation gives

\[
Q_iQ_{i+2}=\frac{Q_i}{Q_{i+2}}+\frac{Q_{i+2}}{Q_i}
+\frac{Q_{i+1}}{Q_{i-2}Q_{i-1}}. \tag{J}
\]

Indeed, before division the identity is
`(Q_iQ_(i+2))²=Q_i²+Q_(i+2)²+Q_(i+1)²-1`; use the displayed formula
for `x_(i+1)` in its last term. Expanding and summing (I), its first
terms sum to `S`, while the two ratio sums and the reciprocal-product
sum are exactly the cyclic sum of (J). Hence

\[
\boxed{\sum_iw_iw_{i+1}=S+Z=2S+F-1=D-2.} \tag{K}
\]

Combining (E), (H), and (K) now gives

\[
4N-8U=\sum_iB_iB_{i+1}=4U(D-2),
\qquad\boxed{N=UD.}
\]

This completes the proof of all three identities (A).

### 6.4 Every positive tangent-factor tuple is actually feasible

Since `U>0`, `S>5`, and `F>=6`, the identity `N=UD` proves `N>0` on
the entire parameter domain. Equations (E) give `B_i>0`. Each adjacent
product is positive and is strictly smaller than their sum; by (H),

\[
B_iB_{i-1}<\sum_jB_jB_{j+1}=4N-8U<4N.
\]

Thus all the finite star tests in Section 3 hold. The unique initial
state, all positive durations, and the full integral trajectory are
constructed by the holonomy formulas; no extra untested shape restriction
is present. Conversely every admissible reverse five-arc trajectory gave
one of these tuples in Section 1. In particular,

\[
a_i=\frac{2w_i}{\sqrt D},\qquad
\sum_i a_i a_{i+1}=4-\frac8D.
\]

## 7. A uniform hand bound above the circle

The exact cost formula in Section 4 now becomes

\[
\boxed{\delta=1+\frac{6-\sum_iw_i^2\log Q_i}{2D}.} \tag{L}
\]

For `Q>1`, put `h=(Q-1)/(Q+1)`. The positive series for `2 atanh h`
gives the rigorous upper bound

\[
\begin{aligned}
\log Q
&\le 2h+\frac{2h^3}{3(1-h^2)}\\
&=\frac{Q-Q^{-1}}6+\frac43\frac{Q-1}{Q+1}
=:\mathcal L(Q).
\end{aligned}
\]

The tail inequality uses `1/(2k+1)<=1/3` for every integer `k>=1`.
It is strict when `Q>1`, because the `h^5` coefficient is strictly smaller
than its bound. Consequently every tuple satisfies

\[
\delta>\delta_{\rm rat}:=
\frac{20N-3\sum_iB_iB_{i+1}-\sum_iB_i^2\mathcal L(Q_i)}{8N}.
\]

Since `w_i²=(Q_i+1)/(Q_i-1)`, direct cancellation gives

\[
w_i^2\mathcal L(Q_i)=\frac{Q_i+Q_i^{-1}+10}{6}.
\]

Thus the rational lower bound simplifies exactly to

\[
\boxed{\delta_{\rm rat}=1-\frac{S+S_{-1}+14}{12D},
\qquad S_{-1}=\sum_iQ_i^{-1}.} \tag{M}
\]

The pentagon product identity gives
`prod(Q_i-Q_i^{-1})=1`. By the arithmetic-geometric mean inequality,

\[
S-S_{-1}\ge5.
\]

Cauchy's inequality also gives `S S_{-1}>=25`. Combining them,
`S>=S_{-1}+5>=25/S+5`, so

\[
S\ge5\varphi,\qquad \varphi=(1+\sqrt5)/2.
\]

Use `S_{-1}<=S-5`, `D=2S+F+1>=2S+7`, and the positivity of all
denominators in (M). It follows that

\[
\begin{aligned}
\delta_{\rm rat}
&\ge1-\frac{2S+9}{12(2S+7)}\\
&=\frac{11}{12}-\frac1{6(2S+7)}\\
&\ge\frac{11}{12}-\frac1{6(10\varphi+7)}
>\frac{11}{12}-\frac1{132}
=\frac{10}{11}.
\end{aligned} \tag{N}
\]

The strict inequality uses `varphi>3/2`. This proves the claimed uniform
bound for every positive tuple, with no numerical premise.

For a self-contained comparison with the circle, polynomial division gives

\[
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=\frac{22}{7}-\pi.
\]

The quotient is `x^6-4x^5+5x^4-4x²+4`, with remainder `-4`.
Since `sqrt3>173/100` by squaring,

\[
\frac\pi{\sqrt{12}}<\frac{1100}{1211}<\frac{10}{11}.
\]

The final comparison has cross-product difference `10`. The octagon is
also strictly below this bound without any decimal estimate:
`sqrt2>707/500` and `log2>2(1/3+1/81)>69/100` give

\[
\delta_{\rm oct}<\frac{827}{914}<\frac{181}{200}<\frac{10}{11}.
\]

There is therefore no equality case with the octagon in the reverse
five-arc class.

## 8. Retained exploratory diagnostics, not proof premises

A finite diagnostic evaluated this rational expression using Python
3.12.14 and mpmath 1.3.0 with 80 decimal digits. Its inputs were

\[
q=1+e^u,\qquad r=1+e^v,\qquad (u,v)\in[-18,18]^2.
\]

The retained script is
[reverse_five_rational_diagnostic.py](../explorations/reverse_five_rational_diagnostic.py).
From the repository root, reproduce it with
`python explorations/reverse_five_rational_diagnostic.py`.

The list comprised the `61 by 61` grid
`u=-18+36i/60`, `v=-18+36j/60`, `0<=i,j<=60`; 3000 pairs generated by
Python `random.Random(5102).uniform(-18,18)`; and the symmetric exact
radical `q=r=varphi`. The random binary64 outputs were converted to
decimal strings before mpmath evaluation. All other constants, matrix
formulas, square roots, and arithmetic used the stated 80-digit setting.

For each point, form the five factors from Section 1, compute `P,F,N,B_i`,
and check `N>0`, the proved positive orientation `B_i>0`, and
`4N-B_iB_(i+1)>0`. Evaluate the exact-cost formula and replace each
logarithm by `L(Q_i)` for the rational diagnostic. All 6722 evaluated
points passed those numerical feasibility tests. The smallest evaluated
rational density was approximately `0.90947666567981533756`, at the
included symmetric point. No evaluated value was below the trial
threshold `109/120`. The later hand bound (N) is stronger than that
threshold and holds on the full unbounded parameter domain.

These are rounded floating-point observations at finitely many points.
The tests do not certify signs near the boundary, cover the unbounded
parameter domain, control values between sample points, prove a global
minimum, or themselves turn a trial threshold into a theorem. No optimizer
or interval certificate was used. None of the mathematical results in
Sections 1–7 depends on this diagnostic.

A second diagnostic discouraged a tempting shortcut: the rational
surrogate did not increase monotonically under the symmetrization
`q²=1+U exp(2t)`, `r²=1+U exp(-2t)` at fixed `U`. At `U=exp(-4)`,
its evaluated values decreased slightly as `t` increased from `0` to
`0.8`, although they stayed far above the desired bound. This is a
numerical warning, not a proved global statement about that derivative.
No such monotonicity is used in this note.

That check, together with a short list of exact-formula evaluations, is
retained in
[reverse_five_exploration.py](../explorations/reverse_five_exploration.py).
Reproduce it with `python explorations/reverse_five_exploration.py`.
It uses the same Python and mpmath versions at 50 decimal digits, with
the finite parameter lists explicitly stated in the script.

The completed comparison uses the exact algebraic identities and the
analytic inequality (N), with the whole endpoint and star domain retained.
It does not assert that the symmetric point is the unique minimizer of
this class, or that `10/11` is its infimum. The unrestricted Reinhardt
comparison still requires treatment of longer words or a proved global
replacement theorem, together with any needed connection to general
measurable controls. No uniform bound on word length is claimed here.

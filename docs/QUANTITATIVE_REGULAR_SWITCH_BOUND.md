# An effective switch bound from a supplied singular clearance

Date: 2026-11-07. Hand proof; no Lean compilation, Lake, or CI.

## Theorem and exact scope

There are explicit constants \(k\in\mathbb N\) and \(c>0\), depending
only on the common strict-star state bounds, a bound on elapsed time,
and projective normalization of the costate, with the following property.
Suppose a free-time Pontryagin trajectory has singular clearance at least
\(\varepsilon>0\) in the precise norm below, and satisfies the optimality
property

> **(E4)** Every interval on which one fixed control coordinate vanishes
> almost everywhere agrees almost everywhere with at most four positive
> constant vertex pieces.

Then its number of positive pieces is at most

\[
\boxed{
N(\varepsilon)=4(2k+1)
 \left\lceil\frac{T_{\max}}
 {c\min(\varepsilon,1,m)}\right\rceil .}
\tag{1}
\]

The positive constant \(m\) is explicit too. Every constant in (1) is
specified in Section 6. In particular this proves an \(O(1/\varepsilon)\)
bound for a supplied clearance in a fixed normalization. The constants
are deliberately coarse; no useful numerical upper bound is claimed.

Actual global minimizers satisfy (E4) by
[EDGE_SWITCH_BOUND.md](EDGE_SWITCH_BOUND.md). The qualitative compactness
result in [GLOBAL_MINIMIZER_COMPACTNESS.md](GLOBAL_MINIMIZER_COMPACTNESS.md)
supplies the existence of a positive clearance, but does not give its
numerical value. The present theorem makes the subsequent conversion
from a certified clearance to a stated integer completely effective.
It neither supplies that missing clearance nor proves a cost comparison
for the resulting words.

The proof quantifies the transported-covector argument in
[GLOBAL_CLOSED_VARIATION.md](GLOBAL_CLOSED_VARIATION.md). It uses a fixed
number of separating lines and a time interval of length proportional
to the clearance. It does not assume a minimum duration for individual
arcs, and it permits arbitrary measurable controls.

## 1. Bounds, normalization, and the clearance being used

All matrix norms are Frobenius norms; operator norms use the induced
Euclidean norm. Retain the original matrices

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad q=1/\sqrt3,
\]

\[
Z_0=\begin{pmatrix}0&1/3\\1&0\end{pmatrix},\quad
Z_1=\begin{pmatrix}q&-2/3\\0&-q\end{pmatrix},\quad
Z_2=\begin{pmatrix}-q&-2/3\\0&q\end{pmatrix}.
\]

Write

\[
\lambda\le0,\qquad A=\Lambda_1-\frac32\lambda J,
\qquad W=\Lambda_R,
\]

\[
P=P_u(X)=\frac{Z_u}{\langle Z_u,X\rangle},\quad
b=-[A,X],\quad
\mathcal L(Y)=[P,Y]-\langle Y,P\rangle[P,X],
\quad \langle Y,Z\rangle=\operatorname{tr}(YZ).
\]

The equations and pointwise Hamiltonian conditions are

\[
\begin{aligned}
X'&=[P,X],&
A'&=[A,X]+\frac32\lambda[J,X],\\
W'&=\mathcal LW+b,& \lambda'&=0,\\
\langle W,X\rangle&=0,&
\max_i\{\langle A,X\rangle-\langle W,P_i(X)\rangle\}&=0.
\end{aligned}
\tag{2}
\]

The maximum condition holds everywhere by continuity of the maximum;
control support is imposed almost everywhere. Suppose throughout the
trajectory

\[
\|X\|\le K_X,\qquad
\gamma_i(X):=-\langle Z_i,X\rangle\ge\Gamma>0,
\qquad 0<T\le T_{\max}.
\tag{3}
\]

These are numerical inputs, not unspecified minima over a compact set.
Set

\[
K_Z=\frac{\sqrt{10}}3,\qquad
K_P=\frac{K_Z}{\Gamma},\qquad
L_P=\frac{K_Z^2}{\Gamma^2}.
\tag{4}
\]

Then \(\|P_u(X)\|\le K_P\) for every simplex control, and

\[
\|P_i(X)-P_i(Y)\|\le L_P\|X-Y\|
\tag{5}
\]

whenever both states satisfy (3). To prove (5), subtract the two scalar
denominators; each has absolute value at least \(\Gamma\). No convexity
assumption on the set of states is needed.

Use the actual reduced cotangent norm

\[
\|\mathcal P\|
 :=\bigl(\lambda^2+\|\Lambda_1\|^2+\|W\|^2\bigr)^{1/2},
\qquad \|\mathcal P(0)\|=1.
\tag{6}
\]

It is a positive definite norm on the six-dimensional extended cotangent
fiber, represented in the seven ambient coordinates with
\(\langle W,X\rangle=0\). Normal and abnormal lifts are both included.

Let

\[
L_0=2K_P+2K_P^2K_X,\qquad
B_P=3\sqrt2K_X+4K_X+L_0,
\]

\[
m=e^{-B_PT_{\max}},\qquad M=e^{B_PT_{\max}}.
\tag{7}
\]

Equations (2) give \(\|\mathcal P'\|\le B_P\|\mathcal P\|\)
almost everywhere. Indeed the three scalar coefficients obtained by
bounding the \(\Lambda_1\) and \(W\) equations are respectively
\(3\sqrt2K_X,4K_X,L_0\) for
\((|\lambda|,\|\Lambda_1\|,\|W\|)\). Their sum is a valid induced
norm bound. Forward and backward Gronwall yield

\[
\boxed{m\le\|\mathcal P(t)\|\le M.}
\tag{8}
\]

The supplied singular clearance means

\[
\boxed{
\bigl(\|X(t)-J\|^2+\|A(t)\|^2+\|W(t)\|^2\bigr)^{1/2}
\ge\varepsilon\quad(0\le t\le T).}
\tag{9}
\]

The zero set in (9) is exactly the full singular locus, including its
irrelevant zero-multiplier point. A clearance given in half-plane
cotangent coordinates must first be converted to (6)--(9). On the
common compact state domain the coordinate changes and their inverses
have bounded derivatives, so this is a finite norm-comparison estimate;
it is not an additional dynamical exclusion.

### Explicit state inputs for global minimizers

The common compact set of Hales--Vajjha, Definition 5.0.1, permits

\[
K_X=9,\qquad \Gamma=\frac{2}{15\sqrt3},\qquad
T_{\max}=\frac\pi3.
\tag{10}
\]

The matrix bound and time bound are proved in
`GLOBAL_MINIMIZER_COMPACTNESS.md`. For the denominator bound, the excluded
half-plane in [Definition 5.0.1](https://arxiv.org/html/2405.04331v1#Ch5)
gives \(y\le15(q-x)\). Thus
\(\gamma_1=2q(q-x)/y\ge2q/15\). The compact set is invariant under the
cyclic rotation, which permutes the three denominators, so the same
bound holds for each \(\gamma_i\). In particular (4) gives
\(K_P=5\sqrt{30}/2\). All state and coefficient inputs to (1) are
therefore explicit before a numerical singular clearance is supplied.

## 2. Two quantitative algebraic lemmas

### 2.1 The zero Hamiltonian controls the missing component of A

For a traceless determinant-one \(X\),

\[
[X,[X,A]]=-4A-2\langle A,X\rangle X.
\]

Since \(b=[X,A]\), equation (2) implies, using any active vertex,

\[
A=-\frac14[X,b]-\frac12\langle W,P_i(X)\rangle X.
\]

Consequently

\[
\boxed{\|A\|\le\frac{K_X}{2}
             \bigl(\|b\|+K_P\|W\|\bigr).}
\tag{11}
\]

This is why a large \(A\) with small \(W\) forces a large first
transported derivative, rather than merely a large component normal
to the state orbit.

### 2.2 The second derivative is quantitatively nonzero away from J

On the positive elliptic orbit,

\[
\boxed{\|[[J,X],X]\|\ge4\|X-J\|.}
\tag{12}
\]

Here is an exact proof in the chosen norm. Write \(X=aJ+S\), where
\(S\) is symmetric and traceless. The positive orbit gives \(a\ge1\),
and \(\det X=1\) gives \(\|S\|^2=2(a^2-1)\). Also

\[
[[J,X],X]=4(aX-J),\qquad
\|X-J\|^2=4a(a-1).
\]

For \(a>1\),

\[
\frac{\|aX-J\|^2}{\|X-J\|^2}
=\frac{(a+1)(2a^2-1)}{2a}\ge1,
\]

because the difference between numerator and denominator is
\((a-1)(2a^2+4a+1)\ge0\). At \(a=1\), one has \(X=J\) and
(12) holds directly.

Define the control-independent second-derivative vector

\[
C(X,\lambda)=-\frac32\lambda[[J,X],X].
\tag{13}
\]

Thus \(\|C(X,\lambda)\|\ge6|\lambda|\|X-J\|\).

## 3. A fixed number of separating lines with explicit margins

Set \(h_i(X,W)=-\langle W,P_i(X)\rangle\). There is a uniform width
bound for every unit vector \(W\in X^\perp\):

\[
\boxed{\max_i h_i(X,W)-\min_i h_i(X,W)\ge\omega,\qquad
\omega:=\frac{2}{\sqrt6 K_XK_Z(1+K_X^2/2)}.}
\tag{14}
\]

To prove it, write a traceless matrix as
\(Y=\left(\begin{smallmatrix}a&b\\c&-a\end{smallmatrix}\right)\)
and put \(r_i=\langle Y,Z_i\rangle\). The explicit inverse is

\[
a=\frac{r_1-r_2}{4q},\qquad
c=-\frac34(r_1+r_2),\qquad
b=r_0+\frac14(r_1+r_2).
\]

It gives \(\|Y\|\le\sqrt6\max_i|r_i|\). If \(\Delta\) denotes
the left side of (14), choose \(s\) to be the midpoint of the largest
and smallest \(h_i\), and set \(Y=W+sX\). Then

\[
|\langle Y,Z_i\rangle|
 =|s-h_i|\,|\langle X,Z_i\rangle|
 \le\frac\Delta2 K_XK_Z.
\]

Moreover \(\langle Y,X\rangle=-2s\), so
\(|s|\le K_X\|Y\|/2\). Hence

\[
1=\|W\|\le(1+K_X^2/2)\|Y\|
 \le(1+K_X^2/2)\sqrt6\frac\Delta2 K_XK_Z,
\]

which proves (14).

Choose the integer and its convenient derivative margin

\[
k=\max\left(2,\left\lceil\frac{8\pi K_P}{\omega}\right\rceil\right),
\qquad \sigma=\frac1k.
\tag{15}
\]

Any larger integer may replace this k if sigma is also replaced by 1/k.
For the explicit inputs (10), the quantities simplify to

\[
\omega=\frac{2}{249\sqrt{15}},\qquad
\frac{8\pi K_P}{\omega}=37350\pi\sqrt2.
\]

Thus the convenient fixed choice k=200000 is valid: the elementary bounds
pi<22/7 and sqrt(2)<3/2 give 37350*pi*sqrt(2)<1232550/7<200000.
It gives B=4(2k+1)=1600004 in (30). This deliberately coarse local count
is not a numerical whole-period bound; the clearance and interval length
in (1) remain necessary.

In the Euclidean plane \(E=X_0^\perp\), take \(k\) equally spaced
lines. Each closed angular sector has width \(\pi/k\). At the middle
unit vector of a sector choose vertex indices \(i,j\) giving the
width in (14). Since \(\|P_i-P_j\|\le2K_P\), every unit vector
\(\xi\) in that closed sector has

\[
h_i(X_0,\xi)-h_j(X_0,\xi)\ge\frac{3\omega}{4}.
\tag{16}
\]

Indeed its distance from the middle vector is at most \(\pi/k\),
and (15) bounds the resulting loss by \(\omega/4\). Thus each sector
has one fixed strictly excluded vertex, including its boundary rays.

For any nonzero \(v\in E\), rotate this equally spaced arrangement
so that the direction of \(v\) lies halfway between two adjacent
lines. The unit normal functionals \(\ell_j\) then satisfy

\[
|\ell_j(v)|\ge\sin\frac\pi{2k}\,\|v\|
             \ge\sigma\|v\|\quad(1\le j\le k).
\tag{17}
\]

The last inequality follows from concavity of sine on \([0,\pi/2]\).
This rotation does not change (16), which was established for any
arrangement of that mesh. Both the number of lines and all the stated
margins are uniform over the initial phase.

## 4. Explicit derivative and perturbation constants

Use the following upper bounds obtained from (8):

\[
K_\lambda=M,\qquad K_W=M,\qquad
K_A=(1+\tfrac32\sqrt2)M.
\]

Define

\[
\begin{aligned}
V_X&=2K_PK_X,\\
V_A&=2K_AK_X+3\sqrt2K_\lambda K_X,\\
V_W&=L_0K_W+2K_AK_X,\\
K_b&=2K_AK_X,\\
V_b&=2K_XV_A+2K_AV_X,\\
K_C&=6\sqrt2K_\lambda K_X^2,\\
V_C&=12\sqrt2K_\lambda K_XV_X,\\
D_0&=4K_X^2+4K_PK_X+2L_0K_X.
\end{aligned}
\tag{18}
\]

They bound respectively the indicated phase speeds, \(\|b\|\),
\(\|b'\|\), \(\|C\|\), and \(\|C'\|\). The last constant gives

\[
\|b'-\mathcal Lb-C(X,\lambda)\|\le D_0\|A\|.
\tag{19}
\]

For (19), differentiate \(b=-[A,X]\), substitute (2), and bound
\(-[[A,X],X]-[A,[P,X]]-\mathcal Lb\). The three bounds are exactly
the three summands in \(D_0\). No derivative of a measurable control
is used.

Fix an initial time \(t_0\). Let \(U'=\mathcal LU\), \(U(t_0)=I\),
on the ambient traceless matrices and set

\[
\eta(t)=U(t)^{-1}W(t)\in E=X(t_0)^\perp.
\]

The membership follows by differentiating \(\langle UY,X\rangle\).
The curve is \(C^1\), its first derivative is absolutely continuous,
and

\[
\eta'=U^{-1}b,\qquad
\eta''=U^{-1}(b'-\mathcal Lb)\quad\hbox{almost everywhere}.
\tag{20}
\]

For \(0\le t-t_0\le h\le1/(2L_0)\),

\[
\|U^{\pm1}\|\le2,\qquad
\|U^{\pm1}-I\|\le2L_0h.
\tag{21}
\]

The following four constants collect the errors used below:

\[
\begin{aligned}
F_0&=4K_PL_0+2L_PV_X,\\
G_0&=2K_PV_W+2L_PK_WV_X,\\
B_1&=2L_0K_b+2V_b,\\
C_1&=2L_0K_C+2V_C+2D_0V_A.
\end{aligned}
\tag{22}
\]

Their precise consequences are as follows.

First, if \(\xi\in E\) is a unit vector, then

\[
\begin{aligned}
&|(h_i-h_j)(X(t),U(t)\xi)-(h_i-h_j)(X(t_0),\xi)|\le F_0h,\\
&|(h_i-h_j)(X(t),W(t))-(h_i-h_j)(X(t_0),W(t_0))|\le G_0h.
\end{aligned}
\tag{23}
\]

These follow from (5), (18), and (21) by adding and subtracting the
value with one argument fixed. Consequently the sector exclusion
margin in (16) remains at least \(\omega/2\) whenever
\(F_0h\le\omega/4\).

Second,

\[
\|\eta'(t)-b(t_0)\|\le B_1h.
\tag{24}
\]

Finally, writing \(C_0=C(X(t_0),\lambda)\),

\[
\|\eta''(t)-C_0\|
 \le2D_0\|A(t_0)\|+C_1h
 \quad\hbox{almost everywhere}.
\tag{25}
\]

For (25), use \(\|A(t)\|\le\|A(t_0)\|+V_Ah\),
\(\|C(t)-C_0\|\le V_Ch\), and (19)--(21). These are bounds on all
measurable controls uniformly, including controls with arbitrarily many
short arcs.

## 5. Clearance gives one of three uniform alternatives

Put

\[
e=\min(\varepsilon,1,m),\qquad
\lambda_{\min}=\frac{m}{2(1+\tfrac32\sqrt2)},\qquad
c_C=3\lambda_{\min},
\]

\[
a=\min\left(\frac18,\frac{\sigma c_C}{8D_0}\right),\qquad
r=\frac{a}{1+K_XK_P},\qquad
c_b=\frac a{K_X}.
\tag{26}
\]

At every initial time \(t_0\), exactly one of the following three
cases applies.

**I. \(\|W(t_0)\|\ge re\).** By (14), there is a vertex comparison
of size at least \(\omega re\). The second bound in (23) preserves
a positive comparison if \(G_0h\le\omega re/2\). One fixed control
coordinate is then zero on the entire short interval, so (E4) gives
at most four pieces.

**II. \(\|W(t_0)\|<re\) and \(\|A(t_0)\|\ge ae\).**
Equation (11) implies

\[
\|b(t_0)\|
 \ge\frac2{K_X}\|A(t_0)\|-K_P\|W(t_0)\|
 \ge c_be.
\tag{27}
\]

Here \(K_XK_Pr<a\). Rotate the guard lines using
\(v=b(t_0)\). By (17) and (24), every projection \(\ell_j(\eta)\)
has a strictly signed first derivative whenever
\(B_1h\le\sigma c_be/2\). It therefore has at most one zero.

**III. \(\|W(t_0)\|<re\) and \(\|A(t_0)\|<ae\).**
Since \(a,r\le1/8\) and \(e\le m\), one has
\(\|A(t_0)\|+\|W(t_0)\|\le m/4\). Also

\[
m\le\|\mathcal P(t_0)\|
\le(1+\tfrac32\sqrt2)|\lambda|
       +\|A(t_0)\|+\|W(t_0)\|.
\]

Thus \(|\lambda|\ge\lambda_{\min}\). The clearance (9) and
\(a,r\le1/8\) give \(\|X(t_0)-J\|\ge e/2\). By (12)--(13),

\[
\|C_0\|\ge c_Ce>0.
\tag{28}
\]

Rotate the guards using \(v=C_0\). By the definition of \(a\),
\(2D_0ae\le\sigma c_Ce/4\). If
\(C_1h\le\sigma c_Ce/4\), (25) gives

\[
\|\eta''-C_0\|\le\frac{\sigma c_Ce}{2}
                  \le\frac{\sigma\|C_0\|}{2}.
\]

Each guard projection has a strictly signed second derivative almost
everywhere. Its first derivative is strictly monotone, so Rolle's
theorem shows that the projection has at most two zeros.

## 6. The explicit formula for c and the complete-period count

Define

\[
h_0=\min\left(\frac1{2L_0},\frac\omega{4F_0}\right)
\]

and, using only the constants (4), (7), (14)--(15), (18), (22), (26),

\[
\boxed{
c=\min\left(
h_0,\ \frac{\omega r}{2G_0},\
\frac{\sigma c_b}{2B_1},\
\frac{\sigma c_C}{4C_1}
\right)>0.}
\tag{29}
\]

Take \(h=ce\). Since \(e\le1\), all the transport and sector
requirements hold on every interval of length at most \(h\). The
three case-specific error bounds of Section 5 hold there as well.

In Case II delete the at most \(k\) guard zeros; in Case III delete
the at most \(2k\) guard zeros. Every remaining connected component
stays in one angular sector. Its actual reduced covector is
\(W=U\eta\), so (16), (21), and (23) give a fixed excluded vertex
throughout that component. Property (E4) provides at most four positive
pieces on its closure: the same coordinate is zero almost everywhere
there, since adjoining finitely many endpoints does not change that
condition. Isolated endpoints have no effect on the almost-everywhere
control or its integral trajectory. Thus every such short interval
has at most

\[
B=4(2k+1)
\tag{30}
\]

positive pieces, uniformly over its initial phase and its measurable
control. This also covers Case I.

Partition a complete period into intervals of length at most \(ce\).
Apply (30) at each interval's left endpoint. Concatenating their vertex
representations and merging equal neighbors gives (1). A subsequent
twisted cyclic reduction can only lower the count.

For \(0<\varepsilon\le\min(1,m)\), this can be displayed as

\[
N(\varepsilon)
\le4(2k+1)\left(1+\frac{T_{\max}}{c\varepsilon}\right).
\tag{31}
\]

All inequalities use interval length, guard zeros, and the exact edge
bound (E4). Individual arcs may be arbitrarily short.

## 7. What is now effective, and what remains open

For normalized global minimizers, equations (10), (4), and (7) give
explicit state and costate bounds. Equations (14)--(15) give a fixed
integer \(k\) and uniform comparison and derivative margins. Equations
(18), (22), (26), and (29) then give \(c\) by finite arithmetic,
exponentiation, and one ceiling. A supplied numerical lower bound for
the singular distance (9) would therefore produce a definite integer
in (1); there is no further unproved switch-count or dwell-time step.

The qualitative compactness theorem gives some positive clearance and
therefore an existential uniform integer. It applies also to precisely
the normalization (6): convert its compact family by the smooth invertible
cotangent-coordinate map, then divide each lift by its positive initial
norm in (6). This is a continuous operation on a compact family; the
initial norm has a positive minimum by nontriviality. Its evaluation image
is compact and still disjoint from the singular locus, so the distance
(9) has a positive minimum. This argument does not evaluate that
clearance. This note does not convert its existence proof into a
numerical estimate, assert a particular integer, or claim that the
bound is small enough for the existing through-five comparison.
A complete global proof still needs a cost comparison on every
remaining complete-period competitor, with the free initial state
and the twisted endpoint conditions preserved.

No increasing-length enumeration, numerical trajectory fit, symbolic
sign oracle, Lean compilation, Lake command, or CI check is part of
this proof. The theorem is a conditional quantitative reduction with
all coefficient constants explicit and its single clearance input
stated in (9).

### Independent hand review

Three separate internal mathematical reviews checked the exact state
denominator bound, both algebraic coercivity estimates, the width constant,
guard rotation, every transport/error budget, the phase thresholds, and
the final count. No substantive gap was found. These reviews are not
external peer review or kernel validation.

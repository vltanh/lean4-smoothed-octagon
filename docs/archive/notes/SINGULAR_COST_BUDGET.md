# A complete-period cost budget gives numerical singular clearance

Date: 2026-11-07. Hand proof; no Lean, Lake, typechecking, or CI.

## Theorem and scope

Every normalized complete-period Pontryagin lift of a global minimizer has
the explicit singular clearance

\[
\boxed{D(t)>10^{-11}\qquad(0\le t\le T).}
\tag{1}
\]

With the edge-optimality property (E4) already proved for global minimizers,
the quantitative three-guard argument consequently gives

\[
\boxed{N<10^{56}}
\tag{2}
\]

positive vertex pieces in a complete period. These statements include
normal and abnormal lifts and all values of the conserved determinant.
No source finite bang-bang theorem, singular-avoidance theorem, minimum arc
duration, numerical escape calculation, or word enumeration is used.

The edge-optimality property used for the count is precisely:

> **(E4)** Every subinterval on which one fixed control coordinate
> vanishes almost everywhere agrees almost everywhere with at most four
> positive constant vertex pieces.

This sharpens the earlier complete numerical reduction in
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md), which gives
\(D>10^{-1906}\) and \(N<10^{5741}\). Its cost--Casimir proof remains
valid. The argument below works directly with the shifted group costate
in every component and improves the projective norm bounds using the
complete-period budget.

The main new inequality is more general. Let a strict-star, free-time
Pontryagin trajectory have the actual complete-period endpoints, twisted
state and costate closure, and total cost \(C<\pi\). Then at every time

\[
\boxed{
\left\|\Lambda_1(t)-\frac32\lambda J\right\|_F
\ge |\lambda|\,\frac{3(\pi-C)}{2\pi-C}.}
\tag{3}
\]

Equation (3) does not require the compact minimizer state domain or
optimality beyond the stated Pontryagin conditions. The explicit constants
in (1)--(2) additionally use that common state domain and the competitive
budget \(C\le A_{\rm oct}\). The count (2) is a numerical reduction, not
a cost comparison or a proof of global minimality or affine uniqueness.

### Conventions and inputs

All matrix norms without an operator-norm subscript are Frobenius norms.
Use exactly the physical-time and cotangent conventions of
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md) and
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md):

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
R=e^{\pi J/3},\qquad
X=\frac1y\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},\quad y>0,
\]
\[
Z_0=\begin{pmatrix}0&1/3\\1&0\end{pmatrix},\quad
Z_1=\begin{pmatrix}1/\sqrt3&-2/3\\0&-1/\sqrt3\end{pmatrix},\quad
Z_2=\begin{pmatrix}-1/\sqrt3&-2/3\\0&1/\sqrt3\end{pmatrix}.
\]

The controls satisfy \(u_i\ge0\), \(\sum_i u_i=1\), and
\(Z_u=\sum_i u_iZ_i\). Write

\[
P_u=\frac{Z_u}{\operatorname{tr}(Z_uX)},\quad
\lambda=-\mu\le0,\quad
A=\Lambda_1+\frac32\mu J,\quad W=\Lambda_R.
\]

The equations and maximum condition needed for (3) are

\[
g'=gX,\qquad \Lambda_1'=[\Lambda_1,X],\qquad
\operatorname{tr}(WX)=0,\qquad
\max_u\{\operatorname{tr}(AX)-\operatorname{tr}(WP_u)\}=0.
\tag{4}
\]

Here \(X^2=-I\), and \(X\) lies on the positive elliptic orbit.
The strict-star condition makes every vertex denominator negative.
The maximum over the simplex equals the maximum over its three vertices.
The maximum condition holds everywhere by continuity; the equations hold
almost everywhere for absolutely continuous trajectories and measurable
controls.

The complete-period conditions are

\[
g(0)=I,\quad g(T)=R,\quad X(T)=R^{-1}X(0)R,
\]
\[
\Lambda_1(T)=R^{-1}\Lambda_1(0)R,\qquad
W(T)=R^{-1}W(0)R.
\tag{5}
\]

The last condition is the free-initial-state transversality condition;
the preceding group-costate condition follows from conservation in (4).
For the numerical theorem use the normalized extended covector

\[
\mathcal P=(\lambda,\Lambda_1,W),\qquad
\|\mathcal P(0)\|^2
 =\lambda^2+\|\Lambda_1(0)\|^2+\|W(0)\|^2=1,
\]
\[
D(t)^2=\|X(t)-J\|^2+\|A(t)\|^2+\|W(t)\|^2.
\tag{6}
\]

The established compact minimizer domain \(K\) is invariant under
\(X\mapsto R^{-1}XR\). Its explicit bounds are

\[
y\le\frac92,\qquad \|X\|\le9,\qquad
\gamma_i(X):=-\operatorname{tr}(Z_iX)\ge
\Gamma:=\frac{2}{15\sqrt3}.
\tag{7}
\]

These are the common state bounds recorded in
[GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md) and the
quantitative note. The source inputs establishing \(K\), the geometric
correspondence, and the Pontryagin conditions remain inputs here. The
singular-avoidance part of the compactness note is not used.

## 1. A strictly interior equilibrium control

Put \(r^2=x^2+y^2\), and define the positive scalar

\[
\rho=-\frac12\operatorname{tr}(JX)
 =\frac{1+r^2}{2y}\ge1.
\tag{8}
\]

At every point of the positive elliptic orbit, choose

\[
u_0^*=\frac{2}{3(1+r^2)},\qquad
u_1^*=\frac{1+3r^2+2\sqrt3x}{6(1+r^2)},\qquad
u_2^*=\frac{1+3r^2-2\sqrt3x}{6(1+r^2)}.
\tag{9}
\]

Their sum is one. The last two numerators are
\((\sqrt3x\pm1)^2+3y^2\), so all three coordinates are strictly
positive. Direct substitution in the displayed vertex matrices gives

\[
Z_{u^*}=\frac{X}{3\rho},\qquad
\operatorname{tr}(Z_{u^*}X)=-\frac2{3\rho},\qquad
\boxed{P_{u^*}=-\frac X2.}
\tag{10}
\]

It is an admissible comparison control at every strict-star state. By
\(\operatorname{tr}(WX)=0\), its state-costate term vanishes. The
maximized Hamiltonian in (4) therefore gives the pointwise inequality

\[
\boxed{\operatorname{tr}(AX)\le0.}
\tag{11}
\]

This compares the Hamiltonian with an instantaneous equilibrium control;
it does not assert that the actual control is an equilibrium.

## 2. An exact left-and-right angular identity

Define the spatial velocity and its positive scalar by

\[
V=gXg^{-1}=g'g^{-1},\qquad
\rho_R=-\frac12\operatorname{tr}(JV).
\tag{12}
\]

Conjugation by \(\mathrm{SL}_2(\mathbb R)\) preserves the positive
elliptic orbit: \(-JX\) is positive definite, with determinant one, and
\[
-J(gXg^{-1})=g^{-T}(-JX)g^{-1}
\]
is positive definite as well. In particular \(\rho_R\ge1\).
For completeness, any matrix on
that orbit has a unique decomposition \(Y=\rho_YJ+S\), where \(S\)
is symmetric and traceless. The identity \(\det Y=1\) gives
\(\|S\|^2=2(\rho_Y^2-1)\), and positivity gives \(\rho_Y\ge1\).
Consequently

\[
\|Y\|^2=4\rho_Y^2-2\le4\rho_Y^2.
\tag{13}
\]

Write

\[
g=sI+tJ+uH+vK_0,
\qquad
H=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
K_0=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

The determinant identity is

\[
s^2+t^2-u^2-v^2=1.
\tag{14}
\]

In particular \(s+it\ne0\). Choose its continuous argument \(\theta\)
with \(\theta(0)=0\). It is absolutely continuous. Computing the
\(J\) coefficient of \(g^{-1}g'\) and \(g'g^{-1}\) gives

\[
\rho=st'-ts'+uv'-vu',\qquad
\rho_R=st'-ts'-uv'+vu'.
\]

Thus, almost everywhere,

\[
\boxed{\rho+\rho_R=2(s^2+t^2)\theta'.}
\tag{15}
\]

Both scalars on the left are at least one, so \(\theta'>0\) almost
everywhere. The endpoint \(g(T)=R\) gives
\(\theta(T)=\pi/3+2\pi n\) for an integer \(n\). Since the argument
increases from zero, \(n\ge0\). Equations (14)--(15) imply

\[
\int_0^T(\rho+\rho_R)\,dt
 \ge2\int_0^T\theta'\,dt
 \ge\frac{2\pi}{3}.
\tag{16}
\]

No assumption about a primary winding is needed: additional turns only
strengthen (16). The cost is \(C=3\int_0^T\rho\,dt\). With

\[
I=\int_0^T\rho\,dt=\frac C3,\qquad
I_R=\int_0^T\rho_R\,dt,
\]

we have the explicit inequality

\[
\boxed{I_R\ge\frac{2\pi-C}{3}.}
\tag{17}
\]

## 3. Conservation turns the period budget into a pointwise bound

The group-costate equation gives the exact spatial conservation law

\[
\Lambda_1(t)=g(t)^{-1}\Lambda_1(0)g(t).
\tag{18}
\]

Set \(A_0=A(0)\) and \(a_0=\|A_0\|\). Since
\(\Lambda_1(0)=-(3/2)\mu J+A_0\), trace invariance gives

\[
\operatorname{tr}(\Lambda_1(t)X(t))
 =\operatorname{tr}(\Lambda_1(0)V(t))
 =3\mu\rho_R(t)+\operatorname{tr}(A_0V(t)).
\]

Substitution in (11) yields

\[
3\mu\rho_R+\operatorname{tr}(A_0V)\le3\mu\rho.
\tag{19}
\]

Frobenius Cauchy--Schwarz and (13) imply
\(\operatorname{tr}(A_0V)\ge-2a_0\rho_R\). Integrating (19),

\[
2a_0 I_R\ge3\mu(I_R-I).
\tag{20}
\]

Because \(C<\pi\), equation (17) gives \(I_R>I>0\). The function
\(r\mapsto1-I/r\) is increasing for \(r>0\). Division by the positive
number \(2I_R\), followed by (17), gives

\[
a_0\ge\frac{3\mu}{2}\left(1-\frac I{I_R}\right)
 \ge\frac{3\mu}{2}\left(1-\frac C{2\pi-C}\right)
 =\mu\,\frac{3(\pi-C)}{2\pi-C}.
\tag{21}
\]

No division by \(\mu\) or by \(3\mu-2a_0\) occurs. In particular,
the calculation includes \(\mu=0\) and requires no separate large-
\(a_0\) case or determinant assumption.

### Applying the bound at every time

The genuine twisted extension from (5) satisfies

\[
g(t+T)=g(t)R,\quad X(t+T)=R^{-1}X(t)R,
\]
\[
\Lambda_1(t+T)=R^{-1}\Lambda_1(t)R,\quad
W(t+T)=R^{-1}W(t)R,
\]

with the corresponding cyclic permutation of controls. It is one
absolutely continuous Pontryagin trajectory across the seam. Fix any
\(t_0\in[0,T]\), and use on \([0,T]\) the rebased frame

\[
\widehat g(s)=g(t_0)^{-1}g(t_0+s).
\]

It satisfies \(\widehat g'=\widehat gX(t_0+s)\),
\(\widehat g(0)=I\), and \(\widehat g(T)=R\). Its initial body
costate is \(\Lambda_1(t_0)\), not a new independently selected
costate. Since \(R\) commutes with \(J\), the cost density is
\(T\)-periodic, so the shifted period has the same total cost \(C\).
Applying (21) to that period proves (3) at \(t_0\). The normalization
of the initial covector is not used in this rebasing argument.

## 4. An elementary rational budget margin

The concrete octagon competitor has the exact circle-representation cost

\[
A_{\rm oct}=2\sqrt3\,
 \frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\tag{22}
\]

Define

\[
\kappa=\frac{3(\pi-A_{\rm oct})}{2\pi-A_{\rm oct}}.
\]

Reuse the finite rational certificate from Section 2 of
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md):

\[
\sqrt2>\frac{140}{99},\qquad
\sqrt3<\frac{97}{56},\qquad
\log2>\frac{693}{1000}.
\tag{23}
\]

The first two follow from \(19600<19602\) and \(9409>9408\).
For the logarithm, integrate the geometric series for
\(1/(1-z^2)\) to obtain

\[
\log2
 =2\sum_{k\ge0}\frac{(1/3)^{2k+1}}{2k+1}
 >2\left(\frac13+\frac1{81}+\frac1{1215}\right)
 =\frac{842}{1215}>\frac{693}{1000}.
\]

The numerator in (22) is positive: \(\sqrt2<3/2\) and
\(\log2<1\) give \(8-4\sqrt2-\log2>1\). Thus substituting (23)
with their indicated directions is legitimate and gives

\[
A_{\rm oct}
 <\frac{97}{28}
   \frac{8-560/99-693/1000}{280/99-1}
 =\frac{15849121}{5068000}
 =\frac{391}{125}-\frac{3583}{5068000}
 <\frac{391}{125}.
\tag{24}
\]

For a short exact lower bound on \(\pi\), the tangent addition formula
gives Machin's identity
\(\pi/4=4\arctan(1/5)-\arctan(1/239)\), with the angle in
\((0,\pi/2)\). Integrating
\(1-t^2<1/(1+t^2)<1\) for \(0<t<1\) then gives

\[
\pi>16\left(\frac15-\frac1{375}\right)-\frac4{239}
 =\frac{281476}{89625}
 =\frac{157}{50}+\frac{107}{179250}
 >\frac{157}{50}.
\tag{25}
\]

The function \(3(p-a)/(2p-a)\) increases in \(p\) and decreases in
\(a\) for \(0<a<p\). Therefore (24)--(25) imply

\[
\boxed{\kappa>\frac9{788}>\frac1{100}.}
\tag{26}
\]

Since \(3(\pi-C)/(2\pi-C)\) decreases with \(C\), every competitive
closed lift with \(C\le A_{\rm oct}\) satisfies

\[
\boxed{\|A(t)\|\ge\kappa\mu\quad\hbox{at every time}.}
\tag{27}
\]

## 5. Uniform covector bounds from the same complete-period budget

The previous Gronwall covector bounds remain valid, but the full period
permits much smaller explicit bounds. This section proves

\[
\boxed{10^{-8}<\|\mathcal P(t)\|<10^8
 \qquad(0\le t\le T).}
\tag{28}
\]

### 5.1 A frame bound depending on total cost

For a positive elliptic matrix, the product of its two singular values
is one and their squared sum is \(4\rho^2-2\), by (13). Its largest
singular value is consequently

\[
\|X\|_{\rm op}=\rho+\sqrt{\rho^2-1}<2\rho.
\]

The integral form of \(g'=gX\) and Gronwall give, for \(0\le t\le T\),

\[
\|g(t)\|_{\rm op}
 \le\exp\left(\int_0^t\|X\|_{\rm op}\,ds\right)
 <e^{2C/3}<e^{2\pi/3}<9.
\tag{29}
\]

To check the last constant exactly, the positive logarithm series gives
\(\log3>2(1/2+(1/2)^3/3)=13/12>22/21>\pi/3\).
Here \(\pi<22/7\) follows, for example, from
\(22/7-\pi=\int_0^1x^4(1-x)^4/(1+x^2)\,dx>0\).
For a determinant-one two-by-two matrix the largest singular value of
its inverse is the same, so \(\|g(t)^{-1}\|_{\rm op}<9\) too.

### 5.2 Zero Hamiltonian bounds the reduced state costate

Set \(h_i=-\operatorname{tr}(WP_i)\). The explicit width estimate in
the quantitative note, for \(\operatorname{tr}(WX)=0\), is

\[
\max_i h_i-\min_i h_i\ge\omega\|W\|,\qquad
\omega=\frac{2}{249\sqrt{15}}>\frac1{500}.
\tag{30}
\]

The last strict inequality uses \(\sqrt{15}<4\). To turn width into
a positive maximum, use the equilibrium control (9). Its control-affine
weights are

\[
\vartheta_i
 =\frac{u_i^*\gamma_i}{\sum_j u_j^*\gamma_j}
 =\frac{3\rho}{2}u_i^*\gamma_i.
\tag{31}
\]

They are positive, sum to one, and satisfy
\(P_{u^*}=\sum_i\vartheta_iP_i=-X/2\). Consequently
\(\sum_i\vartheta_i h_i=0\).

The first coefficient in (9) is
\(u_0^*=1/(3\rho y)\). Equation (7) gives
\(u_0^*\ge2/(27\rho)\). The equilibrium control is equivariant
under cyclic rotation: conjugation by \(R^{-1}\) fixes \(\rho\),
permutes the vertex matrices, and sends its unique expression
\(Z_{u^*}=X/(3\rho)\) to the corresponding expression for
\(R^{-1}XR\). Since \(K\) is invariant under that rotation, the
same height bound applies in each rotated chart. Hence

\[
u_i^*\ge\frac2{27\rho},\qquad
\vartheta_i\ge\frac\Gamma9
 =\frac2{135\sqrt3}>\frac1{135}
\quad\hbox{for all }i.
\tag{32}
\]

Choose an index \(j\) where \(h_j=\min_i h_i\). Since their weighted
mean is zero,

\[
0=\sum_i\vartheta_i h_i
 \le \max_i h_i-\vartheta_j(\max_i h_i-\min_i h_i).
\]

Equations (30)--(32) and the zero maximized Hamiltonian give

\[
\frac{\|W\|}{67500}\le\max_i h_i
 =-\operatorname{tr}(AX)\le9\|A\|.
\]

In particular, with the convenient integer \(L=10^6\),

\[
\boxed{\|W(t)\|\le607500\|A(t)\|\le L\|A(t)\|.}
\tag{33}
\]

This holds also at \(A=W=0\); no division by either norm is used.

### 5.3 Upper and lower projective norms

Initial normalization gives \(\mu\le1\) and
\(\|\Lambda_1(0)\|\le1\). Equations (18), (29), and (33) imply

\[
\|\Lambda_1(t)\|<81,\qquad
\|A(t)\|<81+\frac32\sqrt2<84,\qquad
\|W(t)\|<84L.
\]

It follows that
\(\|\mathcal P(t)\|<1+81+84L=84000082<10^8\).

For the converse, use (33) at the original initial time and put
\(c_J=(3/2)\sqrt2<9/4\). Then

\[
\begin{aligned}
1=\|\mathcal P(0)\|
&\le \mu+\|\Lambda_1(0)\|+\|W(0)\|\\
&\le(1+L)\|\Lambda_1(0)\|+(1+c_JL)\mu\\
&\le81(1+L)\|\Lambda_1(t)\|+(1+c_JL)\mu\\
&\le\left(81(1+L)+1+\frac94L\right)\|\mathcal P(t)\|\\
&=83250082\,\|\mathcal P(t)\|<10^8\|\mathcal P(t)\|.
\end{aligned}
\]

The last strict comparison uses the positive norm of the nontrivial
covector. This proves the lower bound in (28).

## 6. Numerical distance from the full singular locus

Set \(Q=(\|A\|^2+\|W\|^2)^{1/2}\) and
\(d=\sqrt{11/2}<5/2\). The exact decomposition

\[
\mathcal P=(0,A,W)+\lambda\left(1,\frac32J,0\right)
\]

gives \(\|\mathcal P\|\le Q+d\mu\). By (27),
\(\kappa\mu\le\|A\|\le Q\), including when \(\mu=0\).
Therefore

\[
\boxed{
D\ge Q\ge\frac{\kappa}{\kappa+d}\|\mathcal P\|
 >\frac1{251}\|\mathcal P\|.}
\tag{34}
\]

The strict constant follows from (26) and \(d<5/2\). Combining (28)
and (34) gives

\[
D(t)>\frac{10^{-8}}{251}>10^{-11},
\]

which proves (1) for **every** normalized competitive closed lift in
the common state domain. No normal-cost rescaling is needed.

### Independent fallback using the earlier Gronwall normalization

Equation (34) is independent of every improved estimate in Section 5.
For the earlier constants \(m_{\rm old}=M_{\rm old}^{-1}\) of
[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md), its
proved estimate \(m_{\rm old}>10^{-1903}\) immediately gives

\[
D>\frac{m_{\rm old}}{251}>10^{-1906}.
\tag{35}
\]

The same earlier coefficient bound
\(c_{\rm old}>10^{-27}m_{\rm old}^2\), with clearance
\(10^{-1906}\), gives a common short-interval length greater than
\(10^{-5739}\). Thus the unchanged earlier constants already imply
\(N\le56\cdot10^{5739}<10^{5741}\). This alternative uses only
Sections 1--4 and the previous numerical arithmetic.

## 7. The explicit complete-period piece count

For the better bound, use the admissible bounds just proved,

\[
M=10^8,\qquad m=10^{-8}=M^{-1},\qquad
\varepsilon=10^{-11},\qquad T_{\max}=\pi/3<2.
\tag{36}
\]

The proof in Sections 2--6 of the quantitative note uses its covector
bounds only through \(m\le\|\mathcal P\|\le M\). Its original
Gronwall formulas are one sufficient way of obtaining those bounds;
they are not used again in that proof. Reapplying the same proof with
(36) is therefore legitimate. No assertion that the new \(M,m\) equal
the old Gronwall expressions is made.

Here is the complete numerical conversion. Keep its explicit constants
\(K_X=9\), \(K_P=5\sqrt{30}/2<14\), and
\(L_0=2K_P+18K_P^2<3556\). Its width and three-line derivative
margin satisfy

\[
\omega=\frac2{249\sqrt{15}}>10^{-3},\qquad
\sigma=\frac1{56025\pi\sqrt2}>10^{-6}.
\]

Substitution in the derivative and error constants of that note gives

\[
D_0<10^5,\quad F_0<10^6,\quad
G_0<10^6M,\quad B_1<10^6M,\quad C_1<10^8M.
\tag{37}
\]

For example the exact intermediate upper bounds are
\(D_0<64836\), \(F_0<297920\), \(G_0<200368M\),
\(B_1<520416M\), and \(C_1<20826936M\); their multiplication and
addition are displayed in Section 3 of
[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md).
That arithmetic uses only the same \(m,M\), their reciprocal relation,
and the state constants, not its small-multiplier hypothesis.

Write the threshold constants as

\[
s_0=1+\frac32\sqrt2<4,\qquad
c_C=\frac{3m}{2s_0}>\frac m4,
\]
\[
a_*=\min\left(\frac18,\frac{\sigma c_C}{8D_0}\right),\qquad
r_*=\frac{a_*}{1+9K_P},\qquad c_b=\frac{a_*}{9}.
\]

Since \(m\le1\), (37) gives

\[
a_*>10^{-13}m,\qquad r_*>10^{-16}m,\qquad c_b>10^{-14}m.
\]

The actual time coefficient is the same explicit minimum as in that
note:

\[
h_0=\min\left(\frac1{2L_0},\frac\omega{4F_0}\right),\qquad
c=\min\left(h_0,\frac{\omega r_*}{2G_0},
 \frac{\sigma c_b}{2B_1},\frac{\sigma c_C}{4C_1}\right).
\]

The four entries obey respectively

\[
h_0>10^{-10},\qquad
\frac{\omega r_*}{2G_0}>10^{-26}m^2,\qquad
\frac{\sigma c_b}{2B_1}>10^{-27}m^2,\qquad
\frac{\sigma c_C}{4C_1}>10^{-16}m^2.
\]

Thus

\[
\boxed{c>10^{-27}m^2=10^{-43}.}
\tag{38}
\]

The common short-interval length can be chosen as

\[
h=c\min(\varepsilon,1,m)=c\,10^{-11}>10^{-54}.
\tag{39}
\]

The three-guard theorem uses at most 28 positive pieces per such interval,
assuming (E4). Since \(T_{\max}<2\), and \(2\cdot10^{54}\) is an
integer,

\[
N\le28\left\lceil\frac{T_{\max}}h\right\rceil
 \le56\cdot10^{54}<10^{56}.
\tag{40}
\]

Concatenating the interval representations and merging equal neighbors
cannot increase this count. Twisted cyclic reduction cannot increase it
either. This argument bounds the total number of pieces; it does not
give a positive lower bound for individual durations.

## Dependencies and remaining global comparison

The first-order equations, actual boundary conditions, and twisted
extension are those proved in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md), following the Pontryagin
formulation in Hales--Vajjha,
[*Packings of Smoothed Polygons*, Sections 6.6--6.7](https://arxiv.org/html/2405.04331v1#Ch6.S6).
The compact domain and its cyclic symmetry are the domain of
[Definition 5.0.1](https://arxiv.org/html/2405.04331v1#Ch5), with its
explicit bounds retained in the repository notes cited above.
The exact octagon value (22) is the existing concrete candidate value,
also recorded in [NEAR_CIRCLE_BOUND](NEAR_CIRCLE_BOUND.md).

For the piece count,
[MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md) proves (E4)
directly for actual global minimizers by a separate two-state edge PMP
and an integrating factor. It starts with measurable controls and uses
neither Hales--Vajjha Theorem 8.1.4 nor Theorem 16.3.1.
[EDGE_SWITCH_BOUND](EDGE_SWITCH_BOUND.md) remains a separate local
variation argument. The note
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
supplies the independently proved conditional three-guard count.
The clearance (34) and the count (40) do not use Hales--Vajjha Theorem
16.3.1 or any numerical source step identified in
[FINITE_BANG_BANG_SOURCE_AUDIT](FINITE_BANG_BANG_SOURCE_AUDIT.md).
They therefore replace that particular dependency for this numerical
reduction; they do not certify the source's separate escape or basin
claims.

The theorem supplies one fixed explicit cutoff before any additional
closed-word comparison. It does not compare the remaining competitors
with the octagon, resolve equality, or assert that direct enumeration up
to this very large cutoff is practical. The next global task must retain
the actual complete-period state and frame endpoints, the free initial
state, all boundary limits, and the cost budget while proving a uniform
comparison on the bounded domain.

All new identities and numerical inequalities here are hand arguments.
Exact rational arithmetic was used only to check the printed fractions;
the finite certificates are displayed in (23)--(26). No numerical
trajectory or symbolic sign oracle is a premise. This note does not
claim Lean kernel validation of existing drafts.

Independent internal hand reviews by the parent and two mathematical
reviewers checked the equilibrium coefficients, signs and positive
elliptic component, angular identity and winding, complete-period
rebasing, homogeneous inequality, rational budget margin, improved
projective bounds, replacement of the earlier Gronwall constants,
and final integer count. The direct measurable-edge proof was reviewed
separately. No material gap was found in these reviews. They are internal
mathematical checks, not external peer review or Lean kernel validation.

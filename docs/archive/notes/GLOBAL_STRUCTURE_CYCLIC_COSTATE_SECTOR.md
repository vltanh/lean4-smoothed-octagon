# A common costate-sector restriction for pure cyclic periods

Date: 2026-11-07. Hand proof with an
[independent internal audit](GLOBAL_STRUCTURE_CYCLIC_COSTATE_AUDIT.md).
No Lean, Lake, typechecking, or CI. Internal review is not external peer
review or kernel validation.


**Later global resolution:** [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
now closes the entire pure-reverse case R by a minimum-margin PMP
contradiction, independently of the Casimir/sector route studied here.
The earlier limitations below describe this note's own argument; they
do not leave global R open. F and the three mixed cases remain open.

## Result and boundary

Consider an actual normal PMP period consisting entirely of forward
switches, or entirely of reverse switches. Assume positive durations,
strict-star states, the full twisted frame and state endpoints, and the
free-initial-state costate transversality. Normalize the cost multiplier
to `lambda=-1`.

Then its primary costate `Lambda_1` is nonzero and does **not** lie in the
closed positive elliptic cone. In physical coordinates, the excluded
cone is

\[
\mathcal C_+=\left\{
\begin{pmatrix}u&v-w\\v+w&-u\end{pmatrix}:
 w\ge\sqrt{u^2+v^2}\right\}.
\tag{1}
\]

This includes the positive elliptic component (`det Lambda_1>0` and
positive lower-left entry), its nonzero parabolic boundary, and zero.
Consequently the only remaining primary-costate sectors for a pure
cyclic period are the negative elliptic component, its nonzero
parabolic boundary, and the hyperbolic sector. This is a restriction on
both pure cyclic cases at once, with arbitrary unequal factors. It uses
normality and the actual free-initial-state periodic transversality;
it is not a statement about arbitrary fixed-endpoint windows.

The theorem does **not** prove that the primary costate is elliptic.
The hyperbolic and negative parabolic alternatives remain. Even in the
negative elliptic component, the theorem gives no lower bound on its
Casimir, no index sign, and no bound of five. The general F and R cost
comparisons remain open. This result must not be counted as closing
either finite structural case.

## 1. A scalar derivative with a uniform sign

Use the cyclic active margins from
[GLOBAL_FORWARD_INDEX](GLOBAL_FORWARD_INDEX.md), indexed modulo the
number `N` of pieces. Write

\[
a_i>0,\qquad s_i=a_i+a_{i+1},\qquad K_i=a_i^2+4,
\qquad r_i=\frac{s_{i-1}s_i}{K_i}.
\tag{2}
\]

Define the scalar function

\[
8\mathcal J(a)=\sum_i
 \left(3a_i a_{i+1}-4-a_i^2\log r_i\right).
\tag{3}
\]

For a pure forward period, `J=C/sqrt(12)=mathcal J`, and its physical
arc factors are `q_i=r_i>1`. For a pure reverse period,
`J=-mathcal J`, and its arc factors are `q_i=r_i^{-1}>1`.
Both statements retain the exact state closure: the initial active
margin chain is periodic after the required cyclic relabeling. The
adjacent strict-star inequalities are `a_i a_{i+1}<4`.

Here is a check of the reverse sign that does not invoke time reversal.
On its arc `i`, the active/growing/decreasing initial margins are
`(a_i,a_{i-1},b_i)`, where

\[
b_i=\frac{4-a_{i-1}a_i}{s_{i-1}},\qquad
q_i=\frac{K_i}{s_{i-1}s_i}.
\]

The final margins in the same order are `(a_i,b_{i+1},a_{i+1})`.
The exact arc cost is therefore

\[
8J_i=a_i(b_i+b_{i+1}-a_{i-1}-a_{i+1})-a_i^2\log q_i.
\]

Summing and using `log q_i=-log r_i` gives `J=-mathcal J`.
Thus the sign difference in (3) comes from the two actual vertex
updates; no reversed admissible curve has been assumed.

**Lemma.** Every partial derivative of `mathcal J` is strictly positive
on the entire positive orthant, even without the arc-factor or
adjacent-product inequalities.

Differentiating (3) gives

\[
C_i:=\mathcal J_{a_i}=\frac14\left[
 a_{i-1}+a_i+a_{i+1}
 -a_i^2\left(\frac1{s_{i-1}}+\frac1{s_i}\right)
 +\frac{a_i^3}{K_i}-a_i\log r_i\right].
\tag{4}
\]

Put

\[
\rho=\frac{s_{i-1}}{a_i}>1,\qquad
\sigma=\frac{s_i}{a_i}>1,\qquad
\tau=\frac{K_i}{a_i^2}>1.
\]

Then (4) is the exact decomposition

\[
\boxed{\frac{4C_i}{a_i}
 =f(\rho)+f(\sigma)+h(\tau),}
\qquad
f(t)=t-t^{-1}-\log t,\quad
h(t)=\log t-1+t^{-1}.
\tag{5}
\]

Both functions vanish at `t=1`, and for `t>1`

\[
f'(t)=\frac{t^2-t+1}{t^2}>0,\qquad
h'(t)=\frac{t-1}{t^2}>0.
\]

All three summands in (5) are positive. This proves the lemma. In
particular, the actual cyclic cost derivatives have signs

\[
\frac{\partial J}{\partial a_i}>0\quad\text{(forward)},
\qquad
\frac{\partial J}{\partial a_i}<0\quad\text{(reverse)}.
\tag{6}
\]

These are derivatives in the state-closed family before imposing its
three remaining frame constraints. They do not assert monotonicity
along the closed-frame constraint manifold.

## 2. The frame columns have a matching uniform orientation

Work in the triangular coordinates of
[BOUNDED_REDUCTION](BOUNDED_REDUCTION.md), Section 4. These are an
orientation-reversing conjugation of the physical coordinates. Put

\[
R=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\qquad
E=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
T_0(q)=\operatorname{diag}(q,q^{-1}).
\]

For forward periods use

\[
A(q)=T_0(q)R^{-1}
 =\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix},
\quad
P_i=A(q_0)\cdots A(q_{i-1}),\quad M_+=P_N.
\]

Here `N=3k+1`, and the full tangent-frame closure is
`M_+=(-I)^k`. Since the physical tangent product is
`F=M_+R^N`, its right-trivialized active-margin derivative is the
same as that of `M_+` at the period under consideration. The cyclic
version of the exact column formula in
[LOCAL_FORWARD_RANK](LOCAL_FORWARD_RANK.md) is

\[
V_i^+=\frac{\partial M_+}{\partial a_i}M_+^{-1}
 =\operatorname{Ad}_{P_i}
 2\begin{pmatrix}
 -a_i/K_i&q_i^2/s_i\\
 -1/s_{i-1}&a_i/K_i
 \end{pmatrix}.
\tag{7}
\]

The formula is valid at the cyclic seam because the endpoint product
is central. It follows either by differentiating the three affected
factors or by extending the products using
`P_{i+N}=P_i M_+`; centrality makes the adjoint columns periodic.

For a reverse period, use instead

\[
B(q)=T_0(q)R
 =\begin{pmatrix}0&q\\-q^{-1}&q^{-1}\end{pmatrix},
\quad
P_i=B(q_0)\cdots B(q_{i-1}),\quad M_-=P_N.
\]

Now `N=3k+2`, the actual tangent product is `F=M_-R^{-N}`, and
full closure is `M_-=(-I)^{k+1}`. Differentiating
`log q_i=-log r_i` yields

\[
V_i^-:=\frac{\partial M_-}{\partial a_i}M_-^{-1}
 =\operatorname{Ad}_{P_i}
 2\begin{pmatrix}
 a_i/K_i&-1/s_{i-1}\\
 1/(q_i^2s_i)&-a_i/K_i
 \end{pmatrix}.
\tag{8}
\]

For a direct verification of (8), set `Z_i=Ad_{P_i}E`. The derivative
is

\[
-\frac{Z_{i-1}+Z_i}{s_{i-1}}
-\frac{Z_i+Z_{i+1}}{s_i}+\frac{2a_i}{K_i}Z_i,
\]

and use

\[
B(q)^{-1}EB(q)+E=\begin{pmatrix}0&2\\0&0\end{pmatrix},
\quad
E+B(q)EB(q)^{-1}=\begin{pmatrix}0&0\\-2q^{-2}&0\end{pmatrix}.
\]

In both cases the determinant simplifies to

\[
\boxed{\det V_i^\pm
 =\frac{4(s_{i-1}s_i-a_i^2)}{K_i^2}>0.}
\tag{9}
\]

Indeed `s_{i-1}s_i-a_i^2=a_i(a_{i-1}+a_{i+1})+
 a_{i-1}a_{i+1}>0`. Before the determinant-one conjugation, the
lower-left entry in (7) is negative and that in (8) is positive.
Conjugation by an `SL_2(R)` matrix preserves the two elliptic components.
Therefore all `V_i^+` are negative elliptic and all `V_i^-` are
positive elliptic in the triangular coordinates. No assumption that
the factors are equal is present.

## 3. Use the actual periodic PMP boundary term

Represent the cyclic frame multiplier by a traceless matrix `U`, using
the trace pairing. The normal PMP first-variation identity and its
free-initial-state transversality give

\[
\frac{\partial J}{\partial a_i}
 =\operatorname{tr}(U V_i^\pm).
\tag{10}
\]

This relation does not require a choice of a nonzero endpoint minor or
an inverse Hessian. It follows directly from the given normal lift.
For clarity, its relation to the original primary costate is

\[
\boxed{
U=\frac1{\sqrt{12}}
 \operatorname{Ad}_{X_0^{-1}}\Lambda_1^{\rm tri}(0).}
\tag{11}
\]

To check both the sign and the free-initial-state issue, recall the
exact endpoint identity

\[
g_T=X_0 F X_T^{-1}.
\]

Throughout the active-margin family, state closure already holds:
`X_T=R^{-1}X_0R`. At the period, `F=R` and `g_T=R`, so differentiation
gives

\[
\delta g_T\,g_T^{-1}
 =\operatorname{Ad}_{X_0}(\delta F\,F^{-1}).
\tag{12}
\]

The two terms from varying `X_0` cancel in (12). The initial and final
state-covector boundary terms cancel separately by the twisted
free-state transversality. The primary costate paired with the
right-trivialized terminal frame variation is the conserved spatial
matrix `Lambda_1^{tri}(0)`. Divide the physical-cost first-variation
identity by `sqrt(12)`, substitute (12), and use cyclicity of trace.
This gives (10)--(11). In particular the multiplier sign in (10) agrees
with the maximizing convention `lambda=-1`.

## 4. Cone exclusion

Let `C_-^{tri}` be the closed negative elliptic cone in the triangular
coordinates. If `U` is a nonzero member of this cone and `Y` is negative
elliptic, then

\[
\operatorname{tr}(UY)<0.
\tag{13}
\]

If `Y` is positive elliptic, the sign is instead strictly positive.
Here is an elementary proof, including parabolic `U`. An
orientation-preserving conjugation takes the negative elliptic `Y` to
`-tJ`, with `t>0` and `J=[[0,-1],[1,0]]`. Write the conjugate of `U`
as `[[u,b],[c,-u]]`. Membership in the closed negative cone gives
`b>=0`, `c<=0`, and nonzero `U` gives `b-c>0`: if both vanished,
`det U>=0` would force `u=0`. Hence
`tr(U(-tJ))=-t(b-c)<0`. The positive elliptic assertion follows by
negating `Y`.

Suppose first the period is forward and `U` is in this closed negative
cone. If `U=0`, (10) contradicts the positive derivative in (6).
Otherwise (7), (13), and (10) give a negative derivative, again a
contradiction.

For a reverse period, `U=0` contradicts the negative derivative in
(6). For nonzero `U` in the closed negative cone, (8), (13), and (10)
give a positive derivative, also a contradiction. Thus in both cases

\[
U\notin\mathcal C_-^{\rm tri}.
\tag{14}
\]

Conjugation by `X_0` in (11) has determinant one and multiplication by
`sqrt(12)` is positive, so neither changes this cone conclusion.
Finally the triangular coordinate change reverses orientation. It
therefore sends the physical closed positive cone (1) to the closed
negative triangular cone. Equation (14) proves the stated exclusion
for `Lambda_1(0)`. The spatial conservation law makes every other
`Lambda_1(t)` conjugate to it by a determinant-one matrix, so the
exclusion holds at every time.

## What remains

For the negative elliptic sector, the existing complete-period
cost--Casimir inequality in
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) can now be used with the
exact octagon budget. The new argument does not give the opposite
Casimir inequality needed to rule out long forward or reverse returns.
It also does not eliminate hyperbolic or negative parabolic primary
costates. In those sectors the cone-pairing sign in (13) is unavailable.

The signed scalar derivative and elliptic columns are not an index
certificate. A constrained second variation also contains the curvature
of the full matrix endpoint map. The Fourier evaluation in
[GLOBAL_FORWARD_INDEX](GLOBAL_FORWARD_INDEX.md) treats that term only
at the standard equal-arc family. Extending it to arbitrary stationary
periods remains an independent unresolved step.


### Why column orientation alone cannot remove the remaining sectors

There is an exact limitation on the preceding sign argument. In triangular
coordinates set

\[
U_0=\begin{pmatrix}0&-1\\0&0\end{pmatrix},\qquad
U_\epsilon=\begin{pmatrix}\epsilon&-1\\0&-\epsilon\end{pmatrix}.
\tag{15}
\]

The first matrix is positive parabolic. Every negative elliptic forward
column has negative lower-left entry, so `tr(U_0 V_i^+)>0`. Every positive
elliptic reverse column has positive lower-left entry, so
`tr(U_0 V_i^-)<0`. These are exactly the required cost-derivative signs.
They hold for every central-monodromy period as well.

Moreover `det U_epsilon=-epsilon^2<0` for nonzero `epsilon`, and

\[
\operatorname{tr}(U_\epsilon V_i^\pm)
 =2\epsilon(V_i^\pm)_{11}-(V_i^\pm)_{21}.
\]

For any fixed finite period, all the strict signs persist for sufficiently
small nonzero `epsilon`. Thus correctly signed cost derivatives, central
holonomy and elliptic column orientation alone cannot eliminate the
remaining parabolic or hyperbolic sectors. A stronger theorem needs the
**exact magnitudes** in (10) or additional full PMP information.

These matrices are sign-compatible test multipliers, not asserted
stationary multipliers: no equality in (10), full Hamiltonian maximality,
competitive cost or closed PMP counterexample is claimed for them.

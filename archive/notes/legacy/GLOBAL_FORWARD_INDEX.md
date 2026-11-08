# Negative closed-period directions in the standard forward family

Date: 2026-11-07. Hand proof; no Lean compilation, Lake, typechecking, or CI.

## Theorem and scope

Let `k>=1`, `N=3k+1`, and consider the standard regular forward
smoothed `(6k+2)`-gon, with its `N` equal positive vertex arcs. In the
finite-dimensional class with the same forward word, **free initial
state**, and both actual twisted period endpoints, its constrained cost
Hessian has a negative subspace of dimension at least

\[
\boxed{2(k-1).}
\tag{1}
\]

Thus every standard member with `k>=2` admits arbitrarily nearby,
strictly cheaper, exactly closed trajectories with the same number and
order of positive arcs. The proof gives their tangent directions as
the real Fourier modes of frequencies `1,...,k-1`, and uses a rank-three
implicit function theorem to obtain the actual closed variations.

This is a global period variation. The initial state varies, so it
cannot be spliced into a fixed-endpoint local window. It neither proves
a negative Hessian for every six-piece window nor contradicts their
proved strict local minima. It does not extend to arbitrary asymmetric
forward stationary words or to words with reverse switches.

The entire standard family with `k>=2` was already excluded by the
strict cost comparison in
[REGULAR_FAMILY_COMPARISON.md](REGULAR_FAMILY_COMPARISON.md). Accordingly,
(1) is a verified instance of the closed-period index method, not a new
count of unresolved competitors and not a uniform switch bound. The
separate uniform-bound result is
[GLOBAL_CLOSED_VARIATION.md](GLOBAL_CLOSED_VARIATION.md).

## 1. Cyclic active margins resolve the state closure

Use determinant-one physical margins

\[
p_0p_1+p_1p_2+p_2p_0=4,\qquad p_i>0,
\]

and the triangular tangent basis from
[LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md):

\[
R=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\qquad
T_0(q)=\begin{pmatrix}q&0\\0&q^{-1}\end{pmatrix},\qquad
T_i(q)=R^{-i}T_0(q)R^i.
\tag{2}
\]

Number the forward arcs by `i=0,...,N-1`, with control label `i mod 3`.
Choose positive active margins `a_i`, periodically indexed modulo `N`.
Set

\[
b_i=\frac{4-a_{i-1}a_i}{a_{i-1}+a_i},\qquad
q_i=\frac{(a_{i-1}+a_i)(a_i+a_{i+1})}{a_i^2+4}.
\tag{3}
\]

The exact open feasibility domain is

\[
a_i>0,\qquad a_{i-1}a_i<4,\qquad q_i>1
\quad\text{for all }i\pmod N.
\tag{4}
\]

On arc `i`, the active, growing, and decreasing margins start at
`(a_i,b_i,a_{i-1})`. The vertex update gives the terminal ordered triple
`(a_i,a_{i+1},b_{i+1})`. Thus these arcs join exactly. Condition (4)
gives positive endpoint margins and hence positivity on every complete
arc by the explicit monotone vertex flows. The duration of arc `i` is
`a_i log(q_i)/2>0`.

The physical initial state has margins `(a_0,b_0,a_{N-1})`. Since
`N=1 mod 3`, its terminal margins are `(a_{N-1},a_0,b_0)`, exactly the
required twisted permutation. Therefore **state closure is identically
satisfied throughout the open domain (4)**. Both initial-state
coordinates are allowed to vary; fixing them here would change the
global problem.

Write

\[
A(q)=T_0(q)R^{-1}
=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix},\qquad
M(a)=A(q_0)\cdots A(q_{N-1}).
\tag{5}
\]

The actual tangent transition is

\[
F=T_0(q_0)T_1(q_1)\cdots T_{N-1}(q_{N-1})=M(a)R^N.
\]

Given the state closure, the frame endpoint `g(T)=R` is equivalent to
`F=R`; see [WORD_HOLONOMY.md](WORD_HOLONOMY.md). As `R^3=-I`, the
remaining three-dimensional endpoint condition is exactly

\[
\boxed{M(a)=(-I)^k.}
\tag{6}
\]

This is the full frame condition, not only its trace.

## 2. The exact cyclic action and the regular point

Let `J` denote physical cost divided by `sqrt(12)`. Summing the exact
arc cost in the active coordinates gives the cyclic action

\[
\boxed{
8J(a)=\sum_{i=0}^{N-1}\left[
3a_i a_{i+1}-4
-(a_i^2+a_{i+1}^2)\log(a_i+a_{i+1})
+a_i^2\log(a_i^2+4)\right].}
\tag{7}
\]

For a direct check, the arc formula is

\[
8J_i=a_i(a_{i-1}+a_{i+1}-b_i-b_{i+1})-a_i^2\log q_i.
\]

The nonlogarithmic terms associated with one adjacent pair combine to
`2a_i a_{i+1}-(a_i+a_{i+1})b_{i+1}=3a_i a_{i+1}-4`.
Also `log q_i=log(a_{i-1}+a_i)+log(a_i+a_{i+1})-log(a_i^2+4)`.
There are no endpoint terms in the cyclic sum, which proves (7).

For the standard regular member put

\[
\theta=\frac{\pi k}{N},\qquad
q=2\cos\theta,\qquad
a^2=\frac{4q}{4-q},\qquad a_i=a.
\tag{8}
\]

Here `1<q<=sqrt(2)<2`. All conditions (4) are strict, and (3) yields
the common factor `q` and
`b_i=a(2/q-1)>0`. The determinant-one matrix `A=A(q)` has eigenvalues
`exp(plus-or-minus i theta)`. Thus

\[
A^N=(-I)^k,
\]

which verifies the full matrix closure (6). These are the same regular
closed trajectories as in the cited standard-family construction.

## 3. The tangent space to actual closed variations

Put

\[
E=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
Z_i=\operatorname{Ad}_{A^i}E,\qquad
\kappa=2\theta=\frac{2\pi k}{N},\qquad
c_\kappa=\cos\kappa=\frac{q^2}{2}-1.
\tag{9}
\]

For a real variation `v=(v_i)` of the active margins, the first
derivative of `log q_i` at the regular point is

\[
z_i=\frac{v_{i-1}+(2-q)v_i+v_{i+1}}{2a}.
\tag{10}
\]

Since `(dA/d log q)A^{-1}=E`, the right-trivialized derivative of the
frame product is

\[
dM(v)M^{-1}=\sum_i z_iZ_i.
\tag{11}
\]

We now identify its exact rank and kernel, including the three matrix
constraints. Define

\[
U=A-\frac q2I.
\]

This is a nonzero elliptic traceless matrix, it commutes with `A`,
`U^2=-sin(theta)^2 I`, and `tr(UE)=q`. The adjoint action of `A`
fixes the line `R U` and has rotation eigenvalues `exp(plus-or-minus
i kappa)` on its two-dimensional complement `U^perp`. The component
of `E` on `R U` is nonzero because `tr(UE)=q!=0`; its component in
`U^perp` is nonzero because the hyperbolic matrix `E` cannot be a real
multiple of the elliptic matrix `U`. As `sin(kappa)!=0`, that latter
component and its adjoint translate span `U^perp`.

Consequently there are three linearly independent constant matrices
`Z_0^c,Z_1^c,Z_1^s` for which

\[
Z_i=Z_0^c+\cos(i\kappa)Z_1^c+\sin(i\kappa)Z_1^s.
\tag{12}
\]

Equation (11) vanishes exactly when the Fourier coefficients of `z`
at frequencies `0,k,N-k` vanish. The circular difference operator in
(10) acts on frequency `m` by the scalar

\[
\frac{2\cos(2\pi m/N)+2-q}{2a}.
\tag{13}
\]

At frequency zero its numerator is `4-q>0`; at frequencies `k,N-k`
it is `q(q-1)>0`. Thus these three coefficients of `z` vanish exactly
when the corresponding coefficients of `v` vanish. We have proved

\[
\boxed{\operatorname{rank}dM=3,\qquad
\ker dM=\{v:\widehat v_0=\widehat v_k=\widehat v_{N-k}=0\}.}
\tag{14}
\]

The real tangent space has dimension `N-3`. In particular all real
cosine and sine modes with frequencies `1,...,k-1` belong to it.

## 4. Stationarity and the exact endpoint multiplier

Differentiating (7) at the regular point gives a constant gradient

\[
J_{a_i}=g:=\frac{a}{16}(8+q-4\log q).
\tag{15}
\]

Every endpoint-tangent vector in (14) has zero sum, so the regular
point is stationary for the closed endpoint problem. Rank three gives
a unique endpoint multiplier `lambda` as a linear functional on
`sl_2`, determined by `dJ=lambda(dM M^{-1})`.

For clarity, this `lambda` is the finite-dimensional endpoint
multiplier, not the Pontryagin cost multiplier used in the uniform
switch-count note. Set

\[
A_0=8+q-4\log q,\qquad
\ell=\frac{qA_0}{2(4-q)^2},\qquad
\lambda(Y)=\frac\ell q\operatorname{tr}(UY).
\tag{16}
\]

Because `U` commutes with `A`, `lambda(Z_i)=ell` for all `i`.
Moreover (10) gives `sum_i z_i=(4-q)sum_i v_i/(2a)`, and
`ell(4-q)/(2a)=g` by (8), (15). Thus (16) is exactly the required
multiplier, with no unspecified choice or normalization.

## 5. The constrained second variation

For the straight active-margin variation `a_i(epsilon)=a+epsilon v_i`,
the second derivative of `log q_i` is

\[
w_i=-\frac{(v_{i-1}+v_i)^2+(v_i+v_{i+1})^2}{4a^2}
 +\frac{2(a^2-4)v_i^2}{(a^2+4)^2}.
\tag{17}
\]

At an endpoint-tangent vector, the exact second right-trivialized
frame variation is

\[
\mathcal K(v)=\sum_i w_iZ_i+
 \sum_{i<j}z_i z_j[Z_i,Z_j].
\tag{18}
\]

To derive it, differentiate the right logarithmic derivative
`sum_i z_i Z_i`. The derivative of its `i`th prefix conjugation is
`Z_i'=[sum_{j<i}z_j Z_j,Z_i]`. The square of the first logarithmic
derivative in `M''M^{-1}` vanishes when (11) is zero, giving (18).

The Hessian of the cost restricted to the closed endpoint manifold is
therefore

\[
Q(v)=v^t(\operatorname{Hess}J)v-\lambda(\mathcal K(v)).
\tag{19}
\]

This curvature correction is essential. The unconstrained cost Hessian
alone does not describe a closed-period variation.

### 5.1 The ambient action and the scalar second derivatives

Let `v` be a real Fourier mode of frequency `m` not equal to `0,k,N-k`,
and put

\[
\omega=\frac{2\pi m}{N},\qquad c=\cos\omega,\qquad
d=c-c_\kappa\ne0.
\tag{20}
\]

The second derivatives of (7), before division by eight, have diagonal
entry `-2 log q+(5/2)q-q^2/4-3` and neighboring off-diagonal entry
`3/2`. Hence

\[
\frac{v^t(\operatorname{Hess}J)v}{\|v\|^2}
 =h_J(c):=\frac{-2\log q+(5/2)q-q^2/4-3+3c}{8}.
\tag{21}
\]

Using `sum_i v_i v_{i+1}=c||v||^2`, equations (10), (17), and (8) give

\[
\frac{\sum_i w_i}{\|v\|^2}
 =\frac{4-q}{16q}\{q(q-2)-4(1+c)\},\qquad
\frac{\|z\|^2}{\|v\|^2}
 =\frac{4-q}{16q}(2c+2-q)^2.
\tag{22}
\]

These formulas also cover the real single mode `m=N/2` when `N` is
even. If the scalar in (13) happens to vanish at a different frequency,
the second formula simply gives `z=0`.

### 5.2 The commutator contribution

Trace invariance and the two-dimensional adjoint rotation give

\[
\lambda([Z_i,Z_j])
 =\frac{4\ell}{\sin\kappa}\sin\bigl(\kappa(j-i)\bigr).
\tag{23}
\]

Here is a direct normalization check. The left side depends only on
`j-i`, is an odd sinusoid in that difference by the rotation
decomposition (12), and at difference one

\[
A E A^{-1}=\begin{pmatrix}-1&2q^2\\0&1\end{pmatrix},\quad
\operatorname{tr}\bigl(U[E,AEA^{-1}]\bigr)=4q.
\]

Substitution in (16) gives `4ell`, which fixes (23).

For endpoint-tangent `z` define

\[
S(z)=\sum_{i<j}z_i z_j\sin\bigl(\kappa(j-i)\bigr).
\]

It is invariant under a cyclic shift of its entries. Indeed moving
`z_0` from the first to the last position changes the sum by
`-2 z_0 sum_j z_j sin(kappa j)=0`; this last Fourier coefficient
vanishes by (11)--(12). The same holds after every subsequent shift.
Average over all `N` shifts. For a real frequency-`m` mode its cyclic
correlation is `sum_i z_i z_{i+r}=cos(omega r)||z||^2`, so

\[
\begin{aligned}
\frac{S(z)}{\|z\|^2}
 &=\sum_{r=1}^{N-1}\left(1-\frac rN\right)
     \sin(\kappa r)\cos(\omega r)\\
 &=\frac14\left\{\cot\frac{\kappa+\omega}{2}
                 +\cot\frac{\kappa-\omega}{2}\right\}
 =\frac{\sin\kappa}{2d}.
\end{aligned}
\tag{24}
\]

If `z=0`, interpret the corresponding equality without division as
`S(z)=(sin(kappa)/(2d))||z||^2`.
For a self-contained check of the finite trigonometric sum, if
`zeta^N=1` and `zeta!=1`, differentiating the finite geometric sum gives

\[
\sum_{r=1}^{N-1}\left(1-\frac rN\right)\zeta^r
 =\frac\zeta{1-\zeta}.
\]

Its imaginary part is `cot(arg(zeta)/2)/2`. Apply this to
`zeta=exp(i(kappa+omega))` and `exp(i(kappa-omega))`; neither equals
one for the frequencies under consideration. The final equality in
(24) is the elementary cotangent addition identity.

Equations (23)--(24) show that the commutator contribution to
`lambda(mathcal K(v))` is `(2ell/d)||z||^2`. The cyclic averaging
argument applies to the entire endpoint-tangent space. Its polarization
is a real circulant symmetric quadratic form; therefore distinct real
Fourier frequency spaces are orthogonal for this contribution. The
same is manifest for the other terms in (19). Thus the calculation
diagonalizes `Q` on the whole endpoint-tangent space, not just on a
chosen list of individual vectors.

### 5.3 The exact eigenvalue and its useful sign form

Substitute (16), (21), (22), and (24) into (19):

\[
\frac{Q(v)}{\|v\|^2}
 =h_J(c)
 -\frac{A_0\{q(q-2)-4(1+c)\}}{32(4-q)}
 -\frac{A_0(2c+2-q)^2}{16(4-q)d}.
\tag{25}
\]

Replacing `c` by `d+q^2/2-1` and collecting the powers `d,1,d^{-1}`
gives the equivalent formula

\[
\boxed{
\frac{Q(v)}{\|v\|^2}
 =-\frac{(q-1-\log q)d}{2(4-q)}
  -\frac{B(q)}{8(4-q)}
  -\frac{q^2(q-1)^2(8+q-4\log q)}{16(4-q)d},}
\tag{26}
\]

where

\[
B(q)=(-7q^2+8q+8)\log q+3q^3+9q^2-36q+24.
\tag{27}
\]

One can check this collection without a large expansion:
`2c+2-q=2d+q(q-1)` and
`q(q-2)-4(1+c)=-q^2-2q-4d`.
The coefficient of `d` in (25) is
`3/8-A_0/(8(4-q))=-(q-1-log q)/(2(4-q))`.
The constant numerator after multiplication by `32(4-q)` is
`-4B(q)`. The inverse-`d` term is the last term of (26).

## 6. A hand sign certificate and genuine cheaper closed trajectories

Every coefficient in (26), apart from the displayed signs and powers
of `d`, is positive for `1<q<=sqrt(2)`:

\[
q-1-\log q>0,\qquad
8+q-4\log q\ge12-3q>0,
\]

and `B(q)>0`. For the last claim,

\[
B(1)=B'(1)=0,\qquad
B''(q)=-14\log q+18q-3+\frac8q-\frac8{q^2}.
\]

Using `log q<=q-1` gives the strictly positive lower bound

\[
B''(q)\ge4q+11+\frac{8(q-1)}{q^2}>0
\quad(q>1).
\tag{28}
\]

Twice integrating from one proves `B(q)>0` for every `q>1`.

For the frequencies `m=1,...,k-1`,

\[
0<\omega=\frac{2\pi m}{N}<\kappa<\pi,
\qquad d=\cos\omega-\cos\kappa>0.
\]

All three terms in (26) are therefore strictly negative. Each such
frequency supplies two independent real modes, a cosine and a sine.
They are distinct from `0,k,N-k` and from the possible single
frequency `N/2`. The Fourier orthogonality proved above shows that
their direct sum is a negative definite subspace. Its dimension is
`2(k-1)`, proving (1).

Finally, this is an actual endpoint-preserving variation theorem.
The endpoint rank is three by (14), and the target matrix in (6) is
an interior point of `SL_2`. The implicit function theorem makes its
exact local level set a smooth manifold with the displayed tangent
space. Every negative direction is tangent to a smooth curve on that
level set. Stationarity and (19) give a strictly negative second
derivative of cost along that curve, hence strictly lower cost for
all sufficiently small nonzero parameters. The strict feasibility
conditions (4) survive by openness, all physical durations stay
positive, and both the state and frame endpoints remain exact.

The original regular member has physical cost less than `pi` by
[REGULAR_FAMILY_COMPARISON.md](REGULAR_FAMILY_COMPARISON.md). The nearby
lower-cost trajectories do too. The finite-piece geometric bridge in
[MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md), Section 5, uses
this strict `pi` bound, star positivity, and the actual endpoints to
prove primary winding and convex balanced realization. Thus the
variations are genuine nearby closed geometric competitors as well
as solutions of the endpoint equations.

## Validation boundary and the unproved general step

Equations (3)--(7), the three endpoint Fourier coefficients, the
explicit multiplier, the finite commutator sum, and the sign certificate
(28) provide the hand proof. No numerical sign test or symbolic output
is a premise. No Lean source, compilation, typecheck, Lake, CI, or kernel
validation is involved.

Two independent mathematical reviews on 2026-11-07 rederived the cyclic
state and frame closure, the action and its derivatives, the three
Fourier endpoint constraints, the multiplier and endpoint-curvature
correction, the commutator normalization, the finite trigonometric sum,
and the sign calculation. Both found no substantive gap. This records
hand review and does not assert kernel validation.

A general index argument would have to control arbitrary stationary
closed words, with their asymmetric coefficients and all endpoint
constraints. The constant coefficients and cyclic Fourier diagonalization
used here are specific to the regular family. No continuation of the
index to all asymmetric words, and no exclusion of every large minimizing
word, is asserted. The result demonstrates explicitly how variation of
the initial state and the full period can produce negative directions
that a fixed-endpoint local-window problem need not possess.

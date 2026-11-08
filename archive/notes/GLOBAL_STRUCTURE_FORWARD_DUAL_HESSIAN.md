# A dual scalar Hessian for the complete forward index problem

Date: 2026-11-07 UTC. Exact reduction and an open sign target.
No Lean, Lake, typechecking, or CI. This note does **not** close F.

The input is a competitive, normal, entirely forward period in the
strict-star domain, with all actual twisted endpoints, free initial
state, and the geometric sector conditions. Use
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md)
and [GLOBAL_STRUCTURE_FORWARD_ACUTE](GLOBAL_STRUCTURE_FORWARD_ACUTE.md).
Their notation is retained, except that the new positive variables `b_i`
below are auxiliary costate variables, not the third physical margin.

## 1. A second positive margin sequence

Write

\[
s_i=a_i+a_{i+1},\quad K_i=a_i^2+4,\quad
q_i(a)=s_{i-1}s_i/K_i,\quad c=\sqrt{\det U}>0.
\]

After applying `S^(1/2)` to the Jacobi vector sequence, let `delta_i`
be its positively oriented angle from index `i-1` to index `i`.
The acute lemma gives `0<delta_i<pi/2`. Put

\[
\boxed{b_i=2\cot\delta_i>0.}
\tag{1}
\]

The Wronskian, Gram determinant and recurrence imply

\[
e_i=\frac{c b_i}{2K_i},\qquad
d_i=\frac{c(b_i+b_{i+1})}{2s_i^2}.
\tag{2}
\]

For the second identity, take the scalar product of `Hy=0` with
`S y_i` to get `s_i^2 d_i=K_i e_i+K_{i+1}e_{i+1}`.
Substituting (2) in the Gram determinant gives

\[
\boxed{q_i(b)=q_i(a)^2.}
\tag{3}
\]

Define `ell(a)=(log q_i(a))_i` and its symmetric derivative `B(a)`:

\[
B(a)_{ii}=\frac1{s_{i-1}}+\frac1{s_i}-\frac{2a_i}{K_i},
\qquad B(a)_{i,i+1}=\frac1{s_i}.
\tag{4}
\]

The original exact normal stationarity equations become

\[
\boxed{\nabla J(a)=c B(a)b,\qquad \ell(b)=2\ell(a).}
\tag{5}
\]

Indeed the right side of the first equation has component
`c[(b_{i-1}+b_i)/s_{i-1}+(b_i+b_{i+1})/s_i-2a_i b_i/K_i]`,
which is precisely `2(s_{i-1}d_{i-1}+s_i d_i-2a_i e_i)`.

## 2. A scalar potential and the missing angle equation

The potential

\[
\Phi(a)=\sum_i s_i\log s_i-\sum_i a_i\log K_i
        -4\sum_i\arctan(a_i/2)
\tag{6}
\]

satisfies `grad Phi=ell` and `Hess Phi=B`. Also

\[
\Phi(b)-b\cdot\ell(b)=-4\sum_i\arctan(b_i/2).
\tag{7}
\]

Let `n` be the actual projective winding, so `sum delta_i=n pi`.
For the geometrically eligible pure-forward period with `N=3k+1`,
the winding argument in
[MIXED_GLOBAL_PROJECTIVE_WINDING](MIXED_GLOBAL_PROJECTIVE_WINDING.md)
gives `n=k`. Keep `n` visible in the algebra. Define

\[
\boxed{
\Psi(a,b,c)=J(a)-c\,b\cdot\ell(a)
 +\frac c2\Phi(b)+c(N-2n)\pi.}
\tag{8}
\]

Equations (5) are exactly the `a` and `b` critical equations of
`Psi`. Using (7), the `c` equation is

\[
-2\sum_i\arctan(b_i/2)+(N-2n)\pi=0,
\]

which is exactly `sum delta_i=n pi`, by (1). Thus the complete forward
stationary period supplies a critical point of (8). This observation
does not assert that arbitrary critical points of (8) automatically
satisfy the omitted whole-arc PMP or geometric inequalities.

## 3. The full Hessian blocks

Put `C=grad J`, `D=B(b)`, and

\[
M=J''(a)-c\,D B(a)[b].
\]

Here `D B(a)[b]` denotes the directional derivative of the matrix
`B` at `a` in the vector direction `b`; it is symmetric. At a critical
point, in variables `(v,w,gamma)=(delta a,delta b,delta c)`,

\[
\boxed{
\operatorname{Hess}\Psi=
\begin{pmatrix}
M&-cB(a)&-C/c\\
-cB(a)&(c/2)D&0\\
-C^T/c&0&0
\end{pmatrix}.}
\tag{9}
\]

For `j_i=J_{a_i a_{i+1}}` and `t_i=b_i+b_{i+1}`, its adjacent
two-by-two block in the ordering `(a_i,b_i)` is

\[
R_i=\begin{pmatrix}
j_i+2d_i&-c/s_i\\
-c/s_i&c/(2t_i)
\end{pmatrix},\qquad
\det R_i=-\frac{c\beta_i}{2t_i}<0,
\tag{10}
\]

where `beta_i=2d_i-j_i`. The strict sign uses the separate normal
forward-switch transversality argument. Formula (10) alone is not an
inertia bound for the cyclic Hessian.

The diagonal of `M` is explicitly

\[
M_{ii}=J_{a_i a_i}
 +c\left[\frac{t_{i-1}}{s_{i-1}^2}
          +\frac{t_i}{s_i^2}
          +\frac{2b_i(4-a_i^2)}{K_i^2}\right].
\tag{11}
\]

## 4. The doubled-angle Jacobi matrix and the index subtraction

Vary the positive elliptic multiplier `U` with its determinant fixed,
holding the frame prefixes fixed. The resulting two independent
variations of `b_i=tr(U Z_i)/c`, where `Z_i=Ad_{P_i}diag(1,-1)`,
belong to `ker D` by (3). In Euclidean coordinates for the positive
Gram form, write the switch-vector angles as `phi_i`, with
`phi_i-phi_{i-1}=delta_i`. A kernel-vector pair is, up to a fixed
invertible real change of its two components,

\[
z_i=\frac2{\sin\delta_i}
 \begin{pmatrix}
\cos(\phi_{i-1}+\phi_i)\\
\sin(\phi_{i-1}+\phi_i)
\end{pmatrix}.
\tag{12}
\]

Its adjacent angle increments are `delta_i+delta_{i+1}` in `(0,pi)`,
and

\[
\det(z_i,z_{i+1})=2(b_i+b_{i+1})>0.
\]

Thus it has winding `2n` in units of `pi`. The elementary fixed-kernel
Jacobi homotopy in the winding note gives

\[
\boxed{(n_+(D),n_0(D),n_-(D))
 =(2n-1,\,2,\,N-2n-1).}
\tag{13}
\]

The endpoint rank for `N>=7` is the already proved rank-three theorem
on state-closed active margins. The three frame derivatives can be
paired with `U` and with its two independent determinant-preserving
variations. Equivalently the actual tangent equations are

\[
C\cdot v=0,\qquad B(a)v\perp\ker D.
\tag{14}
\]

The first is not an optional extra cost constraint: at stationarity
it is the frame derivative paired with the original normal multiplier.

For a closed tangent, differentiate (3) while keeping `U` fixed in
the frame coordinates. The resulting periodic variation satisfies

\[
D w=2B(a)v.
\tag{15}
\]

The full frame-curvature-corrected cost Hessian therefore equals

\[
\boxed{Q(v)=v^T Mv
 -2c\,(B(a)v)^T D^\dagger B(a)v,\qquad v\text{ satisfying (14)}.}
\tag{16}
\]

For clarity, this also follows directly by differentiating the normal
frame gradient `cB(a)b`: its derivative is
`c D B(a)[b] v+c B(a)w`. The contribution from the second term is
`2c (B(a)v)^T D^dagger B(a)v`, by (15). Kernel-basis changes in `w`
drop out by (14). No endpoint curvature has been omitted.

Eliminate the nonzero part of the `D` block in (9). Its two kernel
directions and the `c` coordinate pair with the three independent
constraints (14). They give three positive and three negative
directions by the elementary bordered-Hessian inertia formula. Hence

\[
\boxed{
n_-(Q)=n_-(\operatorname{Hess}\Psi)
       -(N-2n-1)-3.}
\tag{17}
\]

In particular, an `N`-dimensional negative subspace for (9) would give
`n_-(Q)>=2n-2`, and for `n=k>=2` would close the pure-forward case.
This last negative-subspace assertion is still open.

## 5. A concrete negative-graph candidate and its limitation

Set `T=diag(2b_i/a_i)` and restrict (9) to `w=Tv`, `gamma=0`.
The resulting symmetric matrix is

\[
G=M-c(B(a)T+T B(a))+(c/2)T D T.
\tag{18}
\]

Its exact off-diagonal entries have the useful sign

\[
\boxed{G_{i,i+1}=-\beta_i
 -\frac{2c a_i a_{i+1}}{s_i^2t_i}
 \left(\frac{b_i}{a_i}-\frac{b_{i+1}}{a_{i+1}}\right)^2<0.}
\tag{19}
\]

The exact scaling identity is

\[
\boxed{
(Ga)_i=\frac{
16c b_i(a_i^4+8a_i^2-4b_i^2)-8a_i^2(b_i^2+4)}
{a_i(a_i^2+4)^2(b_i^2+4)}.}
\tag{20}
\]

To verify it without expanding every entry, use

\[
B(a)a=8/K,
\quad D B(a)[b]a+B(a)b=-16ab/K^2,
\quad J''a=C-8a/K^2,
\quad B(b)b=8/(b^2+4).
\]

Equations (19)--(20) do **not** prove `G<0`. In particular a
pointwise negative-diagonal or negative-diagonal-dominance claim using
only one arc's stationarity, the two switching derivative signs, and
the two third-control gaps is not valid. Such local conditions can
allow a positive diagonal of (18); compatibility of neighboring
stationarity equations and of the full period cannot be discarded.
The candidate graph is retained as a precise target, not as an asserted
negative subspace. A different graph may be needed.

## Supplementary checker

Run

```
python explorations/global_structure_forward_dual_certificate.py
```

It verifies the local scalar and matrix identities used above. The
geometric winding, actual endpoint interpretation, kernel rank, and
finite-dimensional inertia argument remain the displayed hand arguments.

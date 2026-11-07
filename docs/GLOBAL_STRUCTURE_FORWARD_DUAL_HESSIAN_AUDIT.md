# Independent audit of the forward dual scalar Hessian

Date: 2026-11-07 UTC. Independent internal hand review of
[GLOBAL_STRUCTURE_FORWARD_DUAL_HESSIAN](GLOBAL_STRUCTURE_FORWARD_DUAL_HESSIAN.md).
No Lean, Lake, typechecking, or CI was run.

## Verdict and scope

The auxiliary positive sequence, scalar stationary potential,
doubled-angle Jacobi kernel, fixed-multiplier curvature formula,
and three-constraint inertia subtraction are correct. In particular,
on the stated rank-three complete forward domain,

\[
\operatorname{ind}_-(Q)
=\operatorname{ind}_-(\operatorname{Hess}\Psi)
 -(N-2n-1)-3.
\]

An `N`-dimensional negative subspace of the scalar Hessian would give
the desired `2(n-1)` closed negative directions. That negative
subspace is not proved in the note. The displayed graph identities,
including their strict off-diagonal signs, do not close F.

## 1. Gram normalization and the auxiliary sequence

The actual positive definite form `S=-J_0U` has
`det S=det U=c^2`. Applying its positive square root to the forward
Jacobi vectors changes their adjacent determinant from `1/K_i` to
`c/K_i`. With the acute-angle input this gives

\[
e_i=(c/K_i)\cot\delta_i=c b_i/(2K_i),\qquad b_i=2\cot\delta_i>0.
\]

Pairing the actual recurrence with its middle vector gives the second
formula for `d_i`. Substituting those two formulas into the Gram
determinant identity gives exactly

\[
\frac{(b_{i-1}+b_i)(b_i+b_{i+1})}{b_i^2+4}
=\left(\frac{s_{i-1}s_i}{K_i}\right)^2.
\]

Thus no determinant or factor-of-two normalization is missing in
`q_i(b)=q_i(a)^2`. These `b_i` are auxiliary costate quantities;
they are not asserted to satisfy the physical third-margin or
strict-star inequalities of an independent control trajectory.

The component formula for `c B(a)b` agrees exactly with the common
normal boundary identity in the forward Gram variables. All three
diagonal and off-diagonal contributions in `B(a)` are required for
this agreement.

## 2. The scalar critical point and its full Hessian

Differentiating the proposed potential `Phi` gives `ell=log q`.
The nonlogarithmic derivative terms cancel because
`2-2a^2/(a^2+4)-8/(a^2+4)=0`. In its Euler expression, all edge
and vertex logarithms cancel, leaving exactly
`Phi(b)-b dot ell(b)=-4 sum arctan(b_i/2)`.

The `c` critical equation therefore supplies the missing angular
sum. Since every `delta_i` is acute,
`arctan(b_i/2)=pi/2-delta_i` with no branch ambiguity. The scalar
critical equation is precisely `sum delta_i=n pi`.

The `a,b,c` Hessian blocks follow by ordinary differentiation. The
contraction `D B(a)[b]` is legitimate because `B=Hess Phi`, so its
third derivative is fully symmetric. The `b,c` block vanishes at a
critical point, whereas the `a,c` block is `-C/c`; discarding the
latter would lose the frame constraint paired with the original
normal multiplier.

For the adjacent two-by-two block, one has
`M_(i,i+1)=j_i+c t_i/s_i^2=j_i+2d_i`. Consequently its determinant
is exactly `-c beta_i/(2t_i)`. The strict sign follows from the
separately proved forward transversality, rather than an added
generic-switch assumption. The diagonal formula for `M` has the
correct derivative `2b_i(4-a_i^2)/K_i^2`.

## 3. Fixed determinant variations and the doubled-angle kernel

Keep the actual frame prefixes fixed and vary the positive elliptic
multiplier with its determinant fixed. In coordinates in which the
Gram form is Euclidean, such a variation is a symmetric trace-zero
two-by-two matrix. If the adjacent vector angles are `alpha,beta`,
its bilinear evaluation is a linear combination of
`cos(alpha+beta)` and `sin(alpha+beta)`.

Using the Wronskian factor `c/K_i` gives the stated kernel pair

\[
z_i=\frac2{\sin\delta_i}
 (\cos(\phi_{i-1}+\phi_i),\sin(\phi_{i-1}+\phi_i))^T.
\]

Their adjacent determinant is

\[
\frac{4\sin(\delta_i+\delta_{i+1})}
 {\sin\delta_i\sin\delta_{i+1}}
=2(b_i+b_{i+1})>0.
\]

Thus the two determinant-preserving multiplier variations really are
independent. Differentiating `ell(b)=2ell(a)` with the prefixes fixed
puts them in `ker D`. The nonzero neighboring coefficients of `D`
bound its kernel dimension by two, so they span the kernel.

The adjacent angular increment is `delta_i+delta_(i+1)`, not one
original increment. Their sum is `2n pi`. Each is less than `pi`
by the acute hypothesis, so the positive-Wronskian homotopy applies
with winding `2n`. The canonical inverse-Wronskian coefficient is
`1/(2t_i)`, whereas the off-diagonal coefficient of `D` is `1/t_i`.
Hence `D` is twice that canonical Jacobi operator, a positive scaling
which leaves its inertia unchanged. This verifies

\[
(n_+(D),n_0(D),n_-(D))=(2n-1,2,N-2n-1).
\]

The doubled-angle vectors are periodic even when the original vectors
are antiperiodic: their lifted angle changes by `2n pi`. This agrees
with the periodic auxiliary sequence and with the stated Fourier count.

## 4. The actual frame tangent and the fixed-multiplier curvature

The original positive elliptic multiplier `U`, together with its two
independent determinant-preserving variations, spans the full
three-dimensional traceless frame-covector space. Pairing the actual
frame derivative with that basis gives respectively

\[
C\cdot v=0,\qquad B(a)v\perp\ker D.
\]

Thus the first equation is one of the three frame constraints. It is
not an extra condition imposed merely to force a favorable cost
derivative. The established full rank on the `N>=7` state-closed
forward family makes all three conditions independent.

Along an actual closed family keep `U` fixed as the multiplier of the
central frame-product constraint. The varying prefixes then determine
`b(a)` with fixed `c`; the exact identity for `q(b)` gives
`D w=2B(a)v`. This use of a fixed multiplier is correct even though
the corresponding physical initial-state trivialization varies. In
the central frame chart those basis-derivative terms multiply the
vanishing first frame derivative of the closed tangent.

At every point of this nearby closed family the covector pairing with
the frame derivative has gradient `c B(a)b(a)`. Differentiating that
gradient at the original stationary point gives

\[
c\,D B(a)[b]v+cB(a)w.
\]

Subtracting it from `J''` gives the displayed corrected cost Hessian.
On a closed tangent the range solution is
`w=2D^dagger B(a)v`, and any added kernel component has zero pairing
with `B(a)v`. This proves the coefficient `-2c` in the curvature
term and its independence of the choice of range solution. No
constant-prefix or zero-curvature assumption was made while varying
the actual trajectory.

## 5. All three bordered-Hessian pairs are present

Eliminating the nonzero part of `(c/2)D` contributes exactly
`N-2n-1` negative directions, since `c>0`. Its two kernel directions
and the scalar `c` coordinate then couple to the three independent
frame constraints just identified. The resulting bordered block has
three positive and three negative directions, independently of its
upper-left block. The remaining quadratic form is precisely `Q` on
the closed tangent space.

The subtraction of three in the index formula is therefore necessary.
There is no unused rotation coordinate in this scalar formulation:
the common angular rotation was already removed in passing from
vectors to the angle differences `b_i`. A dimension check gives
`(N-2)+6+(N-3)=2N+1`, the full dimension of `(a,b,c)`.

## 6. Candidate graph and validation

The candidate graph formula has been independently checked from the
block Hessian. Its off-diagonal entry and scaling identity agree with
the displayed expressions. In particular, using `T a=2b`,
`B(a)a=8/K`, and the directional derivative of that identity cancels
the two `C` terms and gives exactly the numerator in equation (20).

These algebraic facts leave the full negative-subspace sign open.
Negative off-diagonal entries alone do not make a cyclic symmetric
matrix negative definite, and the note correctly records the failure
of a one-arc local diagonal shortcut. Neither the doubled-angle
inertia nor the bordered-Hessian identity supplies that missing sign.

The command

```
python3 explorations/global_structure_forward_dual_certificate.py
```

passes all eight exact checks with Python 3.12.14 and SymPy 1.14.0.
The fixed-multiplier, global endpoint, doubled-winding, and rank-three
arguments reviewed above are the additional hand interfaces. This is
internal mathematical review, not external peer review or kernel
validation.

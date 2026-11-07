# The geometric lift fixes the winding of the collapsed switch vectors

Date: 2026-11-07 UTC. Hand topological interface. No Lean, Lake,
typechecking, numerical angle integration, or CI.

## Statement and scope

Consider an actual finite positive normal minimizing period with its
balanced convex-disk realization and the complete twisted endpoints.
Let `N` be its number of arcs and `m` the number of double reverse runs;
put `m=0` in the pure-forward case. The reverse-run theorem has already
excluded every other reverse-run length and the entirely reverse case.

Collapse the two antiparallel turn identifications around each reverse
run, and change the sign of the switch-vector representative across
each remaining reverse-centre edge. Then all adjacent determinants are
positive. Join successive projective directions by their strictly
positive angle increments less than `pi`. The lifted total angle is

\[
\boxed{n\pi,\qquad n=\frac{N-m-1}{3}.}
\tag{1}
\]

The collapsed cycle has `P=N-2m` nodes and boundary sign `(-1)^n`.
For a pure-forward period `N=3k+1`, (1) is `n=k`. For an all-short
mixed period `(--+)^m`, it is

\[
n=(2m-1)/3.
\tag{2}
\]

This is a winding theorem and an ordinary Jacobi inertia calculation,
not a constrained cost-index theorem. It fixes the
lifted branch that is not determined by central monodromy alone. The
geometric radial-sector input is used explicitly. The result is not
asserted for an arbitrary local window, or for a nongeometric matrix
trajectory with an unspecified winding class.

## 1. The tangent frame has the same relative homotopy class as the physical frame

Write the physical state as `X=Phi(x,y)`, and let `X_*=J` be the
centroid state. The standard rotation `R=exp(pi J/3)` commutes with
`X_*`. The tangent frame is exactly

\[
F(t)=X(0)^{-1}g(t)X(t),\qquad F(0)=I,\quad F(T)=R.
\tag{3}
\]

For `0<=s<=1` put

\[
Y_s(t)=(1-s)X(t)+sX_*,\qquad
X_s(t)=Y_s(t)/\sqrt{\det Y_s(t)}.
\tag{4}
\]

This is an equivariant contraction through the same determinant-one
positive elliptic state orbit. In physical coordinates
`-tr(JX)/2>=1`, so

\[
\det Y_s=(1-s)^2+s^2-s(1-s)\operatorname{tr}(JX)\ge1.
\]

Each strict-star margin is linear and positive on both `X` and
`X_*`; the convex combination and subsequent positive scalar division
keep it positive. Since `X_*` commutes with `R`,

\[
X_s(T)=R^{-1}X_s(0)R.
\]

Consequently

\[
F_s(t)=X_s(0)^{-1}g(t)X_s(t)
\tag{5}
\]

is a homotopy with endpoints fixed at `I,R`. At `s=1` it is
`X_*^-1 g(t) X_*`. The conjugating matrix `X_*` can itself be
connected to the identity inside the rotation subgroup commuting with
`R`. Thus (5) proves that `F` and `g` have the same relative homotopy
class. This homotopy computes a class of frame paths; it is not being
used as a family of trajectories satisfying the control equations.
The state motion in (3) introduces no unexamined extra winding.

The actual geometric radial-sector statement in
[MINIMIZER_WINDOW_AUDIT, Section 3](MINIMIZER_WINDOW_AUDIT.md#3-eligibility-including-the-normalized-radial-sectors)
says that `g(t)v_j`, for `0<t<T`, lies strictly in the sector from
the initial contact `v_j` to its successor `Rv_j`. Its continuous
angle therefore reaches the successor without an extra turn.
For a fixed nonzero vector, the map taking an `SL_2(R)` matrix to
the direction of its image has contractible fibres; equivalently,
after fixing its first column the second column lies on an affine
line with the determinant constraint. This direction detects the
relative homotopy class of a frame path. Hence `g`, and by (5) `F`,
has the class of the canonical path from `I` to `R`.

No radial-sector condition is inferred from control labels here. It
comes from the actual convex boundary and the actual full-period
normalization.

## 2. The central lift of the cyclic product

Now pass to the orientation-reversing triangular coordinates, where

\[
R=\begin{pmatrix}0&1\\-1&1\end{pmatrix}.
\]

Its canonical one-parameter subgroup turns clockwise; three copies
give a clockwise half turn. Let `epsilon_i` be the switch signs and
write

\[
\sum_i\epsilon_i=3k+1.
\tag{6}
\]

The canonical positive factor path is
`T_0(q)=exp((log q)diag(1,-1))`. Use the canonical paths of `R`
and `R^-1` to form the cyclic product

\[
P_N=\prod_i T_0(q_i)R^{-\epsilon_i}.
\]

The exact factorization `F=P_N R^(sum epsilon_i)` holds also for
these chosen lifted paths. Indeed the control-`i` factor is the
canonical conjugate `R^-i T_0(q) R^i`; multiplying these expressions
telescopes the successive label powers. Replacing an integer label by
its residue modulo three changes the conjugating factor only by the
central matrix `-I`, which changes neither the conjugated factor nor
its path.

Section 1 identifies the lift of `F` with the canonical lift of `R`.
Therefore the cyclic product has the central lift

\[
\widetilde P_N=\widetilde R^{\,1-(3k+1)}
=\widetilde R^{-3k}.
\tag{7}
\]

Its net angle on any nonzero vector is exactly `k pi`, and its
matrix endpoint is `(-1)^k I`. A scalar trace or matrix centrality
without the geometric class from Section 1 would determine only a
parity, not the integer in (7).

## 3. The switch-vector interpolation has exactly that lifted angle

Use the actual vectors from
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md):

\[
y_i=\begin{cases}
q_iP_i e_1/(a_i+a_{i+1}),&\epsilon_i=+1,\\
P_i e_2/(q_i(a_i+a_{i+1})),&\epsilon_i=-1.
\end{cases}
\tag{8}
\]

All scalar coefficients are positive. At the end of the preceding
factor, use basis vector `e_1` for a forward sign and `e_2` for a
reverse sign. When the basis vector changes, interpolate `e_1 -> e_2`
by the positive quarter turn, and `e_2 -> e_1` by the negative
quarter turn. Then traverse the canonical `R^-epsilon_(i-1)` factor
and the next `T_0(q_i)` factor. The latter only positively rescales
the selected eigenvector and adds no angle.

Over a period this basis-vector path is a loop of winding zero: its
two types of quarter turns occur equally often and reverse one another.
The group path has central lift (7). Its action on this zero-winding
basis loop therefore gives total switch-vector angle `k pi`.

The branches of the individual increments can also be checked directly
before applying the determinant-one prefix:

| Incident signs | Canonical interpolation | Signed angle branch |
|---|---|---|
| `++` | `e_1 -> R^-1 e_1=e_1+e_2` | strictly between `0` and `pi` |
| `--` | `e_2 -> R e_2=e_1+e_2` | strictly between `-pi` and `0` |
| `+-` | `e_1 -> e_2 -> R^-1 e_2=-e_1` | exactly `+pi` |
| `-+` | `e_2 -> e_1 -> R e_1=-e_2` | exactly `-pi` |

An orientation-preserving prefix keeps the branch and the sign of a
monotone angle path; an antipodal endpoint keeps its exact half turn.
Thus the Wronskian signs are being matched with the correct lifted
product branches, rather than merely assigned after the fact.

## 4. Collapse the turns and make every remaining Wronskian positive

At a turn the exact vector relation is `y_i=-y_(i-1)`. Collapse
the corresponding projective identification. The number of `+-`
turns equals the number of `-+` turns, so removing their signed
half turns changes the total lifted angle by zero.

Every reverse run now has length two, so it leaves one `--` edge;
there are exactly `m` such edges. Across each, change the sign of
the succeeding representative. A raw clockwise angle `-theta`, with
`0<theta<pi`, becomes the positive angle `pi-theta`. Each such
change adds exactly `pi` to the lifted sum. All `++` increments
already have their positive branches.

The collapsed, gauged total angle is consequently

\[
(k+m)\pi.
\tag{9}
\]

There are `2m` reverse switches, hence `sum epsilon_i=N-4m`.
Combining this with (6) gives

\[
k+m=(N-m-1)/3,
\]

which proves (1). The turn identifications remove `2m` nodes, giving
`P=N-2m`, and the representative sign after one cycle is
`(-1)^(k+m)=(-1)^n`, as asserted.

The same lifted count holds after applying any one orientation-
preserving linear map, in particular the positive square root of the
quadratic form `S`. Thus it is the winding relevant to the Gram and
Jacobi formulations, not a winding in an unrelated coordinate system.

## 5. The corresponding ordinary Jacobi inertia is fixed

This section concerns a real symmetric scalar Jacobi matrix, not the
constrained cost Hessian. Write `v_0,...,v_(P-1)` for the collapsed,
gauged switch vectors, extended by `v_(i+P)=(-1)^n v_i`. They have

\[
W_i=\det(v_{i-1},v_i)>0.
\]

Define

\[
c_i=1/W_i,\qquad
b_i=-\frac{\det(v_{i-1},v_{i+1})}{W_iW_{i+1}},
\qquad
(Hz)_i=c_i z_{i-1}+b_i z_i+c_{i+1}z_{i+1},
\tag{10}
\]

on the same `(-1)^n` boundary condition. The determinant identity
in two dimensions gives

\[
c_i v_{i-1}+b_i v_i+c_{i+1}v_{i+1}=0.
\]

Thus its two coordinate sequences lie in the kernel. They are
independent by `W_i>0`, and any solution of the second-order
recurrence is determined by two adjacent values. Consequently
`dim ker H=2`. For `P=2`, both cyclic neighboring contributions are
included with their boundary signs, as in the two-centre calculation;
the same recurrence statement is valid.

The off-diagonal normalization is the one in the actual frame
recurrences: their positive Wronskians are `1/K_i` and their positive
off-diagonal coefficients are `K_i`. Hence (10) is the ordinary
Jacobi matrix in the pure-forward formulation and, after the displayed
gauge, in the all-short formulation of MIXED_GLOBAL_SHORT_RUN_PERIOD.
For other mixed formulations it specifies the canonical scalar
operator of the collapsed switch vectors; a cost-Hessian reduction
still has to retain the dependence of all its coefficients.

Let `theta_i in (0,pi)` be the successive positive angle increments.
By (1), `sum theta_i=n pi`, so `0<n<P`. Write each vector as a
positive radius times its lifted angular unit vector. Interpolate the
logarithms of its radii linearly to zero, and interpolate every
`theta_i` linearly to `n pi/P`. The open conditions `0<theta_i<pi`
and the sum `n pi` are preserved. This produces a continuous
deformation of the vector sequence to the regular sequence

\[
v_i=(\cos(i\theta),\sin(i\theta)),\qquad
\theta=n\pi/P,
\]

up to a harmless common initial rotation. At every stage define the
Jacobi coefficients by (10). Its kernel has exactly dimension two
throughout the deformation. Its other real eigenvalues therefore
cannot cross zero, and its positive and negative indices are constant.

At the regular endpoint,

\[
c_i=c=1/\sin\theta>0,\qquad b_i=-2c\cos\theta.
\]

The boundary Fourier frequencies are
`omega_j=(2pi j+pi alpha)/P`, where `alpha` is the parity of `n`.
The real eigenvalues are

\[
2c(\cos\omega_j-\cos\theta).
\]

Exactly two vanish, at the frequencies congruent to `theta` and
`-theta`. There are `n-1` frequencies in the interval
`(-theta,theta)`, where the eigenvalue is positive, and `P-n-1`
remaining frequencies, where it is negative. Hence

\[
\boxed{n_+(H)=n-1,\qquad n_0(H)=2,\qquad
n_-(H)=P-n-1.}
\tag{11}
\]

This deformation is a proof of a matrix-inertia identity. It need not
stay within the state-closed control family, satisfy PMP, or keep the
cost stationary. Those conditions are unnecessary for preserving
the Jacobi kernel and inertia, and no control comparison is inferred
from the deformation.

## What remains for a cost-index theorem

The integer (1) and the ordinary Jacobi inertia (11) are now fixed on
the actual geometric minimizing domain. Neither is a count of negative
directions of the constrained cost.
That count still requires the complete augmented Hessian and the
curvature of the frame constraint. A proposed inequality such as
`index >=2(n-1)` would have strong consequences, but is not proved by
this note or by the centrality/angle argument.

For all-short M1, `m=2` gives `n=1` and has already been excluded by
the exact cost argument in
[MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
Every other allowed multiplicity has `m>=5` and `n>=3`. These facts
identify a single uniform high-winding problem, rather than an
increasing sequence of closed-word comparisons.

# Independent audit of geometric switch-vector winding and Jacobi inertia

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_PROJECTIVE_WINDING](MIXED_GLOBAL_PROJECTIVE_WINDING.md).
No Lean, Lake, typechecking, numerical angle integration, or CI was run.

## Verdict and boundary

The geometric winding formula and the ordinary Jacobi inertia formula
are valid on the stated actual minimizing domain:

\[
n=(N-m-1)/3,\qquad P=N-2m,
\]

\[
n_+(H)=n-1,\qquad n_0(H)=2,\qquad n_-(H)=P-n-1.
\]

The balanced convex-disk realization is an essential input to the
integer winding. Central matrix monodromy alone fixes only a parity.
The matrix inertia is not the inertia of the constrained cost Hessian.
The note correctly retains the endpoint-curvature and augmented-Hessian
obligation and makes no further F/M1/M2 case-closure claim.

## 1. The actual state motion contributes no extra homotopy class

The tangent-frame identity is the exact endpoint-compatible relation
`F(t)=X(0)^-1 g(t) X(t)`. The normalized linear state contraction
has positive determinant, because

\[
\det((1-s)X+sJ)
=(1-s)^2+s^2-s(1-s)\operatorname{tr}(JX)\ge1.
\]

The last inequality uses the physical positive elliptic component,
where `-tr(JX)/2>=1`. The unnormalized convex combination remains in
that component, and every strict-star margin is a positive linear
functional at both endpoints of the combination. Division by the
positive square root therefore preserves the required state domain.
The contraction is equivariant under `R`, so its state endpoint has
the actual twist for every parameter value.

Substituting it into
`F_s(t)=X_s(0)^-1 g(t)X_s(t)` fixes both frame endpoints exactly at
`I,R`. At the centroid it gives `J^-1 g J`. Conjugation by the
rotation path from `I` to `J`, all of whose matrices commute with
`R`, then gives a second endpoint-fixed homotopy to `g`. These are
homotopies of frame paths, not claimed admissible comparison paths.

The actual geometric contact sector selects the canonical relative
class of `g`: one contact direction reaches its successor without an
extra revolution. The map from `SL_2(R)` to the oriented direction
of the image of a fixed vector has a contractible fibre. That fibre
consists of a positive radial scale and an affine line for the second
column subject to determinant one. Thus the direction really detects
the frame-path winding; it is not merely a necessary endpoint test.

## 2. Full product lifts, rather than matrix parity

In the triangular orientation the canonical rotation `R` is clockwise,
and `R^3=-I` is a clockwise half turn. Taking the initial label to be
zero after an actual cyclic relabeling, the canonical conjugated vertex
factor paths telescope in the universal covering group just as their
matrix products do:

\[
\widetilde F=\widetilde P_N\widetilde R^{\sum_i\epsilon_i}.
\]

Changing an integer label by three changes its conjugating matrix by
`-I`; the entire conjugated positive diagonal factor path is unchanged.
There is consequently no additional lifted loop hidden in the choice
of label representatives.

The first part of the proof supplies `F_tilde=R_tilde`. With
`sum epsilon=3k+1`, the full cyclic product therefore has lift
`R_tilde^(-3k)`, which moves every vector through total angle
`k pi`. Its central matrix endpoint alone would not determine that
integer. The argument explicitly uses the geometric class to remove
this ambiguity.

## 3. The switch-vector paths use the same branch as the product

The interpolation can be checked at the end of each positive diagonal
factor. Put `B_i=P_i T_0(q_i)`. Apart from its positive normalizing
scalar, the actual switch vector is `B_i e_1` when the outgoing sign
is positive and `B_i e_2` when it is negative.

To move to the next switch, first change that selected basis vector,
if necessary, then traverse `R^(-epsilon_i)`, and finally traverse
the next positive diagonal factor. The last factor only rescales the
new selected eigenvector. The two changes of selected basis vector
use opposite quarter turns and occur equally often in a cyclic sign
sequence, so their basis loop has winding zero.

Before applying the common determinant-one prefix, the four angle
branches are exactly those stated in the note. In particular,

\[
e_1\longrightarrow e_2\longrightarrow R^{-1}e_2=-e_1
\]

is a positive half turn at a `+-` turn, whereas

\[
e_2\longrightarrow e_1\longrightarrow Re_1=-e_2
\]

is a negative half turn at a `-+` turn. The canonical elliptic
rotation paths are monotone in the indicated directions. An
orientation-preserving prefix preserves that monotonicity and branch;
for antipodal endpoints the increment remains exactly the indicated
half turn. This checks more than the signs of the endpoint determinants.

The resulting switch-vector interpolation has total lifted angle
`k pi`. Collapsing all turns removes equal numbers of positive and
negative half turns and hence changes the sum by zero. Each remaining
reverse-centre edge has clockwise increment strictly between `-pi`
and zero. The sign gauge replaces it by its complementary positive
increment, adding exactly `pi`. There are `m` such edges, so the
gauged total is `(k+m)pi`.

Finally `sum epsilon=N-4m` gives
`k+m=(N-m-1)/3`. Collapsing the `2m` turns leaves `P=N-2m` nodes,
and the boundary representative sign is `(-1)^(k+m)`. The argument
also covers a seam lying inside a sign run: it uses the continued
actual prefix and cyclic lift, not independent local frames.

## 4. Exact Jacobi kernel and inertia

For the positive-Wronskian sequence, the two-dimensional determinant
identity gives the stated coefficients

\[
c_i=W_i^{-1},\qquad
b_i=-\det(v_{i-1},v_{i+1})/(W_iW_{i+1}).
\]

Indeed, writing `v_(i+1)` in the basis `(v_(i-1),v_i)` makes the
two neighboring terms cancel in that basis. Each coordinate sequence
therefore lies in the scalar kernel. Independence follows from
`W_i>0`; the second-order recurrence with nonzero off-diagonal
coefficients supplies the matching upper bound of two on its kernel
dimension.

The two-node case deserves the stated convention. Its two neighboring
incidences are combined with the boundary signs. Here `0<n<P` forces
`n=1`, the two positive off-diagonal weights are equal, and the
antiperiodic contributions cancel. The resulting two-by-two operator
is zero, with nullity two and both other indices zero, exactly as
the formula predicts.

For general `P`, positive radii and angle increments in `(0,pi)`
can be interpolated to equal radii and equal increments while retaining
their sum `n pi`. The resulting coefficient path is continuous and
keeps precisely the same two-dimensional kernel throughout. Hence
no other real eigenvalue can cross zero. This is a deformation of
scalar matrices; it need not preserve the original control family.

At the regular endpoint the eigenvalues are

\[
2c\bigl(\cos\omega-\cos(n\pi/P)\bigr),
\qquad c>0,
\]

on the periodic or antiperiodic frequency grid determined by the
parity of `n`. The grid points strictly between `-n pi/P` and
`n pi/P` number `n-1`; the two endpoints give zero and the other
`P-n-1` points give negative values. This count also applies when
`n pi/P` exceeds `pi/2`; no acute-angle assumption is needed.

## 5. What this audit does not infer

The ordinary Jacobi operator has a fixed inertia because its kernel
and winding can be deformed as above. A constrained cost Hessian
contains additional derivatives of the active margins and the full
frame-constraint curvature. Its negative index is not obtained by
reading the positive index of `H` or by dropping its pseudoinverse
term.

For all-short M1, the two-centre case has winding one and is separately
excluded by its strict cost bound. Every remaining allowed multiplicity
has winding at least three, but its uniform cost-index or comparison
argument remains an additional mathematical obligation. The same
distinction applies to the whole-period M2 problem and to asymmetric
pure-forward periods.

This review is an independent internal hand audit. It is not external
peer review or Lean kernel validation.

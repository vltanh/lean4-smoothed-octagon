# Independent audit of the signed scalar dual

Date: 2026-11-07 UTC. Internal hand audit of
[MIXED_GLOBAL_SCALAR_DUAL](MIXED_GLOBAL_SCALAR_DUAL.md).
No Lean, Lake, typechecking, or CI.

## Outcome

The signed auxiliary system, potential, angle equation, scalar Jacobi
inertia, full endpoint-curvature formula and three constraint pairs
have been independently reviewed. No substantive correction is needed.
The identities extend the forward dual to every remaining mixed period,
including auxiliary entries `b_i=0` or `b_i<0`.

The uniform negative-subspace target remains open. This review does
not establish an `N`-dimensional negative subspace or close a remaining
comparison case.

## 1. All four incident-sign equations

Write the prefix multiplier as

\[
c\begin{pmatrix}b/2&-h\\k&-b/2\end{pmatrix},\qquad
hk=1+b^2/4,\quad h,k>0.
\]

Direct multiplication by the two factor matrices gives the following
entries of the next prefix multiplier:

\[
\begin{array}{c|c|c}
\epsilon&b_{\rm next}/2&\text{fixed incoming entry}\\ \hline
+&q^2k-b/2&h_{\rm next}=q^2k\\
-&h/q^2-b/2&k_{\rm next}=h/q^2.
\end{array}
\]

Thus `t_i=b_i+b_{i+1}>0`. At an incoming forward switch
`h_i=t_{i-1}/2`; at an incoming reverse switch
`k_i=t_{i-1}/2`. Combining with the outgoing equations gives,
respectively,

\[
q_i^2=\frac{t_{i-1}t_i}{b_i^2+4},\quad
q_i^2=\frac{b_i^2+4}{t_{i-1}t_i},\quad
q_i^2=\frac{t_i}{t_{i-1}},\quad
q_i^2=\frac{t_{i-1}}{t_i}
\]

for `++`, `--`, `-+`, `+-`. These are exactly the signed equation
`ell_epsilon(b)=2 ell_epsilon(a)`. They require no sign assumption
on `b_i`.

Differentiating the signed potential cancels the constants
`epsilon_{i-1}+epsilon_i=2delta_i` against the derivative of the
on-site arctangent term. Hence its gradient and Hessian are the
stated `ell_epsilon` and `B_epsilon` on the entire open domain of
positive adjacent sums. The actual factor derivative paired with
`U` gives `grad J=c B_epsilon(a)b`, with the correct positive sign.

## 2. Angle and Jacobi normalization

At either same-sign index, direct use of the incoming and outgoing
switch vectors gives `e_i=c b_i/(2K_i)`. Gauging a reverse-centre
edge changes this scalar product's sign and changes its negative
Wronskian into the positive one. Consequently its angle is
`pi/2+atan(b_i/2)`; a forward edge has angle
`pi/2-atan(b_i/2)`. The principal real arctangent therefore gives
the displayed signed angle formula on all real `b_i`, including
zero. There are exactly `P` surviving edges, proving the coefficient
`(P-2n)pi` of `c` in the scalar function.

In the normalized prefix frame, the determinant-preserving variation
pair is exactly `zeta_i^C=-2i u v`. A positive diagonal factor leaves
this complex product unchanged. The forward rotation gives column
pair `(u+v,-u)` and kernel increment `pi+gamma-beta` in `(0,pi)`;
the reverse rotation gives `(-v,u+v)` and increment
`gamma-alpha-pi` in `(-pi,0)`. Thus the increments have the stated
lifted branches. Their determinants are
`4|u|^2` and `-4|v|^2` after the diagonal rescaling, namely
`2epsilon_i t_i`.

There are `2m` negative edges, so the sign gauge is periodic. It
changes the total raw kernel angle `2k pi` to `2n pi`. The gauged
off-diagonal coefficient `1/t_i` is **twice** the inverse positive
Wronskian `1/(2t_i)`. Because both operators have the same independent
kernel pair, the diagonal coefficients have the same factor two.
The positive-Wronskian homotopy therefore gives the stated inertia
`(2n-1,2,N-2n-1)` for the actual signed auxiliary matrix.

## 3. Endpoint curvature and inertia transfer

The original multiplier together with its two determinant-level
variations spans all three trace-zero frame covectors. Their pairings
with the endpoint derivative are precisely
`C dot v` and `B_epsilon(a)v` paired with the two kernel vectors of
`B_epsilon(b)`. The proved actual rank-three endpoint theorem applies;
no inverse for `B_epsilon(a)` is assumed or needed.

With `U` fixed and along an actual closed tangent, the prefix-defined
auxiliary variation is periodic to first order and obeys
`D b'=2Bv`. Differentiating the actual normal frame gradient supplies
the curvature term
`-2c(Bv)^T D^dagger Bv`. Changing the auxiliary kernel representative
does not change it because of the two kernel orthogonality conditions.
The scalar `c` pairs with the remaining independent frame constraint,
rather than introducing an extra artificial cost restriction.

After eliminating the nonzero `D` block, its two kernel coordinates
and `c` give exactly three positive and three negative constraint
pairs. There is no leftover rotation coordinate in this scalar
formulation. This verifies the index identity, including the
subtraction by three and the full endpoint curvature.

## 4. The available signed block formulas

The off-diagonal entries of `M` are
`epsilon_i(j_i+c t_i/s_i^2)=epsilon_i(j_i+2d_i)`.
This proves the stated adjacent two-by-two block and determinant
`-epsilon_i c beta_i/(2t_i)`. A reverse block has negative diagonal
entries and positive determinant, so it is negative definite. These
are off-diagonal coupling blocks; their indices cannot be added as
though they were disjoint principal blocks.

On the ratio graph the forward off-diagonal simplification simply
acquires the factor `epsilon_i`; using
`beta_i=epsilon_i(2d_i-j_i)` gives the displayed formula. The signed
scaling identities are

\[
B_\epsilon(a)a=8\delta/K,
\quad D B_\epsilon(a)[b]a+B_\epsilon(a)b=-16\delta ab/K^2,
\]
\[
J''a=C-8\delta a/K^2,
\quad B_\epsilon(b)b=8\delta/(b^2+4).
\]

They give exactly `delta_i` times the forward scaling row, and hence
zero at turns. None of these manipulations divides by an auxiliary
entry. Their signs and smoothness remain valid for real auxiliary
variables with positive adjacent sums.

The missing uniform negative-subspace inequality is explicitly
retained as a separate analytic obligation.

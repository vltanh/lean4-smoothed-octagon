# A uniform reverse-density bound for mixed minimizing periods

Date: 2026-11-07 UTC. Hand proof from the actual mixed joint Hessian.
No Lean, Lake, typechecking, or CI.

## Statement and scope

Consider an actual competitive finite normal minimizing period with
`N>=6`, after the reverse-run classification. Let `m` be its number
of double reverse runs and `P=N-2m` its number of forward switches.
The forward runs have lengths `ell_1,...,ell_m>=1` when `m>0`, so
`P=sum ell_j`. Put

\[
n=(N-m-1)/3=(P+m-1)/3.
\]

The complete-period cost--Casimir bound gives `kappa<3/2`. The actual
normal multiplier is negative elliptic, all switches are transverse,
and the same multiplier is used in the argument below.

The full constrained cost Hessian satisfies the uniform lower bound

\[
\boxed{\operatorname{ind}_-(Q_{\rm closed})
\ge \frac{2m-P-8}{3}.}
\tag{1}
\]

In particular every minimizing period in this domain must satisfy

\[
\boxed{2m\le P+8.}
\tag{2}
\]

If `E=sum(ell_j-1)=P-m` is the number of forward switches beyond one
per forward run, this says `m<=E+8`. Thus the theorem excludes all
reverse-dense mixed periods with `m-E>8` together, with arbitrary
unequal factors. For all-short periods it recovers the uniform
`m>=11` exclusion; allowed multiplicities are `m=2 mod 3`.

The bound does not exclude every M2 period or the remaining all-short
`m=5,8` branches. It supplies no sign for the full radial/phase
Hessian. The relevant exact rank, winding, and inertia transfer are
those of
[MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md).

## 1. Forward pairings are positive also inside mixed periods

At an arc with two forward incident switches, write `a` for its
active margin and `x,y` for its neighbours. The identities needed in
[GLOBAL_STRUCTURE_FORWARD_ACUTE](GLOBAL_STRUCTURE_FORWARD_ACUTE.md)
are local at this arc:

\[
q=\frac{(x+a)(a+y)}{a^2+4}>1,
\qquad ax<4,\quad ay<4,
\]
\[
C=2[(x+a)d_-+(a+y)d_+-2ae],
\]
\[
\det U=(a^2+4)^2(d_-d_+-e^2),
\qquad
d_-\ge\frac{x^2+xa+a^2}{8(x+a)^2},\quad
d_+\ge\frac{a^2+ay+y^2}{8(a+y)^2}.
\tag{3}
\]

All hold for the same actual mixed normal lift. The signs elsewhere
in the period do not occur in their proof. In particular, the
triangle minimization and scalar factorization in that note apply
unchanged: `e<=0` would give `det U>3/16`, hence
`kappa=sqrt(12 det U)>3/2`. Therefore

\[
\boxed{e_i>0\quad\text{at every }(++ )\text{ arc}.}
\tag{4}
\]

Here and below the un-gauged pairing is
`e_i=y_(i-1)^T S y_i`, with the common positive definite `S`.

## 2. The pure-phase block and its centre coupling

Work first with the switch vectors before the sign gauge. At a turn,
`y_i=-y_(i-1)`; the word-fixed collapse identifies these two vectors
up to that sign. There are `P` collapsed nodes. Write `eta` for a
periodic real coefficient on these nodes, and set

\[
W_i=\eta_i I_S y_i,\qquad
I_S=\gamma S^{-1}J_0,\qquad
\gamma=\sqrt{\det S}>0.
\tag{5}
\]

At a turn the two values of `eta` are equal. The coefficient sequence
is periodic even if the vector sequence has the opposite central
boundary sign. Put `Delta_i eta=eta_i-eta_(i-1)` at each surviving
same-sign edge and `delta_i=(epsilon_(i-1)+epsilon_i)/2`.

The exact kernel relation for the collapsed Jacobi matrix turns its
pure vector Hessian into

\[
Q_Y(\eta)=-2\sum_{\delta_i\ne0}
\delta_i K_i e_i(\Delta_i\eta)^2,
\qquad K_i=a_i^2+4.
\tag{6}
\]

For a direct check, expand `2 tr(S W^T H W)`, use
`I_S^T S I_S=S`, and subtract the kernel equation multiplied by
`eta_i^2`. The off-diagonal entry before gauging is `delta_i K_i`,
which gives exactly the sign and factor in (6).

The margin/vector cross term has a similarly simple local form.
Every differentiated diagonal has zero pairing with `I_S y_i`.
At a same-sign arc the differentiated off-diagonal is
`2 delta_i a_i v_i`, and

\[
y_{i-1}^T S I_S y_i
=-\gamma\det(y_{i-1},y_i)
=-\gamma\delta_i/K_i.
\]

Consequently its complete contribution is

\[
-\frac{8\gamma a_i v_i}{K_i}\Delta_i\eta.
\tag{7}
\]

At a turn there is no off-diagonal derivative and the cross term
is zero. These calculations use the full joint Hessian; they do not
discard the endpoint curvature from the constrained cost Hessian.

## 3. A negative graph using only reverse-centre margin variations

Set every margin variation to zero except at reverse centres. For a
centre `j` put `v_j=a_j r_j`, and write `p_j,n_j` for its two
neighbouring margins. Define the positive quantities

\[
\omega_j^-=\beta_{j-1}a_jp_j,\qquad
\omega_j^+=\beta_j a_jn_j,\qquad
M_j=8a_j^2/K_j^2,
\]
\[
D_j=M_j+\omega_j^-+\omega_j^+>0,
\qquad T_j=2a_j^2\gamma/K_j.
\tag{8}
\]

The neighbouring margins are turns. Distinct reverse centres are
never adjacent, so the exact fixed-vector margin block restricts to
the diagonal form `sum D_j r_j^2`. Equation (7) makes its complete
coupling to phases `-4 sum T_j r_j Delta_j eta`.

Choose the following linear graph over all `P` phase coefficients:

\[
r_j=\frac{2T_j}{D_j}\Delta_j\eta.
\tag{9}
\]

Substitution in the full joint Hessian gives exactly

\[
L_{\rm aug}\big|_{(9)}
=-2\sum_{++}K_i e_i(\Delta_i\eta)^2
 +\sum_{--}\left(2K_j e_j-\frac{4T_j^2}{D_j}\right)
                  (\Delta_j\eta)^2.
\tag{10}
\]

Every forward coefficient is strictly negative by (4). At each
reverse centre,
[MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md)
proves

\[
2T_j^2>K_j e_j
\bigl[M_j+2(\omega_j^-+\omega_j^+)\bigr].
\tag{11}
\]

If `e_j<=0`, the reverse coefficient in (10) is immediately
negative. If `e_j>0`, (11), together with
`D_j<M_j+2(omega_j^-+omega_j^+)`, gives the same strict sign.
Thus every coefficient in (10) is strictly negative.

The surviving edges form one connected collapsed cycle. Its only
phase vectors with all differences zero are the constants, which
are exactly the common rotation. Restricting (9), for example, to
`sum eta_i=0` therefore gives a negative subspace of dimension
`P-1` in the actual joint Hessian. No margin matrix inversion or
rank assumption is needed to construct this subspace.

## 4. Full endpoint constraints and the density restriction

The independently audited augmented-index identity, including the
three frame-constraint saddle pairs, gives

\[
\begin{aligned}
\operatorname{ind}_-(Q_{\rm closed})
&=\operatorname{ind}_-(L_{\rm aug})-2(P-n-1)-3\\
&\ge P-1-2(P-n-1)-3\\
&=2n-P-2=\frac{2m-P-8}{3}.
\end{aligned}
\tag{12}
\]

This proves (1). The right side is an integer because
`P+m-1=3n`. If it is positive, the same rank-three theorem integrates
a negative constrained direction to an actual nearby trajectory
with both twisted endpoints. Strict positivity, the strict star,
and the retained geometric realization persist locally, and the
cost decreases. A minimizing period therefore satisfies (2).

Equivalently, if the un-gauged frame-prefix winding is defined by
`P-2m=3k+1`, the bound is `ind_-(Q_closed)>=-k-3` and a minimizer
must have `k>=-3`. This is a restriction on the actual complete
period; it is not inferred from local control labels alone.

The proof uses the local acuteness sign only at `++` arcs and the
uniform reverse-centre inequality only at `--` arcs. Turns are
treated by their exact word-fixed collapse. It therefore covers
arbitrary forward run lengths and the actual twisted seam without
an enumeration of period lengths or a lower duration bound.

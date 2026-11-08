# Every normal pure-forward period has negative elliptic primary costate

Date: 2026-11-07 UTC. Hand proof with a supplementary exact-algebra
checker and an [independent internal audit](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC_AUDIT.md).
No Lean, Lake, typechecking, or CI.

## Theorem and scope

Let a strict-star, finite, positive vertex trajectory have entirely forward
switches and the actual twisted frame, state, and costate endpoints. Assume
one normal free-time PMP lift, with the free-initial-state transversality,
and normalize its physical cost multiplier to `lambda=-1`. Then

\[
\boxed{\Lambda_1(t)\text{ is negative elliptic for every }t.}
\tag{1}
\]

The factors may all be unequal. Double or triple ties and zero first
switching derivatives are retained. No endpoint-Jacobian inverse, rank
assumption, period budget, or bound on the number of pieces is used.

This strengthens the pure-forward part of
[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR](GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md):
the hyperbolic and parabolic alternatives are excluded as well. It does
not compare the remaining negative elliptic periods with the octagon.
In particular, it supplies no lower Casimir bound and no negative-index
assertion for every long period. The whole F comparison remains open.

The proof uses a scalar Jacobi recurrence associated with the **full
central frame monodromy**, not merely the trace of that monodromy.

## 1. Cyclic state coordinates and the frame multiplier

Use the triangular coordinates of the preceding sector note. Write

\[
N=3k+1,\qquad
s_i=a_i+a_{i+1},\qquad K_i=a_i^2+4,\qquad
q_i=\frac{s_{i-1}s_i}{K_i},
\tag{2}
\]

with indices extended periodically, and retain

\[
a_i>0,\qquad a_i a_{i+1}<4,\qquad q_i>1.
\tag{3}
\]

These coordinates resolve the twisted state endpoint with free initial
state. The remaining full frame constraint is

\[
P_N=\epsilon I,\qquad
P_i=A(q_0)\cdots A(q_{i-1}),\qquad
A(q)=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix},\qquad
\epsilon=(-1)^k.
\tag{4}
\]

The case `N=1` cannot satisfy (4), so `N>=4`.

The normalized cost `J=C/sqrt(12)` and its derivatives are

\[
8J=\sum_i(3a_i a_{i+1}-4-a_i^2\log q_i),
\]
\[
C_i:=J_{a_i}=\frac14\left[
 a_{i-1}+a_i+a_{i+1}
 -a_i^2\left(\frac1{s_{i-1}}+\frac1{s_i}\right)
 +\frac{a_i^3}{K_i}-a_i\log q_i\right].
\tag{5}
\]

Let `U` be the traceless cyclic frame multiplier. The actual normal PMP
boundary identity, including cancellation of the free initial-state
terms, is

\[
C_i=\operatorname{tr}(UV_i),\qquad
U=\frac1{\sqrt{12}}
 \operatorname{Ad}_{X_0^{-1}}\Lambda_1^{\rm tri}(0),
\tag{6}
\]
\[
V_i=\operatorname{Ad}_{P_i}
2\begin{pmatrix}
-a_i/K_i&q_i^2/s_i\\-1/s_{i-1}&a_i/K_i
\end{pmatrix}.
\tag{7}
\]

The derivation of (6), with its positive multiplier sign, is in Section 3
of the preceding sector note. It is an identity supplied by the given
normal lift; no endpoint-rank theorem is needed here.

## 2. A two-dimensional kernel for a scalar Jacobi matrix

Put

\[
r_i=P_i e_1,\qquad y_i=\frac{q_i}{s_i}r_i\in\mathbb R^2.
\tag{8}
\]

Extend all indices using (4), so `y_{i+N}=epsilon y_i`. Define a real
symmetric Jacobi matrix `H` on epsilon-periodic scalar sequences by

\[
(Hz)_i=K_i z_{i-1}-s_i^2z_i+K_{i+1}z_{i+1}.
\tag{9}
\]

The two coordinates of `y_i` solve this recurrence. To verify it directly,
let `M_i=P_i^{-1}UP_i` later, but first use only the frame matrices:

\[
y_{i-1}=-\frac1{s_{i-1}}P_i e_2,\qquad
 y_i=\frac{s_{i-1}}{K_i}P_i e_1,
\]
\[
K_{i+1}y_{i+1}
=s_iq_iP_i e_1+\frac{s_i}{q_i}P_i e_2.
\]

The `e_1` terms in (9) cancel and the `e_2` terms cancel because
`s_i/q_i=K_i/s_{i-1}`. Moreover

\[
\boxed{\det(y_{i-1},y_i)=1/K_i>0.}
\tag{10}
\]

Thus the two coordinate solutions are linearly independent. Since a
second-order recurrence with every `K_i>0` is determined by two adjacent
values, the epsilon-periodic kernel of `H` has dimension exactly two.
This is where full central monodromy is used.

Let

\[
J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
S=-J_0U.
\]

The matrix `S` is symmetric and `det S=det U`. Define

\[
d_i=y_i^TSy_i,\qquad e_i=y_{i-1}^TSy_i.
\tag{11}
\]

The preceding two local expressions for `y` and the identity
`P_i^T J_0P_i=J_0` give

\[
d_{i-1}=-\frac{(M_i)_{12}}{s_{i-1}^2},\qquad
 d_i=\frac{s_{i-1}^2}{K_i^2}(M_i)_{21},\qquad
 e_i=\frac{(M_i)_{11}}{K_i}.
\tag{12}
\]

Substitution into (6)--(7) gives the exact cyclic stationarity equation

\[
\boxed{C_i=2\{s_{i-1}d_{i-1}+s_i d_i-2a_i e_i\}.}
\tag{13}
\]

The two-by-two Gram determinant also gives

\[
\boxed{d_{i-1}d_i-e_i^2=\frac{\det U}{K_i^2}.}
\tag{14}
\]

Neither (13) nor (14) assumes that `U` is elliptic.

## 3. The weak forward switching derivative supplies a diagonal bound

At an actual forward switch, rotate its labels to `0 -> 1` and write
the switching-state margins as `(a,b,c)`, where
`c=(4-ab)/(a+b)>0`. Use the tangent frame `F` and the normalized cost
`J`. Let `Kappa=F^{-1}UF`, put `phi_j=tr(Kappa D_j)`, and use state
covector components `eta_a,eta_b`. The vertex log-clock Hamiltonians
in the maximizing convention are

\[
\widehat H_j=-\phi_j+\eta\cdot f_j-\ell_j,
\qquad \ell_j=p_j(a+b+c)/8,
\]
\[
f_0=(0,a+b),\qquad f_1=(-(a+b),0).
\tag{15}
\]

They are positive clock multiples of the actual physical Hamiltonians,
with the cost normalization included:
`widehat H_j=(p_j/(2 sqrt(12)))H_j`. Both vanish at this switch.

Along the control-0 log flow,
`Kappa'=-[Kappa,D_0]`. Substituting the two active zero equations into
the derivative of `widehat H_1` gives

\[
\begin{aligned}
\frac{d\widehat H_1}{ds_0}
&=\operatorname{tr}(Kappa[D_0,D_1])
  +\phi_0+\phi_1+\ell_0+\ell_1
  -(a+b)(\partial_a\ell_0+\partial_b\ell_1)\\
&=2Kappa_{21}-\frac{a^2+ab+b^2}{4}.
\end{aligned}
\tag{16}
\]

For the last line, `[D_0,D_1]+D_0+D_1=2E12`, and direct differentiation
of `c=(4-ab)/(a+b)` gives the displayed cost term.

The physical-time derivative of the actual switching function `H_1-H_0`
is therefore `4 sqrt(12)/(ab)` times (16). It is nonnegative: on the preceding positive arc
the function is nonpositive, and on the following positive arc it is
nonnegative. Its left and right derivatives agree at the tie, since the
difference of its derivatives along the two Hamiltonian fields is its
Poisson bracket with itself. This remains valid at a triple tie or when
the common first derivative is zero. Thus

\[
Kappa_{21}\ge\frac{a^2+ab+b^2}{8}.
\tag{17}
\]

At the end of arc `i`, in its old-label frame,
`Kappa=Ad_{T_0(q_i)^{-1}}M_i`. Equations (12) imply
`Kappa_{21}=q_i^2(M_i)_{21}=s_i^2d_i`. Hence

\[
\boxed{d_i\ge
 \frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}{8s_i^2}
 \ge\frac3{32}>0.}
\tag{18}
\]

The final inequality is just
`a_i a_{i+1}/(a_i+a_{i+1})^2<=1/4`.

## 4. An off-diagonal lower bound from exact stationarity

Write

\[
j_i=J_{a_i a_{i+1}}
=\frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}{4s_i^2}.
\]

Equation (18) says `2d_i>=j_i`. Using this in (13) gives

\[
4a_i e_i
=2s_{i-1}d_{i-1}+2s_i d_i-C_i
\ge s_{i-1}j_{i-1}+s_i j_i-C_i.
\tag{19}
\]

Put `a=a_i`, `x=a_{i-1}`, `y=a_{i+1}` and
`ell=1/(x+a)+1/(a+y)`. The exact scalar simplification is

\[
s_{i-1}j_{i-1}+s_i j_i=(x+y+a^2\ell)/4.
\]

Comparing with (5), (19) becomes

\[
e_i\ge-\frac1{16}
 \left(1-2a\ell+\frac{a^2}{a^2+4}-\log q_i\right).
\tag{20}
\]

Strict star gives `a(x+a)<a^2+4` and `a(a+y)<a^2+4`. Therefore
`a ell>2a^2/(a^2+4)`. Together with `log q_i>0`, this makes the
parenthesis in (20) strictly less than one. In particular,

\[
\boxed{e_i>-1/16\quad\text{at every index}.}
\tag{21}
\]

This lower bound uses exact stationarity, not only the sign of `C_i`.

## 5. Nonelliptic multipliers would give an impossible positive kernel vector

Suppose `det U<=0`. By (14) and (18),

\[
e_i^2\ge d_{i-1}d_i\ge(3/32)^2.
\]

The negative alternative `e_i<=-3/32` contradicts (21), because
`-3/32<-1/16`. Thus

\[
e_i\ge3/32>0\quad\text{for all }i.
\tag{22}
\]

We next construct a real linear functional `lambda` on `R^2` such that
`lambda(y_i)` has one nonzero sign throughout the extended period.

If `det S=0`, (18) forces `S` to be nonzero positive semidefinite of
rank one. Write `S=lambda^T lambda` after scaling the functional.
Then `d_i=lambda(y_i)^2>0` and
`e_i=lambda(y_{i-1})lambda(y_i)>0`, proving the sign assertion.

If `det S<0`, change real coordinates so that `S` has quadratic form
`u^2-v^2`. The first coordinate defines the required functional.
Indeed `d_i>0` gives `|u_i|>|v_i|`, so `u_i` is nonzero; the sign of
`e_i=u_{i-1}u_i-v_{i-1}v_i` is the sign of `u_{i-1}u_i`.
Equation (22) therefore propagates a single sign.

Since `y_{i+N}=epsilon y_i`, this is already impossible when
`epsilon=-1`. When `epsilon=1`, negate the functional if necessary to
obtain a strictly positive periodic scalar solution
`h_i=lambda(y_i)>0` of `Hh=0`.

But such a solution forces the periodic kernel to be one-dimensional.
For every real periodic `z`, use `Hh=0` to expand

\[
\boxed{z^THz
=-\sum_i K_i h_{i-1}h_i
 \left(\frac{z_i}{h_i}-\frac{z_{i-1}}{h_{i-1}}\right)^2.}
\tag{23}
\]

If `Hz=0`, the left side vanishes. All coefficients on the right are
strictly positive, so every ratio `z_i/h_i` is equal. Hence every kernel
vector is proportional to `h`. This contradicts the independent pair
of solutions in Section 2.

Both cases contradict `det U<=0`. Thus `det U>0`. Since (18) also gives
positive values of the quadratic form `S`, it is positive definite.
Consequently `U` is positive elliptic in triangular coordinates.
Equation (6), followed by the orientation-reversing change back to
physical coordinates, proves that `Lambda_1(0)` is negative elliptic.
The primary-costate conjugation law preserves this component and proves
(1) at every time.

## Remaining forward index problem

The theorem places **every** normal pure-forward period in the sector
where the complete-period cost--Casimir inequality applies. For a
competitive period it therefore gives

\[
0<\sqrt{\det\Lambda_1}
\le\frac{3A_{\rm oct}}{2(2\pi-A_{\rm oct})}.
\]

It supplies no reverse inequality contradicting this cap for `N>=7`.
The scalar Jacobi kernel above also does not, by itself, determine the
constrained cost index: the second derivative of the matrix endpoint
constraint must still be included. A universal negative variation or
a further full-period stationary inequality is still needed for case F.

## Appendix: exact Jacobi form of the remaining second variation

This is a reduction of the index problem, not its solution. Keep the
notation above, and regard `Y` as the `N by 2` matrix with row `y_i^T`.
After the theorem, `S` is positive definite. Put

\[
P=YSY^T,\qquad
\beta_i=2d_i-j_i\ge0,
\tag{24}
\]

where the weak sign is exactly the forward switching inequality (18).
For a variation `v` of all active margins, write
`H_v=dH(v)` and let `H^dagger` be the inverse of `H` on the orthogonal
complement of its two-dimensional kernel, extended by zero on that
kernel.

An actual tangent to the full closed-period manifold satisfies

\[
Y^T H_vY=0.
\tag{25}
\]

Along such a closed variation the full, curvature-corrected cost Hessian
is

\[
\boxed{
\begin{aligned}
Q(v)={}&\sum_i\beta_i a_i a_{i+1}
 \left(\frac{v_i}{a_i}-\frac{v_{i+1}}{a_{i+1}}\right)^2
 -\sum_i\frac{8v_i^2}{K_i^2}\\
&\quad-2\operatorname{tr}(P H_v H^\dagger H_v).
\end{aligned}}
\tag{26}
\]

Here (25) is necessary even without any rank assumption. For the remaining
target `N>=7`, [LOCAL_FORWARD_RANK](LOCAL_FORWARD_RANK.md) supplies rank
five for six consecutive positive forward arcs with their initial state
fixed. Restricting those variations to zero terminal-state derivative
still supplies all three frame directions. Extend them by zero through
the rest of the period: they satisfy the linearized twisted state
constraint, so the frame map on the state-closed margin family has rank
three. Thus (25) is the actual tangent constraint there, and an actual
negative tangent direction can be integrated by the implicit function
theorem. No unexamined endpoint minor is presumed nonzero.

For a derivation of (26), the polynomial matrix `H(a)` has off-diagonal
entries `a_i^2+4` and diagonal entries `-(a_i+a_{i+1})^2`. Equations
(12)--(13) give

\[
J_{a_i}=-\operatorname{tr}(P H_{a_i}).
\tag{27}
\]

For the local part `Q_0=J''+tr(P H'')`, the off-diagonal entry is
`j_i-2d_i=-beta_i`; its diagonal entry, using (13), is

\[
J_{a_i a_i}-C_i/a_i
 +2(a_{i-1}d_{i-1}+a_{i+1}d_i)/a_i.
\]

Directly differentiating (5) under common scaling of all margins gives

\[
(\operatorname{Hess}J\,a)_i-C_i=-8a_i/K_i^2.
\tag{28}
\]

Substitute `2d_i=j_i+beta_i` to obtain exactly the first line of (26).

For the endpoint-curvature term, choose the kernel basis along a closed
variation so that `Y'` is orthogonal to the initial kernel. Differentiating
`H Y=0` gives `Y'=-H^dagger H_vY`. A second derivative and multiplication
by the initial `Y^T` gives

\[
Y^T H_{\rm total}''Y
 =2Y^T H_v H^\dagger H_vY.
\]

The contribution from the acceleration of the margin curve cancels
against (27), leaving the last line of (26). A different kernel-basis
gauge gives the same expression because of (25).

Thus the remaining uniform index implication is precise: for every
stationary, strictly feasible forward period with `N>=7`, satisfying the
actual PMP conditions and budget, exhibit a nonzero tangent `v` in
(25) for which (26) is negative, or supply a different full-period cost
obstruction. The signs `beta_i>=0` and `S>0` alone do not determine the
sign of (26); the Jacobi inverse is indefinite. No replacement of its
last term by zero or by an unproved definite sign is justified.

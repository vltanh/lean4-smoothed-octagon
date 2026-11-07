# The complete short-forward-run problem and its two-centre exclusion

Date: 2026-11-07 UTC. Hand identities for whole normal periods.
No Lean, Lake, typechecking, or CI.

**Later uniform progress:**
[MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md)
and its independent audit prove a constrained-index lower bound
`(m-8)/3`, excluding every `m>=11` together. Combined with this
note's `m=2` cost exclusion, only `m=5,8` remain in the sufficient
M1 domain. The common equations and original base-branch proof below
remain unchanged; references below to the remaining `m>=5` problem
describe the domain before that later theorem.

## Scope and reduction

After [MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md),
every mixed normal minimizing period has reverse runs of length exactly
two. A period with any forward run of length at least two contains the
M2 pattern `+--++`. Thus, for a sufficient disjoint assignment of the
remaining mixed competitors, M1 need only handle periods in which
**every forward run has length one**. Their entire switch sequence is

\[
(--+)^m.
\tag{1}
\]

This is a whole-period restriction, not an assertion that other mixed
periods cannot contain local M1 windows. Those other mixed periods
remain assigned to M2. The actual label twist gives

\[
-m\equiv1\pmod3,\qquad m\equiv2\pmod3,
\qquad N=3m.
\tag{2}
\]

The note derives one common cyclic recurrence and one exact cost
identity for **all** positive integers in (2). It then excludes the
smallest multiplicity `m=2` under the competitive cost budget, without
an endpoint-rank assumption or a fixed numerical example. The uniform
`m>=5` exclusion remains open. No increasing-length catalogue is
proposed or used.

## 1. Centre and bridge coordinates

Index the arcs in each triple as

\[
a_j,\quad b_j,\quad c_j,
\]

where `a_j` is the active margin of the middle arc in a double reverse
run. The three intervening switch signs are respectively `-,+,-`,
and the next arc has active margin `a_(j+1)`. Thus each four-arc edge
core has active margins `(a_j,b_j,c_j,a_(j+1))` and alternating
labels `2121` after rotation. Its shared centre arcs also belong to
the adjacent cores; the same actual PMP lift is used throughout.

The minimum theorem gives

\[
a_j<b_j,\qquad a_j<c_{j-1}.
\tag{3}
\]

In the triangular coordinates set `K_j=a_j^2+4`. Formula (2) of
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md) gives
the three exact positive factors

\[
q_{a_j}=\frac{K_j}{(c_{j-1}+a_j)(a_j+b_j)},\qquad
q_{b_j}=\frac{b_j+c_j}{a_j+b_j},\qquad
q_{c_j}=\frac{b_j+c_j}{c_j+a_{j+1}}.
\tag{4}
\]

All are strictly greater than one. In particular

\[
K_j>(c_{j-1}+a_j)(a_j+b_j)>4a_j^2,
\qquad 0<a_j^2<4/3.
\tag{5}
\]

All adjacent products are less than four. No lower bound on an
individual positive duration is required.

## 2. An exact Jacobi recurrence after the turn identifications

Use the actual switch vectors `y_i` and positive definite quadratic
form `S` of MIXED_GLOBAL_COSTATE_ELLIPTIC. At each of the two turn arcs
`b_j,c_j`, successive switch vectors are negatives of one another.
Define `z_j` to be the vector at the reverse switch immediately after
centre arc `a_j`. Then the vectors at the three switches in its triple
are respectively

\[
z_j,\quad -z_j,\quad z_j.
\]

At the next centre the determinant identity therefore reads

\[
\det(z_{j-1},z_j)=-1/K_j.
\tag{6}
\]

The two coordinate vectors are independent. The full frame monodromy
gives the exact boundary sign

\[
z_{j+m}=\sigma z_j,
\qquad \sigma=(-1)^{(m+1)/3}.
\tag{7}
\]

Define

\[
D_j=(a_j+b_j)^2+(c_j+a_{j+1})^2-(b_j+c_j)^2.
\tag{8}
\]

The actual vector sequence satisfies

\[
\boxed{-K_jz_{j-1}+D_jz_j-K_{j+1}z_{j+1}=0.}
\tag{9}
\]

Here is a direct verification from the full vertex products. In the
prefix frame at centre `a_j`, abbreviate

\[
h=c_{j-1}+a_j,\quad u=a_j+b_j,\quad
v=b_j+c_j,\quad w=c_j+a_{j+1},\quad K=K_j.
\]

Write `A_+(q)=T_0(q)R^-1` and `A_-(q)=T_0(q)R`. Then

\[
z_{j-1}=-e_1/h,\qquad z_j=he_2/K,
\]
\[
K_{j+1}z_{j+1}
=w A_-(K/(hu)) A_+(v/u) A_-(v/w)e_2
=\frac Khe_1+\frac hK(u^2+w^2-v^2)e_2.
\]

This is exactly (9). Prefix conjugations preserve it, and (7) supplies
its actual twisted seam. Thus the recurrence does not infer its
monodromy from the control labels alone.

Equivalently the real symmetric Jacobi form is

\[
\mathcal H(z)=\sum_jD_j z_j^2-2\sum_jK_jz_{j-1}z_j
\tag{10}
\]

on the boundary condition (7). Both coordinates of the actual vector
sequence solve its Euler equation. For `m=2`, the two neighboring
off-diagonal contributions are combined with their boundary signs;
they must not be counted as independent matrix entries.

After the scalar gauge `z_j -> (-1)^j z_j`, all off-diagonal
coefficients become positive, and the boundary condition is always
antiperiodic:

\[
\sigma(-1)^m=-1\qquad(m\equiv2\pmod3).
\tag{11}
\]

This parity identity alone is not a winding or index theorem.

## 3. A whole-period Euler identity for the normal cost

Put

\[
d_j=z_j^TSz_j,\qquad e_j=z_{j-1}^TSz_j.
\]

The turn secant formula gives `3/32<d_j<1/8`. The Gram determinant
and the primary normalization give

\[
d_{j-1}d_j-e_j^2=\frac{\det U}{K_j^2},
\qquad \det U=\det\Lambda_1/12>0.
\tag{12}
\]

The exact stationary cost identity is

\[
\boxed{J=\frac C{\sqrt{12}}
=2\sum_{j=0}^{m-1}\frac1{K_j}-8\sum_{j=0}^{m-1}e_j.}
\tag{13}
\]

For a direct derivation, apply simultaneous scaling to all `3m` active
margin variables in the state-closed family. Let `EJ` be its Euler
derivative before imposing the three frame constraints. The signed
action (3) in MIXED_GLOBAL_COSTATE_ELLIPTIC obeys

\[
(a\partial_a+b\partial_b)G(a,b)
=2G(a,b)+16\left(\frac1{a^2+4}+\frac1{b^2+4}\right).
\]

At a turn the two incident signs cancel. At each centre both are
negative. Summation therefore gives

\[
EJ=2J-4\sum_j1/K_j.
\tag{14}
\]

Independently, sum the exact frame columns (9) of that note with their
active-margin coefficients. All edge sums cancel to give

\[
\sum_i a_iV_i
=4\sum_i\frac{\epsilon_{i-1}+\epsilon_i}{a_i^2+4}Z_i.
\]

At a centre, `tr(UZ_i)=2K_j e_j`; at a turn its coefficient is zero.
The actual normal boundary identity consequently gives

\[
EJ=-16\sum_j e_j.
\tag{15}
\]

Combining (14)--(15) proves (13). This calculation uses PMP
stationarity under the full frame multiplier. It does not assert that
common scaling itself preserves the complete endpoints for general `m`.

## 4. The two-centre period cannot be competitive

Take `m=2`. Equation (7) has `sigma=-1`. The recurrence at node 0
becomes

\[
D_0z_0+(K_0-K_1)z_1=0.
\]

Independence in (6) forces `D_0=0` and `K_0=K_1`. The second
recurrence also gives `D_1=0`. Since both centre margins are positive,

\[
a_0=a_1=:a>0,\qquad K=a^2+4,
\]
\[
(b_0-a)(c_0-a)=2a^2,
\qquad (b_1-a)(c_1-a)=2a^2.
\tag{16}
\]

Also `z_-1=-z_1`, so symmetry of `S` gives
`e_0=-e_1`. Formula (13) simplifies to

\[
J=4/K.
\tag{17}
\]

Write `x=b_0/a`, `z=c_0/a`, `y=b_1/a`, and `t=c_1/a`.
They are all greater than one by (3). Equations (16) give

\[
xz=x+z+1,\qquad yt=y+t+1.
\]

Since `(x-1)(z-1)=2`, the elementary arithmetic-geometric mean
inequality gives

\[
xz=x+z+1\ge3+2\sqrt2=(1+\sqrt2)^2,
\qquad yt\ge(1+\sqrt2)^2.
\tag{18}
\]

Let `tau=K/a^2`. Strict positivity of both centre durations in (4)
requires

\[
\tau>\max\{(1+t)(1+x),(1+z)(1+y)\}.
\]

Multiplication of the two displayed products and (18) yield

\[
\tau>2\sqrt{xz\,yt}\ge6+4\sqrt2,
\tag{19}
\]

where `(1+x)(1+z)=2xz` and `(1+y)(1+t)=2yt` were used.
Consequently (17) gives the strict whole-period lower bound

\[
\boxed{
J=1-\tau^{-1}>\sqrt2-\tfrac12,
\qquad C>2\sqrt6-\sqrt3>\pi.
}
\tag{20}
\]

For an entirely rational check of the last comparison,
`2sqrt(6)-sqrt(3)>22/7` reduces, after squaring positive quantities,
to `545^2>3*308^2`, namely `297025>284592`.
The standard strict bound `pi<22/7` follows from
`integral_0^1 x^4(1-x)^4/(1+x^2) dx=22/7-pi>0`.

Every competitive minimizer has `C<=A_oct<pi`, contradicting (20).
This excludes every actual normal closed two-centre period with
arbitrary unequal positive factors, all endpoint ranks, and all tie
limits allowed in the positive representation. The proof does not
construct a local replacement or assume a rank-three constraint fibre.

## Uniform remaining obligation

The whole short-forward-run problem is now the single cyclic family
(4), (7), (9), (12)--(15) with `m>=5`, `m≡2 mod3`, the actual full
PMP inequalities, and the competitive budget. Its length is not being
enumerated.

The centre-minimum property gives `1/K_j>3/16`, but it does not by
itself control the sign of `e_j`. The nonelliptic argument in
MIXED_GLOBAL_COSTATE_ELLIPTIC proved a negative centre cross pairing
only under the contradicted hypothesis `det U<=0`; it cannot be used
after positive ellipticity has been established. The local normal
conditions and Casimir cap likewise require a separate proof before
one can assert negative centre pairings.

If a valid whole-period inequality gave `sum e_j<=0`, (13) and (5)
would imply `C>(3sqrt(3)/4)m`, immediately excluding every `m>=5`.
That aggregate inequality, a suitable complete-period index theorem,
or a different global comparison remains to be proved. The parity
statement (11) and the two-dimensional Jacobi kernel alone supply none
of those conclusions. In particular this note closes the two-centre
subcase, not the whole sufficient M1 target.

## Validation boundary

The three-factor calculation proving (9), exact Euler derivative,
two-centre algebra and rational cost comparison are displayed above.
[mixed_global_short_run_certificate.py](../explorations/mixed_global_short_run_certificate.py)
checks eight exact identities from those calculations; all pass with
Python 3.12.14 and SymPy 1.14.0. The proof uses the already audited
full-period action and multiplier interface. Numerical trajectories,
period enumeration, determinant-only closure, and implicit endpoint-rank
assumptions are absent.

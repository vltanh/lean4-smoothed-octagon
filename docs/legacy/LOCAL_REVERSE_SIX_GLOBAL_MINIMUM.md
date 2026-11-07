# Global fixed-endpoint minima in the local 021210 domain

Date: 2026-11-07. This is a separate strengthening of
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md).
Its additional external input is the sufficient-optimality theorem of
Agrachev–Stefani–Zezza (ASZ). The self-contained at-most-six result in the
base note does not depend on this strengthening. **The full argument and
the exact external-theorem hypotheses received independent hand review.**

## Theorem and exact scope

Fix a sufficiently small positive core size `b` in the base note. Then
there is `h_0(b)>0` such that, for every `0<h<h_0(b)`, the six-piece
window `P_h` of word `021210` has no cheaper strict-star competitor with
its prescribed initial and final frame and state, among **all measurable
simplex controls and all positive terminal times**.

The pieces of `P_h` remain positive, its cost can be arbitrarily small,
and it satisfies the input sector condition established in the base
note. This refutes the universal L3 statement on that explicit superset even
after removing the replacement-piece cap. It does not establish occurrence
of the example inside a closed Reinhardt minimizer, and does not refute
Reinhardt's conjecture or a reduction requiring additional global embedding.

The proof has two separate stages. First apply ASZ to **one fixed**
positive-pad reference `P_H`. Then trim that reference's two outer pads
and use compactness plus the exact edge dual to globalize the trimmed
paths. There is no assertion of a uniform strong-optimality neighborhood
for a family whose padding tends to zero.

## 1. Exact equivalence to a smooth control-affine problem

Write the original physical state equations using

\[
\gamma_i(X)=-\operatorname{tr}(Z_iX)>0,
\qquad \gamma_u=\sum_i u_i\gamma_i.
\]

For every measurable original control `u` define

\[
\theta_i={u_i\gamma_i\over\gamma_u}.
\tag{1}
\]

Then `theta` is simplex-valued, and the original state equation is the
convex combination of the three physical vertex fields, with weights
`theta`. Conversely,

\[
u_i={\theta_i/\gamma_i\over\sum_j\theta_j/\gamma_j}
\tag{2}
\]

recovers the original control. On a compact strict-star set these
transformations are continuous in the state, measurable in time, and
have positive uniformly bounded denominators. This is an exact change
of control coordinates, not a relaxation of the problem.

Use the state-only clock and group coordinate from equation (9) of the
base note:

\[
d\tau=y\,dt,\qquad w=y^{-2},\qquad A=gK(x).
\]

Let `Y=(x,w,A)` on the five-dimensional smooth strict-star state
manifold. Its three fields `f_i(Y)` are exactly that table, and

\[
{dY\over d\tau}=\sum_i\theta_i f_i(Y),\qquad
\mathcal L(Y)=1+(1+x^2)w.
\tag{3}
\]

The scaled physical cost is `mathcal A=(2/3)C=int mathcal L d tau`.
The fields are smooth on the open strict-star set. They are distinct:
the two edge fields have different `w` components, and the zero vertex
has a different `x` component. All controls in (3) correspond to actual
original controls by (2), and the physical clock is recovered from
`dt=d tau/y`.

The state-only nature of this clock is useful below: convergence of
states and physical durations implies convergence of the accumulated
clock and its inverse without any separate convergence theorem for
switching times or control-dependent clocks.

## 2. A fixed positive-pad reference satisfies the ASZ assumptions

The external result is Theorem 2.6 of Agrachev, Stefani, and Zezza,
[*Strong Optimality for a Bang-Bang Trajectory*](https://people.sissa.it/~agrachev/agrachev_files/bang-bang.pdf),
SIAM J. Control Optim. 41 (2002), 991–1014. For a smooth control-affine
Mayer problem on a fixed interval, it gives strict strong local
optimality from a regular normal bang-bang extremal, simple switches,
the strict switching Legendre condition, and positive second variation
of the finite switching-time problem. Strong refers to the uniform
state topology. Its Assumptions 2.1–2.3 and equation (2.8) specify the
conditions being checked here.

### 2.1 One fixed sufficiently short positive padding

Choose one `H>0`, sufficiently small for Sections 3 and 6.4 of the base
note, and keep it fixed from now on. The reference `P_H` has six
positive pieces and five switches.

Its normal adjoint is the exact covector constructed in equations
(10)–(18) of that note, extended onto its two outer control-0 pieces.
The active minimizing Hamiltonian is zero on every piece. The other
vertex is strictly unfavorable on each open edge piece except at its
prescribed switch; the zero-vertex gap is strictly positive on the
whole open core. At each outer join it vanishes with a nonzero crossing,
and continuation onto the outer arcs makes control 0 strictly optimal.
The unused third vertex has a strict gap at every switch.

The internal edge switches are transverse because
`lambda'(x_i)=x_i^2-mu` at the three zeros `x_i=-s,0,s`, and none of
these three values is zero. The outer crossings are transverse by
inequality (17): the one-sided slopes at the two zero endpoints have
strict opposite signs. Switching-function derivatives from the two
active Hamiltonians agree at a tie; their difference is the Poisson
bracket of the switching function with itself. Thus every switch is
simple and satisfies the strict Legendre sign after changing from the
minimizing to the maximizing convention of ASZ.

### 2.2 The finite endpoint Hessian is positive

The smooth five-variable map in Section 6.4 of the base note consists
of the two outer physical durations and the three middle-edge endpoint
coordinates. Its derivative is invertible at zero padding: the edge
columns span the kernel of `dN`, while the two outer columns have the
independent normal projections (23). It stays invertible at the chosen
positive `H`.

Consequently the full six-duration fixed-endpoint fiber near `P_H`
has dimension one. On that exact fiber the two outer durations are
fixed, as are the actual initial and final frame/state endpoints of
the middle edge path. Both outer costs are therefore constant. The
constrained second variation is exactly the reverse-edge variation

\[
\sum_{j=1}^3 k_jw(x_j)(\mu-x_j^2)v_j^2>0
\quad\text{for every nonzero admissible tangent }v.
\tag{4}
\]

The rank-two switch constraints in the base note show that its tangent
is genuinely one-dimensional; the three coefficients in (4) are
strictly positive. This is the Hessian on the actual endpoint fiber,
including endpoint curvature, not an unconstrained duration Hessian.
Normal stationarity follows independently from the adjoint above.

### 2.3 Exact fixed-interval augmentation for free time

Introduce a constant state `rho>0` for total tau-duration, and a cost
coordinate `z`, on the fixed interval `[0,1]`. The fields are

\[
\mathsf X_i(Y,z,\rho)=(\rho f_i(Y),\rho\mathcal L(Y),0).
\tag{5}
\]

The initial submanifold fixes `Y=Y_i` and `z=0`, leaving `rho` free.
The terminal submanifold fixes `Y=Y_e`, leaving `z,rho` free. The
objective is final `z`. These are smooth submanifolds of a
seven-dimensional manifold, and the fields (5) are smooth and distinct.

Six positive tau-durations are locally equivalent to the free initial
`rho` and five ordered switching times on `[0,1]`. They are also locally
equivalent to six positive physical durations. The latter conversion is
triangular: the tau-duration of arc `j` depends only on physical durations
through `j`, and its derivative in its own physical duration is the
positive terminal value of `y` on that arc. Thus the rank and positive
constrained Hessian in §2.2 are precisely the switching variation in
ASZ's equation (2.8), in smoothly changed coordinates. Its dimension
is `(one free initial rho)+(five switches)-(five endpoint constraints)=1`,
with rank supplied above rather than assumed from this count.

For transversality, use cost covector `-1` in the maximizing convention
and the negative of the minimizing state covector. The augmented maximizing Hamiltonian is minus `rho` times the
minimizing Hamiltonian. Consequently the rho covector has derivative
equal to the active minimizing Hamiltonian, and is constant zero. It therefore meets
both the free initial-rho and free terminal-rho transversality conditions.
The terminal-z covector is `-1`, as required by the Mayer objective.
There are no other free initial directions. Multiplication by positive
`rho` preserves the switching gaps and strict Legendre signs.

All hypotheses of ASZ Theorem 2.6 are therefore met at this **fixed**
positive `P_H`. It has a fixed neighborhood in the uniform topology of
`(Y,z,rho)` on `[0,1]` containing no strictly cheaper admissible path.

## 3. Compactness of arbitrary cheaper measurable competitors

Suppose, contrary to the theorem, that there are `h_n->0` and
strictly cheaper measurable-control competitors `Q_n` for `P_(h_n)`.
Assume `h_n<H`, passing to a tail of the sequence.

The first-exit argument of Section 6.1 of the base note uses vertex
bounds and therefore applies to their convex combinations (1). It
gives a common compact strict-star state box, a uniform frame bound,
`C(Q_n)<1/1000`, and physical durations `T_n<1/3000`. The vector fields,
`y`, and the cost densities are uniformly bounded on this compact set;
`y` is bounded above and below by positive constants.

The physical vertex fields are `y f_i`, because `d tau/dt=y`;
the `f_i` in (3) are the tau-clock fields. Normalize physical time to
`[0,1]`. The normalized integral equation therefore uses the fields
`T_n y_n f_i(Y_n)` and the correspondingly pulled-back controls.
Pass to a subsequence such that
`T_n->T_*`, the states converge uniformly, and the bounded simplex
controls `theta_n` converge weak-star in `L^infinity`. Uniform state
compactness follows from the uniformly bounded derivatives and
Arzela–Ascoli. Weak-star subsequences exist because the time interval
has separable `L^1`; alternatively one can extract the uniformly
Lipschitz primitives of the three controls.

The core's two endpoints are distinct. Since the physical fields are
uniformly bounded, `T_*` cannot be zero. In the integral state equation,
the physical field factors `y_n f_i(Y_n)` converge uniformly and
`T_n` converges, so weak-star convergence of the controls suffices to
pass to the limit. The limit is an admissible
measurable-control path with the core endpoints. Physical cost density
depends only on the state, so its cost is the limit of the costs of `Q_n`
and is at most the core cost.

### 3.1 The limit is precisely the edge core

For `v=gX e_1`, the physical tangent-angle speed after the exact
convexification (1) is

\[
\psi'={2\theta_0\over\gamma_0\|v\|^2}.
\tag{6}
\]

Its coefficient is uniformly bounded below by a positive number on
the compact set. All these tangent vectors stay in a common open
half-plane, so there is no winding ambiguity. The input and output
fix their total angle difference, and that difference for `P_h` is
`O(h)`. Hence

\[
\int_0^{T_n}\theta_{n,0}(t)\,dt=O(h_n).
\tag{7}
\]

Since `T_*>0`, the weak-star limiting control has zero component at
vertex 0. The limiting path is an edge path. The exact inequality (8)
of the base note, including its equality case, now forces it to be
the **unique** reverse-edge core, with the original physical duration
`T_* = T_core`. This uses global edge optimality, not a local minimum
or a Pontryagin condition.

### 3.2 Convergence in the clock used by ASZ

Let `s` denote normalized physical time. Define the cumulative clock

\[
\tau_n(s)=T_n\int_0^s y_n(r)\,dr,
\qquad \rho_n=\tau_n(1).
\tag{8}
\]

The uniform state convergence and `T_n->T_core>0` make `tau_n` converge uniformly and
`rho_n` converge as real numbers to the core clock and total
clock length. The derivatives `T_n y_n(s)` have a uniform positive
lower bound for large `n`. Therefore the inverses of the normalized
clocks `tau_n(s)/rho_n` converge uniformly as well: this follows directly
from the inverse Lipschitz bound and the uniform difference of the
clock functions.

Let `r` denote normalized tau time, let `chi_n` be the inverse of
`s -> tau_n(s)/rho_n`, and write `Y_n^tau(r)=Y_n(chi_n(r))`.
It follows that `(Y_n^tau,z_n^tau,rho_n)` converges uniformly to the
core in normalized tau time. For the cost coordinate, use

\[
z_n^\tau(r)=\rho_n\int_0^r
  \mathcal L\bigl(Y_n^\tau(a)\bigr)\,da,
\]

whose integrand also converges uniformly. No control-dependent-clock
limit or convergence of a switching schedule has been assumed.

## 4. Splice into the fixed strong-minimal extension

The small padded path `P_h` is exactly the middle subpath of the fixed
`P_H` after deleting physical duration `H-h` from each of its outer
control-0 arcs, followed by initial left-frame normalization. Its state
ODE is unaffected by that left normalization.

Replace this middle subpath of `P_H` by `Q_n`, undoing its initial frame
normalization by left multiplication by the fixed-prefix endpoint frame.
Retain the initial and final portions of `P_H`, each of physical duration
`H-h_n`. Both frame and state match at the two joins, so the concatenation
is an admissible measurable-control path with exactly the fixed endpoints
of `P_H`. Its cost is strictly smaller than `C(P_H)` by additivity.

Its total physical duration tends to `2H+T_core`, and the prefix and
suffix converge to the two whole outer arcs of `P_H`. Section 3 makes
the inserted middle converge to the core. Concatenation on intervals
whose lengths converge therefore gives uniform convergence in normalized
physical time to `P_H`. All paths have uniform Lipschitz bounds, so
moving the joins causes no difficulty. Applying the state-only clock
argument (8) to these full concatenations gives convergence in the
uniform augmented-state topology `(Y,z,rho)` of §2.3.

For sufficiently large `n`, these strictly cheaper fixed-endpoint paths
lie in the one fixed strong-optimality neighborhood of `P_H`. This
contradicts ASZ. The contradiction proves the all-measurable theorem.

## Dependencies and review boundary

The proof's new outside dependency is ASZ Theorem 2.6. The remaining
inputs are the explicit core, full-arc needle signs, endpoint normal
columns, edge Hessian, small-cost first-exit box, and exact edge equality
already supplied by the base note. In particular it does not assume
that PMP conditions alone are sufficient, nor that a strong-local
minimum is automatically a global minimum. The fixed-extension splice
is the step connecting the separate local and global statements.

No Lean compilation, typechecking, Lake, or CI was performed. No
numerical optimizer, factor enumeration, or unproved compactness of
an unbounded state domain is used.

Independent review checked ASZ against its primary paper, the exact
constraint space and free-duration transversality, the endpoint-fiber
Hessian, measurable compactness, clock inverses, and the fixed-reference
splice. These are hand reviews, not kernel validation or external peer
review of this new result.

# A six-piece replacement obstruction in the local 021210 domain

Date: 2026-11-06. Hand proof; no Lean compilation, Lake, or CI.

## Theorem and exact scope

**Stronger result available:**
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
adds an explicit application of the published ASZ sufficient-optimality
theorem and proves that sufficiently small members of this same family
have no cheaper competitor among all measurable simplex controls, without
a replacement-piece cap. The self-contained proof below retains its narrower
at-most-six scope and does not depend on that additional theorem.

There are strict-star six-piece windows with word **021210** and
arbitrarily small positive cost, satisfying the input sector conditions
of `BOUNDED_REDUCTION.md`, for which **no replacement with at most six
positive vertex pieces has the same frame and state endpoints and lower
cost**. The replacement may use any word and any positive terminal time.

Thus the original sufficient L3 statement, when quantified over its
explicit necessary superset of minimizer windows and restricted to
replacements with at most six pieces, is false. The examples are not
shown to be windows of an actual closed Reinhardt minimizer. This does
not refute Reinhardt's conjecture, Hales's geometrically embedded link
reduction, or, by itself, the relaxed local target allowing seven or more
replacement pieces. The separate stronger note handles all measurable
full-simplex controls; no such assertion is a premise of the proof here.

The proof first supplies an exact normal first-variation certificate:
the middle reverse four-piece segment has positive cost for every
third-vertex needle, and it extends to positive control-0 padding at
both ends. That necessary condition alone would not prove optimality.
The final finite-piece argument uses compactness, an exact edge dual
inequality, and two endpoint coordinates to exclude **every** shorter
or equal-length word. The number six is used explicitly there.

## 1. A scaled reverse-edge core

Use the original half-plane coordinates, with

\[
q=1/\sqrt3,\qquad
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},\qquad w=y^{-2}.
\]

The star domain is `-q<x<q`, `w>0`, and
`w<1/(q^2-x^2)`. Fix

\[
0<b\le q/10000,\qquad s=b/2.
\tag{1}
\]

On `[0,b]` define

\[
w_*(x)=
\begin{cases}
2q^2/(q+x)^2,&0\le x\le s,\\[3pt]
2q^2(q-s)^2/((q+s)^2(q-x)^2),&s\le x\le b,
\end{cases}
\qquad w_*(-x)=w_*(x).
\tag{2}
\]

Its four controls on `(-b,-s),(-s,0),(0,s),(s,b)` are respectively
`2,1,2,1`. This is twice the positive profile in
`REVERSE_ALTERNATION_OBSTRUCTION.md`; the scaling changes its state and
is essential below. It does not change the four arc factors.

The following bounds hold even under the weaker restriction `b<=q/100`:

\[
19/10<w_*(x)<21/10,
\qquad w_*(x)(q^2-x^2)<7/10<1.
\tag{3}
\]

For example, bound (2) between `2/(1+b/q)^2` and
`2/(1-b/q)^2`. These imply (3). Put

\[
S(x)=\int_0^x w_*(r)\,dr,\qquad L=S(b)>0,
\qquad y_b=w_*(b)^{-1/2}.
\]

The core begins at `x=-b,y=y_b,g=I` and ends at
`x=b,y=y_b` with frame

\[
\Gamma=
\begin{pmatrix}
1-bS_*&-2b+b^2S_*\\ S_*&1-bS_*
\end{pmatrix},\qquad S_*=2L.
\tag{4}
\]

Its physical cost satisfies

\[
C_*={3\over2}\left(2b+S_*+\int_{-b}^b x^2w_*(x)\,dx\right)<10b.
\tag{5}
\]

### The exact edge dual, including a moving-endpoint lower bound

The edge logarithmic derivatives are

\[
b_-(x)=-2/(q+x)\quad(\text{control }2),\qquad
b_+(x)=2/(q-x)\quad(\text{control }1).
\]

Every measurable edge control gives
`b_- w<=w'<=b_+ w` almost everywhere. Set

\[
\mu={\int_0^s x^2w_*(x)\,dx\over\int_0^s w_*(x)\,dx},
\qquad 0<\mu<s^2,
\]
\[
\lambda(x)={1\over w_*(x)}
     \int_0^x(r^2-\mu)w_*(r)\,dr.
\tag{6}
\]

Writing `b_*` for the four successive coefficients of (2),

\[
\lambda'+b_*\lambda=x^2-\mu.
\tag{7}
\]

The only zeros of `lambda` are `-s,0,s`, and its successive signs are
`-,+,-,+`. The proof is direct: on `(0,s)` its defining integral first
decreases and then increases to zero; beyond `s` it is positive; oddness
supplies the negative half. Consequently `lambda>0` selects the upper
bound `b_+`, and `lambda<0` selects the lower bound `b_-`.

Continue `w_*` and (7) a little beyond both endpoints with their outer
vertex controls. The signs remain strict there. For **any** measurable
edge path on a nearby interval `[a',b']`, integration by parts gives

\[
\begin{aligned}
\mathcal A(w):={2\over3}C(w)
 &= (b'-a')+(1+\mu)\int_{a'}^{b'}w
       +\lambda(b')w(b')-\lambda(a')w(a')\\
 &\quad-\int_{a'}^{b'}\lambda(x)(w'(x)-b_*(x)w(x))\,dx\\
 &\ge (b'-a')+(1+\mu)\int_{a'}^{b'}w
       +\lambda(b')w(b')-\lambda(a')w(a').
\end{aligned}
\tag{8}
\]

This is an exact inequality, not a Taylor estimate. The integrand in
the last subtracted integral is nonpositive. For the endpoint data
of (4), equality forces `w'=b_*w` almost everywhere, hence `w=w_*`.
Thus the core is the unique global edge optimum with its endpoints.
Scaling by two does not alter this dual proof.

## 2. Exact third-control needle signs on the core

This section constructs the endpoint covector used later. A positive
needle sign by itself is not being used as an optimality theorem.

Set

\[
K(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},\qquad
A=gK(x),\qquad d\tau=y\,dt,
\qquad d=1-w(q^2-x^2)>0.
\]

The scaled cost `mathcal A=(2/3)C` has `tau`-density

\[
\mathcal L=1+(1+x^2)w.
\]

Direct substitution in the state equations gives the three vertex
fields in the variables `(x,w,A)`:

\[
\begin{array}{c|c|c|c}
 &x_\tau&w_\tau&A_\tau\\ \hline
1,2&1&b_\pm w&A(wE_{21})\\
0&1-r_0&-2r_0xw^2&A(wE_{21}-r_0E_{12})
\end{array}
\qquad r_0=2/d.
\tag{9}
\]

Here `E_ij` denotes a matrix unit. The original measurable simplex
fields are convex combinations of these vertex fields after the
positive trace-denominator weights are absorbed. Thus comparing the
three vertex Hamiltonians is the relevant full-control needle test.

Use the minimizing Hamiltonian `H=mathcal L+p.f`, with normal cost
coefficient one. Let `m,n,k` be the group-covector evaluations on
`E_21,E_12,diag(1,-1)` respectively. On the edge set

\[
p_w=-\lambda,\qquad m=-1-\mu,\qquad k=2mS,
\qquad n=n_0+(1+\mu)S^2,
\]
\[
p_x=-1-(x^2-\mu)w-b_*wp_w.
\tag{10}
\]

These are actual adjoint solutions. In particular
`p_w'+b_*p_w=mu-x^2`,
`p_x'=-2xw-b_*'wp_w`, `m'=0`, `k'=2wm`, and `n'=-wk`.
The active edge Hamiltonian is identically zero. The signs in (6)
make its edge competitor strictly more expensive away from the three
switches.

On an arc of control 2 put `sigma=+1`; on control 1 put `sigma=-1`.
Write

\[
r=q+\sigma x,\qquad W=r^2w,
\]

where `W` is constant on that arc. Define

\[
Q(x)=1+(x^2-\mu)w
       -\sigma w(rw+1/r)p_w,
\qquad B(x)=n(x)-Q(x).
\tag{11}
\]

The zero-control gap is exactly

\[
\boxed{H_0-H_{\rm active}=-2B/d.}
\tag{12}
\]

For verification, before substitution the bracket multiplying `-2/d`
is

\[
p_x+n+2xw^2p_w+(d/2)b_*wp_w.
\]

Using (10) and `b_*=-2sigma/r` reduces this bracket to (11).
Because `w` is even and `lambda` is odd, `Q` is even. Choose

\[
n_0=Q(b)-(1+\mu)L^2.
\tag{13}
\]

Then `B(-b)=B(b)=0`: control 0 ties the adjoining edge control at
both ends.

### A hand sign certificate over the whole interval

Differentiation on each open vertex arc, using `S'=w`, gives

\[
\boxed{ B_{SS}
 =2\left(1-{q^2\over W}-\sigma qx(1+1/W)\right). }
\tag{14}
\]

One short check is to set `z=wp_w`, so `z'=w(mu-x^2)`.
Equation (11) then gives

\[
Q_S=2x+\sigma(W-1)(x^2-\mu)/r+(W+1)z/W,
\]

and a second derivative gives
`Q_SS=2mu+2q^2/W+2sigma qx(1+1/W)`. Subtract this from
`n_SS=2(1+mu)` to obtain (14).

Bounds (3) and `b<=q/100` imply

\[
3/5<W<3/4,\qquad |qx|\le1/300.
\]

Consequently (14) is at least
`2(1-5/9-2/225)=196/225>4/5` on each open arc.

At a switch `x_i=-s,0,s`, one has `p_w=0`. Taking the one-sided
values in the displayed formula for `Q_S` shows that `B_S` has a
negative jump of magnitude

\[
J_i=2q\left({1\over q^2-x_i^2}-w(x_i)\right)|x_i^2-\mu|.
\tag{15}
\]

The expression in parentheses is positive by strict star. Since
`|x_i^2-mu|<=s^2` and `q^2-s^2>q^2/2`,

\[
\sum_iJ_i\le3b^2/q\le3b/100.
\tag{16}
\]

Use the nonnegative Dirichlet Green function for `-d^2/dS^2` on
`[-L,L]`. It is at most `L-|S|` at any fixed observation point `S`.
Equations (14)--(16), with zero endpoint values, therefore give

\[
\begin{aligned}
B(S)
 &\le {2\over5}(S^2-L^2)
          +\left(\sum_iJ_i\right)(L-|S|)\\
 &\le-\left({2\over5}L-\sum_iJ_i\right)(L-|S|)\\
 &\le-{7b\over10}(L-|S|)<0\qquad(-L<S<L).
\end{aligned}
\tag{17}
\]

The last estimate uses `L>(19/10)b`, so the coefficient before
`L-|S|` is at least `(19/25-3/100)b=73b/100`.
This Green-function step can equivalently be proved by subtracting
`(2/5)(S^2-L^2)+sum_i J_i G(S,S_i)` and observing that the difference
is convex with zero endpoint values.

Thus every control-0 needle strictly inside the core has positive
reduced first variation. Its physical-time gap for the scaled cost `mathcal A` is

\[
\Gamma_0(x)=y(x)\bigl(H_0-H_{\rm active}\bigr)>0,
\qquad \Gamma_0(-b)=\Gamma_0(b)=0.
\tag{18}
\]

All signs are proved on complete intervals, not sampled points.

## 3. Add two positive control-0 arcs

Extend the core backwards by control 0 for physical duration `h`, and
forwards by control 0 for the same duration. Normalize the initial
frame of the resulting segment to `I`. For every sufficiently small
`h>0` this gives a strict-star window with word `021210`; call it
`P_h`, with initial state `i_h` and terminal pair `E_h`.

For explicit factors put

\[
P={q-s\over q-b},\qquad Q_1={q+s\over q},
\qquad p_0={\sqrt3(b^2+y_b^2-q^2)\over y_b}>0.
\]

Its six factors in the repository's triangular chart are

\[
\boxed{(e^{2h/p_0},P,Q_1,Q_1,P,e^{2h/p_0}).}
\tag{19}
\]

Both outer active margins equal `p_0`; the two outer physical durations
are exactly `h`. Every factor in (19) is strictly greater than one.
The initial state is the inverse control-0 flow of `Phi(-b,y_b)`.

The costate (10) also extends onto these arcs. At the first join the
control-0 gap has strictly positive derivative into the core, and at
the last join it has strictly negative derivative out of the core, by
(17). The switching-function derivative agrees from either active
Hamiltonian at a tie: the difference is the Poisson bracket of that
switching function with itself, which is zero. Thus, for sufficiently
short padding, control 0 uniquely minimizes the Hamiltonian on both
outer open arcs. The other edge control has a strict gap at each
join by (6). All five switches are simple. This gives an exact normal
first-order certificate on all six pieces.

For context, the same-word obstruction is stronger than a stationary
numerical example. On the fixed-endpoint reverse-edge fiber the old
constrained Hessian is

\[
\sum_{i=1}^3 k_iw(x_i)(\mu-x_i^2)v_i^2>0
\]

for every nonzero tangent vector: the `k_i` signs are `-,+,-`, while
`mu-x_i^2` has signs `-,+,-`. The two endpoint constraints have rank
two. This is the sign opposite to the forward-alternation exclusion.
The proof below uses the global edge dual (8), not just this Hessian.

## 4. Two endpoint coordinates that detect control 0

For a fixed initial pair `g_i=I,X_i`, put

\[
c_i=e_1,\qquad v_i=X_i e_1,\qquad
c_e=g_e e_1,\qquad v_e=g_eX_e e_1,
\]
\[
N_1=\det(v_i,v_e),\qquad N_2=\det(v_i,c_e-c_i).
\tag{20}
\]

Both coordinates vanish on **every** pure-edge path. Its contact-0
curve is straight, with positive tangent scale. More explicitly, if
its initial coordinate is `a`, final state coordinates are `(b',w_b)`,
and `S'=int_a^(b') w`, its final frame is

\[
g_e=\begin{pmatrix}
1+aS'&a-b'-ab'S'\\ S'&1-b'S'
\end{pmatrix}.
\tag{21}
\]

Conversely, (20) equal to zero and `det g_e=1` force (21), near the
reference endpoint. Indeed `N_2=0` fixes the first column to
`(1+aS',S')`; `N_1=0` and the determinant then fix the second column.
The differentials `dN_1,dN_2` are independent. For instance `N_2`
varies with the first column of `g_e`, while the derivative of `N_1`
with respect to final `b'`, holding that frame fixed, is nonzero.
Thus the edge endpoints form a smooth three-dimensional submanifold
of the five-dimensional final `(g,X)` space.

### The normal column of a zero-control needle

Along the reference core, `v(x)=(a,1)/y(x)`, with `a=-b`. An inserted
control-0 arc of physical duration `epsilon` at `x` changes `(N_1,N_2)`
to first order by `epsilon nu(x)`, where

\[
\boxed{
\nu(x)=A(x)\bigl(1,\ y_b(L-S(x))\bigr),\qquad
A(x)={2y(x)^2\over\gamma_0(x)y_b^2}>0,
}
\tag{22}
\]

and `gamma_0=(x^2+y^2-q^2)/y>0`.

Here is a direct derivation. Put `V=gX`, `c=ge_1`, and `v=Ve_1`.
The state equations give

\[
\det(v,v')=2u_0/(-\operatorname{tr}(Z_uX)).
\]

On the reference edge the tangent scale is `rho(x)=y_b/y(x)`.
The needle produces a normal tangent component
`2/(gamma_0 rho(x))`; subsequent edge transport multiplies it by
`rho(b)/rho(x)`, giving the first coordinate of (22). Integrating that
normal tangent component to the endpoint gives the second, since
`int_x^b rho(t)/rho(b) dt=y_b int_x^b w`.

In particular

\[
\nu(-b)=A(-b)(1,2y_bL),\qquad
\nu(b)=A(b)(1,0)
\tag{23}
\]

are linearly independent. The two positive padding arcs in `P_h` give

\[
N(i_h,E_h)=h\bigl(\nu(-b)+\nu(b)\bigr)+O(h^2).
\tag{24}
\]

The changing initial state does not add a normal term: the two
coordinates vanish identically on pure-edge paths for every initial
state. This observation also prevents uncontrolled quadratic core
variations from contaminating the normal comparison below.

## 5. A smooth endpoint lower bound for every deleted-edge path

For initial coordinates `(a',w_a)` and arbitrary final data
`(g_e,b',w_b)` near the core endpoint, define

\[
\Psi(i,E)=(b'-a')+(1+\mu)(g_e)_{21}
          +\lambda(b')w_b-\lambda(a')w_a.
\tag{25}
\]

On pure-edge paths, `(g_e)_21=S'`, so (8) says exactly
`mathcal A>=Psi`. This remains true for arbitrary measurable edge
controls, not only four-piece controls.

Let `ell` be the terminal endpoint covector of the first-variation
certificate above, with sign chosen so that
`delta mathcal A=ell(delta E)` on active-arc duration variations.
The four edge-duration variables map with rank three to edge endpoints:
use final `b'` as one coordinate, and the rank-two map
`(log w(b'),int w)` from the three switches as the other two.
The endpoint ranks follow from the strictly ordered tails in
`FORWARD_ALTERNATION_EXCLUSION.md`, Section 2, regardless of switch
orientation.

Because `mathcal A-Psi` is nonnegative on an open neighborhood of
these edge parameters and equals zero at the reference, its first
derivative vanishes there. Therefore `ell-d_E Psi` annihilates the
edge endpoint tangent space. By (20)--(21), there are constants
`alpha,beta` such that the smooth function

\[
\mathcal F(i,E)=\Psi(i,E)+\alpha N_1(i,E)+\beta N_2(i,E)
\tag{26}
\]

has `d_E mathcal F=ell` at the reference. On **every** edge path
`mathcal F=Psi`, so its exact lower bound is unchanged.

An inserted control-0 arc has first variation of
`mathcal A-mathcal F` equal to the gap (18). Active-edge variations
have zero first variation. Variations of the initial state also have
zero first variation when restricted to the edge family: the smooth
nonnegative function `mathcal A-Psi` has an interior minimum zero
there. The two padding gaps vanish at the endpoints, hence

\[
\mathcal A(P_h)-\mathcal F(i_h,E_h)=O(h^2).
\tag{27}
\]

Only ordinary differentiation of finite smooth flow compositions is
used in this argument. No Hamiltonian sufficiency theorem is assumed.

## 6. Excluding every replacement with at most six pieces

Suppose the theorem were false for arbitrarily small padding. There
would be `h_n->0` and strictly cheaper vertex competitors `Q_n`, each
having at most six positive pieces and the same input `i_(h_n)` and
output `E_(h_n)` as `P_(h_n)`. Merge adjacent equal labels first.
We derive a contradiction.

### 6.1 Uniform compactness and a bound on total control-0 duration

For small `h`, (1) and (5) give `C(P_h)<1/1000`. Every competitor has
`T<=C/3<1/3000`, because the physical cost density of a star state is
at least three. Its initial coordinates satisfy
`|x_i|<1/100` and `2/3<y_i<3/4`.

Before a first exit from

\[
|x|\le1/10,\qquad 3/5\le y\le4/5,
\tag{28}
\]

the vertex fields obey `|x'|<40`, `|y'|<=5`. For the zero vertex use
`x^2+y^2-q^2>=2/75` in

\[
x'=y-2y^3/(x^2+y^2-q^2),\qquad
y'=2xy^2/(x^2+y^2-q^2).
\]

For the other vertices use `x'=y` and
`|y'|=y^2/(q\mp x)`. Integration up to a proposed first exit, over
time less than `1/3000`, contradicts that exit. Thus all states stay
in a fixed compact subset of the strict star domain. On it `||X||<3`,
so `g'=gX` gives a uniform frame bound and
`||g-I||<=exp(3T)-1<1/100`.

In particular `v= gX e_1` stays in the upper half-plane, uniformly
away from zero. Its lifted angle has no branch ambiguity. Its total
increase is fixed by the endpoint data, and is `O(h_n)`. The angle
speed is zero on vertices 1,2 and is

\[
2/(\gamma_0\|v\|^2)>0
\]

on vertex 0, uniformly bounded below on this compact set. Therefore

\[
\text{total physical duration of control 0 in }Q_n=O(h_n).
\tag{29}
\]

There is no cancellation in this estimate.

There are finitely many reduced words of length at most six. Pass to
a subsequence with fixed word, and then to a convergent subsequence
of its bounded nonnegative durations. Smooth dependence of the flows
on the compact set gives a limiting trajectory. Its zero-control
arcs disappear by (29), its endpoints are the core endpoints, and
its cost is at most `C_*`. The exact edge inequality (8), including
its equality case, forces this limit to be precisely the reverse
four-piece core. It has four strictly positive edge pieces, in order
`2121`. No minimizer-attainment assumption is needed for this subsequence
argument.

### 6.2 Positive interior gaps force all leading zero-control mass to the ends

Delete every control-0 piece of `Q_n`, retaining the other physical
arc durations and the same initial state; call the resulting pure-edge
path `D_n`. The state and frame fields are uniformly smooth on the
compact set. By (29), deletion changes its endpoint and cost by
`O(h_n)`, and `D_n` converges to the core. Since the original endpoint
is exactly `E_(h_n)=E_0+O(h_n)`, the deleted path endpoint is also
`O(h_n)` from the core endpoint. The exact inequality (8) gives

\[
\mathcal A(D_n)-\mathcal F(i_{h_n},E(D_n))\ge0.
\tag{30}
\]

Let `epsilon_(j,n)` be the durations of its deleted zero-control
pieces, and let `x_j` be their limiting positions on the reference
core, after another subsequence. There are at most six such positions.
Taylor-expand the finite composition of flows in those deleted
durations at zero. The second derivatives are uniformly bounded,
and the first derivatives converge to the reference needle gaps.
Using (29) and (30) gives

\[
\mathcal A(Q_n)-\mathcal F(i_{h_n},E_{h_n})
 \ge\sum_j\Gamma_0(x_j)\epsilon_{j,n}+o(h_n).
\tag{31}
\]

This expansion is uniform even when two edge pieces merge after a
zero-duration deletion: the original finite flow composition is
smooth at zero duration. First-order errors are `o(1)` times the
total deleted duration; second-order errors are `O(h_n^2)`.

The assumed cheaper cost and (27) imply that the right side of (31)
is at most `O(h_n^2)`. Pass to limits of the bounded nonnegative
numbers `epsilon_(j,n)/h_n`. By (18), any positive limiting mass must
be placed at `x_j=-b` or `x_j=b`. No interior point can carry positive
normalized zero-control mass.

### 6.3 Both endpoints must carry positive mass

The coordinates (20) vanish exactly on `D_n`. Their same finite-flow
Taylor expansion, now using (22), gives

\[
{N(i_{h_n},E_{h_n})\over h_n}
 =\sum_j {\epsilon_{j,n}\over h_n}\nu(x_j)+o(1).
\tag{32}
\]

There is no term depending only on the deviation of `D_n` from the
core: `N` vanishes on every edge path, not merely to first order.
By (24), (31), and the independence in (23), the total limiting
normalized durations at `-b` and `b` must each equal **one**.
Thus there are at least two distinct zero-control pieces, one at
each end in the limit.

The limit already needs four positive edge pieces. At most six
pieces are available. Hence there are exactly two zero-control
pieces and exactly four edge pieces, all of the latter with positive
limits. The zero pieces must be the first and last pieces, since a
positive core piece cannot precede a zero piece whose limiting time
is the initial endpoint, or follow one at the final endpoint.
Consequently the fixed word of this subsequence is exactly

\[
021210.
\tag{33}
\]

This is where the at-most-six restriction enters. More pieces could
place small zero-control arcs close to an endpoint while splitting
an adjacent edge arc; this argument does not exclude that possibility.

### 6.4 The same word cannot be cheaper

There is a local coordinate description of the full endpoint map by
five variables: the initial and final zero-control durations, and the
three intervening edge endpoint coordinates `(b',w_b,S')` from (21).
At zero padding, the three edge derivatives span the kernel of `dN`.
The two outer derivatives have the independent normal columns (23).
The resulting five-by-five derivative is invertible.

The implicit function theorem, with initial state as an additional
parameter, therefore gives a local inverse uniformly near the
reference zero-padding point. For the input and output of `P_h`, any
nearby `021210` path must have exactly the same two outer durations
`h,h` and exactly the same three middle endpoint coordinates as
`P_h`. This conclusion does not follow from a dimension count: the
rank-three edge map and the two independent normal columns prove
invertibility.

The middle segment now has precisely the original fixed edge endpoints.
Inequality (8) gives its cost at least the core cost, with equality
only for the core. The two outer trajectories are fixed by their
states, controls and durations, so their costs also agree with the
reference. This contradicts strict cheapness of `Q_n`.

The contradiction proves that for every fixed `b` as in (1), there
exists `h_0(b)>0` such that every `0<h<h_0(b)` has the claimed
at-most-six replacement obstruction. The assertion is an existence
counterexample with a hand proof; no numerical lower bound on `h_0`
is needed or claimed.

## 7. Input eligibility and consequences

All six factors (19) are positive, and (3) plus continuity gives strict
star membership throughout the padded window. Its cost tends to `C_*`
as `h->0`; by taking `b` small and then `h` small it can be arbitrarily
small, and in particular lies below the octagon sublevel.

The sector restriction is also satisfied. With initial frame `I`,
all contact curves have positive polar angular speed by strict star.
For (28) and `||g-I||<1/100`, their angular speeds are uniformly below
four. The total time is below `1/3000`, so no contact advances as much
as `pi/3`. Every contact stays strictly between its initial ray and
its successor ray for every positive time in this window. The fixed
linear change to triangular coordinates preserves precisely those
oriented radial cones. Thus these examples belong to the explicit
local input domain, not merely to a sampled or unconstrained superset
of that domain.

The example shows why a positive-dimensional same-word fiber is not
an improvement theorem. Here the reverse-edge fiber is strictly
minimizing, all full-control first-order needle signs have the proper
optimality orientation, and the complete at-most-six comparison is
an obstruction. The companion GLOBAL_MINIMUM note now also excludes a cheaper
arbitrary measurable replacement for sufficiently small pads, using a separate
published sufficiency theorem and a fixed-reference limiting argument.

It remains possible that the windows which occur in actual closed
global minimizers obey additional conditions that exclude these
examples. No global closure or geometric embedding of this local
window has been established. The original five-template coverage
argument remains a combinatorial statement; this result concerns one
of its originally proposed analytic sufficient inputs.

## References and validation boundary

- `REVERSE_ALTERNATION_OBSTRUCTION.md`: reverse four-piece edge dual,
  endpoint reconstruction, and the original unscaled example.
- `EDGE_SWITCH_BOUND.md` and `FORWARD_ALTERNATION_EXCLUSION.md`: exact
  edge endpoints, rank-two switch map, and constrained Hessian formula.
- `BOUNDED_REDUCTION.md`: the local input domain and the distinction
  between a sufficient superset and actual minimizing windows.
- Hales, *On the Reinhardt Conjecture*, Section 7.6, Conjecture 56:
  https://arxiv.org/pdf/1103.4518 . Its geometric embedding hypothesis
  is stronger than the local sector tests alone.

Every inequality used above has an analytic proof. No floating-point
optimizer, sampled sign, interval certificate, Lean compilation, or
kernel-validation claim is a premise. The proof explicitly stops at
six replacement pieces and does not claim that PMP conditions alone
are sufficient for unrestricted optimality.

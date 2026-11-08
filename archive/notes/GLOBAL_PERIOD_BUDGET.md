# A global continuation obstruction for the small reverse-six family

Date: 2026-11-07. Hand argument; no Lean, Lake, typechecking, or CI.

## Result and scope

For every core size `0<b<=q/10000`, the exact padded
`021210` windows of
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md)
cannot occur in a **closed free-time Pontryagin extremal with the twisted
state and costate endpoints**. This holds for every sufficiently small
positive padding for which that note supplies the full-rank window.
In particular, these windows cannot occur in an actual global minimizer
of cost at most the octagon's.

The obstruction is stronger than a cost estimate for this family. Its
unique normalized adjoint forces the outgoing control 0 all the way to
the strict-star boundary in finite time, without a further switch.
A twisted periodic extremal extends indefinitely inside the strict star,
which is incompatible with that continuation.

This does not contradict
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md):
the same windows are global minima for their **fixed local endpoints**.
A complete-period minimizer has additional adjoint closure conditions.
No cheaper local replacement is constructed or asserted here. Nor is
geometric embedding in an arbitrary nonextremal closed trajectory ruled
out.

The independent endpoint-tie filter in
[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md), Section 6, already
excludes these pads when they are required to be **six complete pieces**:
their external cuts have strict inactive gaps. The present result also
excludes occurrence as an arbitrary subwindow whose first and last
control-0 portions were cut inside longer pieces. It uses the forced
future trajectory, rather than assuming a switch at either external cut.

The proof gives a finite set of explicit inequalities on a state and
its adjoint that excludes a larger continuation region. It does not
exclude every L3 window, prove a uniform number of pieces, or settle any
of the other four local templates. The whole-period budget remains
necessary in a general repair: the standard forward families in
[LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md) satisfy periodic
PMP but exceed that budget. The present reverse-family obstruction
already occurs before any budget comparison is needed.

## 1. The closed lift cannot choose a different local adjoint

Use the scaled cost `A=(2/3)C`, with minimizing Hamiltonian
`H=L+p.f` and normal cost coefficient one, as in the reverse-six note.
Fix a sufficiently small positive padding `h`. The six independent
physical durations of `P_h` have a rank-five endpoint map to the actual
five-dimensional `(g,X)` state manifold. Section 6.4 of that note proves
this by the rank-three middle-edge map and two independent outer normal
columns, not by counting variables.
The independent full-domain result in
[LOCAL_MIXED_SIX_RANK.md](LOCAL_MIXED_SIX_RANK.md) now proves rank five
for every positive strict-star L3 input; only the earlier family-specific
rank is needed below. The common global implication is also developed in
[GLOBAL_PERIODIC_PMP.md](GLOBAL_PERIODIC_PMP.md).

For a free-time Pontryagin lift, the first-variation identity for those
six independent durations is

\[
\lambda_0\,d\mathcal A=\ell_e\circ dE.               \tag{1}
\]

Here `ell_e` is the signed terminal covector; in the minimizing
Hamiltonian convention it is the negative terminal canonical covector.
The active Hamiltonian is zero because time is free. If `lambda_0=0`,
surjectivity of `dE` forces the terminal covector to vanish. The homogeneous
adjoint equation then makes the entire abnormal lift zero, contrary to
nontriviality. Thus every such lift is normal. Normalize `lambda_0=1`.
Equation (1) now uniquely determines `ell_e`, and the linear adjoint
initial-value problem determines the whole local lift.

Consequently any global lift containing `P_h` restricts to the exact
adjoint already constructed in the reverse-six note. Multiplying the
cost by a positive constant or changing from minimizing to maximizing
conventions changes only its common normalization, not the maximizing
control or the argument below.

A genuine closed lift satisfies, in the original matrix conventions,

\[
\begin{aligned}
g(T)&=R,&X(T)&=R^{-1}X(0)R,\\
\Lambda_1(T)&=R^{-1}\Lambda_1(0)R,&
\Lambda_R(T)&=R^{-1}\Lambda_R(0)R.
\end{aligned}                                                     \tag{2}
\]

These are Hales--Vajjha, Section 6.6, equation (6.6.1). They allow the
state, adjoint, and control to be continued through every seam by the
same cyclic conjugation. The continuation remains strict star for all
positive time. The group-costate equation and its conserved spatial
form are given in their Section 6.5; no extra choice of group covector
at the seam is available.

On an interval with a unique minimizing vertex, Hamiltonian minimality
forces that vertex almost everywhere, even among arbitrary measurable
simplex controls. The smooth vertex state and adjoint equations then
have unique continuation. At a transverse two-way tie, the derivative
of the switching function is the same under either tied Hamiltonian:
the difference is its Poisson bracket with itself. Thus the prescribed
outgoing branch is also forced through the switches used here. With the
original state-dependent convex control weights, the same assertion holds:
on the maximizing locus all supported vertex Hamiltonians share the value
zero, so the extra term `sum H_i d theta_i` vanishes. The Hamiltonian
vector field is the convex combination of the tied vertex fields there.

## 2. An explicit criterion forcing a control-1 arc to leave the star

This section applies to any normal lift in the indicated region, not
only to the reverse-six family.

Put

\[
q=1/\sqrt3,\qquad w=y^{-2},\qquad
K(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},\qquad A=gK(x),
\qquad d\tau=y\,dt.
\]

The strict star is

\[
-q<x<q,\qquad w>0,\qquad d=1-w(q^2-x^2)>0.
\]

Let `m,n,k` be the group-covector evaluations on
`E_21,E_12,diag(1,-1)`. The scaled running cost and vertex fields are
those of equation (9) in the reverse-six note. On a control-1 arc,

\[
x_\tau=1,\qquad w_\tau={2w\over q-x},\qquad
A_\tau=A(wE_{21}),\qquad
\mathcal L=1+(1+x^2)w.                            \tag{3}
\]

The group equations give

\[
m_\tau=0,\qquad k_\tau=2wm,\qquad n_\tau=-wk.
\]

Write

\[
\mu=-1-m,\qquad
W=(q-x)^2w>0.
\]

Both `mu` and `W` are constant along this arc. The state adjoint obeys

\[
p_w'+{2p_w\over q-x}=\mu-x^2,                    \tag{4}
\]

where the prime in (4) is differentiation with respect to `x`, which
coincides with `tau` on this arc. The active equation `H_1=0` gives

\[
p_x=-1-(x^2-\mu)w-{2w\over q-x}p_w.
\]

Define the third-control comparison function

\[
\begin{aligned}
Q&=1+(x^2-\mu)w+w\left((q-x)w+{1\over q-x}\right)p_w,\\
B&=n-Q.
\end{aligned}                                                     \tag{5}
\]

The two inactive gaps are exactly

\[
H_2-H_1=-{4q\over q^2-x^2}\,wp_w,
\qquad
H_0-H_1=-{2B\over d}.                             \tag{6}
\]

Hence negative `p_w` and negative `B` make control 1 the unique
minimizing vertex.

### 2.1 The exact third-gap differential identity

Suppose the arc starts at `x=a` with `0<a<q`, and put

\[
c={W\over q-a},\qquad
S(x)=\int_a^x w(r)\,dr={W\over q-x}-c.
\]

Along this single vertex arc, every normalized adjoint satisfying
`H_1=0` has

\[
\boxed{\quad B_{SS}={8\over3}-{2q(W+1)\over S+c}.\quad}           \tag{7}
\]

Here no special choice of the group covector or its integration
constants is assumed. One direct verification sets `u=S+c=W/(q-x)`.
Then (4) becomes

\[
(u^2p_w)'=W(\mu-q^2)+{2qW^2\over u}-{W^3\over u^2},
\]

where this prime is differentiation in `u`. After integration and
substitution in (5), `Q` has the form

\[
Q=(\mu-q^2)u^2+2q(W+1)u\log u+\alpha u+(W+1)^2.
\]

The arbitrary constant `alpha` does not affect its second derivative.
Also `n_{SS}=-2m=2(1+mu)`. Subtracting gives (7), since `q^2=1/3`.
In particular,

\[
B_S(S)=B_S(0)+F(S),\qquad
F(S)={8\over3}S-2q(W+1)\log(1+S/c).              \tag{8}
\]

### 2.2 The finite escape test

The forward control-1 state first meets the star boundary at

\[
x_e=q{1-W\over1+W},\qquad
S_e={1+W\over2q}-c>0.                             \tag{9}
\]

Indeed `d>0` is equivalent to `W(q+x)/(q-x)<1`. The initial strict-star
condition implies `a<x_e<q`. Put

\[
\mathscr R=1+{S_e\over c}
 ={(1+W)(q-a)\over2qW}>1.                         \tag{10}
\]

Assume that, at the initial point of an outgoing control-1 arc,

\[
\begin{gathered}
0<a<q,\quad p_w(a)\le0,\quad \mu\le a^2,\\
B(0)<0,\quad B_S(0)\le0,\quad \mathscr R\ge5.
\end{gathered}                                                     \tag{11}
\]

Then both gaps in (6) are strictly positive for every `a<x<x_e`.
For the edge gap, multiply (4) by its positive integrating factor.
Its source `mu-x^2` is strictly negative for `x>a>0`, so `p_w(x)<0`.

For the third gap, the exact endpoint value in (8) is

\[
F(S_e)=2q(W+1)
 \left(2(1-1/\mathscr R)-\log\mathscr R\right)<0.  \tag{12}
\]

To verify the strict inequality without decimals, the function
`log r-2+2/r` is increasing for `r>2`, and

\[
\log5
 =2\int_0^{2/3}{dt\over1-t^2}
 >2\sum_{j=0}^3{(2/3)^{2j+1}\over2j+1}
 ={122492\over76545}
 ={8\over5}+{4\over15309}>{8\over5}.              \tag{13}
\]

The strict integral inequality follows by expanding a finite geometric
sum with its positive remainder. Finally,

\[
F''(S)={2q(W+1)\over(S+c)^2}>0.
\]

A convex function lies below its endpoint chord. Since `F(0)=0` and
`F(S_e)<0`, it follows that `F(S)<0` for `0<S<=S_e`. Equations (8)
and (11) give `B_S<0`, hence `B(S)<B(0)<0` throughout that interval.
This proves both gap signs.

The boundary is reached in finite physical time:

\[
t_e-t_a=\int_a^{x_e}{dx\over y(x)}
 =\sqrt W\log{q-a\over q-x_e}
 =\sqrt W\log\mathscr R<\infty.                 \tag{14}
\]

At the limiting endpoint, `y=(q-x_e)/sqrt W` is positive and `|x_e|<q`;
it is exactly `d=0` that fails. No switch is possible before this exit,
because the active vertex stays unique. Therefore an extremal satisfying
(11) cannot have an indefinitely strict-star PMP continuation. Cyclic
relabeling gives the analogous exclusion for either other vertex.

The threshold 5 is merely a convenient exact certificate. The proof
also works with the weaker scalar inequality
`log R > 2(1-1/R)` in place of `R>=5`.

## 3. The exact reverse-six family satisfies the escape test

Retain the original core notation from the reverse-six note:

\[
0<b\le q/10000,\qquad s=b/2,
\]

\[
w_*(x)=
\begin{cases}
2q^2/(q+x)^2,&0\le x\le s,\\
2q^2(q-s)^2/((q+s)^2(q-x)^2),&s\le x\le b,
\end{cases}
\qquad w_*(-x)=w_*(x).
\]

The core has controls `2121`. Write `y_b=w_*(b)^(-1/2)` for its final
height. Its normal adjoint has strict full-control gaps on the open
core, a transverse final `1 -> 0` switch, and the positive control-0
padding. These are the exact statements proved in Sections 2--3 of the
base note.

Conjugate state and frame by `R^{-1}`, which takes old control `0` to
new control `1`, old `1` to new `2`, and old `2` to new `0`. This rotation
preserves the physical cost and the normal coefficient. Let the new
outgoing arc start at `x=a_b`, `y=tilde y_b`, and put

\[
W_b=(q-a_b)^2/\widetilde y_b^2.
\]

At `b=0` the limiting old state is `i/sqrt2`. Its rotated state is

\[
a_0={3q\over5},\qquad
\widetilde y_0={4\sqrt2\over5},\qquad
\widetilde w_0={25\over32},\qquad W_0={1\over24}.  \tag{15}
\]

The rotated state is strict star. Moreover `a_b>0` throughout the stated
range: its numerator is `sqrt3(1-b^2-y_b^2)-2b`, which is positive from
`y_b^2<1/2` below, `b<1/100`, and `sqrt3>1`. Hence `0<a_b<q`.

At the new `2 -> 1` switch, equation (6) gives `tilde p_w(a_b)=0`.
Its strict outgoing crossing forces

\[
\widetilde\mu-a_b^2<0.                            \tag{16}
\]

Indeed the coefficient of `p_w` in the first gap of (6) is negative;
at its zero, the positive outgoing derivative of that gap has the sign
of `-(tilde mu-a_b^2)` by (4). The same switching derivative is obtained
from either tied Hamiltonian. The old inactive control 2 has a strict
positive gap at the final core switch, so the new third gap is strict:

\[
\widetilde B(0)<0.                                \tag{17}
\]

### 3.1 The exit ratio exceeds five exactly

Set

\[
D=b^2+y_b^2-q^2>0,\qquad t=b/q\in(0,1).
\]

The explicit rotated half-plane coordinates give

\[
W_b={3D^2\over4y_b^2},\qquad
\mathscr R_b=1+{2(1+\sqrt3 b)\over3D}.             \tag{18}
\]

For example, the denominator of the Mobius map `R^{-1}.(b+iy_b)` is
`1-2sqrt3 b+3(b^2+y_b^2)` after multiplication by four. Substitution
in (10) yields the second identity. The cancellation can also be
checked from

\[
4y_b^2+3D^2
 ={(3D+2-2\sqrt3 b)(3D+2+2\sqrt3 b)\over3}.
\]

The core's exact endpoint value has the simpler form

\[
y_b^2={1\over2}\left(1-{t^2\over2-t}\right)^2.
\]

Consequently

\[
D-{1\over6}
 ={t^2(5t^2-2t-4)\over6(2-t)^2}<0\qquad(0<t<1). \tag{19}
\]

The quadratic in the numerator is negative on `[0,1]`: convexity
bounds it above by the larger of its endpoint values `-4,-1`.
Thus `0<D<1/6`, and (18) gives `mathscr R_b>5` for every positive core
size under consideration. No limiting or sampled logarithm test is
being substituted for this inequality.

### 3.2 The initial third-gap derivative is negative, with explicit bounds

The remaining sign is

\[
\boxed{\quad \widetilde B_S(0)<0\quad
       \text{for every }0<b\le q/10000.\quad}                    \tag{20}
\]

We prove it directly, without an unspecified small-parameter remainder.
Use unadorned variables for the old core and its old `tau` clock. The
exact Green-function bound (17) of the base note, together with
`B(L)=0`, gives its left endpoint derivative

\[
B_{\rm core,S}(b)\ge 7b/10>0.                    \tag{21}
\]

The notation means the derivative at `x=b`, expressed in the old edge
coordinate `S`. Along the incoming old control 1, `x_tau=1`. At the
final tie, `H_1-H_0=2B_core/d` and `B_core(b)=0`, so

\[
(H_1-H_0)'={2wB_{\rm core,S}\over d}>0.            \tag{22}
\]

The Poisson identity at a tie makes (22) also the derivative along the
outgoing old control 0. All primes below denote that outgoing old
`tau` derivative, evaluated at the same switch.

For the other old edge gap set

\[
G_{21}=H_2-H_1=Cp_w,\qquad
C=-{4qw\over q^2-x^2}<0.
\]

At the switch `p_w=-lambda(b)<0`. Put `r_0=2/d`. Directly
differentiating the control-0 Hamiltonian and using `H_0=H_1=0` gives

\[
p_w'=\mu-x^2+r_0w(3x-q)p_w.
\]

The old control-0 state equations are
`x'=1-r_0`, `w'=-2r_0xw^2`. Consequently

\[
G_{21}'=C\left(\mu-x^2+\mathcal D p_w\right),
\qquad
\mathcal D={2x(1-r_0)\over q^2-x^2}+r_0w(x-q)<0. \tag{23}
\]

Here `x=b>0`, `r_0>2`, and `x<q`. The necessary size estimates all
follow from the base note's bounds:

\[
b<1/100,\quad w<21/10,\quad d>3/10,\quad
r_0<7,\quad q<3/5,\quad q^2-b^2>3/10.
\]

They imply

\[
|\mathcal D|<40b+{441\over50}<10.
\]

Also `0<mu<b^2/4`. From the integral defining `lambda`, its positivity
and `19/10<w_*<21/10` give

\[
0<\lambda(b)
 \le {1\over w_*(b)}\int_0^b x^2w_*(x)\,dx
 <{7\over19}b^3<{b^3\over2}.
\]

Thus the parenthesis in (23) is strictly negative:

\[
\mu-b^2+\mathcal D p_w
 <-{3b^2\over4}+5b^3<0.
\]

Since `C<0`, this proves `G_21'>0`. Combining with (22), the old
third comparison

\[
G=H_2-H_0=(H_2-H_1)+(H_1-H_0)
\]

satisfies, at the outgoing switch,

\[
G>0,\qquad G'>0.                                  \tag{24}
\]

It remains to track the rotation and clock exactly. Set
`kappa=y_old/y_new>0`. The new tau Hamiltonians are the corresponding
old ones multiplied by `kappa`. On the zero active Hamiltonian,
`d/d tau_new=kappa d/d tau_old`. Since the old control 2 becomes the
new control 0, their positive trace denominators satisfy

\[
\widetilde\gamma_0=\gamma_2={2q(x+q)\over y},
\qquad
\widetilde d={\widetilde\gamma_0\over\widetilde y}.
\]

Therefore, along the outgoing old control-0 branch,

\[
\widetilde B
 =-{\widetilde d\over2}\kappa G
 =-q(x+q)\widetilde w\,G.                          \tag{25}
\]

As the new active vertex is 1,
`(log tilde w)'=2/((q-tilde x)kappa)` in the old clock, and
`d/d tilde S=(kappa/tilde w)d/d tau_old`. The explicit Mobius formulas
from (18) then give

\[
\begin{aligned}
\widetilde B_S(0)
 &=-q\kappa\left((x+q)G'+\mathcal L_0G\right),\\
\mathcal L_0
 &=x'+(x+q){\widetilde w'\over\widetilde w}
 ={x^2-y^2+4qx+1\over x^2+y^2-q^2}>0
 \quad\text{at }(x,y)=(b,y_b).
\end{aligned}                                                     \tag{26}
\]

For the last sign, the denominator is `D>0`, while the numerator is
positive because `x=b>0` and `y_b^2<1/2`. One can verify the displayed
identity by substituting `x'=1-2y^2/D` and
`tilde w'/tilde w=4q/D`. Equations (24) and (26) prove (20).

The derivation uses (5) only on the active zero-Hamiltonian branch.
In particular, it does not differentiate an identity obtained by
eliminating `H_1` as though that identity held off that energy surface.

Equations (16)--(20) verify every condition in (11) for the entire
stated core range. The outgoing old control 0 is therefore forced
until a finite strict-star exit.

## 4. Why the forced exit excludes a complete-period minimizer

Suppose a closed extremal contains one of these `P_h` windows. Rebase
and cyclically relabel it into the displayed conventions. Section 1
forces its normalized adjoint to be the one just analyzed. Its final
positive control-0 pad starts the outgoing branch, and Section 3
forces the continuation after that pad to follow the same vertex
until the star boundary.

This conclusion cannot be avoided by placing the global terminal seam
before the exit. The twisted state and adjoint conditions (2) continue
the closed lift through that seam, and through every subsequent one,
inside the same invariant strict-star domain. The continued lift must
still solve the same locally unique maximizing Hamiltonian equations.
It therefore reaches the forbidden finite-time boundary, a contradiction.

Thus, for every `0<b<=q/10000` and all sufficiently small positive
pads `h`, these windows have **no closed twisted-periodic PMP extension**.
In the range where the companion fixed-endpoint theorem applies, this
excludes those fixed-endpoint global minima from every closed extremal. No restriction on
the number of pieces or the cost of a hypothetical extension was used.
For actual global minimizers, the published maximum principle supplies
(2), so this is a genuine global exclusion of the counterexample family.

## 5. What this contributes to a repaired finite plan

The explicit local domain was too large because it allowed fixed-endpoint
minima whose unique normal adjoint cannot complete a period. For this
family, full-period PMP closure supplies a strict additional restriction,
and (11) gives a finite, verifiable continuation test that detects it.

This is not a universal L3 theorem. An arbitrary L3 window need not
satisfy `a>0`, the two derivative signs, or the exit-ratio condition after
rotation. Full-domain L3 endpoint rank is now established; rank questions
for other templates, especially competitive L2 inputs, remain separate.
The finite five-template coverage remains usable only
with a newly proved global exclusion or replacement statement on each
remaining parameter region; this note closes one explicit region of L3,
not one of the five universal gates.

The complete-period budget cannot be discarded for other regions.
In particular, the established forward polygon examples admit twisted
periodic full-PMP lifts but have total cost above the octagon's. A
future common exclusion must retain either that budget, a stronger
global necessary condition, or a complete replacement argument. This
note establishes an actual exclusion inequality rather than treating
periodic extendibility itself as a proved complexity bound.

## Independent concurrent derivation

[PADDED_L3_PMP_CONTINUATION](PADDED_L3_PMP_CONTINUATION.md) independently
analyzes the same outgoing continuations in triangular log-factor coordinates.
It proves the boundary obstruction for sufficiently small cores and adds a
two-sided cost obstruction before boundary exit. The present note gives the
explicit range `0<b<=1/(10000*sqrt(3))` and the finite phase-region criterion
(11). These are complementary certificates for the same family, not two
different excluded global classes.

## Sources, exploration, and validation boundary

- [LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md):
  the exact scaled core, normal covector, gap identity, derivative jumps,
  transverse joins, and full endpoint rank.
- [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md):
  the independent all-measurable fixed-endpoint optimality statement.
- [LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md):
  the general rank/normality argument and the importance of the whole-period
  cost budget for forward families.
- Hales--Vajjha, [Sections 6.5--6.6](https://arxiv.org/html/2405.04331v1#Ch6.S5):
  the adjoint equations, conserved group covector, and twisted costate
  transversality. Their [Theorem 16.3.1](https://arxiv.org/html/2405.04331v1#Ch16.S3)
  supplies the separate finite bang-bang conclusion for actual minimizers;
  no numerical bound follows from it here.

A transient floating-point integration suggested the outgoing vertex
and its star exit. It was not a retained certificate and is not used in
any inequality above. The proof uses explicit vertex equations, a
finite logarithm bound, and explicit rational estimates. The core bound
is the stated `b<=q/10000`; no numerical cutoff for the sufficiently small
allowed padding is asserted. No
Lean compilation, typechecking, Lake, CI, or kernel validation was run.

An independent hand review checked the rotation and clock conventions,
the universal gap identity, logarithm certificate, finite boundary time,
exact exit ratio, and the finite-b derivative proof (20)--(26). A separate
review checked the global normality and periodic continuation bridge. No
material gap was found. These reviews do not supply any of the remaining
universal exclusions or a kernel-validation claim.

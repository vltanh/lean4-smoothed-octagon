# Independent audit of the asymmetric short-pad PMP obstruction

Date: 2026-11-07 UTC. Internal mathematical review of
[MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION](MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION.md)
and its exact rational checker. No Lean, Lake, typechecking, or CI.
Internal review and symbolic arithmetic are not external peer review or
kernel validation.

## Conclusion

No substantive gap was found in the stated **local** obstruction. The
fixed asymmetric core admits one continuous normal PMP lift, a positive
incoming control-0 germ, and an outgoing control-0 arc whose first next
tie occurs before the positive critical point needed by the proposed
escape argument. The cost and negative-elliptic Casimir pass the stated
necessary budget tests.

The scope is correctly restricted. This is not a complete-switch M1
counterexample: the initial control-0 piece starts at an arbitrary short
cut, not a certified earlier switch. Geometric-sector eligibility,
embedded realization, the complete-period endpoints, and variational
minimality are all explicitly unproved. The certificate therefore
obstructs the indicated local inference, not the revised global M1 target.

## Independently checked interfaces

### 1. Actual state and adjoint on all four core arcs

Direct integration of the four rational state profiles reproduces

\[
T_a=-323/490,\quad T_b=38/49,
\quad Z_a=P((7/3)L-2M-11/30),\quad
Z_b=P(16/21-(8/3)L).
\]

The factors are exactly `6/5,7/5,7/5,7/5`, with positive durations.
The three upper bounds on `w(q^2-x^2)` are `171/490`, `19/30`, and
`209/490`, all below one. The weighted inner moment fixes
`mu=4/5-(7/3)log(7/5)`. Since `0<mu<(2q/5)^2`, the integrating-factor
numerator `w p_w=q^3 Z` has signs `+,-,+,-` on the four open arcs and
vanishes at each prescribed inner switch. The state covector is
continuous there because the control-dependent term in `p_x` vanishes.
The group covector is continuous by its common polynomial dependence
on the accumulated variable `S=qT`.

The two endpoint equations for `K_0,n_0` were independently reconstructed
by solving `n=Q` at both ends. Thus both adjoining control-0 ties use
one adjoint, rather than separately selected multipliers.

### 2. Whole-arc third-control inequalities

In the minimizing, scaled-cost coordinates, the actual Hamiltonians give

\[
H_0-H_i=-2B/d,\qquad d=1-w(q^2-x^2)>0.
\]

One direct check uses
`A_frame,tau=A_frame(w E21+(x_tau-1)E12)`.
The edge controls have `x_tau=1`; control 0 has
`x_tau=1-2/d` and `w_tau=-4xw^2/d`. Substituting the zero active
Hamiltonian gives exactly the note's expression for `Q`, for both
edge labels.

The curvature constants independently simplify to

\[
B_{SS}\le-91/171\quad\text{on the first arc},\qquad
B_{SS}\le-10/133\quad\text{on the fourth arc},
\]
\[
B_{SS}\ge74/285\quad\text{on each inner arc}.
\]

The strict negative initial slope, strict positive final slope, and
strict negative center value then prove `B<0` throughout all four
open arcs. This argument controls the whole intervals and does not
replace a third-control check by sampling or by the edge PMP alone.

### 3. Physical costate normalization and incoming branch

For minimizing cost `A=(2/3)C`, write
`M=[[k/2,m],[n,-k/2]]` in the shear frame `A_frame=gK(x)`.
The physical maximizing covector for `lambda=-1` is

\[
\Lambda_1=-\frac32 K(x) M K(x)^{-1},\qquad
p_x^{\rm phys}=-\frac32(p_x+n),\qquad
p_y^{\rm phys}=3p_w/y^3.
\]

The term `n` comes from `K^{-1} dK=E12 dx`, and the second state
conversion uses `dw=-2y^{-3}dy`. The positive clock `d tau=y dt`
then gives the physical switching gap
`H_0-H_2=3y B/d` on the initial control-2 arc. Its derivative at the
left tie is strictly negative because `B_x=w B_S<0`.

For two smooth physical Hamiltonians, the derivative of their difference
along either Hamiltonian field is the same: the difference is its
Poisson bracket with itself. The actual control-0 field can therefore
be solved backward for a short time to obtain an ordinary incoming
control-0 arc with the correct strict gap. The remaining vertex is
strictly inactive there. This justifies the incoming branch without
using a reversed maximum principle.

At the core center `K(0)=I`, so the primary determinant is exactly
`(9/4)((1+mu)n_0-K_0^2/12)`. Its positive determinant and the negative
upper-right entry of `M` imply that the physical `Lambda_1=-(3/2)M`
is negative elliptic. The `9/4` normalization factor is correct.

### 4. The outgoing event is the first event

Independent state and cotangent rotation reproduces

\[
a_+/q=-15/547,\quad
W=236883/1824760,\quad R=3769/843,
\]

and the displayed formulas for `mu_+`, `B_0`, and `B_1/q`.
The initial tie gives `E(1)=0`, and
`mu_+-a_+^2<0` starts the outgoing arc on the required side.

The conditions `B_0<0`, `B_1<0`, and `R>16/5` imply `B<0` all the
way to the star boundary by the previously proved endpoint test.
Hence a third-control tie cannot precede the proposed edge event.

On `1<=r<=201/200`, `x(r)<0` and `x'(r)>0`. Consequently
`mu_+-x(r)^2` is strictly increasing. It starts negative and is
already strictly positive at `251/250`. Therefore `E` first strictly
decreases and then strictly increases on this interval. The certified
signs `E(251/250)<0<E(201/200)` imply a unique zero after the initial
tie, in the displayed bracket, and its derivative is positive.
There is no earlier missed edge zero. Both bracket points precede
`x=0` and the star boundary, so this first return lies strictly before
`+sqrt(mu_+)`.

At that root the third gap remains strict. The same physical
Hamiltonian-derivative identity makes the crossing a genuine outgoing
switch to the other tied vertex, old control 1. Thus this is an actual
PMP continuation event, not merely a zero of an uncontrolled extension.

## Arithmetic and limitations

The four logarithm enclosures follow from the positive remainder of the
finite artanh series. The checker evaluates only rational intervals and
exact matrix identities. It was read and rerun in this audit and reported
**71 successful exact identities and sign checks**. Independent symbolic
calculations reproduced the endpoint moments and slopes, physical
Casimir, rotated data, and outgoing gap formula.

The cap comparison has the correct direction: `A_oct>311/100` and
`pi<22/7` give a **lower** bound `2177/1482` on the permitted negative
elliptic Casimir threshold, whose square exceeds `107/50`. The example's
determinant is strictly below `107/50`. The local cost estimate likewise
leaves room for a sufficiently short positive incoming germ.

These arithmetic checks do not prove global closure, geometric eligibility,
or minimality. The note correctly states those limitations, and the
previous long-pad escape theorem retains its stated padding hypothesis.

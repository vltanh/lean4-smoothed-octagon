# Independent internal audit of normal outgoing tie branches

Date: 2026-11-07 UTC. This reviews
[NORMAL_TIE_BRANCHING](NORMAL_TIE_BRANCHING.md). It is an independent
internal hand audit, not external peer review or Lean kernel validation.
No Lean, Lake, typechecking, or CI ran.

## Finding

The necessary-and-sufficient tests in equations (1)--(2) are valid for
**positive constant-vertex PMP germs at a normal, zero-Hamiltonian,
strict-star phase**. They cover every initially zero alternative by a
nonzero derivative of order at most three. The tests do not presume
transversality, eliminate any passing branch, prove local optimality,
or assert existence of a closed period.

The interface to global minimizers is correctly conditional on the
existing positive finite-vertex representation and normality theorems.
Arbitrary measurable singular trajectories without a positive vertex
germ are outside this classification. The proof supplies no uniform
positive duration, numerical tolerance, or interval-arithmetic error
bound near its equality strata.

## 1. Physical signs, zero energy, and the state-only clock

With physical maximizing multiplier `lambda=-1`, write
`H_max=p_max.f-L_C`. The minimizing cost `A=(2/3)C` uses the full
cotangent vector `p_min=-(2/3)p_max`. In the same physical clock,

\[
H_{\min,t}=-(2/3)H_{\max,t}.
\]

For `d tau=y dt`, the corresponding Hamiltonian is
`H_min,tau=H_min,t/y`, so equivalently

\[
H_{\max,t}=-(3/2)yH_{\min,\tau}.
\tag{1}
\]

Here `y>0`; the sign change is exactly the change from maximizing to
minimizing. It is not an unexplained reversal of the switching test.
State-dependent time changes also change the cotangent equations away
from zero energy. On the active zero-Hamiltonian locus the extra
term proportional to `H` vanishes, so the stated canonical equations
in the `tau` clock are valid. Autonomous vertex flow preserves its
zero active Hamiltonian.

For a direct check of both gaps, put `d=1-w(q^2-x^2)>0` and let
`m,n` be the group covector evaluations on `E21,E12`. The three
minimizing Hamiltonians in the shear coordinates are

\[
\begin{aligned}
H_1&=1+(1+x^2)w+mw+p_x+\frac{2wp_w}{q-x},\\
H_2&=1+(1+x^2)w+mw+p_x-\frac{2wp_w}{q+x},\\
H_0&=1+(1+x^2)w+mw+(1-2/d)p_x
          -\frac{4xw^2p_w+2n}{d}.
\end{aligned}
\tag{2}
\]

Eliminating `p_x` with `H_1=0` and `m=-1-mu` gives exactly

\[
H_2-H_1=-\frac{4qwp_w}{q^2-x^2},\qquad
H_0-H_1=-\frac{2B}{d}.
\tag{3}
\]

Both denominators are positive in strict star. Therefore `E<0,B<0`
mean that the candidate uniquely **minimizes** (2), hence uniquely
**maximizes** the physical Hamiltonian (1). The positive fractional
weights of the actual simplex Hamiltonian preserve this vertex
comparison for every simplex control.

This check uses the full-system free-time zero-energy equation. It does
not import a zero-Hamiltonian condition into the separate fixed-time
edge PMP of MEASURABLE_EDGE_PMP_BOUND.

## 2. Independent derivative check

Along the candidate vertex-1 flow, `u=W/(q-x)` and `S=u-c`, with
`W,c>0`. Direct differentiation of the displayed numerator gives

\[
E'=W(\mu-x^2),\qquad
E''=-\frac{2W^2x}{u^2},\qquad
E'''=\frac{4W^2x}{u^3}-\frac{2W^3}{u^4}.
\tag{4}
\]

The successive initial derivatives, each under vanishing of all the
preceding ones, are therefore:

| Gap numerator | Order | Initial value or derivative |
|---|---:|---|
| E | 0 | c^2 p_w(a) |
| E | 1 | W(mu-a^2) |
| E | 2 | -2W^2 a/c^2 |
| E | 3 | -2W^3/c^4, when a=mu=p_w(a)=0 |
| B | 0 | B_0 |
| B | 1 | B_1 |
| B | 2 | (4/3)(2-R) |
| B | 3 | 2q(W+1)/c^2, when B_0=B_1=0 and R=2 |

The third row for `E` is negative when `a>0`, positive when `a<0`,
and its remaining zero case has the strictly negative fourth row.
The quadratic `B` derivative is negative precisely when `R>2`;
its remaining zero case has a strictly positive cubic derivative.
These signs yield exactly the two boxed tests of the proof note.
No identically zero numerator or higher-order zero remains on a
constant vertex arc.

As a further independent calculation, differentiating
`B=n-1-(x^2-mu)w-w((q-x)w+1/(q-x))p_w` with the actual canonical
vertex equations, and dividing by `S'=w` at each step, gives

\[
B_{SS}=\frac83-\frac{2q(W+1)}{S+c}.
\tag{5}
\]

It does not require a particular group covector, sign of `a`, or value
of `p_w(a)`. This verifies that the second-gap derivative table applies
at all the asserted triple and nontransverse phases, not only at the
symmetric escape examples.

The gap and derivative checks were also reproduced by six exact symbolic
identities using rational operations and `q^2=1/3`. This was supplementary
algebra, not a floating-point search or a new numerical premise.

## 3. Analytic germs and the clock interface

The vertex state and adjoint vector fields are analytic near every
strict-star phase. A nonzero first Taylor coefficient fixes a strict
right-hand sign on some positive interval. If both tests pass, intersect
the two such intervals and shrink once more to remain in strict star.
The inactive physical Hamiltonians are then strictly lower throughout
the resulting open interval, so the exact candidate flow satisfies the
full PMP. Conversely, every failed test has an explicitly positive
leading numerator, which violates PMP immediately to the right.

This necessity argument also covers an arc whose Hamiltonian inequalities
are initially stated only almost everywhere. A positive analytic gap
on a right interval has positive-measure violation; continuity extends
the allowed inequalities to the initial cut.

The independent-variable changes preserve the orders and leading signs:

\[
\frac{du}{d\tau}=w>0,\qquad
\frac{d\tau}{dt}=y>0,\qquad
\frac{du}{dt}=1/y>0.
\tag{6}
\]

Also `S=u-c` has derivative one in `u`. Multiplication by the smooth
positive gap denominators preserves a nonzero leading order. Thus
none of the cubic cases relies on a singular clock or on comparing
derivatives in incompatible orientations.

## 4. Triple ties, the circle, and finite representation

At a triple tie, each candidate gets its own cyclic coordinate rotation
and the **same transported covector**. No component is reset to make a
candidate pass. Testing all three candidates and retaining every passing
one is a complete finite rule for positive vertex germs. The proof does
not attach an unverified incoming vertex to a quadratic contact and does
not assume that exactly one candidate passes.

At the normalized circle singular phase the minimizing group matrix is
`M=J`, with `a=0,w=1,p_w=0,mu=0`. Here `W=1/3,c=q,R=2` and
`B_0=B_1=0`. Equation (4) gives the negative cubic edge numerator;
the final row of the table gives the positive cubic third-control
numerator. Thus all three pure-vertex departures fail, while the
centroid-controlled circle itself is not excluded. This is consistent
with the claimed scope and is a useful check of both signs.

For an actual minimizing trajectory with a positive finite vertex
representation, every outgoing positive piece is one of the tested
germs. The representation theorem supplies that premise; the local
Taylor analysis does not prove it. A passing germ remains only a PMP
possibility: full frame/state/costate return, competitive cost, and
variational minimality are separate conditions.

No material correction to NORMAL_TIE_BRANCHING was needed. The five
uniform case-C comparisons, the sharp octagon inequality, and affine
rigidity remain open.

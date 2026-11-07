# Independent audit of the pure reverse minimum-margin exclusion

Date: 2026-11-07 UTC. This is an independent internal mathematical review
of [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md),
not external peer review or Lean kernel validation. No Lean, Lake,
typechecking, or CI ran.

## Finding

The local theorem is valid: a normal free-time strict-star PMP lift
cannot contain four positive arcs `0210` whose third constant active
margin is no larger than the other three. The resulting minimum argument
excludes **every entirely reverse finite positive closed PMP period
with the actual twisted state, frame, and cotangent endpoints**.

Together with the retained global normality and finite-representation
inputs, this closes the pure reverse case R. No primary-costate sector,
Casimir bound, cost cap, endpoint-rank hypothesis, or transverse-switch
assumption is used. The other four global case targets are unaffected.

## 1. The actual margin inequalities

At the middle switch use label-order margins `(B,A,Z)`. Directly undoing
the preceding control-2 factor `b>1` gives

\[
P=(B+Z)/b-Z,\qquad Q=bA+(b-1)Z.
\]

Applying the following control-1 factor `c>1` gives its terminal
label-0 margin `E=(B-(c-1)A)/c`. The four active margins are therefore
`P,Z,A,E`, exactly as claimed. The minimum condition gives

\[
Z\ge A,\quad B\ge bA+(b-1)Z,\quad B\ge(2c-1)A.
\]

These statements include equal minima. The invariant
`PQ+QZ+ZP=AB+AZ+BZ=4` is preserved, so the state matrix `Y` used in
the endpoint calculation is the actual determinant-one strict-star
state at the first internal switch.

## 2. Independent endpoint and cost reconstruction

I reconstructed the six formal columns directly from
`T_i(q)=exp(-(log q)D_i)` and their half-factors, rather than inferring
rank or cancellation from a dimension count. In chronological order
`0,1,2,0,1,0` with base factors `1,1,b,1,c,1`, the proposed linear
combination gives exactly

\[
\delta F F^{-1}=0,\qquad
\delta G G^{-1}=-2b(b-1)(c-1)Y.
\]

The second matrix is a scalar multiple of the **initial state at that
cut**, not of an unrelated earlier state. Consequently

\[
\delta(G^{-1}YG)=G^{-1}[Y,\delta G G^{-1}]G=0.
\]

The actual endpoint identity `g_e=YF X_e^{-1}` then gives `delta g_e=0`
as well. The scalar state-stabilizer direction in the paired products
is genuinely in the differential kernel of the actual five-dimensional
endpoint map. It does not omit a state endpoint condition.

Separately, differentiating the three margin updates and the full
single-arc cost through all six formal factors gives zero terminal
margin derivatives and

\[
\delta J=ZN/4,
\]

with exactly the two brackets and logarithmic coefficients in the proof
note. The starting margins were held fixed during this differentiation;
their formulas in `A,B,Z,b` describe the baseline only. This distinction
is necessary to obtain the stated first variation.

Both reconstructions were also checked by exact symbolic arithmetic.
They do not require the determinant invariant when viewed as algebraic
identities, but the physical application retains that invariant.

## 3. Uniform strict sign

The first bracket is negative already from
`B>=(2c-1)A>cA` and `0<eta(c)<zeta(c)`.
For the second, dividing by `A^2` and setting `z=Z/A>=1` and
`beta=B/A` gives

\[
T(\beta,z)=b(\beta+bz)\eta(b)-\beta(b+z)\zeta(b).
\]

Its derivative in `beta` is strictly negative. Substitute the smallest
allowed value `beta=b+(b-1)z`. A short independent strict comparison is

\[
\frac{\zeta(b)}{\eta(b)}>\frac{2b+1}{b+2},\qquad b>1.
\]

Indeed this is equivalent to
`log b>3(b^2-1)/(b^2+4b+1)`. The difference vanishes at one and has
strictly positive derivative

\[
\frac{(b-1)^4}{b(b^2+4b+1)^2}.
\]

After that substitution the decisive numerator is exactly

\[
\begin{aligned}
&b[b+(2b-1)z](b+2)
 -(b^2+b^2z+(b-1)z^2)(2b+1)\\
&\qquad=-(b-1)[b^2+2bz(z-1)+z^2]<0.
\end{aligned}
\]

Thus the second bracket is also strictly negative for the whole
unbounded domain. This proves `N<0` without sampling, strict minimum
inequalities, or an implicit bound on `b,c`. The sign can approach
zero in collapsed-duration limits; those limits are not actual positive
arcs and no uniform cost gap is asserted.

## 4. Positive needle clocks and the two stripped outer arcs

The missing-control coefficients are
`w_1=B(c-1)>0` and `w_2=b[A(c-1)+Z(b-1)]>0`. Their physical duration
derivatives are, respectively,

\[
Qw_1/2>0,\qquad Bw_2/2>0.
\]

The first needle inserts control 1 at the `0 -> 2` switch; the second
inserts control 0 at the `2 -> 1` switch. All associated margins are
positive. The physical maximum principle gives `H_i<=0` for these
missing controls, including a possible triple tie.

For cost `J=C/sqrt(12)`, the normal adjoint first variation is

\[
\partial J-\xi\partial(g_e,X_e)
=-\frac{p_i}{2\sqrt{12}}H_i
\]

per unit inserted log factor. The active original factors give zero.
Changes of subsequent physical durations induced by varying factors
multiply their zero active Hamiltonians and introduce no extra defect.
The displayed sign therefore makes the two positive needles contribute
nonnegative defects.

The formal first and last factors are also legitimate in this linear
identity. They represent control 0 at genuine cuts adjacent to actual
positive control-0 arcs, so `H_0=0` there by continuity. Their signed
coefficients consequently multiply zero, even though a formal negative
duration by itself would not be admissible.

Equivalently, one may restore the two positive outer base factors.
The vertex-0 flows commute with themselves, so splitting each into a
fixed base and its infinitesimal log-factor change produces the same
columns after the appropriate fixed conjugations. The initial state of
the whole four-arc window stays fixed. The zero core terminal state
derivative means restoring the fixed final base flow adds no first-order
cost or endpoint change. For sufficiently small positive insertion
parameter, all original outer factors remain greater than one. This
provides a further check that stripping does not invent a boundary
variation unavailable to the original positive window.

Only the adjoint first-variation identity and Hamiltonian inequalities
are needed for the contradiction. An endpoint derivative of zero is
**not** being promoted to an exactly endpoint-preserving nonlinear
competitor. There is no hidden inverse-function or constant-rank step.

## 5. Minimum placement and the actual twisted seam

In an entirely reverse extended trajectory, every consecutive four
labels can be cyclically relabeled to `0210`. The actual twist sends
both the active control index and its state margin forward by one.
Their values therefore satisfy `a_(j+N)=a_j`, even though the control
labels themselves are not ordinarily periodic.

A minimum exists in the finite set of active margins of one period.
Place that arc third in the four-arc block ending one arc later. The
same periodic value comparison gives all three required inequalities.
The twisted state and cotangent endpoints continue the **same** PMP
lift through any seam crossed by this block.

This also covers a short period whose four-arc block uses more than
one period of the extension. The argument uses local necessary-PMP
identities on that lift; it does not compare a multi-period replacement
with the single-period cost budget. It needs no claim that repeated
periods are minimizing.

No material gap was found in the endpoint, sign, or global placement
argument. Pure reverse R is excluded under the stated finite and normal
PMP hypotheses. The pure forward and mixed cases, the final octagon
inequality, and affine equality classification remain separate tasks.

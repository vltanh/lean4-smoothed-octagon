# Cyclic time and terminal conditions from actual balanced geometry

`SmoothedOctagon/CyclicClock.lean` completes the cyclic part of the forward passage
from an actual worst disk to the Reinhardt control problem. It starts with
`IsWorstDisk K`, a balanced pair `IsBalancedPair K σ tf`, and its circle
representation. The positive successor map, determinant clock, constant contact
time step, and matrix terminal conditions are all derived from those inputs.

**Validation: not run.** This is source-level Lean and a hand derivation. Lean
compilation, Lake commands, kernel validation, and CI have not been run. The module
introduces no axiom, `sorry`, or `admit`.

## The two constructed changes of parameter

The actual geometric successor from `ContactLift.lean` is a map `φ : ℝ → ℝ` with

\[
\phi\in C^1,\qquad \phi'(t)>0,\qquad
\sigma_j(\phi(t))=\sigma_{j+1}(t),\qquad
\phi^{\circ6}(t)=t+6t_f.
\]

Its construction uses the unique critical contact configuration at a boundary
point of the actual worst disk. No smooth successor is assumed as extra data in
the theorem here.

The determinant clock from `DeterminantClock.lean` constructs `P > 0` and an
increasing order isomorphism `a : ℝ ≃o ℝ` satisfying

\[
a(0)=0,\qquad a\in C^1,\qquad a'(s)>0,\qquad
 a(s+P)=a(s)+6t_f.
\]

Its exact derivative is the reciprocal of the raw determinant speed at `a(s)`.
The speed-covariance equation under `φ` implies that
`a⁻¹ ∘ φ ∘ a` has derivative one everywhere. Its sixfold relation forces its
translation constant to be `P / 6`. Thus

\[
\phi(a(s))=a(s+P/6).
\]

The full argument, including the zero-derivative constancy step and sixfold
iteration, is recorded in [DETERMINANT_CLOCK.md](DETERMINANT_CLOCK.md).

## Balanced contacts with a constant time step

Put

\[
T=P/6,\qquad \tau_j(s)=\sigma_j(a(s)).
\]

Combining the two constructed identities gives

\[
\tau_j(s+T)=\sigma_j(\phi(a(s)))
 =\sigma_{j+1}(a(s))=\tau_{j+1}(s).
\]

This equality holds for every real `s`, not just at the terminal time.
`BalancedClock.lean` proves the full statement `IsBalancedPair K τ T`. In
particular, it derives the global Lipschitz property of `τ_j'` from the periodic
normalized frame and its globally Lipschitz state. The proof does not assume a
Lipschitz derivative for an arbitrary `C¹` change of parameter.

Because `a(0) = 0`, circle representation is preserved:

\[
\tau_j(0)=\sigma_j(0)=s_j^*.
\]

These conclusions provide exactly the geometric hypotheses needed by upstream
`eqn_cost`, including its one-contact cyclic shift.

## The frame and its logarithmic state

Write

\[
G(s)=\operatorname{contactFrame}(\sigma,a(s)),\qquad
Y(s)=a'(s)\,\operatorname{contactLogDerivative}(\sigma,a(s)).
\]

The determinant-clock construction has already proved

\[
\det G(s)=1,\qquad G'(s)=G(s)Y(s),\qquad
\operatorname{IsStarState}(Y(s)),
\]

and global Lipschitz regularity of the entries of `Y`. The contact-frame action is
`τ_j(s) = G(s) s_j*`. Since `R s_j* = s_{j+1}*`, uniqueness of the frame determined
by two adjacent contacts gives

\[
G(s+T)=G(s)R.
\]

Differentiate this identity. The two derivatives of its sides are equal, so

\[
G(s+T)Y(s+T)=G(s)Y(s)R.
\]

Substituting the frame shift yields

\[
G(s)R Y(s+T)=G(s)Y(s)R.
\]

The determinant-one hypothesis makes `G(s)` invertible. The same frame identity,
after taking determinants, gives `det R = 1`, so `R` is invertible too. Left
multiplication by these inverses gives the precise conjugacy

\[
\boxed{Y(s+T)=R^{-1}Y(s)R.}
\]

The helper `state_cyclic_of_frame` proves this implication directly for any global
frame differential equation and determinant-one frame satisfying the displayed
cyclic identity. The order of the inverse factors is fixed by the calculation;
it agrees with the corrected `IsReinhardtAdmissible` definition upstream.

At time zero, circle representation and `a(0)=0` give `G(0)=I`. Substituting zero
into the two global cyclic identities therefore gives

\[
\boxed{G(0)=I,\qquad G(T)=R,\qquad Y(T)=R^{-1}Y(0)R.}
\]

## Public theorem and scope

`balanced_exists_cyclic_determinant_clock hK hbal hcirc` supplies `P > 0`, the
constructed order isomorphism `a`, and the following conclusions together:

- The zero value, `C¹` regularity, positive derivative, and full-period drift of `a`.
- A balanced pair and circle representation for `τ_j = σ_j ∘ a` at `T = P / 6`.
- The global contact shift `τ_j(s + T) = τ_{j+1}(s)`.
- The normalized state's global star conditions and entrywise Lipschitz regularity.
- The global frame differential equation `G' = GY`.
- The global frame shift and state conjugacy.
- The identity initial frame and both exact terminal conditions.

`ControlTrajectory.lean` supplies an actual measurable simplex-valued control and
the integral state equations from these frame and state data. The subsequent
`AdmissibleRealization.lean` combines those results with the terminal conditions and
upstream `eqn_cost` to give an admissible realization with the geometric area as
its cost.

This is a forward construction from an actual worst disk. It does not prove that
every admissible control trajectory comes from a convex balanced disk, and it does
not alone assert global control minimality. The separate `ReverseComparison.lean`
module supplies the full reverse construction and derives that conclusion from
both directions.

## Sources and dependencies

The upstream polygon dependency is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- [AreaFormula.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/AreaFormula.lean):
  `oct_R_mulVec_sixthRoot` and `eqn_cost`.
- [ControlProblem.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/ControlProblem.lean):
  `IsReinhardtAdmissible` and its corrected terminal-state conjugacy.
- [MatrixEntrywise.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Calculus/MatrixEntrywise.lean):
  `HasDerivAtEntrywise.scomp`, `mul_const`, and `unique`.

The actual successor and clock constructions are detailed in
[CONTACT_LIFT.md](CONTACT_LIFT.md), [DETERMINANT_CLOCK.md](DETERMINANT_CLOCK.md),
and [BALANCED_CLOCK.md](BALANCED_CLOCK.md).

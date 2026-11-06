# Rigidity on an interval of zero reduced costate

`SmoothedOctagon/SingularArc.lean` proves a local rigidity statement for an actual
`IsPontryaginExtremal`. It consumes the upstream integral equations, the
almost-everywhere zero-Hamiltonian condition, and the pointwise nontriviality
condition. It does not assume classical costate equations or continuity of the
measurable control.

The mathematical target is the state and control content of Hales–Vajjha,
[Theorem 8.2.3](https://arxiv.org/html/2405.04331v1#Ch8.S2), with the integral-solution
details made explicit. The book's full-control singular case must be distinguished
from a maximizing edge: a nonunique Hamiltonian maximizer alone does not provide
the hypothesis used here.

## Exact interval assumptions and conclusion

The main declaration is `pontryagin_zero_reducedCostate_rigidity`. Its inputs are:

- An actual `IsPontryaginExtremal T u g X Λ₁ ΛR lam`.
- Real endpoints `a < b`.
- The inclusion `Ioo a b ⊆ Ioo 0 T`.
- The pointwise identity `ΛR t = 0` for every `t ∈ Ioo a b`.

It concludes:

\[
\lambda_{\mathrm{cost}}<0,
\qquad
\Lambda_1(t)=\frac32\lambda_{\mathrm{cost}}J,
\qquad X(t)=J
\quad(t\in(a,b)).
\]

The original control satisfies

\[
u(t)=(1/3,1/3,1/3)
\quad\text{for almost every }t\in(a,b),
\]

and the original frame has the classical derivative `g′(t) = g(t)J` throughout
the open interval. The theorem does not replace the original control on its
exceptional null set or assert pointwise control equality there.

`pontryagin_controlIndependent_interval_rigidity` supplies the same conclusion
when the input instead says that the Hamiltonian is independent of the control
throughout the full simplex at every interval point. It uses the proved
pointwise equivalence in `SingularLocus.lean` to obtain `ΛR = 0`.

There is also a consequence concerning the **entire** minimizing interval:
`controlMinimizer_reducedCostate_not_identically_zero` states that a full control
minimizer with an actual Pontryagin lift cannot have `ΛR = 0` throughout `(0,T)`.
Otherwise the rigidity theorem would give `X = J` throughout `(0,T)`, contradicting
the whole-circle exclusion in `CircleExclusion.lean`. The existence of the lift
remains an explicit input, and this argument does not exclude proper subarcs.

## Why the integral hypotheses suffice

### 1. The algebra has no hidden zero denominator

For traceless `X` with determinant one, the upstream trace identity gives
`traceForm X X = -2`. The upstream centralizer theorem states that a traceless
matrix commuting with nonzero `X` is a scalar multiple of `X`. Consequently a
commuting matrix perpendicular to `X` vanishes. The declaration
`commuting_perpendicular_eq_zero` packages this argument.

Put `A = Λ₁ - (3/2 * lam) • J`. At a time when the reduced costate and its
derivative vanish, its differential equation gives `[A,X] = 0`, up to an
irrelevant minus sign. The zero Hamiltonian gives `traceForm A X = 0`.
`costate_eq_cost_of_zero_reduced_derivative` therefore determines `Λ₁`.

### 2. Almost-everywhere information is upgraded before differentiation

The reduced costate is identically zero on the open interval, so its classical
derivative there is zero by local equality with a constant function. Separately,
the Lebesgue fundamental theorem of calculus recovers its actual differential
equation almost everywhere from the supplied integral equation. On the common
full-measure set with the zero-Hamiltonian condition, the preceding algebra
determines the first costate.

The first costate is continuous on `[0,T]` directly from its integral equation.
`Measure.eqOn_open_of_ae_eq` upgrades its almost-everywhere equality to the constant
matrix to equality at every point of `(a,b)`. This is the content of
`pontryagin_costate_eq_on_zero_reducedCostate`; it does not require a nonempty
interval, because its conclusion is an equality on the specified set.

### 3. Nontriviality and the first costate equation determine the state

For the main theorem, `a < b` supplies an actual interval point. If `lam` were
zero, both costates would vanish there, contradicting the extremal's pointwise
nontriviality. Combining `lam ≠ 0` with the supplied `lam ≤ 0` yields strict
negativity.

The first costate's velocity `[Λ₁,X]` is continuous: both matrix curves are
continuous. The classical fundamental theorem of calculus therefore gives this
differential equation at every interior point. Differentiating the now-proved
constant first-costate identity yields `[J,X] = 0`.

The declaration `starState_eq_J_of_commutator_zero` then uses trace zero,
determinant one, and the positive star component to obtain `X = J`. The positive
component matters: commutation and determinant alone would also allow `-J`.

### 4. The state equation determines the original control almost everywhere

The interval identity `X = J` gives zero classical derivative. The actual state
integral equation gives `[controlP (u t) J, J] = 0` almost everywhere. For a
simplex control,

\[
\operatorname{traceForm}(\operatorname{controlMatrix}(u),J)=-2/3.
\]

Thus the denominator is explicitly nonzero. Expanding the commutator gives
`u₁ = u₂` and `2u₀ = u₁ + u₂`. Together with `u₀ + u₁ + u₂ = 1`, these force the
uniform control. This is `circle_control_unique`.

## Declaration map

| Declaration | Result |
| --- | --- |
| `commuting_perpendicular_eq_zero` | Algebraic centralizer and trace-form rigidity |
| `costate_eq_cost_of_zero_reduced_derivative` | First costate from the zero derivative and Hamiltonian equations |
| `starState_eq_J_of_commutator_zero` | Circle state selected by the star component |
| `circle_control_unique` | Uniform simplex control from the stationary circle state |
| `pontryagin_costate_eq_on_zero_reducedCostate` | Pointwise first-costate identity from actual integral extremality |
| `pontryagin_zero_reducedCostate_rigidity` | Normality, circle state, uniform control almost everywhere, and frame dynamics on the explicit interval |
| `pontryagin_controlIndependent_interval_rigidity` | The same conclusions from full-simplex control independence |
| `controlMinimizer_reducedCostate_not_identically_zero` | Exclusion of a zero reduced costate throughout an entire minimizing trajectory with an actual lift |

## Scope and validation

This result does not construct a Pontryagin lift for a global minimizer. It does
not rule out a proper circular subarc, an isolated meeting with the singular
locus, or infinitely many control switches accumulating there. Those statements
require further arguments. It does not establish the remaining universal control
lower bound or classify all minimizers.

The separate current hand proof in [CIRCLE_VARIATION.md](CIRCLE_VARIATION.md) now supplies
the proper circle-subarc exclusion by constructing a geometric competitor. Combining it
with this module's interval rigidity gives the corresponding hand exclusion for a
zero-reduced-costate interval of an actual lift. No new Lean implementation is asserted.

The exact pinned `IsPontryaginExtremal`, matrix FTC, centralizer, trace-form, and
Mathlib open-set almost-everywhere equality interfaces were inspected. There are
no added proof placeholders or axioms. Compilation, Lean typechecking, Lake, and
CI have not been run; the declarations remain unvalidated source development.

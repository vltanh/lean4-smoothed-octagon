# Explicit Euclidean arclength reparametrization

`SmoothedOctagon/ArcLength.lean` constructs an increasing `C¹` arclength
reparametrization for every regular `C¹` periodic plane curve. It supplies the
reparametrization needed when the regular boundary curve is assembled into the
balanced-curve reduction at global gate G2.

**Validation: not run.** The Lean source and the hand proof below have been reviewed
against the pinned Mathlib interfaces. Lean compilation, Lake commands, kernel
checks, and CI have not been run. This module introduces no axiom, `sorry`, or `admit`.

## Interface

The hypotheses are a curve `γ : ℝ → Fin 2 → ℝ`, `ContDiff ℝ 1 γ`, a nonzero derivative
at every point, and a positive period `T`. The theorem constructs `P > 0` and an
order isomorphism `a : ℝ ≃o ℝ` satisfying

\[
a(0)=0,\qquad a\in C^1,\qquad a'(t)>0,\qquad
 a(t+P)=a(t)+T,
\]

and

\[
\bigl((\gamma\circ a)'(t)_0\bigr)^2+
\bigl((\gamma\circ a)'(t)_1\bigr)^2=1.
\]

The exported statement is:

```lean
theorem exists_unitSpeed_reparam {γ : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t, deriv γ t ≠ 0) (hT : 0 < T)
    (hperiod : Function.Periodic γ T) :
    ∃ P : ℝ, 0 < P ∧ ∃ a : ℝ ≃o ℝ,
      a 0 = 0 ∧ ContDiff ℝ 1 (fun t ↦ a t) ∧
      (∀ t, 0 < deriv (fun u ↦ a u) t) ∧
      (∀ t, a (t + P) = a t + T) ∧
      (∀ t, (deriv (γ ∘ a) t 0) ^ 2 + (deriv (γ ∘ a) t 1) ^ 2 = 1)
```

An order isomorphism is globally strictly increasing and onto. Those properties are
part of the constructed object, so subsequent code can use its inverse and order
properties directly. There is no assumption that an arclength map already exists.
The given period need not be the least positive period.

## Hand proof of the construction

### 1. Define the Euclidean speed

Write

\[
v(t)=\sqrt{\gamma'_0(t)^2+\gamma'_1(t)^2}.
\]

At least one coordinate of the tangent is nonzero, so `v(t) > 0`. Its square is
exactly the displayed sum of squares. Since `γ` is `C¹`, both tangent coordinates
are continuous, and so is `v`.

Differentiating `γ(t + T) = γ(t)` gives `γ'(t + T) = γ'(t)`, hence
`v(t + T) = v(t)`.

The formula explicitly uses Euclidean speed. The default norm on `Fin 2 → ℝ` is
not substituted for it. That norm remains part of Mathlib's ambient calculus
instances; it is not used to define the geometric length.

### 2. Integrate speed and prove global invertibility

Define the signed accumulated length and the length of one period by

\[
S(t)=\int_0^t v(u)\,du,
\qquad
P=S(T)=\int_0^T v(u)\,du.
\]

The oriented interval integral is defined for every real `t`, including negative
`t`. Continuity of `v` gives

\[
S'(t)=v(t)>0.
\]

Thus `S` is continuous and strictly increasing, `S(0) = 0`, and `P > 0` because
`T > 0`. Periodicity of the integrand gives

\[
S(t+T)=S(t)+P.
\]

A positive periodic integrand has accumulated integral tending to `+∞` at `+∞`
and to `-∞` at `-∞`; the source uses the pinned periodic-integral theorems for both
limits. Continuity and these limits make `S` surjective by the intermediate value
property.

Choose a right inverse from surjectivity. Strict monotonicity makes it a two-sided
inverse and bundles `S` as an order isomorphism `e`. Set `a = e.symm`. This is the
point at which the inverse is constructed. In particular,

\[
S(a(t))=t.
\]

Injectivity of `S` now proves `a(0) = 0` and, using its period drift,

\[
a(t+P)=a(t)+T.
\]

### 3. Prove regularity of the inverse

An order isomorphism of the real line is continuous. The inverse derivative theorem
therefore applies to the already constructed inverse, since `S'(a(t)) = v(a(t))`
is nonzero. It gives

\[
a'(t)=\frac{1}{v(a(t))}>0.
\]

The right side is continuous, so `a` is `C¹`. This argument differentiates `S`,
not `v`; no second derivative of `γ` is assumed.

The general helper `exists_inverse_integral_reparam` proves these assertions for
any continuous, strictly positive, periodic real function `v`. It retains both the
explicit new period `∫₀ᵀ v` and the inverse derivative as a `HasDerivAt` statement.

### 4. Verify unit speed

The chain rule gives

\[
(\gamma\circ a)'(t)=v(a(t))^{-1}\gamma'(a(t)).
\]

Consequently its squared Euclidean speed is

\[
v(a(t))^{-2}
 \bigl(\gamma'_0(a(t))^2+\gamma'_1(a(t))^2\bigr)
=v(a(t))^{-2}v(a(t))^2=1.
\]

Cancellation is justified by the previously proved strict positivity of `v`.

## Role in the global reduction

For the regular polar parametrization of an actual worst disk, use its positive
period `T = 2π`. The theorem constructs the change of parameter that makes the
zeroth boundary curve have Euclidean unit speed. The order isomorphism and period
identity also supply the endpoint and order information needed to transport
injectivity and boundary coverage over a single period.

The balanced-pair assembly must still transport all six boundary contacts and use
the relevant boundary theorems for the remaining regularity, tangent, and curvature
conditions. The arclength theorem by itself states no optimality inequality or
candidate classification.

## Declaration inventory

| Declaration | Result |
| --- | --- |
| `euclideanSpeed` | Explicit coordinate formula for Euclidean speed. |
| `euclideanSpeed_pos` | Positivity from a nonzero tangent. |
| `euclideanSpeed_sq` | Exact sum-of-squares identity. |
| `continuous_euclideanSpeed` | Continuity for a `C¹` curve. |
| `periodic_euclideanSpeed` | Inheritance of the curve's period. |
| `exists_inverse_integral_reparam` | Full construction and `C¹` regularity of the inverse integrated-speed map. |
| `exists_unitSpeed_reparam` | Increasing periodic arclength reparametrization with Euclidean unit speed. |

## Pinned Mathlib interfaces

These interfaces were inspected at the package's Mathlib revision
`9d581dfff2e41de989072ea63abf3daf69311520`.

- [FundThmCalculus.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean):
  `Continuous.integral_hasStrictDerivAt`.
- [Periodic.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean):
  `Function.Periodic.intervalIntegral_add_eq_add` and the `atTop` and `atBot`
  variants of `tendsto_intervalIntegral_of_pos'`.
- [Deriv/MeanValue.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean):
  `strictMono_of_hasDerivAt_pos`.
- [IntermediateValue.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/Order/IntermediateValue.lean):
  `Continuous.surjective`.
- [Order/Hom/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Order/Hom/Basic.lean):
  `StrictMono.orderIsoOfRightInverse`.
- [MonotoneContinuity.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/Order/MonotoneContinuity.lean):
  `OrderIso.continuous`.
- [Deriv/Inverse.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/Inverse.lean):
  `HasDerivAt.of_local_left_inverse`.
- [ContDiff/Deriv.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean):
  `contDiff_one_iff_deriv`.

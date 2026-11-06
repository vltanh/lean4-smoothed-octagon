# Preserving the balanced pair under the determinant clock

[`SmoothedOctagon/BalancedClock.lean`](../SmoothedOctagon/BalancedClock.lean)
proves that the determinant-time normalization preserves every clause of an
`IsBalancedPair`. The analytic point is global Lipschitz regularity of the new
contact derivatives. It is derived from the normalized matrix equation and the
periodic frame, without adding a Lipschitz assumption on the inverse clock's
derivative.

**Validation: not run.** The module contains source-level Lean proofs with the
hand derivation below. Lean compilation, Lake commands, kernel validation, and
CI have not been run. The module introduces no axiom, `sorry`, or `admit`.

## Exact interface

Start with `hbal : IsBalancedPair K σ tf`. The constructed determinant clock
provides an increasing order isomorphism `a : ℝ ≃o ℝ`, a positive new full period
`P`, and the following properties:

\[
a(0)=0,\qquad a\in C^1,\qquad a'(t)>0,\qquad
a(t+P)=a(t)+6t_f.
\]

For

\[
G(t)=\operatorname{contactFrame}(\sigma,a(t)),\qquad
Y(t)=\operatorname{normalizedContactState}(\sigma,a,t),
\]

the clock construction also gives `G′ = GY` and global entrywise Lipschitz
regularity of `Y`.

The public theorem

```lean
balancedPair_determinantClock_reparam
  hbal a ha0 haC hapos hP haper hLip hg
```

concludes

```lean
IsBalancedPair K (fun j ↦ σ j ∘ a) (P / 6)
```

All the clock hypotheses are already outputs of
`balanced_exists_determinant_clock`. The new balanced parameter is `P / 6`, so
its full period, as required by the upstream definition, is exactly `P`.

## The global frame velocity bound

The frame has full period `P`, since the original contacts have full period
`6 tf` and `a` has the prescribed period drift. Differentiating this periodicity
shows that `G′ = GY` also has period `P`.

On any compact interval, each entry of `G` is `C¹`, hence Lipschitz. Each entry
of `Y` is Lipschitz by construction. Both functions are bounded on that compact
interval. The product estimate

\[
|f(x)h(x)-f(y)h(y)|
\le |f(x)|\,|h(x)-h(y)|
   +|h(y)|\,|f(x)-f(y)|
\]

makes each entry of `GY` Lipschitz there.

The public helper `frame_velocity_lipschitz_periodic` in
[`ControlTrajectory.lean`](../SmoothedOctagon/ControlTrajectory.lean) upgrades
this to a global bound. Its local interval is `[0,2P]`. For two arguments less
than one period apart, shift both by the same integer multiple of `P` into that
interval. For arguments at least one period apart, a uniform bound `M` on the
absolute value of the periodic function gives

\[
|f(x)-f(y)|\le 2M\le\frac{2M}{P}|x-y|.
\]

Combining these cases yields a finite global Lipschitz constant for every entry
of `GY`. The argument requires neither periodicity of `Y` as a separate
hypothesis nor additional differentiability of `Y`.

## Contact derivatives are fixed linear combinations

Write `τⱼ = σⱼ ∘ a`. The contact frame acts on the fixed sixth-root vectors:

\[
\tau_j(t)=G(t)s_j^*.
\]

Differentiation gives

\[
\tau'_j(t)=(G(t)Y(t))s_j^*.
\]

For a fixed vector `w`, the `i`th coordinate of `V(t)w` is

\[
V_{i0}(t)w_0+V_{i1}(t)w_1.
\]

If the two matrix entries have Lipschitz constants `Cᵢ₀` and `Cᵢ₁`, this coordinate
has constant `Cᵢ₀|w₀| + Cᵢ₁|w₁|`. A finite common constant for the two coordinates
therefore bounds the plane-valued function in its sup norm. The source uses the
sum of the two coordinate constants as one such common bound.

This is proved by `lipschitz_mulVec_of_entrywise`, then applied in
`contact_derivatives_lipschitz_of_frame_velocity`. It yields

```lean
∀ j, ∃ C, LipschitzWith C (deriv (τ j))
```

on all of `ℝ`.

## Geometric and topological clauses

The helper `positiveBoundaryParam_of_balanced` extracts each original positive
boundary parametrization from the balanced pair. The earlier theorem
`positiveBoundaryParam_reparam` transports it through the increasing regular
order isomorphism. The chain rule gives

\[
\tau'_j(t)=a'(t)\sigma'_j(a(t)),
\]

so regularity and the positive boundary determinant are preserved. Surjectivity
of `a` preserves the full boundary range. The multi-point identities hold
pointwise at `a(t)`.

The new global derivative Lipschitz bound allows the upstream convex-boundary
lemma `lemma2_4_6` to recover the almost-everywhere curvature inequality for the
new curves directly. The geometric star-cone lemma `lemma2_4_5` supplies the star
condition. Thus the proof does not need to transport an exceptional null set
through the time change.

For simplicity and exact coverage on one period, the starting-point and drift
identities give

\[
a(0)=0,\qquad a(P)=6t_f.
\]

Since `a` is an order isomorphism,

\[
\boxed{a([0,P))=[0,6t_f).}
\]

The original injectivity on `[0,6tf)` and injectivity of `a` give injectivity of
every `τⱼ` on `[0,P)`. The displayed image identity also gives exact boundary
coverage on that interval. Finally,

\[
\tau_j(t+P)=\sigma_j(a(t)+6t_f)=\tau_j(t).
\]

The proof records `6 * (P / 6) = P` explicitly before filling the balanced-pair
period, injectivity, and image fields.

| Balanced-pair requirement | Source of the new witness |
| --- | --- |
| The disk is compact, convex, centrally symmetric, with interior | Original balanced pair |
| Every contact is regular and `C¹` | Positive regular change of parameter |
| Every contact derivative is globally Lipschitz | Periodic frame velocity and fixed matrix-vector action |
| Normalized multi-point identities | Original identities at `a(t)` |
| Almost-everywhere nonnegative curvature | Convex-boundary lemma applied to the new curves |
| Strict star cone | Geometric star-cone lemma |
| Positive full period, simplicity, and boundary image | Order-isomorphism image of the half-open period interval |

## Declarations and downstream use

- `lipschitz_mulVec_of_entrywise` converts entrywise global Lipschitz bounds into
  a vector-valued bound after applying a fixed vector.
- `contact_derivatives_lipschitz_of_frame_velocity` applies that conversion to
  the six contact derivatives.
- `balancedPair_reparam_of_derivatives_lipschitz` transports all balanced-pair
  fields under a positive regular order isomorphism with the specified period
  drift, once the new derivative bound has been supplied.
- `balancedPair_determinantClock_reparam` derives that bound from the actual
  determinant-clock outputs and concludes the full new balanced pair.

This module does not itself construct the cyclic contact lift or prove that a
single successor takes constant time. `ContactLift.lean` and `CyclicClock.lean`
supply those statements. Together, the new balanced pair and the all-time cyclic
shift provide the geometric hypotheses used by the upstream exact area-cost
formula. The result does not reconstruct a disk from an arbitrary control
competitor and does not establish control optimality.

## Pinned sources

The upstream polygon dependency is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- [Defs.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean):
  the complete `IsBalancedPair` definition, including global derivative
  Lipschitz regularity and the full period `6 tf`.
- [Boundary.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Boundary.lean):
  `lemma2_4_5` and `lemma2_4_6` for star and curvature conditions.
- [MatrixEntrywise.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Calculus/MatrixEntrywise.lean):
  `HasDerivAtEntrywise.mulVec_const`, the entrywise Lipschitz definition, and
  uniqueness of derivatives.
- [BalancedReduction.lean](../SmoothedOctagon/BalancedReduction.lean):
  `positiveBoundaryParam_reparam`.
- [ControlTrajectory.lean](../SmoothedOctagon/ControlTrajectory.lean):
  `positiveBoundaryParam_of_balanced` and
  `frame_velocity_lipschitz_periodic`.
- [DeterminantClock.lean](../SmoothedOctagon/DeterminantClock.lean):
  `balanced_exists_determinant_clock` and `contactFrame_action`.

The finite-coordinate metric and Lipschitz APIs were inspected at the resolved
Mathlib pin `9d581dfff2e41de989072ea63abf3daf69311520`:

- [MetricSpace/Pseudo/Pi.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/MetricSpace/Pseudo/Pi.lean):
  `dist_pi_le_iff`.
- [MetricSpace/Lipschitz.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/MetricSpace/Lipschitz.lean):
  `LipschitzWith.of_dist_le'` and the ordinary distance bound.
- [EMetricSpace/Lipschitz.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/EMetricSpace/Lipschitz.lean):
  `lipschitzOnWith_univ`.

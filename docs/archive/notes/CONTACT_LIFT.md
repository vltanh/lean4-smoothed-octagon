# Constructing the cyclic contact lift

[`SmoothedOctagon/ContactLift.lean`](../SmoothedOctagon/ContactLift.lean) constructs a
smooth, positive successor map for the six contacts of an actual worst disk. The
main input is a balanced pair in circle representation. The successor map is
derived from that geometric data; its existence, regularity, and winding number
are not additional hypotheses.

**Validation: not run.** The file contains source-level Lean proof bodies and the
hand argument below. Lean compilation, Lake commands, kernel validation, and CI
have not been run. The module introduces no axiom, `sorry`, or `admit`.

## Exact statement and scope

The theorem `exists_positive_cyclic_contact_lift` assumes

```lean
hK : IsWorstDisk K
hbal : IsBalancedPair K σ tf
hcirc : IsCircleRepresentation σ
```

It constructs `φ : ℝ → ℝ` with all of the following properties:

```lean
ContDiff ℝ 1 φ
∀ t, 0 < deriv φ t
∀ j t, σ j (φ t) = σ (j + 1) t
∀ t, φ^[6] t = t + 6 * tf
∀ t, φ (t + 6 * tf) = φ t + 6 * tf
∀ t, t < φ t
```

Here `φ^[6]` denotes sixfold function iteration. The time parameter still has
full period `6 tf`. This theorem does not assert that one successor step has
constant duration in that parameter. The determinant clock subsequently makes
the successor a translation by one sixth of its new full period.

The actual-worst-disk hypothesis is used when identifying a balanced contact
configuration with the unique indexed critical hexagon through its zeroth
contact. The result is not stated for arbitrary six boundary curves or arbitrary
admissible controls. The preceding balanced reduction constructs the required
balanced circle representation from an actual worst disk.

## The canonical radial successor

Write `b(θ) = rein_bd K θ`. The earlier boundary-trace construction selects the
unique indexed least-area circumscribed hexagon `V(θ)` whose zeroth edge midpoint
is `b(θ)`. Let

\[
m_j(\theta)=\operatorname{hexMidpoint}(V(\theta),j).
\]

Thus `m₀ = b`, each `mⱼ` is continuous, and each is injective on every half-open
interval of length `2π`. All six have full period `2π` and cover the boundary.

Define the lifted angle of the next contact by

\[
F(\theta)=\theta+
  \arg\left(\frac{m_1(\theta)}{b(\theta)}\right),
\]

where plane vectors are identified with complex numbers. In the source this is
`successorAngle hG`, using the upstream `rein_φ` with contact index `1`.

The upstream angle lemmas show that `F` is continuous, strictly increasing, and
satisfies

\[
F(\theta+2\pi)=F(\theta)+2\pi.
\]

The adjacent-midpoint determinant is positive. Since the denominator vector is
nonzero, the imaginary part of the complex ratio is positive, and its argument
lies strictly between `0` and `π`. Consequently

\[
\theta<F(\theta)<\theta+\pi.
\]

The polar description of `m₁(θ)` and uniqueness of the positive radial boundary
point give `m₁(θ) = b(F(θ))`. Shift the indexing of `V(θ)` by one. Its zeroth
midpoint is now `b(F(θ))`, so uniqueness of the indexed critical hexagon identifies
it with `V(F(θ))`. This proves the complete contact identity

\[
\boxed{m_j(F(\theta))=m_{j+1}(\theta).}
\]

Induction gives `mⱼ(Fⁿ(θ)) = mⱼ₊ₙ(θ)` for every natural number `n`, with contact
indices taken in `ZMod 6`.

## Determining the winding exactly

The identity after six successor steps determines a radial angle only modulo
`2π`. The proof must also rule out additional full turns.

From the one-step bounds,

\[
\theta<F^2(\theta)<\theta+2\pi.
\]

The determinant of midpoint `0` and midpoint `2` is positive. Replacing midpoint
`2` by `b(F²(θ))` shows

\[
\sin(F^2(\theta)-\theta)>0.
\]

For an angle strictly between `0` and `2π`, positive sine places it strictly
between `0` and `π`. Therefore

\[
F^2(\theta)<\theta+\pi.
\]

Applying the one-step bound once more yields

\[
\theta<F^3(\theta)<\theta+2\pi.
\]

Central symmetry of the indexed hexagon gives

\[
b(F^3(\theta))=m_3(\theta)=-m_0(\theta)=-b(\theta).
\]

Central symmetry of the disk also gives `b(θ + π) = −b(θ)`. Both `F³(θ)` and
`θ + π` lie in the same half-open interval `[θ, θ + 2π)`. Injectivity of the
radial boundary curve on that interval then proves

\[
\boxed{F^3(\theta)=\theta+\pi.}
\]

Applying this identity twice gives

\[
\boxed{F^6(\theta)=\theta+2\pi.}
\]

This is the exact full-turn relation, with no unspecified integer winding.

## Transport to the given balanced parameter

For the zeroth balanced curve `γ = σ₀`, use the upstream global logarithmic-angle
lift

\[
\alpha(t)=\operatorname{Im}\int_0^t
 \frac{\gamma'(u)}{\gamma(u)}\,du.
\]

The balanced star condition makes this angle strictly increasing. The upstream
star-curve theorem uses simplicity over the full period to prove

\[
\alpha(t+6t_f)=\alpha(t)+2\pi.
\]

This drift and continuity imply that `α` is surjective onto `ℝ`. Strict
monotonicity therefore makes it an order isomorphism `e : ℝ ≃o ℝ`.

Circle representation gives `γ(0) = (1,0)`. Exponential reconstruction from the
logarithmic integral shows that `γ(t)` has positive radial factor and direction
`α(t)`. Since it lies on the disk boundary,

\[
\sigma_0(t)=b(e(t)).
\]

For each `t`, the actual worst-disk uniqueness lemma `bdy_eq_hexMidpoint` now
identifies all six contacts, not just contact zero:

\[
\sigma_j(t)=m_j(e(t)).
\]

Define

\[
\phi=e^{-1}\circ F\circ e.
\]

The contact identity for `F` gives `σⱼ(φ(t)) = σⱼ₊₁(t)`. The exact sixfold relation
and the period drift of `e` give `φ⁶(t) = t + 6 tf`. The full-period covariance
and the strict inequality `t < φ(t)` also follow directly by conjugation.

## Smoothness and the positive derivative

The construction so far gives a continuous successor. Its differentiability is
proved separately by `contDiff_pos_of_positive_curve_comp`.

Suppose two `C¹` plane curves `γ, η` have positive determinant densities and a
continuous map `h` satisfies `γ(h(t)) = η(t)`. At a fixed `t`, some coordinate of
`γ′(h(t))` is nonzero. Apply the scalar inverse-composition derivative theorem to
that coordinate. This proves differentiability of `h` without first assuming
that `h` is differentiable.

The vector chain rule then gives

\[
h'(t)\,\gamma'(h(t))=\eta'(t).
\]

Take determinants with `γ(h(t)) = η(t)` to obtain

\[
h'(t)=
 \frac{\det(\eta(t),\eta'(t))}
      {\det(\gamma(h(t)),\gamma'(h(t)))}>0.
\]

Both determinant densities are continuous and the denominator is everywhere
positive. Hence `h′` is continuous and `h` is `C¹`. Applying the theorem to
`γ = σ₀`, `η = σ₁`, and `h = φ` completes the construction.

## Main declarations

| Declaration | Result |
| --- | --- |
| `successorAngle_continuous`, `successorAngle_strictMono` | Topological regularity of the radial successor |
| `successorAngle_bounds` | Strict one-step advance below `π` |
| `criticalBoundaryTrace_successor` | All six indexed contacts shift together |
| `successorAngle_twice_lt_add_pi` | Two steps remain before the antipodal point |
| `successorAngle_iterate_three`, `successorAngle_iterate_six` | Exact half-turn and full-turn relations |
| `contDiff_pos_of_positive_curve_comp` | `C¹` regularity and positive derivative from a continuous curve transition |
| `exists_positive_cyclic_contact_lift` | The actual smooth successor in the original balanced parameter |

## Pinned sources

The upstream polygon dependency is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- [Reinhardt.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Reinhardt.lean):
  `rein_φ_spec`, `rein_continuous_φ`, `rein_strictMono_φ`, `rein_φ_add_int`, critical
  hexagon shifts, midpoint symmetry, and radial determinant-angle identities.
- [Boundary.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Boundary.lean):
  `bdy_eq_hexMidpoint` and central symmetry of the boundary.
- [StarCurve.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Convex/StarCurve.lean):
  exponential reconstruction, the monotone global angle, and its exact full-period drift.
- [AreaFormula.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/AreaFormula.lean):
  `oct_isStarCurve` and `oct_det2_deriv_pos`.
- [BoundaryTrace.lean](../SmoothedOctagon/BoundaryTrace.lean): the constructed
  indexed critical hexagons and their continuous radial midpoint curves.

The relevant Mathlib APIs were inspected at the resolved pin
`9d581dfff2e41de989072ea63abf3daf69311520`:

- [Deriv/Inverse.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/Inverse.lean):
  `HasDerivAt.of_comp_left`.
- [Deriv/Comp.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/Comp.lean):
  the scalar-vector chain rule `HasDerivAt.scomp`.
- [Complex/Arg.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean):
  the argument inequalities used for the strict half-turn bound.
- [Function/Iterate.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Logic/Function/Iterate.lean):
  successor and addition identities for iterated functions.
- [Order/Hom/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Order/Hom/Basic.lean):
  `StrictMono.orderIsoOfRightInverse`.

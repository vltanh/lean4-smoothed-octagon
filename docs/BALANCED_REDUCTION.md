# An actual worst disk gives a balanced circle minimizer

This document completes the source-level G2 argument and explains the exact remaining
targets. The construction starts with an actual global packing minimizer. Its regular
boundary curve, arclength parameter, and balanced representation are proved to exist.

**Lean compilation, typechecking, kernel validation, and CI have not been run.** The
source bodies and hand argument have been reviewed independently; this is not a
kernel-verification claim.

## Constructing the representation

Start with `IsWorstDisk K`. The affine-normalization theorem constructs an invertible
orientation-preserving linear map `e` such that `e '' K` is still an actual worst disk,
has the same greatest packing density, and has six critical contacts at the sixth
roots of unity. Write `K` for this normalized image in the following construction.

The preceding modules now supply:

1. A six-component continuous boundary trace `σ`, constructed from unique indexed
   critical hexagons. It has normalized multi-point relations, common period `2π`,
   simple and exhaustive traversal on `[0,2π)`, and the required initial values.
2. The identity `σ₀ = rein_bd K` and a proof that this radial curve is a regular
   positive `C¹` parametrization. Unique supporting lines produce continuous
   supporting covectors; a bilateral slope squeeze differentiates the angular gauge.
3. By upstream Lemma 2.4.2, regular positive `C¹` parametrizations for all six components.
4. A global increasing `C¹` order isomorphism `a` that makes `σ₀ ∘ a` Euclidean unit
   speed, fixes zero, and satisfies `a(t+P)=a(t)+2π` for a positive perimeter `P`.

Reparametrize every component by the same map:

\[
\tau_j(t)=\sigma_j(a(t)).
\]

The chain rule gives

\[
\tau'_j(t)=a'(t)\,\sigma'_j(a(t)).
\]

Because `a′ > 0`, each component remains regular and positively oriented. Surjectivity
of `a` preserves its range, and the common change of parameter preserves every
multi-point identity.

## Every balanced-pair field

The proof of `normalized_worstDisk_exists_balanced_circle` supplies the entire upstream
predicate, whose fields are worth keeping explicit:

| Field | Construction or theorem |
| --- | --- |
| Centrally symmetric convex disk | The actual worst-disk hypothesis |
| Six regular `C¹` component curves | Radial regularity, Lemma 2.4.2, and the chain rule |
| Globally Lipschitz derivatives | Lemma 2.4.3, using the constructed Euclidean unit speed of component zero |
| Multi-point relations | The critical contact configuration, preserved by common reparametrization |
| Nonnegative curvature determinant almost everywhere | Lemma 2.4.6, using the established Lipschitz derivatives |
| Strict star tangent condition | Lemma 2.4.5 for the positive boundary multi-curve |
| Positive `tf` | Set `tf = P / 6`, with `P > 0` |
| Common full period `6 * tf` | The exact drift identity for `a` and the original period `2π` |
| Injectivity on a half-open full period | The order isomorphism maps `[0,P)` exactly onto `[0,2π)` |
| Full boundary image on that period | The same interval correspondence and original exhaustive traversal |
| Circle representation | `a(0)=0` preserves the sixth-root initial values |

The half-open intervals matter: both endpoints of a closed full period are the same
boundary point. Since `a(0)=0` and `a(P)=2π`, monotonicity and surjectivity give the
exact image equality used for both simplicity and coverage.

No step presupposes that the component curves are translates by one sixth of the
period. That stronger cyclic-time identity is not part of `IsBalancedPair`; it is a
separate input to the later area-cost theorem and remains a G3 construction.

## Area minimization is preserved

For every balanced pair, the upstream density theorem gives

\[
\delta(K)=\frac{\operatorname{area}(K)}{\sqrt{12}}.
\]

Let `K` be the constructed balanced representative of an actual worst disk, and let
`K′` be any balanced circle competitor. Global packing minimality gives
`δ(K) ≤ δ(K′)`. Both denominators are the same positive number, so

\[
\operatorname{area}(K)\le\operatorname{area}(K').
\]

The source converts this real-area inequality to the measure-valued inequality in
`IsBalancedCircleMinimizer`, using compactness to show both areas are finite. Therefore
the constructed representative is a balanced circle area minimizer.

This proves the main source theorem:

```lean
theorem worstDisk_balanced_normalization (hK : IsWorstDisk K) :
  ∃ (e : Plane ≃L[ℝ] Plane) (d : ℝ),
    rein_PosLin e d ∧ IsWorstDisk (e '' K) ∧
    IsBalancedCircleMinimizer (e '' K) ∧
    greatestPackingDensity (e '' K) = greatestPackingDensity K
```

Here `Plane` abbreviates `Fin 2 → ℝ` in this displayed explanation; the source uses
the full type. Applying the construction to the upstream existence theorem gives
`exists_balancedCircle_worst_disk` with no existence hypothesis.

## The converse comparison

Suppose `K` is any balanced circle area minimizer. The preceding existence result
supplies a balanced circle representative `W` of an actual global worst disk.
Area minimality gives `area(K) ≤ area(W)`, hence `δ(K) ≤ δ(W)`.

For every centrally symmetric convex disk `L`, global minimality of `W` gives
`δ(W) ≤ δ(L)`. Thus `δ(K) ≤ δ(L)` for every original competitor `L`, proving that
`K` is itself an actual worst disk. This is `balancedCircleMinimizer_isWorstDisk`.

The argument does not assume that an arbitrary original competitor has a balanced
representation. Only an actual global minimizer is normalized; that is enough for
the reverse minimization comparison.

## The exact remaining conjecture

The candidate octagon already has a balanced circle representation. The two directions
above therefore show that it is globally worst exactly when it minimizes balanced area.
`BalancedTargets.lean` records the unrestricted lower-bound proposition

```lean
def BalancedAreaLowerBound : Prop :=
  ∀ K σ tf, IsBalancedPair K σ tf → IsCircleRepresentation σ →
    volume octagon ≤ volume K
```

and proves

```lean
ReinhardtConjecture ↔ BalancedAreaLowerBound
```

There is also an equivalent criterion asking for the same area bound only on balanced
circle minimizers. Existence is already discharged, so this criterion is nonvacuous.
Neither inequality is proved in this PR.

For equality classification, define `BalancedAffineRigidity` to assert that every
balanced circle minimizer is an invertible linear image of the octagon. Global affine
rigidity implies this because every balanced minimizer is globally worst. Conversely,
normalize any actual worst disk by `e`, classify the normalized image by `A`, and pull
back through `e⁻¹`. The original disk is `(e⁻¹ ∘ A) '' octagon`. This proves

```lean
FullReinhardtConjecture ↔ BalancedAreaLowerBound ∧ BalancedAffineRigidity
```

The universal area inequality and the affine classification remain the substantive
targets. No uniform switching bound, finite candidate list, control optimality, or
smoothed-polygon classification follows merely from this reduction.

## Source references

The new implementations are [BalancedReduction.lean](../SmoothedOctagon/BalancedReduction.lean)
and [BalancedTargets.lean](../SmoothedOctagon/BalancedTargets.lean).
They use the pinned upstream
[Boundary.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Boundary.lean)
and [BalancedDensity.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/BalancedDensity.lean),
plus the explicit constructions documented in the adjacent hand-proof files.

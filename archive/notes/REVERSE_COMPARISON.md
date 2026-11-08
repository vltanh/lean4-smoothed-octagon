# Completing the geometric and control reduction

`SmoothedOctagon/ReverseComparison.lean` assembles a reverse comparison for
**every** trajectory admitted by the upstream integral-form Reinhardt control
problem. It constructs a balanced circle disk with area no greater than the
cost. In the low-cost regime the areas are exactly equal. The construction
does not assume a smooth control, a simple boundary, or a finite switching
pattern.

Together with the forward realization, this supplies an actual global control
minimizer from a geometric worst disk and identifies the exact remaining
control inequality equivalent to Reinhardt's minimality conjecture.

**Validation is still source-level. Lean compilation, typechecking, Lake,
kernel validation, and CI have not been run.** All the results below have
Lean proof bodies and accompanying hand proofs. Source review does not
establish that those bodies elaborate or pass the kernel.

## Low-cost reconstruction from the actual admissible definition

Start with

```lean
hadm : IsReinhardtAdmissible T u g X
hcost : reinhardtCost T X < Real.pi
```

The construction proceeds through inputs proved from this data.

1. `AdmissibleRegularity.lean` derives continuity of both states, Lipschitz
   regularity of `X` on the entire closed interval, `C¹` frame entries,
   endpoint derivatives within the interval, and a.e. nonnegative curvature
   for all six contact curves. The control remains merely measurable.
2. `CyclicExtension.lean` constructs global states `G,Y` agreeing with `g,X`
   throughout `[0,T]`. The endpoint identities give both value and velocity
   matching. Integral gluing proves global frame derivatives, including at
   every seam. Finite-piece estimates and periodicity give global state
   Lipschitz regularity. Countably many measure-preserving translations
   carry the a.e. curvature inequalities to the line. The extension preserves
   the original cost exactly.
3. `LowCostWinding.lean` proves that the reflected first row advances by
   exactly `π/3` on the original segment. `ReverseGeometry.lean` repeats
   that turn using the actual cyclic matrix identity. A determinant-one
   obstruction prevents the first contact from being opposite to the
   reflected row. Continuity and positive angular speed then force exactly
   one contact turn over `6T`, and hence simple traversal.
4. The actual set

   \[
   K=\operatorname{radialHull}
     \bigl(t\mapsto G(t)s_0^*,\,0,\,6T\bigr)
   \]

   is proved compact, centrally symmetric, with nonempty interior and convex.
   The convexity theorem consumes the now-proved simplicity, derivative
   Lipschitz bound, and a.e. curvature. The six curves
   `σ_j(t)=G(t)s_j*` satisfy every balanced-pair clause and circle
   representation.

The cyclic identity `σ_j(t+T)=σ_(j+1)(t)` and frame equation `G'=GY` supply
the exact hypotheses of upstream `eqn_cost`. The real area conversion in
`cost_eq_area_of_balanced_cyclic` gives

\[
\operatorname{area}(K)=\operatorname{cost}(T,Y)
 =\operatorname{cost}(T,X).
\]

The upstream balanced density formula then yields

\[
\delta(K)=\frac{\operatorname{cost}(T,X)}{\sqrt{12}}.
\]

These are the conclusions of `lowCost_admissible_balanced_realization`.
The resulting `lowCostBalancedComparison` theorem proves the corresponding
comparison predicate defined earlier in `ControlBounds.lean`.

## The full comparison class

For a trajectory with cost at least `π`, the concrete octagon is already a
balanced circle competitor of strictly smaller area. Its area bound was
proved upstream and connected to the actual set in `ControlBounds.lean`.

Combining the two cost regimes proves

```lean
admissibleBalancedComparison : AdmissibleBalancedComparison
```

This comparison permits a different disk for high-cost trajectories. A frame
may make additional full turns and still satisfy its terminal matrix
condition, so exact reconstruction as a simple boundary is neither required
nor asserted in that regime.

## Actual global control minimizers

Let a normalized actual worst disk have the constructed forward realization
`(T,u,g,X)`. For any admissible competitor `(T',u',g',X')`, the proved reverse
comparison supplies a balanced circle disk `K'` with

\[
\operatorname{area}(K')\leq\operatorname{cost}(T',X').
\]

The original worst disk minimizes area over all balanced circle disks, so

\[
\operatorname{cost}(T,X)=\operatorname{area}(K)
\leq\operatorname{area}(K')
\leq\operatorname{cost}(T',X').
\]

`normalized_worstDisk_controlMinimizer` therefore proves the exact unrestricted
predicate `IsReinhardtMinimizer`. `exists_worstDisk_controlMinimizer` also
supplies the actual worst disk from the existing existence theorem, giving
a nonvacuous control minimizer with cost below `π` and `T<π/3`.

Conversely, any global control minimizer has the same cost as this constructed
one, by applying their two minimizing inequalities. Thus

\[
\operatorname{cost}(T,X)/\sqrt{12}=\operatorname{minimaxDensity}.
\]

It also has cost below `π`, so the low-cost reconstruction applies. Its
reconstructed disk has precisely the minimax density and is an actual worst
disk. These facts are `controlMinimizer_density_eq_minimax` and
`controlMinimizer_balanced_worstDisk`.

There is no circular existence argument: geometric worst-disk existence
precedes the forward realization; reverse reconstruction uses arbitrary
admissibility and the cost split, not a minimizing control; only then are
the minimizing inequalities transferred.

## What remains to prove

`ControlLowerBound` is the unrestricted inequality

\[
\operatorname{area}(K_{\rm oct})
\leq\operatorname{cost}(T,X)
\]

for every admissible trajectory. The source now proves, with no assumed
comparison bridge,

```lean
ReinhardtConjecture ↔ ControlLowerBound
```

The high-cost case is already supplied, so it is equivalent to the
`LowCostControlLowerBound` interface. This inequality remains open. The
construction of a minimizer and equivalence of two optimization problems do
not identify the octagon as that minimizer.

The next control route requires a suitable Pontryagin lift for the actual
minimizer and a globally exhaustive comparison, or a direct inequality that
bypasses classification. Neither a uniform switching bound nor coverage of
all switching words has been proved here. Affine equality classification is
also separate. The ledger marks the geometric/control comparison supplied
in source, while retaining those later research obligations.

## Source map

- [ADMISSIBLE_REGULARITY.md](ADMISSIBLE_REGULARITY.md): regularity and curvature
  from the actual integral trajectory definition.
- [CYCLIC_EXTENSION.md](CYCLIC_EXTENSION.md): seams, global bounds, a.e.
  transport, and cost preservation.
- [LOW_COST_WINDING.md](LOW_COST_WINDING.md) and
  [REVERSE_GEOMETRY.md](REVERSE_GEOMETRY.md): winding, simplicity, and the
  actual convex radial hull.
- [ADMISSIBLE_REALIZATION.md](ADMISSIBLE_REALIZATION.md): forward construction
  and exact geometric cost.
- [CONTROL_BOUNDS.md](CONTROL_BOUNDS.md): cost regimes and the named target
  interfaces discharged or used in this assembly.

All upstream mathematics is taken from polygon commit
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`; the mathlib pin is
`9d581dfff2e41de989072ea63abf3daf69311520`.

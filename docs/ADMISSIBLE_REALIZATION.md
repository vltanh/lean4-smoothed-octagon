# Exact admissible realizations of actual worst disks

`SmoothedOctagon/AdmissibleRealization.lean` assembles the geometric construction
into an admissible trajectory of the upstream Reinhardt control problem, with
cost exactly equal to the area of the normalized disk. The starting input is
an actual worst disk. A smooth parametrization, a time change, a measurable
control, and a state trajectory are all constructed by the preceding modules.

**Compilation, typechecking, Lake, and kernel validation have not been run.**
These are source-level Lean proofs with source review. The construction adds
no axiom or proof placeholder.

## Main conclusions

For a worst disk `K` in the normal position `rein_Std K`, the theorem
`normalized_worstDisk_admissible_realization` constructs a positive terminal
time `T`, a boundary multi-curve `σ`, and global matrix functions `g` and `X`.
It proves all of the following together:

- `IsBalancedPair K σ T` and `IsCircleRepresentation σ`;
- the contact-frame equations `σ_j(t) = g(t) s_j*` for every contact and time;
- the cyclic equations `σ_j(t + T) = σ_(j+1)(t)` for every contact and time;
- `IsReinhardtAdmissible T (boundaryControl X) g X`;
- `reinhardtCost T X = volume.real K`;
- `greatestPackingDensity K = reinhardtCost T X / √12`.

The control is the explicit repaired curvature formula `boundaryControl X`.
Its measurability, simplex membership at every time, and the two integral state
equations are proved in `ControlTrajectory.lean`.

For an arbitrary worst disk, `worstDisk_admissible_realization` first constructs
the positive linear normalization `e`. The image `e '' K` is again an actual
worst disk and has the same greatest packing density as `K`. It then provides
the same boundary and admissible-control witnesses for that image, with

\[
\operatorname{cost}(T,X)=\operatorname{area}(eK),
\qquad
\delta(K)=\frac{\operatorname{cost}(T,X)}{\sqrt{12}}.
\]

`exists_worstDisk_admissible_realization` applies the upstream worst-disk
existence result as well. It therefore gives an actual inhabitant with exact
area cost, without requiring a worst disk as an external hypothesis.

## How the pieces fit

The realization uses the following construction chain.

1. `Normalization.lean` puts a worst disk in the required linear normal
   position and proves preservation of its packing density.
2. `BoundaryTrace.lean`, `SupportNormal.lean`, `RadialRegularity.lean`, and
   `ArcLength.lean` construct a regular balanced circle representation.
   `BalancedReduction.lean` assembles the full balanced-pair clauses from
   the actual worst disk.
3. `DeterminantClock.lean` constructs the global contact frame and integrates
   its positive determinant speed. The inverse clock normalizes `det X` to
   one and supplies global entrywise Lipschitz regularity of `X`.
4. `ContactLift.lean` constructs the positive smooth successor of the six
   contact points. Its sixth iterate advances by exactly one original full
   period. `CyclicClock.lean` proves that the determinant clock changes this
   successor into translation by one sixth of its new full period. The frame
   then satisfies `g(t + T) = g(t) R`, and the normalized state satisfies
   `X(t + T) = R⁻¹ X(t) R`.
5. `BalancedClock.lean` proves that the reparametrized curves still satisfy
   every balanced-pair clause, including global Lipschitz derivatives.
   `ControlTrajectory.lean` constructs the measurable control and integral
   equations. The cyclic identities supply the remaining admissible terminal
   conditions.

The identity initial frame follows from circle representation and the fact
that the inverse clock sends zero to zero. The frame shift gives `g(T) = R`.
Differentiating the full-time frame shift gives the terminal state condition
`X(T) = R⁻¹ X(0) R`, with the conjugation direction used by the pinned upstream
definition.

## Checking the real area identity

The upstream `eqn_cost` theorem requires a complete balanced pair, its frame
equations, its frame differential equation, and the **full-time cyclic shift**.
Those are supplied by the construction above. Merely knowing that the boundary
is periodic after `6T` would not satisfy this theorem.

Its conclusion is initially an extended-real equality:

\[
\operatorname{volume}(K)
=\operatorname{ENNReal.ofReal}(\operatorname{cost}(T,X)).
\]

An equality of this form alone would not distinguish zero from a negative
real cost. `cost_eq_area_of_balanced_cyclic` explicitly uses the disk's
nonempty open interior to prove positive volume. The equality then implies
strictly positive cost. Only after this step does it apply `toReal` and obtain
the real area equality. The packing-density identity follows from the upstream
balanced-disk density theorem, whose denominator is `√12`.

## What remains open

This establishes the forward geometric realization at the source level. It
does not establish `IsReinhardtMinimizer` for the resulting control. A disk
that minimizes area among balanced geometric competitors has not yet been
compared with every object admitted by the upstream integral-form control
definition.

The remaining reverse comparison must show that every admissible control has
a balanced circle competitor with area at most its cost. Extra winding is a
real issue in that comparison: an admissible frame can make additional full
rotations before reaching the same terminal matrix. The proposed low-cost
winding argument is recorded in `CONTROL_TRAJECTORY.md`, with its unproved
reconstruction obligations stated explicitly. `LowCostWinding.lean` supplies
some supporting results for smooth arcs; it does not silently replace the
general integral-form admissibility hypothesis.

After the reverse comparison, the global control-optimality and switching
classification arguments must still show that the smoothed octagon attains
the minimum. Affine uniqueness is a separate target. None of the realization
theorems assert either conclusion.

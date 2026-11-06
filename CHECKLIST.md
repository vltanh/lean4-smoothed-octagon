# Mathematical progress and proof ledger

Status date: **2026-11-06**. The current priority is a complete hand proof of the
unrestricted comparison. Existing Lean files remain uncompiled drafts. The working
agreement changed in commit `4ffe766`; new formalization infrastructure is paused.

## Current mathematical frontier

Write `A = area(octagon)` in circle representation and `C = reinhardtCost T X`.
The central open statement is `A ≤ C` for every admissible trajectory. Known
geometric/control reductions may be used in the hand research; their implementation
substeps do not count as excluded competitors or progress on this inequality.

| Result or class | Mathematical status | Exact scope |
| --- | --- | --- |
| Costs at least `π` | Excluded from beating the octagon, since `A < π` | Every admissible trajectory in this cost range |
| Entirely circular state | Costs at least `π`, hence cannot minimize | `X=J` on the entire open interval; proper subarcs are separate |
| A proper circle-state interval | Excluded from a global minimizer by a constructed lower-density competitor | Known Hales–Vajjha exclusion, recovered with an exact area-deficit formula and full hand checks |
| Trajectories confined near `J` | Excluded if `n/m ≤ η₀ < π/A−1` throughout the interval | Arbitrary measurable controls; `m=(c−b)/2`, `n=√(a²+((b+c)/2)²)` |
| Controls on a fixed simplex edge | Cannot satisfy `g(0)=I`, `g(T)=R` in the strict star domain | Arbitrary measurable controls, without a cost bound or terminal condition on `X` |
| Vertex words omitting a letter | Infeasible by the fixed-edge exclusion | Every word length and unequal positive durations; one- and two-arc words are included |
| Words violating the cyclic ordering test | Infeasible after an actual cyclic time rebase | `last(j) > first(j−1)` is required for every letter; it excludes every word with at most three arcs |
| Noncentral nonelliptic word holonomy | Infeasible when tangent closure holds | Any finite length and positive factors with `|tr(RH)|≥2` and `RH≠±I` |
| Exactly four positive vertex pieces | Full asymmetric comparison proved by hand: `C ≥ A`, with octagon equality only | Every reduced four-letter word, arbitrary positive durations and initial state; no PMP or symmetry hypothesis |
| Five-piece noncyclic orbit `01020` | Full asymmetric strict comparison proved by hand: `C > A` | All positive factors and initial states satisfying the actual endpoints, including all five cyclic rebases of this word |
| Five-piece reverse cyclic orbit `02102` | Cost comparison open | The only genuine five-piece orbit left after the ordering test, rebasing, and the proved `01020` comparison |
| Quantitative circle deficit | `π−C ≤ 3∫n` and `C ≥ (π²+9T²)/(2π)` | Every actual admissible trajectory with `C<π` |
| Strong-lift switching margin | Cubic margin proved on the stated family | Does not compare arbitrary competitors or bound switching times uniformly |
| Unrestricted octagon inequality | Open | Trajectories leaving the excluded neighborhood, with arbitrary control history |
| Affine equality classification | Open | Every global minimizer, independently of the inequality |

The near-circle exclusion and its complete hand proof are in
[docs/NEAR_CIRCLE_BOUND.md](docs/NEAR_CIRCLE_BOUND.md). For every global minimizer it gives
`∫n ≥ (π−A)/3` and `max(n/m) ≥ π/A−1`. It does not keep a trajectory uniformly away
from the singular locus or provide a finite switch bound.

[docs/SWITCHING_WORDS.md](docs/SWITCHING_WORDS.md) proves every admissible control must
satisfy `∫u_j>0` for each of the three coordinates. This excludes a whole edge even with
arbitrarily many switches, but gives no common positive lower bound on those integrals.
[docs/VERTEX_WORD_REDUCTION.md](docs/VERTEX_WORD_REDUCTION.md) strengthens this through
every cyclic rebase, proves the four-arc word classification without endpoint elimination,
and records exact whole-arc feasibility inequalities and costs for arbitrary finite words.

[docs/CIRCLE_VARIATION.md](docs/CIRCLE_VARIATION.md) gives an actual balanced convex
competitor whenever a nonempty interval has `X=J`, with exact area gain
`3∫sinh²(εχ)`. It recovers a known local exclusion and does not handle arbitrary nearby
or chattering trajectories. Improvements supported on an interval of length `ℓ` are
less than `3ℓ`, so this local mechanism gives no positive uniform deficit as `ℓ→0`.

[docs/FOUR_LINK_HAND_PROOF.md](docs/FOUR_LINK_HAND_PROOF.md) closes the entire four-piece
comparison. Endpoint algebra leaves one word and a one-parameter family; a strict
integral inequality selects its symmetric octagon member. Equality is classified within
that class. No theorem restricts every global minimizer to four pieces, so the
unrestricted comparison and affine equality classification remain open.

[docs/FIVE_ARC_PROGRESS.md](docs/FIVE_ARC_PROGRESS.md) reduces the five-piece words
to a four-piece degeneration and two genuine orbits. It proves strict comparison for
the entire asymmetric `01020` orbit by endpoint elimination, exact cost integration,
and a sharp logarithmic envelope. The middle duration can approach zero and the cost
can approach the octagon; no uniform positive gap is asserted. The reverse cyclic
orbit `02102` and arbitrary longer words remain open.

[docs/WORD_HOLONOMY.md](docs/WORD_HOLONOMY.md) supplies a complete fixed-factor endpoint
test at arbitrary finite word length. Noncentral elliptic holonomy determines the only
possible initial state; finitely many exact margin signs check each entire arc. The
central cases `RH=±I` retain a cone of initial directions and are not discarded.
This removes unspecified shape parameters but does not prove the remaining cost bound.

## Failed global comparison shortcuts

[docs/GLOBAL_CALIBRATION.md](docs/GLOBAL_CALIBRATION.md) records three exact obstructions.
A state-only endpoint potential has zero gap at the circle. A separable `kθ+V(X)`
certificate on the full domain can supply at most `π/2`. A frame-only certificate
cannot reach the octagon bound: an exact finite frame path has `C<31/10<A` after
the state-evolution equation is removed. Its state jumps violate actual admissibility,
so it is a failed relaxation, not a counterexample to Reinhardt.

The note also derives three explicit vertex inequalities for a genuinely coupled
phase/state calibration, along with the twisted endpoint and radius constraints.
No function satisfying the required inequalities is supplied. Restricting to three
control vertices still leaves a continuous, noncompact state domain.

The five-piece proof also records a false global-concavity shortcut. The function
`F(1−exp(−x))` becomes convex for large `x`; the successful argument instead proves
strict concavity of a different scalar function to obtain an exact sharp envelope.

## Earlier source construction ledger

These are source deliverables, not kernel-certified milestones.
They record the constructive implementation of reductions and analytic lemmas; they
must not be counted as new cases of the unrestricted octagon comparison.

- [x] Reuse the actual octagon, its admissibility, exact density, and a worst disk from the
  pinned reference project. State global minimality and affine rigidity separately.
- [x] Give equivalent global closure criteria, including a density lower bound on any
  actual worst disk. The existence input is an upstream theorem, not an added hypothesis.
- [x] Supply a complete hand proof and Lean proof bodies for the new rational switching
  margin, including `(r-y)^3/8 ≤ hmaxF y r` throughout `2 ≤ y ≤ r ≤ 4`.
- [x] Transport the margin to the actual switching functions of normalized strong lifts:
  `χ₃₂(t) ≥ √3 t³/2` and `χ₃₁(t) ≥ √3 (t_sw-t)³/2` on the whole segment.
- [x] Construct a density-preserving affine normalization of an actual worst disk, with
  its critical contact midpoints at the sixth roots of unity. Prove the normalized area
  objective and pointwise six-contact configurations.
- [x] Construct the actual continuous six-contact boundary trace, with common period
  `2π`, simple traversal, full boundary coverage, and the prescribed initial values.
- [x] Construct a continuous normalized supporting covector field from unique support
  lines, with domination of the gauge and no assumed smooth boundary.
- [x] Prove the radial boundary is a regular positive `C¹` curve from that supporting
  field, including the exact orientation formula `det(b,b') = 1 / gauge(dir)^2`.
- [x] Construct a global increasing `C¹` arclength change of parameter with positive
  derivative, exact period drift, and Euclidean unit speed.
- [x] Assemble all balanced-pair fields for a normalized actual worst disk and prove it
  minimizes balanced circle area. Prove conversely that a balanced circle minimizer is
  an actual worst disk.
- [x] Transfer global minimality and affine rigidity to exact unrestricted balanced
  targets, with no assumed minimizer-reduction theorem.
- [x] Construct the global determinant-one contact frame and the positive periodic clock
  making its logarithmic derivative a determinant-one star state with Lipschitz entries.
- [x] Construct an everywhere-simplex measurable curvature control and prove both integral
  state equations, using pointwise convex curvature and the absolutely-continuous FTC.
- [x] Construct the actual positive `C¹` successor of all six contact curves and prove
  that its sixth iterate advances by exactly one full period.
- [x] Preserve all balanced-pair fields in determinant time and derive the uniform
  cyclic contact shift, initial identity frame, and both control terminal conditions.
- [x] Construct a full admissible realization of an actual worst disk with cost equal
  to its normalized area and original packing density equal to cost divided by `√12`.
- [x] For smooth global star arcs of cost below `π`, prove the reflected first row
  turns by exactly `π/3` on the terminal interval, excluding additional full turns.
- [x] Derive closed-interval continuity, state Lipschitz bounds, frame `C¹` regularity,
  actual a.e. dynamics, and all six curvature inequalities from arbitrary integral trajectories.
- [x] Prove `3T ≤ cost` for every integral trajectory, bound an actual worst realization
  by the octagon's area below `π`, and discharge the high-cost reverse-comparison case.
- [x] Construct a balanced convex radial hull from a low-cost smooth cyclic frame,
  deriving one-turn simplicity and all geometric fields without assuming a boundary disk.
- [x] Extend every integral-admissible segment through its cyclic seams, deriving global
  `C¹` frame regularity, Lipschitz state, a.e. curvature, and exact cost preservation.
- [x] Complete the reverse comparison for every admissible control and construct an actual
  global control minimizer from a worst disk. Prove the exact minimax-value correspondence
  and `ReinhardtConjecture ↔ ControlLowerBound` without an assumed reduction bridge.
- [x] Prove the general pointwise singular-control test: full-simplex Hamiltonian
  independence is equivalent to zero reduced costate. A nonzero reduced costate confines
  every maximizing control to one proper simplex edge.
- [x] Prove every entirely circular admissible trajectory has cost at least `π`, while
  every full control minimizer has cost below `π`. Thus a minimizer has a noncircular
  interior state; proper circular subintervals remain possible at this stage.
- [x] For an actual Pontryagin extremal, prove that vanishing reduced costate on a
  nonempty open interval forces a normal multiplier, circle state, and uniform control
  almost everywhere there. The actual lift is an explicit input, not an existence result.
- [x] Map every mathematical claim to source declarations and record the validation boundary.
- [ ] Compile and inspect kernel dependencies. **Not run under the current workflow.**

The existing candidate construction and its qualitative switching signs are upstream work.
They are not counted as newly closed conjecture cases. The new cubic margin strengthens one
local estimate; it does not establish global optimality.

## Global obligations

This is a finite list of obligations, **not** a claim that the remaining bodies form a finite
list, that the tasks have comparable difficulty, or that they are all routine formalization.

| Gate | Exact completion condition | Present status |
| --- | --- | --- |
| G1 — Fix the global target | Use the existing greatest packing density of congruent copies for every centrally symmetric convex disk; identify the concrete octagon and state affine rigidity separately. | Source draft supplied in `Problem.lean`; validation deferred. |
| G2 — Normalize an actual minimizer | Construct a balanced circle representation of an actual worst disk, preserving the relevant density and supplying every boundary parametrization hypothesis. | Source proof supplied through `worstDisk_balanced_normalization` in `BalancedReduction.lean`. Every parametrization hypothesis is constructed. Kernel validation remains deferred. |
| G3 — Justify the chosen reduction | If using the smoothed-polygon route, prove the needed optimal-control, extremal-lift, and Mahler First bridges for the minimizer from G2. | The geometric/control comparison is constructed in both directions, including actual global control-minimizer existence. The Pontryagin-lift and later Mahler First bridges remain open. |
| G4 — Make the global comparison exhaustive | Prove either a direct inequality covering all normalized competitors, or an explicit uniform switch/side bound plus coverage of all words, parameter ranges, limits, and degeneracies. | Open research obligation. No finite case list is available yet. |
| G5 — Prove the octagon lower bound | Discharge `octagonDensity ≤ greatestPackingDensity K` for a genuine worst disk and apply `reinhardtConjecture_of_worst_disk`. | Open. Comparisons within the regular `(6k+2)` family cannot close this gate. |
| G6 — Classify equality | Prove `AffineRigidity`: every worst disk is an invertible linear image of the centered octagon. | Open; not implied by G5. |
| V — Validate the final theorem | Compile and audit `FullReinhardtConjecture`, its exact statement, and its complete dependency closure in the agreed kernel workflow. | Deferred; requires a change to the current no-compilation policy. |

G4 has two possible routes. A direct global inequality can bypass a finite classification;
otherwise the uniform bound and coverage proof must precede any claim of exhaustive case
enumeration. Merely showing that each minimizer has finitely many switches is insufficient.

## G2 construction ledger

All completed entries below mean source proof bodies and hand arguments have been supplied;
none has yet been checked by Lean. Substeps are not separate global conjecture cases.

| Step | Required output | Status |
| --- | --- | --- |
| G2a — Affine normalization | Starting with an actual worst disk, construct a normalized image, preserve its worst status and density, and identify density as area divided by `2 * √3`. | Source draft supplied in `Normalization.lean`. |
| G2b — Continuous boundary trace | Construct six continuous contact curves, a common period, simple traversal, full boundary coverage, and the initial sixth-root values. | Source draft supplied in `BoundaryTrace.lean`; no curve is assumed as an input. |
| G2c — Regular radial parametrization | Deduce a positive regular `C¹` polar boundary curve from the actual minimizer's unique supporting line at every boundary point. | Source proofs supplied in `SupportNormal.lean` and `RadialRegularity.lean`, including the bilateral slope squeeze and exact orientation formula. |
| G2d — Common arclength parameter | Construct a global increasing periodic change of parameter with Euclidean unit speed for curve zero. | Source proof supplied in `ArcLength.lean`; the speed is the explicit Euclidean coordinate formula. |
| G2e — Balanced assembly | Apply the upstream regularity, Lipschitz, star, and curvature lemmas; transport the period, simplicity, coverage, and initial values through the common change of parameter. | Source proof supplied in `BalancedReduction.lean`, including the balanced-area minimizer property and its converse. |

## Exact remaining comparison

`BalancedTargets.lean` proves the source equivalences

```lean
ReinhardtConjecture ↔ BalancedAreaLowerBound
AffineRigidity ↔ BalancedAffineRigidity
FullReinhardtConjecture ↔ BalancedAreaLowerBound ∧ BalancedAffineRigidity
```

`BalancedAreaLowerBound` quantifies over **every** balanced disk in circle representation.
`BalancedAffineRigidity` quantifies over **every** balanced circle minimizer. Both are still
open propositions. Their equivalence to the original targets does not establish either one.

## G3 construction ledger

| Step | Required output | Status |
| --- | --- | --- |
| G3a — Matrix frame | Construct the `SL₂` frame of the actual contact curve and its positive-determinant logarithmic derivative. | Source proof supplied in `DeterminantClock.lean`, with explicit frame, derivative, and star signs. |
| G3b — Determinant clock | Construct a global positive time change making the logarithmic derivative determinant one, with the needed regularity. | Source proof supplied in `DeterminantClock.lean`; the clock assumed by upstream Proposition 3.1.9 is now constructed. |
| G3c — Cyclic boundary and cost | Prove the common cyclic shift `σ_j(t+tf)=σ_(j+1)(t)` and the exact area-cost identity in the new parameter. | Source construction supplied through `AdmissibleRealization.lean`, with every hypothesis of `eqn_cost` discharged and a real-valued exact area identity. |
| G3d — Admissible comparison | Supply measurable simplex controls and integral state trajectories, then justify comparison with every control-admissible competitor or a precisely restricted equivalent class. | Source proof supplied in `ReverseComparison.lean`. Every low-cost admissible trajectory constructs an equal-area balanced disk; high costs use the octagon. Actual worst disks produce full `IsReinhardtMinimizer` witnesses. |
| G3e — Extremals and polygon reduction | Obtain the relevant Pontryagin lift and the complete Mahler First reduction for the actual minimizer. | Source work supplies pointwise singular-control algebra and singular-interval rigidity. A complete hand variation now excludes proper circle-state intervals. Actual lift existence and the later Mahler First machinery remain formalization gaps; new Lean infrastructure is paused. |

### Reverse-comparison substeps

These are constructions within G3d, not separate cases of the conjecture.

| Step | Status |
| --- | --- |
| Derive regularity from integral admissibility | Source proof supplied in `AdmissibleRegularity.lean`, including endpoint derivatives within the interval and all six a.e. contact curvatures. |
| Construct a smooth cyclic extension | Source construction supplied in `CyclicExtension.lean` from actual admissibility, with closed-segment agreement, seam derivatives, global state bounds, a.e. curvature, and cost preservation. |
| Exclude extra winding at low cost | Source proofs supplied in `LowCostWinding.lean` and `ReverseGeometry.lean`, applied to arbitrary admissible segments through the constructed extension. |
| Construct the balanced convex competitor | Source proof supplied in `ReverseGeometry.lean` from the explicit smooth cyclic-extension interface; simplicity, convexity, symmetry, and coverage are conclusions. |
| Handle high costs and close the comparison | Source proof supplied in `ReverseComparison.lean`: both `LowCostBalancedComparison` and `AdmissibleBalancedComparison` are discharged. |

The remaining global inequality is now stated equivalently as

```lean
ReinhardtConjecture ↔ ControlLowerBound
```

`ControlLowerBound` covers every admissible control and all terminal times. Its low-cost
restriction is sufficient, since the concrete octagon already handles costs at least `π`.
The equivalence and existence of a minimizer do not establish this inequality.

### Extremal and singular-control substeps

| Step | Status |
| --- | --- |
| Construct a lift of the actual global minimizer | Open. The source extremal predicate requires integral costate dynamics, reduced nontriviality, Hamiltonian maximization and zero value, and endpoint transversality. |
| Identify the control-independent locus | Source proof supplied in `SingularLocus.lean` for general star states and perpendicular traceless reduced costates. |
| Derive singular-interval rigidity | Source proof supplied in `SingularArc.lean` for an actual extremal with zero reduced costate on the stated nonempty interval. |
| Exclude an entirely circular minimizer | Source proof supplied in `CircleExclusion.lean` from actual admissibility and minimality, without requiring a lift. |
| Exclude proper circle-state subarcs | Complete hand argument in `docs/CIRCLE_VARIATION.md`, recovering the known variation result. For a zero-reduced-costate interval of an actual lift, the rigidity theorem supplies the circle state. No new Lean implementation is claimed. |
| Complete the Mahler First reduction | Open. Edge extremality, switching accumulation, and the later singular analysis remain to be supplied. A uniform side bound would be a separate stronger requirement. |

## Current hand-research tasks

Attack **G4–G5** directly: seek an unrestricted cost inequality or a global calibration,
and derive genuine exclusions from the exact endpoint and control equations. The local
circle-subarc variation is now fully checked as a hand argument. Every finite-word
investigation must retain arbitrary word
length, unequal positive durations, and the complete star-domain constraints until a
coverage theorem says otherwise.

[docs/PONTRYAGIN_LIFT.md](docs/PONTRYAGIN_LIFT.md) records every field required by the
actual extremal predicate. The lift must preserve free terminal time, the coupled
endpoints, and nontriviality in the reduced cotangent space; an ambient nonzero covector
alone does not meet that last condition. This is a later formalization boundary, not
the current research priority. No finite switching search is justified yet.

## Progress entries

- **2026-11-06, foundations:** concrete global target, equivalent closure criteria, exact
  scalar margin, and strong-lift transport supplied in three initial commits.
- **2026-11-06, G2a:** actual-minimizer affine normalization and normalized area objective
  supplied; commit `2c7dd88`.
- **2026-11-06, G2b:** actual continuous six-contact trace supplied, including common period,
  simplicity, coverage, and circle representation; commit `2ccfe60`.
- **2026-11-06, G2c support field:** unique normalized supporting covectors constructed;
  a uniform compact box and uniqueness of cluster points prove continuity; commit `b01624d`.
- **2026-11-06, G2c regularity:** bilateral supporting-slope squeeze differentiates the
  angular gauge. The radial curve is `C¹`, nonvanishing, and positively oriented;
  commit `abe06e2`.
- **2026-11-06, G2d:** integrate the positive periodic Euclidean speed, prove global
  surjectivity, construct the inverse order isomorphism, and prove unit speed and period drift;
  commit `eb339a6`.
- **2026-11-06, G2e and target transfer:** all balanced-pair fields assembled from an actual
  worst disk, with density preserved. Balanced area minimizers and actual packing minimizers
  are linked in both directions; commit `4ed2dda`. The unrestricted area bound and rigidity
  remain open.
- **2026-11-06, G3a–G3b:** construct the contact frame, raw logarithmic derivative,
  positive determinant speed, and inverse clock. A proved covariance identity conjugates
  a positive sixfold contact successor to translation by `P / 6`; the actual successor
  construction is integrated separately; commit `b18fe62`.
- **2026-11-06, G3d forward dynamics:** define the repaired measurable curvature control,
  prove simplex membership at every time, and obtain both integral equations from actual
  normalized boundary geometry. Global periodic frame-velocity Lipschitz regularity is
  also supplied for the cyclic balanced assembly; commit `a94ac12`. Reverse comparison is
  still open.
- **2026-11-06, G3c contact lift:** construct the contact successor from unique indexed
  critical hexagons, prove its exact one-turn sixfold relation, and derive its positive
  `C¹` regularity from the actual boundary curves; commit `7f6809f`. No contact map is
  assumed as an input.
- **2026-11-06, G3c cyclic clock:** prove the new contact derivatives are globally
  Lipschitz, retain the full balanced pair, and conjugate the actual successor to the
  uniform shift `P / 6`. Derive `G(0)=I`, `G(T)=R`, and `X(T)=R⁻¹X(0)R` with the
  same time parameter used by the integral dynamics; commit `b34e8e7`.
- **2026-11-06, G3c–G3d forward realization:** assemble the full admissible trajectory
  from an actual worst disk and prove `cost = normalized area` and `density = cost / √12`.
  Positive disk area is checked before converting the extended-real area formula. The
  existence theorem supplies an actual witness, without an assumed normalized minimizer;
  commit `60d1ee9`.
- **2026-11-06, G3d low-cost winding:** construct a continuous logarithmic angle without
  simplicity assumptions. A positive quadratic form bounds reflected-row angular speed
  by the trace cost density. Cost below `π` forces the endpoint angle to be exactly `π/3`.
  The theorem's global smooth-arc scope remains explicit; commit `fdbc79c`.
- **2026-11-06, G3d admissible regularity:** derive all needed interval regularity from
  the integral-form state equations. Compactness of time times the entire control simplex
  bounds the commutator without assuming continuity of the selected control. The Lebesgue
  FTC and the simplex formula give a.e. nonnegative curvature for all six contacts;
  commit `f1c391c`.
- **2026-11-06, G3d cost regimes:** prove `3T ≤ cost` for every state trajectory and
  construct an actual worst realization with `cost ≤ area(octagon) < π` and `T < π/3`.
  The octagon handles every cost at least `π`. The remaining reverse comparison and
  low-cost global inequality are named explicitly; their conditional consequences retain
  the corresponding inputs; commit `c6bfb14`.
- **2026-11-06, G3d reverse geometry:** a determinant obstruction prevents the first
  contact from being opposite to the reflected first row. The row's full turn therefore
  forces exactly one contact turn, and positive angular speed yields simplicity. The
  radial hull is then proved convex and balanced from actual a.e. curvature. The theorem
  consumes the explicit global cyclic-extension interface, not an assumed geometric disk;
  commit `758a6d1`.
- **2026-11-06, G3d cyclic extension:** construct all global cyclic-frame inputs from
  arbitrary integral admissibility. Matching endpoint values and velocities give every
  seam derivative via integral gluing. Finite piece bounds and periodicity give global
  state Lipschitz regularity; measure-preserving translations transport the actual null
  sets. The entire closed segment and its exact cost are preserved; commit `52b1824`.
- **2026-11-06, G3d completed in source:** assemble equal-area reconstruction for every
  low-cost admissible trajectory and the high-cost octagon comparator. Construct a full
  global control minimizer from an actual worst disk; every control minimizer conversely
  reconstructs a worst disk with `cost / √12 = minimaxDensity`. The exact unrestricted
  control inequality is equivalent to Reinhardt minimality and remains unproved;
  commit `f64f2bf`.
- **2026-11-06, G3e pointwise singular locus:** prove the exact denominator-weighted
  Hamiltonian gap identity and maximizing-support rule. Equal vertex Hamiltonians force
  zero reduced costate under the explicit star, tracelessness, and perpendicularity
  conditions; a nonzero reduced costate excludes one fixed vertex from every maximizer.
  This pointwise result neither supplies a lift nor bounds switching along a trajectory;
  commit `46f7d59`.
- **2026-11-06, G3e entire-circle exclusion:** derive exact cost `3T` and unit lifted
  angular speed for a circular state. The actual admissible cyclic extension and primary
  winding theorem force cost at least `π`; comparison with the constructed competitor
  excludes an entirely circular full minimizer. No costate or assumed lift is required,
  and no proper singular subarc is excluded; commit `387c6a7`.
- **2026-11-06, G3e singular-interval rigidity:** starting with an actual integral-form
  Pontryagin extremal, upgrade the a.e. costate equations and zero Hamiltonian to the
  pointwise identity `Λ₁ = (3λ/2) J`. Nontriviality gives `λ < 0`; the remaining equations
  force `X = J` and uniform control a.e. on the specified interval. Full-simplex control
  independence implies the same rigidity. Together with entire-circle exclusion, an
  actual lifted minimizer cannot have zero reduced costate on its whole interval.
  Commit `70b75f4`.
- **2026-11-06, G3e lift-interface audit:** inspect every required extremal field and
  the exact existing coordinate transformations. Record the free-time, coupled-endpoint,
  and quotient-covector obligations, including why the known polygon lifts do not
  construct a lift of the actual minimizer. This is an audit of an open gate, not its closure.
- **2026-11-06, hand comparison after workflow change:** derive the exact anisotropy
  bounds `π−C ≤ 3∫n`, `C ≥ π/(1+max(n/m))`, and `C ≥ (π²+9T²)/(2π)` for arbitrary
  low-cost admissible trajectories. This excludes entire trajectories confined to the
  stated neighborhood of `J`, without a symmetry or finite-switch assumption. The hand
  algebra and integral inequalities were independently reviewed; no new Lean was added;
  commit `4cbaaf8`.
- **2026-11-06, hand fixed-edge exclusion:** integrate the exact measurable-control
  equations when `u₀=0` a.e. The required group endpoint forces the initial half-plane
  coordinate onto the forbidden star boundary. Exact rotation conjugation covers every
  edge. Therefore every admissible trajectory uses each control coordinate on a set of
  positive measure, excluding every finite vertex word that omits a letter. The proof
  uses no costate, cost bound, terminal state equation, or switch-count assumption;
  commit `2ece1fc`.
- **2026-11-06, hand circle-subarc variation:** construct a smooth periodic perturbation
  of an actual circular piece and check all balanced convex geometry. Its exact area
  gain is `3∫sinh²(εχ)>0`, without normalizing the perturbed determinant clock. This
  recovers the published local exclusion, including proper subarcs. Quantitative
  bounds record the vanishing gain on shrinking supports and the separate curvature
  requirement for nearby arcs. It is not new closure of the global octagon inequality;
  commit `066cd53`.
- **2026-11-06, full asymmetric four-piece comparison:** preserve the concurrent hand
  proof added in commit `2ea4e93` and independently audit all endpoint, cost, and
  logarithmic identities. Add a short state-holonomy certificate for the forced initial
  shape and a positive-margin certificate for the per-piece costs. Every four-piece
  competitor is now compared with the octagon without imposing symmetry or equal
  durations, and equality is identified within this class. Longer trajectories remain open.
  The independent audit and shorter certificates are committed as `fd80676`.
- **2026-11-06, cyclic word exclusions:** prove that time rebasing preserves actual
  integral admissibility and increases the wrapped control labels by one. Fixed-edge
  exclusion in every rebased window gives `last(j)>first(j−1)`, rules out all words with
  at most three arcs, and leaves only forward `0120` at four arcs. Exact margin flows
  give full continuous-arc star constraints and cost formulas. A retained symbolic
  exploration is reproducible but is not used by the hand proof.
  Commit `febed18`.
- **2026-11-06, global calibration obstructions:** construct an exact finite strict-star
  frame path of cost below the octagon after dropping state dynamics. Prove that this
  relaxed bound, a state-only endpoint potential, and a separable linear-phase potential
  cannot give the desired global certificate on their stated domains. Retain the exact
  coupled vertex residuals and additional frame-radius constraint as an open route.
  Commit `da31f3c`.
- **2026-11-06, arbitrary-word endpoint test:** separate the chronological tangent
  product from the reversed state-conjugator product. Prove that full endpoints reduce
  exactly to tangent closure and commutation with `RH`. Exclude every noncentral
  hyperbolic/parabolic holonomy and determine the unique elliptic candidate, with full
  continuous-arc star checks. Retain central holonomies as an explicit cone and quadratic
  cost quotient, without an implicit nonsingularity assumption or a word-length bound.
  Commit `c7f498b`.
- **2026-11-06, asymmetric five-piece orbit:** enumerate all seven words surviving
  cyclic ordering. One rebases to four pieces; the other six form two genuine orbits.
  Prove every `01020` competitor costs strictly more than the octagon by deriving its
  two-parameter endpoint family, forced initial shape, exact logarithmic cost, and
  a sharp global envelope. The independent hand audit checks every identity and sign.
  Preserve the failed concavity shortcut and reproducible exact algebra separately.
  The reverse cyclic `02102` orbit and all longer words remain open.

The cubic switching margin is available for later quantitative control estimates. A new
estimate should be tied to one of G2–G6 before it is added to the progress ledger. In particular,
this margin vanishes at the switching endpoint, so it is not a uniform dwell-time theorem.

## Literature boundary

Hales–Vajjha, *Packings of Smoothed Polygons* (2024), proves Mahler's First conjecture and
leaves octagon selection open. Appendix B.4 explicitly does not provide a uniform edge bound.
The abstract and research-problem section are the relevant source checks:

- <https://arxiv.org/abs/2405.04331>
- <https://arxiv.org/html/2405.04331v1>

The pinned reference repository implements substantial Chapters 2–7 material; its report
lists the later Mahler First machinery outside the completed formalization. Its name must
not be read as evidence that every published smoothed-polygon reduction is already formalized.

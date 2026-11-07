# Proof without computer assistance: active finite ledger

Date: 2026-11-07 UTC.

## Goal and baseline

The current user request is to find a hand proof of the sharp
smoothed-octagon theorem that does not depend on computer assistance.
The completed [hand/computer-assisted argument](GLOBAL_COST_EQUALITY_ASSEMBLY.md)
remains the baseline. Its successful interval executions establish its
stated computational scope; they do not discharge this new request.

The new proof must contain the inequalities and their sign arguments in
readable mathematical form. Computation may suggest an identity or expose
a false conjecture. A numerical optimizer, interval cover, executable
sign check or unexplained large coefficient list cannot be a premise of
the new proof. A displayed algebraic identity with an explicit short sign
argument is acceptable regardless of how the identity was discovered.

No Lean, Lake, typechecking or CI is run. Existing Lean sources and
dependency pins stay untouched. The actual common PMP covector, full
twisted seam, genuine switches and whole-period cost constraints remain
in force.

## Finite remaining mathematical tasks

| Gate | Required hand replacement | Current status |
| --- | --- | --- |
| H-F | Uniform exclusion of all-forward periods through stationary norm bounds and a Casimir inequality | Closed by the [complete hand theorem](HAND_FORWARD_PERIOD_EXCLUSION.md) and [scalar audit](HAND_FORWARD_NORM_AUDIT.md). Both former forward covers are replaced. |
| H-S | Exclusion when the smaller turn at a minimum reverse centre has a short forward run | Open. The separate opposite-norm floor face is now excluded by hand. Three remaining root/cost boundary faces still need analytic exclusions. |
| H-N | Exclusion when that smaller turn has a nonshort forward run, for either actual successor sign | Open. Retain the scalar boundary comparison and concavity reduction; replace the reverse, low-a and forward endpoint exclusions. The old small-parameter coefficient argument is now bypassed by the proved strict duration-ratio gap. |
| H-A | Audit and assemble a dependency chain using only hand arguments and the declared external geometric/PMP results | Open. In particular, distinguish supplementary identity checks from indispensable executable sign checks. |

These are uniform period classes. They are not a plan to enumerate more
word lengths or replay larger covers. An alternative hand argument may
replace an entire class without reproducing the old scalar domain.

### Completed all-forward gate and other hand prerequisites

- The [all-forward period exclusion](HAND_FORWARD_PERIOD_EXCLUSION.md)
  is complete by hand. The first stationary row and genuine exterior
  floors imply delta u+delta v<1/35 and delta v<1/64; a concave
  two-vertex comparison then gives gamma^2>23/125, contradicting the
  competitive cap gamma^2<9193/50000. See the
  [norm audit](HAND_FORWARD_NORM_AUDIT.md) and updated
  [dependency inventory](HAND_FORWARD_DEPENDENCY_INVENTORY.md).
- The shared small-forward-minimum hard face has a complete
  [integral/cubic replacement](SMALL_FORWARD_MINIMUM_HAND_PROOF.md).
- Both forward neighbor ratios are strictly below 4/3 by the
  [integral proof](HAND_FORWARD_NEIGHBOR_INTEGRAL.md), its
  [asymmetric completion](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md), and
  [independent audit](HAND_FORWARD_NEIGHBOR_AUDIT.md).
- The smaller-nonshort case now satisfies
  [t=a/(a+c)<2/5](MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md) and hence
  [a<4/5](MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md), with a
  [complete hand audit](NONSHORT_HAND_SCALE_AUDIT.md).
- The nonshort small-parameter corner is removed by the strict
  [duration ratio greater than 1/10](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md).

These completed inequalities strengthen the remaining domains; they
do not by themselves exclude either nonshort successor.

## New analytic results

[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md) supplies explicit
proofs of the following stronger necessary conditions:

1. Every competitive actual period has
   `gamma^2 < 9193/50000`, using the spectral cost inequality and short
   rational estimates of the octagon cost and pi.
2. At a global minimum reverse centre, `a^2 < 2/3`. The proof reduces to
   a monotone one-variable function and three terms of a positive
   logarithm series.
3. At a forward successor, the outgoing norm has a quantitative gap above
   `3/4`, depending on `eta=r(d+r)/(r^2+4)`. A short logarithm inequality
   and a factored quadratic discriminant prove the gap.
4. The same gap transfers correctly through the scalar boundary
   comparison and improves both necessary endpoint alternatives.

[Independent internal hand review](HAND_PROOF_REFINEMENTS_AUDIT.md)
accepts these refinements. These necessary conditions alone do not
close an exclusion gate; H-F is closed by the additional norm arguments
and actual-period assembly linked above.

## Dependency pruning under review

[The independent reduction review](HAND_REDUCTION_REVIEW.md) accepts
the following pruning and distinguishes its proved implications from
the remaining exclusion targets.

The earlier theorem excluding two adjacent short bridges at a minimum
is not needed if H-S is proved directly: choose the smaller adjacent
turn immediately, then apply H-S or H-N according to its actual run.
Its large coefficient tables would then disappear from the final chain.
The elementary secant and outer-root facts used by the direct short-side
interface still need to be retained with their own proofs.

[MIXED_NONSHORT_UPPER_ENVELOPE_GAP](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md)
and its [independent hand review](MIXED_NONSHORT_UPPER_ENVELOPE_GAP_AUDIT.md)
prove `d^2+2cd>4` and then `(d-a)/(a+c)>1/10`. Thus the whole old
`epsilon<=1/32` corner is absent for actual data, including the original
delta0-maximal chart. Its coefficient table is no longer needed by the
refined hand route. The same note proves two simple turn-length bounds
and records which additional reverse-successor constraints survive the
comparison.

The broad circular-region argument in F already has a hand proof; its
older interval-Hessian calculation need not be imported into a new
dependency chain. The shared hard small-forward-minimum face now has a
complete [integral and cubic hand proof](SMALL_FORWARD_MINIMUM_HAND_PROOF.md),
accepted in its [independent review](SMALL_FORWARD_MINIMUM_HAND_AUDIT.md).
This replaces the old H5 coefficient table and establishes the required
minimum structure for both F and the mixed cases. The neighbor inequality
also now has a hand proof. The two sufficient stationary norm bounds
and resulting Casimir contradiction are now proved by hand as well.

## Further accepted reductions, with explicit open hypotheses

[HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) proves exterior-factor
concavity and a stronger whole-period cost budget retaining both exterior
factors. Its older sufficient sum targets 1/40 and 1/39 remain valid
conditional lemmas, but are no longer needed. The completed route uses
the [two-norm criterion](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md):
delta u+delta v<1/35 and delta v<1/64. Both residuals decrease with
the larger neighboring margin. On the equal-neighbor domain, the
[sum initial/low-D argument](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md),
[high-D completion](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md), and
[larger-norm tangent proof](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md)
supply every sign. The [scalar audit](HAND_FORWARD_NORM_AUDIT.md) and
[actual-period theorem](HAND_FORWARD_PERIOD_EXCLUSION.md) close H-F.
The [earlier target note](HAND_FORWARD_OPEN_TARGET.md) preserves exact
stationary formulas and the refuted relaxations; dropping both genuine
exterior floors remains invalid.

[MIXED_SMALLER_SHORT_OUTER_ENVELOPE](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md)
removes the opposite turn and its independent norm from one necessary
outer-root condition, for both diagonal signs. Its exact loss formulas
show how a quantitative corrected Casimir cap could be transported.
Neither the useful ratio bound nor the required physical cost-defect
exclusion is claimed established.

Both reductions have [independent internal hand acceptance](HAND_REDUCTION_REVIEW.md).

### Further mixed-case dimension reductions

[Nonshort shape monotonicity](MIXED_NONSHORT_SHAPE_MONOTONICITY.md)
shows that the incident-upper residual numerator is affine and strictly
increasing in the shape variable. It reduces the low-a residual problem
to two lower shape faces, without claiming their signs.
[Weighted secant concavity](MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION.md)
then gives a two-endpoint alternative for the reverse successor. Its
lower endpoint retains the positive reverse turn; the upper endpoint
has a saturated incident ceiling. Their
[independent review](MIXED_NONSHORT_SHAPE_REDUCTION_AUDIT.md) checks all
domain and sign directions. Enlarged endpoint positivity remains open.

The subsequent [rational reverse secant comparison](MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON.md)
makes the lower comparison gap affine and strictly decreasing in shape,
leaving a single necessary upper endpoint. The retained symmetric
central lower bound also decreases with shape, so its high-a cap
condition can be used there with the exact incoming secant fixed.
The [exact secant refinement](MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON.md)
strengthens that upper endpoint and gives d<7c/3, as well as d<7r/3
for a reverse successor. The [actual-floor order argument](MIXED_NONSHORT_REVERSE_ORDER_BOUND.md)
also proves d<b*, adding k>=2t+x to the shape lower bound. The
[order-face hand proof](MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION.md)
now excludes that lower face, including ties, by first-event concavity
and two explicit endpoint signs. The [unit-shape theorem](MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md),
with [independent audit](MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md), now
also excludes k=1. Only k=(29/4)t^2 remains in this lower-face route;
the alternative upper-shape-endpoint sign remains open.

[The short-side root and angle reduction](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md)
keeps an actual outer root while decreasing the Casimir, with an explicit
positive determinant bound. A circle formula maximizes the polar angle
over the remaining matrix parameter. The resulting relaxed cost bound
is preserved through the comparison to four boundary faces. Its
[independent review](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_AUDIT.md) accepts
the implications, not an exclusion of those enlarged faces.

The [explicit turn floor](EXPLICIT_TURN_NORM_FLOOR.md) improves the
earlier norm gap by a single AM--GM argument. The
[retained central Casimir bound](MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md)
uses that floor while keeping the incoming secant; its arguments remain
unchanged in the scalar boundary comparison. The
[nonpositive short-diagonal lemma](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md)
removes the D<=0 part of a separate opposite-floor stopping face.
Their [hand review](HAND_FURTHER_REFINEMENTS_AUDIT.md) does not claim
the remaining positive-D face or the other short faces are excluded.

[The shear/cost formulas](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md)
identify every possible scale minimum of the relaxed short cost: scale
endpoints, the clipping point, and one explicit critical angle.
For the separate opposite-floor face, a two-step Jensen argument removes
the apparent root-interval endpoint. Completed squares, one short
polynomial identity and a monotone constrained quadratic minimum exclude
both the outer-scale and central-duration endpoints. This removes the
separate v=3/4 face entirely. The remaining three root/cost faces are
t=r, v=U(t), and w=3/4. These
[reviewed results](HAND_ENDPOINT_REDUCTIONS_AUDIT.md) do not claim their
exclusion. Actual lower Casimir
information, including a bound from the fixed incoming turn, is retained
in the cost score without claiming a lower bound on the artificially
deformed determinant.

The [fixed outer-norm deformation](MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION.md)
further reduces the E_L>=0 part of w=3/4 to listed endpoints while
preserving the cap and necessary cost score. It retains the actual
outgoing-turn floor in that score. The elementary bound
E_L>1+rho_A-1/(8rho_A) shows that every A>=5/7 point is in this
nonnegative-pairing part. Its terminal signs and the E_L<0 part remain
open, as recorded in the [endpoint review](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).


Both actual stationary-control slacks also survive the first short
root comparison, by their explicit positive derivatives in
[MIXED_SMALLER_SHORT_SLACK_RETENTION](MIXED_SMALLER_SHORT_SLACK_RETENTION.md).
All three terminal faces may therefore retain them. On w=3/4 the
middle slack has a short quadratic-in-scale expression. Its retention
during the further pairing deformation is conditional on J>=0, or
requires an additional zero-slack stop; no uniform sign is presumed.


For the common region a<=1/2, the
[low-scale domain bounds](MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION.md)
give t<7/20 and x>3/13 without any successor or Casimir premise.
The [forward scale-Casimir reduction](MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR.md)
writes the boundary determinant as a concave quadratic in squared
physical scale. A compact eligible-set argument retains the stronger
outgoing norm floor and reduces the lower endpoint to shape boundary
faces or the existing stronger upper endpoint. Their final signs remain
open; these are hand reductions, not completed exclusions.

## Acceptance rule

Close a gate only after an independent reading checks its complete
domain, all endpoint signs, the actual same-covector interface and every
logical dependency. The final hand-proof claim requires all four rows
above to be closed. The computational baseline has its own completed
ledger and is not relabeled as a proof without computer assistance.

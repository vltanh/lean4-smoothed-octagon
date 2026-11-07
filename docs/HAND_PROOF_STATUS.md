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
| H-F | Uniform exclusion of all-forward periods, including the neighbor bound and complementary Casimir inequality | Open. The hard small-minimum face now has a complete hand replacement. The two later covers still need hand replacements. |
| H-S | Exclusion when the smaller turn at a minimum reverse centre has a short forward run | Open. Replace the six-variable cost/angle and outer-root exclusion by an analytic argument. |
| H-N | Exclusion when that smaller turn has a nonshort forward run, for either actual successor sign | Open. Retain the scalar boundary comparison and concavity reduction; replace the reverse, low-a and forward endpoint exclusions. The old small-parameter coefficient argument is now bypassed by the proved strict duration-ratio gap. |
| H-A | Audit and assemble a dependency chain using only hand arguments and the declared external geometric/PMP results | Open. In particular, distinguish supplementary identity checks from indispensable executable sign checks. |

These are uniform period classes. They are not a plan to enumerate more
word lengths or replay larger covers. An alternative hand argument may
replace an entire class without reproducing the old scalar domain.

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
accepts these refinements. None of the three main exclusion gates is
marked closed on the strength of these necessary conditions alone.

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
minimum structure for both F and the mixed cases. It does not close
either of the later forward inequalities.

## Further accepted reductions, with explicit open hypotheses

[HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) proves exterior-factor
concavity and reduces a sufficient neighbor bound to two planar signs.
It also proves that the bounds `z,w<=4/3` and
`(u-3/4)+(v-3/4)<=1/40` imply `gamma^2>23/125` by hand. Proving those
two bounds for actual stationary data remains open; numerical evidence
for them is not a proof premise.
The same note strengthens the whole-period cost budget by retaining
both exterior factors, using the positive mixed derivative of the
scalar edge cost and an explicit seven-edge accounting argument.
Its sharper-cap extension permits the norm-sum target `1/39`.
It also proves `(3-U)(q-1)<3/13`; a proposed homogeneous norm estimate
would imply the sufficient target, but that estimate is still unproved.

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

[The short-side root and angle reduction](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md)
keeps an actual outer root while decreasing the Casimir, with an explicit
positive determinant bound. A circle formula maximizes the polar angle
over the remaining matrix parameter. The resulting relaxed cost bound
is preserved through the comparison to four boundary faces. Its
[independent review](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_AUDIT.md) accepts
the implications, not an exclusion of those enlarged faces.

## Acceptance rule

Close a gate only after an independent reading checks its complete
domain, all endpoint signs, the actual same-covector interface and every
logical dependency. The final hand-proof claim requires all four rows
above to be closed. The computational baseline has its own completed
ledger and is not relabeled as a proof without computer assistance.

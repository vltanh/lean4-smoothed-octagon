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
| H-F | Uniform exclusion of all-forward periods, including the small-minimum sign argument, neighbor bound and complementary Casimir inequality | Open. The two existing covers and the hard small-minimum coefficient face are discovery evidence only for this goal. |
| H-S | Exclusion when the smaller turn at a minimum reverse centre has a short forward run | Open. Replace the six-variable cost/angle and outer-root exclusion by an analytic argument. |
| H-N | Exclusion when that smaller turn has a nonshort forward run, for either actual successor sign | Open. Retain the scalar boundary comparison and concavity reduction; replace the reverse, low-a and forward endpoint exclusions. The small-parameter coefficient argument also needs a complete readable hand justification or a bypass. |
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

The earlier theorem excluding two adjacent short bridges at a minimum
is not needed if H-S is proved directly: choose the smaller adjacent
turn immediately, then apply H-S or H-N according to its actual run.
Its large coefficient tables would then disappear from the final chain.
The elementary secant and outer-root facts used by the direct short-side
interface still need to be retained with their own proofs.

The broad circular-region argument in F already has a hand proof; its
older interval-Hessian calculation need not be imported into a new
dependency chain. The remaining small-forward-minimum polynomial face
is a separate issue and is still included in H-F.

## Acceptance rule

Close a gate only after an independent reading checks its complete
domain, all endpoint signs, the actual same-covector interface and every
logical dependency. The final hand-proof claim requires all four rows
above to be closed. The computational baseline has its own completed
ledger and is not relabeled as a proof without computer assistance.

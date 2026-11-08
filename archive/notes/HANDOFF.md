# Historical handoff -- superseded for the lighter-proof request

**Current work (8 November 2026):** use the
[replacement ledger](../../docs/lighter-proofs/README.md).
The completion claims below record the previous acceptance. All requested
S1 replacements now have separate reviews, while the two S2 ratio rows
remain open under the requested hand-proof standard. Existing Lean
formalizations outside H-S are a separate, unchanged baseline.

Date: 2026-11-08 UTC.

Start with [HAND_ONLY_COMPLETION_PLAN](HAND_ONLY_COMPLETION_PLAN.md),
[HAND_PROOF_STATUS](HAND_PROOF_STATUS.md) and
[HAND_GLOBAL_DEPENDENCY_AUDIT](HAND_GLOBAL_DEPENDENCY_AUDIT.md).
These are the current authority; historical next-worker suggestions
in older notes describe earlier stages.

## Accepted mathematical state

H-F, both H-N successors, H-S and H-A are complete by hand. The
[short-period theorem](MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md)
has an accepted [period audit](MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md)
and [separate scope audit](MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md).
The [final hand theorem](HAND_COST_EQUALITY_THEOREM.md),
[global dependency audit](HAND_GLOBAL_DEPENDENCY_AUDIT.md),
[finite-period review](HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md) and
[inequality/equality review](HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md)
accept the complete global conclusion. No hand-proof gate remains open.

The [lower-ratio theorem](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md)
now proves x>2 using the original covector's corrected Casimir
comparison and explicit central/outer signs. The
[upper-ratio theorem](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md)
proves x<13/6 independently. The
[displacement theorem](MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION.md)
then applies on the actual interval and proves delta<1/19.

The [extended upper order](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md)
and [extended Casimir floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md),
with its [six new derivative signs](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
and [review](MIXED_SMALLER_SHORT_EXTENDED_SHAPE_AUDIT.md), cover the
whole interval through 13/6, including the former strip beyond 15/7.
The actual shape has alpha=1+eta*delta, 13/5<=eta<=3, and
Gamma_actual>1829/10000. At delta=0 the shape is alpha=1,beta=x.

The [actual-root shear theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md)
and [physical completion-cost theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
now have all their caller hypotheses. Their separate reviews accept
the root-to-physical-scale implication and the strict original-period
cost contradiction, including zero displacement.

## Final global acceptance

A1 is accepted. The short theorem's original common covector,
first switches, unequal positive factors, equal-turn symmetry,
twisted endpoints and single whole-period completion budget have
passed two separate reviews. The final global reviews accept:
finite representation before normality; uniform all-forward,
all-reverse and both mixed alternatives; direct terminal count;
arbitrary measurable competitors; affine equality of the original
disk. The external classical geometric/PMP inputs are stated explicitly.

The hand-proof task is complete. The
extended Casimir proof replaces the old coefficient-group premises
rather than assuming their validity outside their original interval.
Further mathematical changes should identify the affected theorem
and receive a focused review. External peer review and Lean
formalization remain separate activities, not unfinished hand gates.

## Preserved computational baseline

The earlier [hand/computer-assisted theorem](GLOBAL_COST_EQUALITY_ASSEMBLY.md)
and [independent audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) remain
complete at their stated external-input and arithmetic execution
boundary. Their frozen sources, full logs, receipts and replay
commands are retained in [CERTIFICATE_REPLAY](CERTIFICATE_REPLAY.md).
They are not indispensable premises of the new hand argument.

The previously interrupted three-root forests are superseded
historical investigations, not remaining tasks. The refuted
unconditional local shortening claim remains refuted. Do not revive
either as a shortcut to the active result.

## Workflow and mathematical invariants

- Preserve the actual twisted state/frame/costate seam, free initial
  state and original common normal covector.
- Keep genuine first/last switches, positive durations and original
  whole-period costs. Artificial scalar points receive only the
  inequalities proved for them.
- Work with uniform whole-period theorems. Do not enumerate growing
  word lengths or report speculative completion percentages.
- Use explicit analytic inequalities and finite algebraic signs.
  Computation may assist discovery and transcription checks, but
  executable covers and unexplained large coefficient minima are
  not hand-proof premises.
- Commit and push reviewed increments with [skip ci].
- Run no Lean, Lake, typechecking or CI. Leave Lean sources and
  dependency pins untouched. Kernel checking and external peer
  review remain separate activities.

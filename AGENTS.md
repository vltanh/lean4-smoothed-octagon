# Working agreement

## Current priority: mathematical closure before Lean

The user changed the immediate workflow on 2026-11-06: stop building Lean infrastructure;
attack the unrestricted Reinhardt comparison directly. Computer assistance is permitted
for exploration and direction, but an eventual proof must have a complete hand argument.
Numerical optimization, sampled inequalities, and symbolic output are not certificates.

Make small, mathematically coherent commits on the existing PR branch. Keep CHECKLIST.md
focused on actual excluded competitors, proved inequalities, and exact remaining gaps.
Preserve failed approaches when they prevent repetition. Do not count added notation,
reformulations, or formalization substeps as mathematical closure.

Do not compile Lean, run Lake, typecheck, or add, modify, or run CI. Existing Lean files
remain uncompiled drafts. No new Lean proof is required at this stage. A future numerical
script must state its domain, constraints, reproducibility information, and limitations.

Keep the PR description, CHECKLIST.md, README.md, SOURCE_MAP.md, and
DEEP_AUDIT_CHECKLIST.md consistent with the current mathematical status. Open mathematics
must remain documented obligations, never assertions with a proof hole or a new axiom.
Keep conditional hypotheses visible and do not import upstream Challenge stubs.

Use the pinned lean4-smoothed-polygon source for existing definitions and the published
papers for known mathematical reductions. Distinguish arbitrary smoothed polygons from
the symmetric (6k+2) family. A finite list of research obligations is not a finite list
of candidate bodies. Do not advertise exhaustive search without a proved uniform bound
and coverage theorem. Report global minimality, affine uniqueness, and kernel validation
separately.

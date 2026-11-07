# Current mathematical audit gates

The historical full audit checklist is preserved at [legacy snapshots](docs/legacy/snapshots/DEEP_AUDIT_CHECKLIST.md). Current hand results have independent *internal* reviews and exact checks, but **no Lean compilation/kernel validation or external peer review**.

## F

- [x] Verify the normal negative elliptic sector; \(N\le61\), \(4/3<a_{\min}^2<20/11\), \(q<7/4\).
- [x] Prove the uniform whole-period cost/Casimir contradiction for every unequal-factor F period: [full exclusion](docs/GLOBAL_FORWARD_PERIOD_EXCLUSION.md), with the completed 20,999-node exact cover.
- [x] Independently audit the same actual multiplier, all exterior floors, whole-period cost, twist, weak ties, positive-window nondegeneracy and boundary cover: [completion audit](docs/GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md). This necessary-condition proof does not require a constrained variation.

## M2

- [x] Every reverse run length two, global minimum a reverse centre touching a nonshort forward run, reverse-centre \(a^2<12/17\).
- [ ] Prove the actual nonshort-bridge first-event/return/cost/index exclusion using the same continuous normal PMP multiplier.
- [ ] Audit all diagonal signs, unequal factors, geometric restrictions, zero-duration limits, endpoint rank, full curvature and three constraint pairs.

## Final assembly

- [ ] Verify sufficient case coverage R/M1/M2/M3/F; through-five sharp cost comparison and all equality/boundary branches.
- [ ] Prove global affine rigidity, not merely a cost lower bound.
- [ ] Trace every imported mathematical assumption and check exact rational identities/certificates. Keep internal hand review distinct from deferred Lean verification.

**Invalid shortcuts:** local PMP windows are not globally closed periods; the unconditional local L3 replacement assertion is disproved; the theoretical bound \(N<10^{56}\) is not a practical enumeration plan.

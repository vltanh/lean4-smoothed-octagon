# Smoothed octagon: research toward the Reinhardt conjecture

**The unrestricted cost inequality and affine uniqueness are still OPEN.** This draft PR contains research hand proofs and exact algebra certificates, not Lean-kernel verification. No Lean, Lake, typechecking or CI was run for the current hand-proof programme.

## Where to start

- **[Authoritative handoff](docs/HANDOFF.md)** — exact M2 remaining statements, current restrictions and finite acceptance gates.
- **[Compact progress ledger](CHECKLIST.md)** — active gates and the definition of completion.
- **[Active proof map](docs/ACTIVE_MAP.md)** — precise theorem dependencies and audit/checker entry points.
- **[Certificate replay guide](docs/CERTIFICATE_REPLAY.md)** — build commands, quantified domains and full-cover acceptance checks.
- **[Legacy archive](docs/legacy/INDEX.md)** — retired roadmaps, old local windows, weaker bounds and original verbose status documents, preserved intact.

## Global case status

| Sufficient whole-period case | Status |
| --- | --- |
| R — entirely reverse | Closed |
| M3 — forbidden long reverse runs | Closed |
| M1 — all-short mixed | Closed |
| F — entirely forward with at least six pieces | Closed |
| M2 — mixed with at least one long forward run | **Open** |

This is a **case count**, not a completion percentage. Case closures use hand proofs, exact algebra/rational certificates, internal audits and named inputs.

A global minimizer has \(N<10^{56}\) under the established geometric/PMP inputs; [the pure-forward class with at least six pieces is now excluded uniformly](docs/GLOBAL_FORWARD_PERIOD_EXCLUSION.md). Its exact complementary-domain certificate processed 20,999 nodes with no unresolved box. In M2, the [smaller-short branch is now excluded](docs/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md) by a complete 107,977-node directed cover with no unresolved box. The remaining task is to exclude both next-switch alternatives when the smaller turn at a global minimum belongs to a nonshort forward run.

## Working rules

Do not enumerate growing word lengths; do not treat local PMP screening as full-period closure; do not resurrect the disproved unconditional L3 six-window shortening lemma. Preserve the actual twisted seam, same covector, exterior switching tests, all frame constraints and boundary limits. Hand/exact proof before marking a gate closed; optional numerical exploration for discovery only.

See [AGENTS.md](AGENTS.md), [source map](SOURCE_MAP.md) and [audit checklist](DEEP_AUDIT_CHECKLIST.md). Existing Lean drafts, exact-check scripts, and dependency pins are unchanged by the documentation reorganization.

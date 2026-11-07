# Explorations and exact certificate scripts

The active sources and exact certificate scripts remain here; historical probes, local-window diagnostics and superseded special-case scripts have been moved byte-for-byte to [legacy/](legacy/README.md). They are **not** Lean tests and no script alone proves a global exclusion without its audited mathematical reduction. Current instructions: [docs/HANDOFF.md](../docs/HANDOFF.md).

The [certificate replay guide](../docs/CERTIFICATE_REPLAY.md) collects the current build commands, domain coverage and acceptance conditions in one place.

For **F**, consult the global_structure_forward_small_minimum, global_structure_forward_minimum_budget, global_structure_forward_angle_count, global_structure_forward_dual and global_structure_forward_ellipticity certificate scripts.

For **M2**, consult the mixed_global_short_bridge family of certificates and CSV tables, mixed_reverse_centre_scale, mixed_global_reverse_angle_density, mixed_global_turn_elimination and mixed_global_scalar_dual certificates.

For **closed-case regressions**, consult abnormal_normality, pure_reverse_minimum and mixed_global_short_run_angle certificates.

The **terminal cost and equality** checker is `small_period_cost_equality_certificate.py`: 72 exact identities and terminal word-coverage checks, supporting the independently audited minimizer-only through-five argument. The global assembly remains conditional on M2.

The completed **F** cover is `global_forward_completion_casimir_certificate.cpp`, with its source hash and result in `global_forward_completion_casimir_certificate_result.txt`. Its 20,999-node exact rational cover discharges the complementary domain of the hand circular-corner proof.

The completed **smaller-short M2** caller is `mixed_smaller_short_interval_certificate.cpp`. Its full directed cover has 107,977 nodes and 53,989 excluded leaves, with zero unresolved boxes; hashes and reproduction commands are in `mixed_smaller_short_interval_certificate_result.txt`. The shared backend `certified_mpfr_interval.hpp`, regression checker and build instructions are documented in [INTERVAL_ARITHMETIC_ENGINE](../docs/INTERVAL_ARITHMETIC_ENGINE.md). The mathematical interface is separately audited; floating-point LP proposals never directly discharge a box.

The new mixed continuation identity checks are `mixed_general_short_defect_interface_certificate.py`, `mixed_general_short_slack_certificate.py`, and `mixed_nonshort_completion_continuation_certificate.py`. The additional radial-completion identities are in `global_radial_completion_certificate.py`.

The **nonshort M2** identities and hand corner are checked by `mixed_nonshort_completion_blowup_certificate.py` and `mixed_nonshort_small_parameter_certificate.py`. The portable `mixed_nonshort_coefficients.py` verifies every expression in the committed `mixed_nonshort_coefficients.hpp` without changing it.

The **nonshort reverse-next branch is closed** by `mixed_nonshort_reverse_boundary_interval_certificate.cpp`: a new boundary comparison reduces every original chart to two four-variable roots. Both the original execution and an independent fresh replay have 106,134 nodes, 53,068 leaves, no pending or unresolved boxes and maximum depth 26. `mixed_nonshort_reverse_boundary_result.json` records the source hashes and both complete logs. `mixed_nonshort_reverse_boundary_certificate.py` checks 20 exact transfer/contractor identities and verifies the published receipt and logs. The [independent audit](../docs/MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md) accepts its actual-period interface and source.

The forward endpoint comparison is proved in [MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION](../docs/MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md), with nine exact identities in `mixed_nonshort_forward_boundary_certificate.py`. It requires independent acceptance of the common low-a exclusion and both endpoint covers before closing the forward-next branch.

The former three-root caller is `mixed_nonshort_completion_interval_certificate.cpp`, with the separately audited `certified_lp_proposal.hpp`. Its incomplete forests are not premises of the boundary method.

With matching MPFR development headers installed, build and replay the two branches as follows:

```sh
g++ -std=c++17 -O3 explorations/mixed_nonshort_completion_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_nonshort_completion_interval_certificate
/tmp/mixed_nonshort_completion_interval_certificate 2000000 0
/tmp/mixed_nonshort_completion_interval_certificate 2000000 1
```

Each invocation starts from all three complementary chart roots. The hand corner covers `epsilon<=1/32`. A successful resumed pending stack is explicitly labelled as insufficient for a stand-alone full-domain proof. See the [source audit](../docs/MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md) for hashes and the complete coverage boundary.

The independently reviewed `mixed_nonshort_completion_cover_chain.py`
can schedule exact prefixes of that unchanged caller in parallel.
`mixed_nonshort_cover_chain_verify.py` checks the complete rooted graph,
every exact checkpoint assignment, source and process records, and local
and aggregate cover counts. The [accounting proof](../docs/EXACT_COVER_CHAIN.md)
explains why a fully verified chain covers the same original roots.
The live chains remain pending; individual child results are not
stand-alone domain exclusions.

The earlier numerical return/event probes, local L1–L4 tests, small-word experiments and superseded M1/reverse-five scripts are archived under **[explorations/legacy](legacy/README.md)**. Archived inter-script imports remain together. Original script paths in old notes must be adjusted using the legacy index; the original file layout is retained in immutable Git history. Their corresponding [notes are archived](../docs/legacy/INDEX.md).

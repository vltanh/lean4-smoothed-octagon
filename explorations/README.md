# Explorations and exact certificate scripts

These scripts are preserved for reproducibility, including the older probes. They are **not** Lean tests and no script alone proves a global exclusion without its audited mathematical reduction. Current instructions: [docs/HANDOFF.md](../docs/HANDOFF.md).

For **F**, consult the global_structure_forward_small_minimum, global_structure_forward_minimum_budget, global_structure_forward_angle_count, global_structure_forward_dual and global_structure_forward_ellipticity certificate scripts.

For **M2**, consult the mixed_global_short_bridge family of certificates and CSV tables, mixed_reverse_centre_scale, mixed_global_reverse_angle_density, mixed_global_turn_elimination and mixed_global_scalar_dual certificates.

For **closed-case regressions**, consult abnormal_normality, pure_reverse_minimum and mixed_global_short_run_angle certificates.

The **terminal cost and equality** checker is `small_period_cost_equality_certificate.py`: 72 exact identities and terminal word-coverage checks, supporting the independently audited minimizer-only through-five argument. The global assembly remains conditional on M2.

The completed **F** cover is `global_forward_completion_casimir_certificate.cpp`, with its source hash and result in `global_forward_completion_casimir_certificate_result.txt`. Its 20,999-node exact rational cover discharges the complementary domain of the hand circular-corner proof.

The completed **smaller-short M2** caller is `mixed_smaller_short_interval_certificate.cpp`. Its full directed cover has 107,977 nodes and 53,989 excluded leaves, with zero unresolved boxes; hashes and reproduction commands are in `mixed_smaller_short_interval_certificate_result.txt`. The shared backend `certified_mpfr_interval.hpp`, regression checker and build instructions are documented in [INTERVAL_ARITHMETIC_ENGINE](../docs/INTERVAL_ARITHMETIC_ENGINE.md). The mathematical interface is separately audited; floating-point LP proposals never directly discharge a box.

The new mixed continuation identity checks are `mixed_general_short_defect_interface_certificate.py`, `mixed_general_short_slack_certificate.py`, and `mixed_nonshort_completion_continuation_certificate.py`. The additional radial-completion identities are in `global_radial_completion_certificate.py`.

The remaining numerical event probes, local L1–L4 certificates and earlier finite-window work are historical diagnostics, retained in place to avoid breaking script imports. The corresponding [notes are archived](../docs/legacy/INDEX.md).

# Historical exploration scripts (legacy)

**Not part of the active proof replay.** These are exploratory numerical probes, earlier finite-window tests, local-variation diagnostics and superseded special-family certificate scripts. They are retained byte-for-byte (the original Git blob SHAs were reused during the move); no research conclusion is silently discarded.

The live workflow starts at [the handoff](../../docs/HANDOFF.md), then [the exact certificate replay guide](../../docs/CERTIFICATE_REPLAY.md) and [the active exploration index](../README.md). Do not treat successful executions here as an exclusion of any remaining M2 whole-period class. The historical [documentation archive](../../docs/legacy/INDEX.md) includes obsolete six-window shortening proposals; in particular the unconditional local L3 claim is false.

## Archived scripts, by purpose

- **Finite-word and return/event investigations:** `closed_period_index_probe.py`, `finite_window_cover.py`, `five_arc_01020.py`, `octagon_boundary_probe.py`, `pmp_return_probe.py`, `pmp_return_tests.py`, `structural_case_probe.py`, `vertex_event_certificate.py`, `vertex_word_algebra.py`.
- **Local window, rank and attempted shortening diagnostics:** `local_forward_nonlocal_certificate.py`, `local_forward_nonlocal_fraction_certificate.py`, `local_forward_stationary_obstruction.py`, `local_l1_needle_certificate.py`, `local_l3_exact_certificate.py`, `local_l4_switch_obstruction.py`, `local_six_fiber_probe.py`.
- **Superseded symmetric/special-word probes:** `m1_interval_certificate.py`, `m1_slice_probe.py`, `reverse_five_exploration.py`, `reverse_five_rational_diagnostic.py`.

## Path compatibility and reproducibility

Run archived Python scripts from this directory if they depend on sibling imports (for example, `pmp_return_tests.py` imports `pmp_return_probe.py`). The original repository-root invocations in old research notes should be adjusted from `explorations/<script>.py` to `explorations/legacy/<script>.py`. The pre-move originals remain viewable at [the immutable earlier tree](https://github.com/vltanh/lean4-smoothed-octagon/tree/c53914bc33aedff9ab12b1bd56e9ded0e6fabad7/explorations), so original instructions and inbound links can be reconstructed.

**Active critical filenames were not moved:** `mixed_nonshort_completion_interval_certificate.cpp`, `mixed_nonshort_coefficients.hpp`, `certified_lp_proposal.hpp`, `certified_mpfr_interval.hpp`, `mixed_nonshort_completion_cover_chain.py`, `mixed_nonshort_cover_chain_verify.py`, completed F and smaller-short callers, and their audited result records.

# Sources and attribution

The mathematical program is based on Karl Reinhardt's conjecture and the optimal-control
development of Thomas Hales and Koundinya Vajjha,
[*Packings of Smoothed Polygons*](https://arxiv.org/abs/2405.04331).

The concrete Lean geometry, packing-density definitions, candidate construction, and cited
theorems are reused by dependency from
[`vltanh/lean4-smoothed-polygon`](https://github.com/vltanh/lean4-smoothed-polygon), pinned to
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`. Its contributors and provenance are recorded
in the [upstream credits](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/CREDITS.md).
That project is distributed under Apache-2.0; this project uses the same license.

The source contributions in this PR include the explicit global targets, the quantitative
rational switching certificate, and constructions completing the actual-minimizer balanced
reduction and starting its control realization. Hand proofs and source drafts are reviewed
within this assistant session. The analytic normalization and reduction arguments implement
known mathematical ideas and the pinned upstream geometric results; this is not a claim of
new priority for those ideas or of kernel verification.

The logarithmic-angle construction in `LowCostWinding.lean` adapts the proof in upstream
`Basic/Analysis/Convex/StarCurve.lean` to nonvanishing `C¹` arcs without simplicity or
periodicity hypotheses. The original implementation remains credited to that pinned
dependency and is reused under its Apache-2.0 license.

mathlib supplies the logarithm inequalities, real algebra, measure theory, and Lean proof
infrastructure. Its exact revision is recorded in the package configuration and source map.

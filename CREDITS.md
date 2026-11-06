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

The new work in this initial PR is the explicit global-target interface and the quantitative
rational certificate for the upstream switching expression, with its hand proof and source
draft. The certificate was derived algebraically and independently reviewed within this
assistant session. This statement makes no claim of priority beyond the comparison with the
pinned repository, and no claim of kernel verification.

mathlib supplies the logarithm inequalities, real algebra, measure theory, and Lean proof
infrastructure. Its exact revision is recorded in the package configuration and source map.

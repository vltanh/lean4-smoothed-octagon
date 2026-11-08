# Credits

The-Anh Vu-Le chose the problem, directed the work, and is the author and maintainer of this
repository.

## The proof

The proof was written in this repository, from 6 to 8 November 2026, and its history is the record
of how. It starts from Thomas Hales's formulation of the problem as optimal control on `SL₂(ℝ)` and
from Hales and Vajjha's [*Packings of Smoothed Polygons*](https://arxiv.org/abs/2405.04331).

- ChatGPT Pro (OpenAI, in ChatGPT) drafted the argument, in the working notes kept in
  [`archive/`](archive/README.md): the reduction to finite normal periods, the five classes of
  switch patterns and their exclusions, the terminal comparison and the equality case, with the
  scalar estimates of each case.
- Claude Opus 5.5 (Anthropic, in Claude Code) wrote the Lean proof and organized it, with
  sub-agents of the same model that stated and proved the stages in parallel, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill. It also wrote the
  axiom audit, the figures, the playground and this documentation.

No person has reviewed the proof. Lean's kernel checks every step.

## Libraries

The proof builds on two Lean libraries by the same author:
[lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon) (Hales and Vajjha's book:
the packing problem, critical lattices, Fejes Tóth's theorem, the control reformulation, the
Pontryagin lift of a minimizer, Theorem 5.0.2, the smoothed octagon and its density) and
[lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control) (Filippov's theorem and the
Pontryagin maximum principle). The definitions of `Palomar/Challenge.lean` are copied from the
first, which is distributed under Apache-2.0 like this project.

## History of the problem

[`prior-work.md`](prior-work.md) lists the work on the Reinhardt problem since 1934 with
references.

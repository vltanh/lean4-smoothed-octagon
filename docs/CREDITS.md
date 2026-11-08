# Credits

The-Anh Vu-Le directed the work and is the author and maintainer of this repository.

## The informal proof

ChatGPT Pro (OpenAI) found the proof, in the research notes of [`archive/`](archive/README.md),
starting from Thomas Hales's formulation of the problem as optimal control on `SL₂(ℝ)` and from
Hales and Vajjha's [*Packings of Smoothed Polygons*](https://arxiv.org/abs/2405.04331). The notes
first closed the argument with seven interval-arithmetic covers computed in C++ with MPFR
([`archive/explorations/`](archive/explorations/README.md)), then replaced all seven by hand
arguments ([`archive/notes/HAND_PROOF_STATUS.md`](archive/notes/HAND_PROOF_STATUS.md)).

## The Lean proof

Claude Opus 5.5 (Anthropic), in Claude Code, wrote the Lean formalization from 7 to 8 November 2026,
coordinating sub-agents that inventoried the notes, stated each stage, and proved the stages in
parallel, and generated Bernstein certificates, checked by `ring`, for the largest polynomial signs;
it also wrote the figures, the playground and this documentation. Five of the largest signs of the
nonshort case follow ChatGPT Pro's lighter hand proofs (pull request #2). The procedure followed the
[formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill (version 3.0.0), with
shorter routes than the notes allowed wherever they exist (marked `Route:` in the docstrings).

The formalization builds on two Lean libraries by the same author:
[lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon) (Hales and Vajjha's book:
the packing problem, critical lattices, Fejes Tóth's theorem, the control reformulation, the
Pontryagin lift of a minimizer, Theorem 5.0.2, the smoothed octagon and its density) and
[lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control) (Filippov's theorem and the
Pontryagin maximum principle). The definitions of `Palomar/Challenge.lean` are copied from the
first, which is distributed under Apache-2.0 like this project.

## History of the problem

[`docs/prior-work.md`](prior-work.md) lists the work on the Reinhardt problem since 1934 with
references.

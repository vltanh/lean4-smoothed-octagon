# Lean 4 research toward the Reinhardt conjecture

This project starts from the concrete smoothed octagon in
[`vltanh/lean4-smoothed-polygon`](https://github.com/vltanh/lean4-smoothed-polygon)
and targets its **global minimality among all centrally symmetric convex disks**, followed
by uniqueness up to affine equivalence.

The candidate density is

\[
\delta_{\mathrm{oct}}=
\frac{8-\sqrt{32}-\log 2}{\sqrt 8-1}.
\]

`SmoothedOctagon/Problem.lean` states the conjecture against the existing geometric
packing definitions, reuses the concrete candidate's exact density, and gives equivalent
closure criteria. The conjecture and affine rigidity remain open propositions.

**Initial source draft. Compilation, typechecking, and CI have not been run.**

Dependencies are pinned to `lean4-smoothed-polygon` commit
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f` and its resolved mathlib commit
`9d581dfff2e41de989072ea63abf3daf69311520`, with Lean `v4.36.0-rc2`.
Access to the private reference repository is needed to resolve the dependency.

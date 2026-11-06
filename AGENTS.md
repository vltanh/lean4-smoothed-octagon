# Working agreement

Develop this project on a dedicated branch and keep the PR description synchronized with
the actual proof status. Make small, mathematically coherent commits.

The current workflow is source-level Lean plus hand proofs. Do not compile Lean, run Lake,
typecheck, or add, modify, or run CI unless the user changes that policy. Record validation
as **not run**; source review is not kernel verification.

Keep `CHECKLIST.md`, `DEEP_AUDIT_CHECKLIST.md`, `SOURCE_MAP.md`, and `README.md` current.
Represent open mathematics as named propositions or documented obligations, never as
an asserted theorem with a proof hole or a new axiom. Keep every conditional result's
hypotheses visible. Do not import the upstream `Challenge` module.

Reuse the pinned `lean4-smoothed-polygon` source modules for existing geometry and
packing-density results. Distinguish a result for its symmetric `(6k+2)` family from a
result about arbitrary smoothed polygons or arbitrary centrally symmetric convex disks.

A finite list of roadmap obligations is not a finite classification of candidate bodies.
Do not advertise a finite case search until its uniform bound and coverage theorem exist.
Report global minimality, affine uniqueness, and kernel validation separately.

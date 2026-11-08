# Archive: the informal proof

This directory keeps the informal proof that the Lean formalization follows, as its author wrote
it. ChatGPT Pro (OpenAI) wrote it in pull request #1 (branch `feat/reinhardt-foundations`), merged
here up to commit `5a6c628`, and the lighter proofs of its largest polynomial signs in pull request
#2 (branch `proof/lighter-signs`), merged up to commit `277c660`. Nothing in it is a premise of the Lean proof. Lean's kernel checks
every step, and the notes serve as the reference the Lean docstrings cite.

| Path | Contents |
| --- | --- |
| [`notes/`](notes) | The proof notes, one Markdown file per result or reduction, with their audits |
| [`notes/legacy/`](notes/legacy) | Earlier versions and snapshots that the notes link to |
| [`lighter-proofs/`](lighter-proofs/README.md) | Lighter hand proofs of the largest polynomial signs, written for the formalization (pull request #2), with errata to the notes |
| [`explorations/`](explorations/README.md) | The computations: the C++/MPFR interval covers, exact-arithmetic scripts and their result records |
| [`AGENTS.md`](AGENTS.md), [`CHECKLIST.md`](CHECKLIST.md), [`DEEP_AUDIT_CHECKLIST.md`](DEEP_AUDIT_CHECKLIST.md), [`SOURCE_MAP.md`](SOURCE_MAP.md) | The directions and checklists that guided the notes' author |

## Where to start

- [`notes/HAND_PROOF_STATUS.md`](notes/HAND_PROOF_STATUS.md): the current state. Every case is now
  proved by hand (gates H-F, H-N, H-S and H-A).
- [`notes/HAND_COST_EQUALITY_THEOREM.md`](notes/HAND_COST_EQUALITY_THEOREM.md): the final theorem
  and its assembly.
- [`notes/GLOBAL_COST_EQUALITY_ASSEMBLY.md`](notes/GLOBAL_COST_EQUALITY_ASSEMBLY.md): the earlier
  assembly, which used seven interval covers.
- [`notes/ACTIVE_MAP.md`](notes/ACTIVE_MAP.md) and [`notes/HANDOFF.md`](notes/HANDOFF.md): reading
  paths through the notes.

## How the Lean proof uses the notes

Lean docstrings name a note by its file name: `MIXED_SMALLER_SHORT_PERIOD_EXCLUSION` is
[`notes/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md`](notes/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).
A `Route:` line in a docstring marks a step that the Lean proof takes differently from the notes,
usually a shorter argument.

The Lean proof follows the hand arguments of the notes for every case; it uses no interval cover.
Five of the largest polynomial signs of the nonshort case follow the lighter proofs of
[`lighter-proofs/`](lighter-proofs/README.md). The largest signs of the smaller-short case (gate H-S)
are proved by generated Bernstein certificates checked by `ring`
(`SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/`, generators in `scripts/certificates/`), or by
shorter routes marked `Route:`.

## Reading the notes

The notes are kept as written. Some of their links point at the original Lean draft of the pull
request, for example `../SmoothedOctagon/BoundaryTrace.lean`; those files now live in
[`SmoothedOctagon/Foundations/`](../../SmoothedOctagon/Foundations). The instructions in `AGENTS.md`
(for example, not to run Lean) were addressed to the notes' author and do not apply to this
repository. No person has reviewed the notes; their "accepted" and "audited" labels record the
author's own reviews.

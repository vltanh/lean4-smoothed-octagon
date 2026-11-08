# Archive: the working notes

This directory keeps the working notes in which the argument was drafted, from 6 to 8 November 2026,
by ChatGPT Pro (OpenAI), in pull requests #1 (branch `feat/reinhardt-foundations`, merged here up to
commit `5a6c628`) and #2 (branch `proof/lighter-signs`, merged up to commit `277c660`). They are kept
as written. The proof of record is the Lean proof; nothing here is one of its premises.

| Path | Contents |
| --- | --- |
| [`notes/`](notes) | The working notes, one Markdown file per result or reduction, with their reviews |
| [`notes/legacy/`](notes/legacy) | Earlier versions and snapshots that the notes link to |
| [`lighter-proofs/`](lighter-proofs/README.md) | Proofs of the largest polynomial signs by small identities and monotonicity arguments |
| [`explorations/`](explorations/README.md) | Computations used while drafting: interval covers in C++ with MPFR, exact-arithmetic scripts and their records |
| [`AGENTS.md`](AGENTS.md), [`CHECKLIST.md`](CHECKLIST.md), [`DEEP_AUDIT_CHECKLIST.md`](DEEP_AUDIT_CHECKLIST.md), [`SOURCE_MAP.md`](SOURCE_MAP.md) | The working directions and checklists of the drafting |

## Where to start

- [`notes/HAND_COST_EQUALITY_THEOREM.md`](notes/HAND_COST_EQUALITY_THEOREM.md): the theorem and its
  assembly.
- [`notes/HAND_PROOF_STATUS.md`](notes/HAND_PROOF_STATUS.md): the cases and where each is proved.
- [`notes/ACTIVE_MAP.md`](notes/ACTIVE_MAP.md) and [`notes/HANDOFF.md`](notes/HANDOFF.md): reading
  paths through the notes.
- [`lighter-proofs/README.md`](lighter-proofs/README.md): the index of the sign proofs.

Lean docstrings cite a note by its file name: `MIXED_SMALLER_SHORT_PERIOD_EXCLUSION` is
[`notes/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md`](notes/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).

## Reading the notes

Some links in the notes point at files of an earlier layout, for example
`../SmoothedOctagon/BoundaryTrace.lean`, now in
[`SmoothedOctagon/Foundations/`](../../SmoothedOctagon/Foundations). The directions in `AGENTS.md`
were addressed to the drafting and do not apply to the repository. No person has reviewed the notes;
their "accepted" and "audited" labels record the drafting's own reviews.

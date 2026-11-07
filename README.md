# Smoothed octagon: a hand and computer-assisted proof

**The hand/computer-assisted proof of the sharp Reinhardt cost bound and affine equality case is complete, with independent internal mathematical and source reviews.** All five sufficient whole-period cases, the terminal comparison and the final dependency audit are closed under the documented external geometric/PMP inputs and arithmetic execution trust boundary. Existing Lean drafts remain unverified; no Lean, Lake, typechecking or CI was run in this programme.

## Main result

Let

\[
\delta_{\rm oct}=\frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]

Every centrally symmetric planar convex disk K satisfies

\[
\delta(K)\ge\delta_{\rm oct},
\]

with equality exactly for the affine images of the smoothed octagon.
The control formulation proves \(C\ge\sqrt{12}\,\delta_{\rm oct}\) for
every trajectory in the original integral admissible class, including
measurable controls. The [final proof and equality argument](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md)
state the quantifiers and explain the passage from actual minimizers to
arbitrary competitors. The [independent dependency audit](docs/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md)
identifies the external inputs and every computational trust boundary.

## Read the completed proof

1. [Authoritative handoff and completion record](docs/HANDOFF.md).
2. [Global cost and affine equality theorem](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md), with its [independent audit](docs/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md).
3. [Uniform M2 theorem](docs/MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md), with its [whole-period audit](docs/MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md).
4. [Certificate replay guide](docs/CERTIFICATE_REPLAY.md), [finite gate ledger](CHECKLIST.md), and [active proof map](docs/ACTIVE_MAP.md).

| Sufficient whole-period case | Accepted exclusion |
| --- | --- |
| R: entirely reverse | [Reverse-period theorem](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION.md) |
| M3: forbidden mixed reverse runs | [Minimum structure](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE.md) |
| M1: all-short mixed | [Whole-period angle theorem](docs/MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md) |
| F: entirely forward with at least six pieces | [Uniform forward theorem](docs/GLOBAL_FORWARD_PERIOD_EXCLUSION.md) |
| M2: mixed with a nonshort forward run | [Uniform mixed theorem](docs/MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md) |

These are assignments of complete minimizing periods. The proof uses
neither growing word-length enumeration nor the refuted unconditional
local L3 shortening assertion.

## The final M2 step

At a global minimum reverse centre, choose the smaller adjacent turn.
The smaller-short case has its accepted 107,977-node cover. For the
nonshort case, a [scalar boundary comparison](docs/MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md)
preserves the incident upper norm and decreases the transported outgoing
norm. It reduces every original maximal chart to two four-variable
charts, including the original delta0-maximal region.

The reverse-next case is excluded by a complete 106,134-node cover.
A common 74,772-node cover proves a>1/2. For the forward-next case,
[Casimir concavity](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md)
places the actual solution between two endpoints and forces at least
one endpoint to satisfy the competitive cap. The [two endpoint covers](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md)
exclude those alternatives in 37,940 and 60,976 nodes. All four new
covers have independent mathematical/source audits and fresh complete
replays, with zero pending or unresolved boxes.

The original and replay logs, frozen source hashes, root domains and
exact leaf accounting are retained with each receipt. To check their
published record consistency:

```sh
python explorations/mixed_nonshort_boundary_records_verify.py
```

The [replay guide](docs/CERTIFICATE_REPLAY.md) gives the C++ commands that
re-execute the quantified covers and the symbolic checks supporting the
hand reductions. A record verifier is separate from an arithmetic replay.

## Scope and repository organization

The proof imports the explicitly identified geometric existence,
balanced-boundary/area and compact-domain results, together with the
standard Pontryagin principles. The [compact-domain source audit](docs/COMPACT_DOMAIN_SOURCE_AUDIT.md)
checks the all-control margin normalization and exact density separation.
Computer-assisted steps trust the reviewed C++ callers, directed
MPFR/GMP arithmetic and execution platform. Internal review does not
constitute external peer review or Lean kernel verification.

- `docs/`: active theorem and independent audit notes; [SOURCE_MAP.md](SOURCE_MAP.md) indexes dependencies.
- `explorations/`: exact identity checkers, frozen cover callers, arithmetic headers, receipts and complete logs.
- `docs/legacy/` and `explorations/legacy/`: historical plans, probes, rejected shortcuts and superseded local investigations. Their old status statements describe earlier stages.
- `SmoothedOctagon/*.lean` and dependency pins: existing formalization drafts, untouched by this hand-proof completion.

The old incomplete three-root nonshort runs are not premises of the
completed boundary proof. The theoretical switch bound \(N<10^{56}\)
is used for finite minimum selection and case coverage, not a catalogue.
